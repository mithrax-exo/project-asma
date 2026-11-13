/-!
  formal/lean/Frontier7000ZeroDeps.lean
  Apache-2.0 License.

  Zero-dependency stock Lean 4 (`Init`-only, compatible with v4.21.0 and v4.35.0)
  certificate checks for Frontier 7000 (`PR #7000` & `PR #7001`), Role 275 two-probe
  rank-one determinant obstructions (`PR #7493`), and exact `119,542`-bit / `141,746`-bit
  cover-power and `kstar` bit-length inequalities via 18-step binary squaring (`powBits`).

  Requires zero Mathlib imports and declares zero axioms.
-/

namespace KappaCheck.Frontier7000ZeroDeps

def kappaNum : Int := 363005817
def kappaDen : Int := 100000000000

theorem frontier7000_kappa_hierarchy_and_supplier_margin :
    kappaNum * 32768 > 118 * kappaDen ∧
    kappaNum * 32768 < 119 * kappaDen ∧
    kappaNum * 1000000000 > 3125804 * kappaDen ∧
    385248 * 1000 - kappaNum = 22242183 ∧
    (22242183 : Int) > 0 ∧
    (826790496 : Int) < 1000000000 ∧
    ¬ (kappaNum ≥ 385248 * 1000) := by
  decide

theorem frontier7000_unit_job_and_rank_mass_ledger :
    (4075 + 828 + 811 + 241 + 320 + 17 + 12 + 6 : Int) = 6310 ∧
    (1 * 4075 + 2 * 828 + 3 * 811 + 4 * 241 + 5 * 320 + 6 * 17 + 7 * 12 + 8 * 6 : Int) = 10962 ∧
    (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 + 595 : Int) = 1080 ∧
    (1 * 13 + 2 * 18 + 3 * 44 + 4 * 215 + 5 * 68 + 6 * 42 + 7 * 18 + 8 * 67 + 9 * 595 : Int) = 7650 ∧
    (6310 + 1080 : Int) = 7390 ∧
    (10962 + 7650 : Int) = 18612 ∧
    (400 + 1080 - 192 : Int) = 1288 ∧
    (7390 - 192 : Int) = 7198 ∧
    (18612 - 192 : Int) = 18420 ∧
    (0 : Int) < 1125 ∧
    (1125 : Int) < 1520 := by
  decide

theorem rank_one_probe_det_zero (s1 s2 a b : Int) :
    (s1 * a) * (s2 * b) - (s1 * b) * (s2 * a) = 0 := by
  have h : (s1 * a) * (s2 * b) = (s1 * b) * (s2 * a) :=
    calc
      (s1 * a) * (s2 * b) = s1 * (a * (s2 * b)) := Int.mul_assoc s1 a (s2 * b)
      _ = s1 * ((s2 * b) * a) := congrArg (fun t => s1 * t) (Int.mul_comm a (s2 * b))
      _ = s1 * (s2 * (b * a)) := congrArg (fun t => s1 * t) (Int.mul_assoc s2 b a)
      _ = s1 * (s2 * (a * b)) := congrArg (fun t => s1 * (s2 * t)) (Int.mul_comm b a)
      _ = s1 * ((a * b) * s2) := congrArg (fun t => s1 * t) (Int.mul_comm s2 (a * b))
      _ = s1 * (a * (b * s2)) := congrArg (fun t => s1 * t) (Int.mul_assoc a b s2)
      _ = s1 * ((b * s2) * a) := congrArg (fun t => s1 * t) (Int.mul_comm a (b * s2))
      _ = s1 * (b * (s2 * a)) := congrArg (fun t => s1 * t) (Int.mul_assoc b s2 a)
      _ = (s1 * b) * (s2 * a) := (Int.mul_assoc s1 b (s2 * a)).symm
  rw [h, Int.sub_self]

theorem rank_one_fusion_impossible (s1 s2 a b u1 u2 v1 v2 : Int)
    (hdet : u1 * v2 - u2 * v1 ≠ 0) :
    ¬ (u1 = s1 * a ∧ u2 = s1 * b ∧ v1 = s2 * a ∧ v2 = s2 * b) := by
  intro ⟨hu1, hu2, hv1, hv2⟩
  apply hdet
  rw [hu1, hu2, hv1, hv2]
  exact rank_one_probe_det_zero s1 s2 a b

theorem role275_fixed_fusion_impossible (s1 s2 a b : Int) :
    ¬ ((2 : Int) = s1 * a ∧ (-1 : Int) = s1 * b ∧ (2 : Int) = s2 * a ∧ (1 : Int) = s2 * b) :=
  rank_one_fusion_impossible s1 s2 a b 2 (-1) 2 1 (by decide)

def valBits : List Bool → Nat
  | [] => 0
  | false :: bs => valBits bs + valBits bs
  | true :: bs => (valBits bs + valBits bs) + 1

def powBits (b : Nat) : List Bool → Nat
  | [] => 1
  | false :: bs =>
    let p := powBits b bs
    p * p
  | true :: bs =>
    let p := powBits b bs
    (p * p) * b

theorem pow_add_nat (b m n : Nat) : (b ^ m) * (b ^ n) = b ^ (m + n) := by
  induction n with
  | zero => exact Nat.mul_one (b ^ m)
  | succ k ih =>
    calc
      (b ^ m) * ((b ^ k) * b) = ((b ^ m) * (b ^ k)) * b := (Nat.mul_assoc (b ^ m) (b ^ k) b).symm
      _ = (b ^ (m + k)) * b := congrArg (fun t => t * b) ih

theorem powBits_eq_pow (b : Nat) (bs : List Bool) : powBits b bs = b ^ (valBits bs) := by
  induction bs with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false =>
      change (powBits b rest) * (powBits b rest) = b ^ (valBits rest + valBits rest)
      rw [ih]
      exact pow_add_nat b (valBits rest) (valBits rest)
    | true =>
      change ((powBits b rest) * (powBits b rest)) * b = (b ^ (valBits rest + valBits rest)) * b
      rw [ih]
      exact congrArg (fun t => t * b) (pow_add_nat b (valBits rest) (valBits rest))

theorem pow2_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  induction h with
  | refl => exact Nat.le_refl (2 ^ a)
  | @step m _ ih =>
    exact Nat.le_trans ih (Nat.le_add_left (2 ^ m) (0 + 2 ^ m))

def bits_2228 : List Bool := [false, false, true, false, true, true, false, true, false, false, false, true]
def bits_1920 : List Bool := [false, false, false, false, false, false, false, true, true, true, true]
def bits_119542 : List Bool := [false, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, true]
def bits_119541 : List Bool := [true, false, true, false, true, true, true, true, false, true, false, false, true, false, true, true, true]
def bits_14064 : List Bool := [false, false, false, false, true, true, true, true, false, true, true, false, true, true]
def bits_14065 : List Bool := [true, false, false, false, true, true, true, true, false, true, true, false, true, true]
def bits_141746 : List Bool := [false, true, false, false, true, true, false, true, true, false, false, true, false, true, false, false, false, true]
def bits_141745 : List Bool := [true, false, false, false, true, true, false, true, true, false, false, true, false, true, false, false, false, true]
def bits_14084 : List Bool := [false, false, true, false, false, false, false, false, true, true, true, false, true, true]
def bits_14085 : List Bool := [true, false, true, false, false, false, false, false, true, true, true, false, true, true]

def H11 : Nat := 14174600000000000
def step11 : Nat := 100000000000
def kstar11 : Nat := 1920 * (153 ^ 1920) * ((H11 + 1) ^ 2)

theorem frontier7000_cover_119542_and_kstar11_bounds :
    (H11 + 1) ^ 2228 < 2 ^ 119542 ∧
    2 ^ 119541 ≤ (H11 + 1) ^ 2228 ∧
    2 ^ 119541 ≤ (H11 - step11 + 1) ^ 2228 ∧
    2 ^ 14064 ≤ 4096 * kstar11 ∧
    4096 * kstar11 < 2 ^ 14065 ∧
    4096 * kstar11 < 2 ^ H11 := by
  have h1 : powBits 14174600000000001 bits_2228 < powBits 2 bits_119542 := by decide
  have h2 : powBits 2 bits_119541 ≤ powBits 14174600000000001 bits_2228 := by decide
  have h3 : powBits 2 bits_119541 ≤ powBits 14174500000000001 bits_2228 := by decide
  have hk_lo : powBits 2 bits_14064 ≤ 4096 * (1920 * powBits 153 bits_1920 * ((H11 + 1) ^ 2)) := by decide
  have hk_hi : 4096 * (1920 * powBits 153 bits_1920 * ((H11 + 1) ^ 2)) < powBits 2 bits_14065 := by decide
  have eb1 : powBits 14174600000000001 bits_2228 = (H11 + 1) ^ 2228 := powBits_eq_pow (H11 + 1) bits_2228
  have eb2 : powBits 14174500000000001 bits_2228 = (H11 - step11 + 1) ^ 2228 := powBits_eq_pow (H11 - step11 + 1) bits_2228
  have e42 : powBits 2 bits_119542 = 2 ^ 119542 := powBits_eq_pow 2 bits_119542
  have e41 : powBits 2 bits_119541 = 2 ^ 119541 := powBits_eq_pow 2 bits_119541
  have e153 : powBits 153 bits_1920 = 153 ^ 1920 := powBits_eq_pow 153 bits_1920
  have e64 : powBits 2 bits_14064 = 2 ^ 14064 := powBits_eq_pow 2 bits_14064
  have e65 : powBits 2 bits_14065 = 2 ^ 14065 := powBits_eq_pow 2 bits_14065
  rw [eb1, e42] at h1
  rw [e41, eb1] at h2
  rw [e41, eb2] at h3
  rw [e64, e153] at hk_lo
  rw [e153, e65] at hk_hi
  have hle : 14065 ≤ H11 := by decide
  exact ⟨h1, h2, h3, hk_lo, hk_hi, Nat.lt_of_lt_of_le hk_hi (pow2_mono hle)⟩

def step14 : Nat := 100000000000000
def H14 : Nat := 14174600000000000000
def kstar14 : Nat := 1920 * (153 ^ 1920) * ((H14 + 1) ^ 2)

theorem frontier7000_interval_gate_141746_and_kstar14_bounds :
    (H14 + 1) ^ 2228 < 2 ^ 141746 ∧
    2 ^ 141745 ≤ (H14 - step14 + 1) ^ 2228 ∧
    2 ^ 14084 ≤ 4096 * kstar14 ∧
    4096 * kstar14 < 2 ^ 14085 ∧
    4096 * kstar14 < 2 ^ H14 := by
  have h1 : powBits 14174600000000000001 bits_2228 < powBits 2 bits_141746 := by decide
  have h2 : powBits 2 bits_141745 ≤ powBits 14174500000000000001 bits_2228 := by decide
  have hk_lo : powBits 2 bits_14084 ≤ 4096 * (1920 * powBits 153 bits_1920 * ((H14 + 1) ^ 2)) := by decide
  have hk_hi : 4096 * (1920 * powBits 153 bits_1920 * ((H14 + 1) ^ 2)) < powBits 2 bits_14085 := by decide
  have eb1 : powBits 14174600000000000001 bits_2228 = (H14 + 1) ^ 2228 := powBits_eq_pow (H14 + 1) bits_2228
  have eb2 : powBits 14174500000000000001 bits_2228 = (H14 - step14 + 1) ^ 2228 := powBits_eq_pow (H14 - step14 + 1) bits_2228
  have e46 : powBits 2 bits_141746 = 2 ^ 141746 := powBits_eq_pow 2 bits_141746
  have e45 : powBits 2 bits_141745 = 2 ^ 141745 := powBits_eq_pow 2 bits_141745
  have e153 : powBits 153 bits_1920 = 153 ^ 1920 := powBits_eq_pow 153 bits_1920
  have e84 : powBits 2 bits_14084 = 2 ^ 14084 := powBits_eq_pow 2 bits_14084
  have e85 : powBits 2 bits_14085 = 2 ^ 14085 := powBits_eq_pow 2 bits_14085
  rw [eb1, e46] at h1
  rw [e45, eb2] at h2
  rw [e84, e153] at hk_lo
  rw [e153, e85] at hk_hi
  have hle : 14085 ≤ H14 := by decide
  exact ⟨h1, h2, hk_lo, hk_hi, Nat.lt_of_lt_of_le hk_hi (pow2_mono hle)⟩

end KappaCheck.Frontier7000ZeroDeps
  
