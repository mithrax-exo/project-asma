/-!
  formal/lean/Frontier7000ZeroDeps.lean
  Apache-2.0 License.

  Zero-dependency stock Lean 4 ('Init'-only, compatible with v4.21.0 and v4.35.0)
  certificate checks for Frontier 7000 ('PR #7000' & 'PR #7001'), Role 275 two-probe
  rank-one determinant obstructions ('PR #7493'), and exact '119,542'-bit / '141,746'-bit
  cover-power and 'kstar' bit-length inequalities via 'powBits' binary squaring.

  Requires zero Mathlib imports and declares zero axioms.
-/

namespace KappaCheck.Frontier7000ZeroDeps

def kappaNum : Int := 363005817
def kappaDen : Int := 100000000000

theorem frontier7000_kappa_hierarchy_and_supplier_margin :
    kappaNum * 32768 > 118 * kappaDen /\
    kappaNum * 32768 < 119 * kappaDen /\
    kappaNum * 1000000000 > 3125804 * kappaDen /\
    385248 * 1000 - kappaNum = 22242183 /\
    (22242183 : Int) > 0 /\
    (826790496 : Int) < 1000000000 /\
    Not (kappaNum >= 385248 * 1000) := by
  decide

theorem frontier7000_unit_job_and_rank_mass_ledger :
    (4075 + 828 + 811 + 241 + 320 + 17 + 12 + 6 : Int) = 6310 /\
    (1 * 4075 + 2 * 828 + 3 * 811 + 4 * 241 + 5 * 320 + 6 * 17 + 7 * 12 + 8 * 6 : Int) = 10962 /\
    (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 + 595 : Int) = 1080 /\
    (1 * 13 + 2 * 18 + 3 * 44 + 4 * 215 + 5 * 68 + 6 * 42 + 7 * 18 + 8 * 67 + 9 * 595 : Int) = 7650 /\
    (6310 + 1080 : Int) = 7390 /\
    (10962 + 7650 : Int) = 18612 /\
    (400 + 1080 - 192 : Int) = 1288 /\
    (7390 - 192 : Int) = 7198 /\
    (18612 - 192 : Int) = 18420 /\
    (0 : Int) < 1125 /\
    (1125 : Int) < 1520 := by
  decide

theorem rank_one_probe_det_zero (s1 s2 a b : Int) :
    (s1 * a) * (s2 * b) - (s1 * b) * (s2 * a) = 0 := by
  have h1 : (s1 * a) * (s2 * b) = (s1 * s2) * (a * b) := by
    calc
      (s1 * a) * (s2 * b) = s1 * (a * (s2 * b)) := Int.mul_assoc s1 a (s2 * b)
      _ = s1 * ((a * s2) * b) := by rw [Int.mul_assoc a s2 b]
      _ = s1 * ((s2 * a) * b) := by rw [Int.mul_comm a s2]
      _ = s1 * (s2 * (a * b)) := by rw [Int.mul_assoc s2 a b]
      _ = (s1 * s2) * (a * b) := (Int.mul_assoc s1 s2 (a * b)).symm
  have h2 : (s1 * b) * (s2 * a) = (s1 * s2) * (a * b) := by
    calc
      (s1 * b) * (s2 * a) = s1 * (b * (s2 * a)) := Int.mul_assoc s1 b (s2 * a)
      _ = s1 * ((b * s2) * a) := by rw [Int.mul_assoc b s2 a]
      _ = s1 * ((s2 * b) * a) := by rw [Int.mul_comm b s2]
      _ = s1 * (s2 * (b * a)) := by rw [Int.mul_assoc s2 b a]
      _ = s1 * (s2 * (a * b)) := by rw [Int.mul_comm b a]
      _ = (s1 * s2) * (a * b) := (Int.mul_assoc s1 s2 (a * b)).symm
  rw [h1, h2, Int.sub_self]

theorem rank_one_fusion_impossible
    (s1 s2 a b u1 u2 v1 v2 : Int)
    (hdet : Not (u1 * v2 - u2 * v1 = 0)) :
    Not (u1 = s1 * a /\ u2 = s1 * b /\ v1 = s2 * a /\ v2 = s2 * b) := by
  intro h
  apply hdet
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  exact rank_one_probe_det_zero s1 s2 a b

theorem role275_fixed_fusion_impossible (s1 s2 a b : Int) :
    Not ((2 : Int) = s1 * a /\ (-1 : Int) = s1 * b /\ (2 : Int) = s2 * a /\ (1 : Int) = s2 * b) :=
  rank_one_fusion_impossible s1 s2 a b 2 (-1) 2 1 (by decide)

theorem pow2_add (a b : Nat) : (2 ^ a) * (2 ^ b) = 2 ^ (a + b) := by
  induction b with
  | zero => exact (Nat.mul_one (2 ^ a)).symm
  | succ k ih =>
      calc
        (2 ^ a) * (2 ^ (k + 1)) = (2 ^ a) * ((2 ^ k) * 2) := rfl
        _ = ((2 ^ a) * (2 ^ k)) * 2 := (Nat.mul_assoc (2 ^ a) (2 ^ k) 2).symm
        _ = (2 ^ (a + k)) * 2 := congrArg (fun t => t * 2) ih
        _ = 2 ^ (a + (k + 1)) := rfl

theorem pow2_mono {a b : Nat} (h : a <= b) : 2 ^ a <= 2 ^ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
      exact Nat.le_trans ih (Nat.le_mul_of_pos_right (2 ^ m) (by decide : 0 < 2))
def valBits : List Bool -> Nat
  | [] => 0
  | false :: bs => 2 * valBits bs
  | true :: bs => 2 * valBits bs + 1

def powBits (b : Nat) : List Bool -> Nat
  | [] => 1
  | false :: bs => let p := powBits b bs; p * p
  | true :: bs => let p := powBits b bs; p * p * b

theorem succ_add_eq (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) :=
  Nat.succ_add n m

theorem two_mul_eq (n : Nat) : 2 * n = n + n :=
  Nat.two_mul n

theorem pow_add_eq (b m n : Nat) : b ^ (m + n) = (b ^ m) * (b ^ n) := by
  induction n with
  | zero => exact (Nat.mul_one (b ^ m)).symm
  | succ k ih =>
      calc
        b ^ (m + Nat.succ k) = (b ^ (m + k)) * b := rfl
        _ = ((b ^ m) * (b ^ k)) * b := congrArg (fun t => t * b) ih
        _ = (b ^ m) * ((b ^ k) * b) := Nat.mul_assoc (b ^ m) (b ^ k) b

theorem powBits_eq_pow (b : Nat) : (bs : List Bool) -> powBits b bs = b ^ valBits bs
  | [] => rfl
  | false :: bs => by
      have ih := powBits_eq_pow b bs
      calc
        powBits b (false :: bs) = powBits b bs * powBits b bs := rfl
        _ = (b ^ valBits bs) * (b ^ valBits bs) := congrArg (fun t => t * t) ih
        _ = b ^ (valBits bs + valBits bs) := (pow_add_eq b (valBits bs) (valBits bs)).symm
        _ = b ^ (2 * valBits bs) := congrArg (fun t => b ^ t) (two_mul_eq (valBits bs)).symm
  | true :: bs => by
      have ih := powBits_eq_pow b bs
      calc
        powBits b (true :: bs) = (powBits b bs * powBits b bs) * b := rfl
        _ = ((b ^ valBits bs) * (b ^ valBits bs)) * b := congrArg (fun t => (t * t) * b) ih
        _ = (b ^ (valBits bs + valBits bs)) * b := congrArg (fun t => t * b) (pow_add_eq b (valBits bs) (valBits bs)).symm
        _ = (b ^ (2 * valBits bs)) * b := congrArg (fun t => (b ^ t) * b) (two_mul_eq (valBits bs)).symm
        _ = b ^ (2 * valBits bs + 1) := rfl

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

theorem lt_pow_of_powBits
    (b1 : Nat) (bs1 : List Bool) (e1 : Nat) (he1 : valBits bs1 = e1)
    (b2 : Nat) (bs2 : List Bool) (e2 : Nat) (he2 : valBits bs2 = e2)
    (h : powBits b1 bs1 < powBits b2 bs2) :
    b1 ^ e1 < b2 ^ e2 := by
  have h1 : powBits b1 bs1 = b1 ^ e1 :=
    Eq.trans (powBits_eq_pow b1 bs1) (congrArg (fun t => b1 ^ t) he1)
  have h2 : powBits b2 bs2 = b2 ^ e2 :=
    Eq.trans (powBits_eq_pow b2 bs2) (congrArg (fun t => b2 ^ t) he2)
  exact Eq.mp (congrArg (fun t => b1 ^ e1 < t) h2) (Eq.mp (congrArg (fun t => t < powBits b2 bs2) h1) h)

theorem le_pow_of_powBits
    (b1 : Nat) (bs1 : List Bool) (e1 : Nat) (he1 : valBits bs1 = e1)
    (b2 : Nat) (bs2 : List Bool) (e2 : Nat) (he2 : valBits bs2 = e2)
    (h : powBits b1 bs1 <= powBits b2 bs2) :
    b1 ^ e1 <= b2 ^ e2 := by
  have h1 : powBits b1 bs1 = b1 ^ e1 :=
    Eq.trans (powBits_eq_pow b1 bs1) (congrArg (fun t => b1 ^ t) he1)
  have h2 : powBits b2 bs2 = b2 ^ e2 :=
    Eq.trans (powBits_eq_pow b2 bs2) (congrArg (fun t => b2 ^ t) he2)
  exact Eq.mp (congrArg (fun t => b1 ^ e1 <= t) h2) (Eq.mp (congrArg (fun t => t <= powBits b2 bs2) h1) h)

theorem kstar_bounds_of_powBits
    (H : Nat)
    (bs_lo : List Bool) (e_lo : Nat) (he_lo : valBits bs_lo = e_lo)
    (bs_hi : List Bool) (e_hi : Nat) (he_hi : valBits bs_hi = e_hi)
    (he1920 : valBits bits_1920 = 1920)
    (h_lo : powBits 2 bs_lo <= 4096 * (1920 * powBits 153 bits_1920 * ((H + 1) ^ 2)))
    (h_hi : 4096 * (1920 * powBits 153 bits_1920 * ((H + 1) ^ 2)) < powBits 2 bs_hi) :
    2 ^ e_lo <= 4096 * (1920 * (153 ^ 1920) * ((H + 1) ^ 2)) /\
    4096 * (1920 * (153 ^ 1920) * ((H + 1) ^ 2)) < 2 ^ e_hi := by
  have hp1920 : powBits 153 bits_1920 = 153 ^ 1920 :=
    Eq.trans (powBits_eq_pow 153 bits_1920) (congrArg (fun t => 153 ^ t) he1920)
  have hplo : powBits 2 bs_lo = 2 ^ e_lo :=
    Eq.trans (powBits_eq_pow 2 bs_lo) (congrArg (fun t => 2 ^ t) he_lo)
  have hphi : powBits 2 bs_hi = 2 ^ e_hi :=
    Eq.trans (powBits_eq_pow 2 bs_hi) (congrArg (fun t => 2 ^ t) he_hi)
  have h1 : 2 ^ e_lo <= 4096 * (1920 * (153 ^ 1920) * ((H + 1) ^ 2)) :=
    Eq.mp (congrArg (fun t => 2 ^ e_lo <= 4096 * (1920 * t * ((H + 1) ^ 2))) hp1920)
      (Eq.mp (congrArg (fun t => t <= 4096 * (1920 * powBits 153 bits_1920 * ((H + 1) ^ 2))) hplo) h_lo)
  have h2 : 4096 * (1920 * (153 ^ 1920) * ((H + 1) ^ 2)) < 2 ^ e_hi :=
    Eq.mp (congrArg (fun t => 4096 * (1920 * t * ((H + 1) ^ 2)) < 2 ^ e_hi) hp1920)
      (Eq.mp (congrArg (fun t => 4096 * (1920 * powBits 153 bits_1920 * ((H + 1) ^ 2)) < t) hphi) h_hi)
  exact And.intro h1 h2

def H11 : Nat := 14174600000000000
def step11 : Nat := 100000000000
def kstar11 : Nat := 1920 * (153 ^ 1920) * ((H11 + 1) ^ 2)

theorem frontier7000_cover_119542_and_kstar11_bounds :
    (H11 + 1) ^ 2228 < 2 ^ 119542 /\
    2 ^ 119541 <= (H11 + 1) ^ 2228 /\
    2 ^ 119541 <= (H11 - step11 + 1) ^ 2228 /\
    2 ^ 14064 <= 4096 * kstar11 /\
    4096 * kstar11 < 2 ^ 14065 /\
    4096 * kstar11 < 2 ^ H11 := by
  have h1 : (H11 + 1) ^ 2228 < 2 ^ 119542 :=
    lt_pow_of_powBits (H11 + 1) bits_2228 2228 (by decide)
      2 bits_119542 119542 (by decide) (by decide)
  have h2a : 2 ^ 119541 <= (H11 + 1) ^ 2228 :=
    le_pow_of_powBits 2 bits_119541 119541 (by decide)
      (H11 + 1) bits_2228 2228 (by decide) (by decide)
  have h2b : 2 ^ 119541 <= (H11 - step11 + 1) ^ 2228 :=
    le_pow_of_powBits 2 bits_119541 119541 (by decide)
      (H11 - step11 + 1) bits_2228 2228 (by decide) (by decide)
  have hk :
      2 ^ 14064 <= 4096 * kstar11 /\
      4096 * kstar11 < 2 ^ 14065 :=
    kstar_bounds_of_powBits H11
      bits_14064 14064 (by decide)
      bits_14065 14065 (by decide)
      (by decide) (by decide) (by decide)
  have hlt : 4096 * kstar11 < 2 ^ H11 :=
    Nat.lt_of_lt_of_le hk.2 (pow2_mono (by decide : 14065 <= H11))
  exact And.intro h1 (And.intro h2a (And.intro h2b (And.intro hk.1 (And.intro hk.2 hlt))))

def step14 : Nat := 100000000000000
def H14 : Nat := 14174600000000000000
def kstar14 : Nat := 1920 * (153 ^ 1920) * ((H14 + 1) ^ 2)

theorem frontier7000_interval_gate_141746_and_kstar14_bounds :
    (H14 + 1) ^ 2228 < 2 ^ 141746 /\
    2 ^ 141745 <= (H14 - step14 + 1) ^ 2228 /\
    2 ^ 14084 <= 4096 * kstar14 /\
    4096 * kstar14 < 2 ^ 14085 /\
    4096 * kstar14 < 2 ^ H14 := by
  have h1 : (H14 + 1) ^ 2228 < 2 ^ 141746 :=
    lt_pow_of_powBits (H14 + 1) bits_2228 2228 (by decide)
      2 bits_141746 141746 (by decide) (by decide)
  have h2 : 2 ^ 141745 <= (H14 - step14 + 1) ^ 2228 :=
    le_pow_of_powBits 2 bits_141745 141745 (by decide)
      (H14 - step14 + 1) bits_2228 2228 (by decide) (by decide)
  have hk :
      2 ^ 14084 <= 4096 * kstar14 /\
      4096 * kstar14 < 2 ^ 14085 :=
    kstar_bounds_of_powBits H14
      bits_14084 14084 (by decide)
      bits_14085 14085 (by decide)
      (by decide) (by decide) (by decide)
  have hlt : 4096 * kstar14 < 2 ^ H14 :=
    Nat.lt_of_lt_of_le hk.2 (pow2_mono (by decide : 14085 <= H14))
  exact And.intro h1 (And.intro h2 (And.intro hk.1 (And.intro hk.2 hlt)))

end KappaCheck.Frontier7000ZeroDeps

#print axioms KappaCheck.Frontier7000ZeroDeps.frontier7000_kappa_hierarchy_and_supplier_margin
#print axioms KappaCheck.Frontier7000ZeroDeps.frontier7000_unit_job_and_rank_mass_ledger
#print axioms KappaCheck.Frontier7000ZeroDeps.role275_fixed_fusion_impossible
#print axioms KappaCheck.Frontier7000ZeroDeps.frontier7000_cover_119542_and_kstar11_bounds
#print axioms KappaCheck.Frontier7000ZeroDeps.frontier7000_interval_gate_141746_and_kstar14_bounds

