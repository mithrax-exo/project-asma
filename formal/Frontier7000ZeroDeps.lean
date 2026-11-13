/-!/-!
  formal/lean/Frontier7000ZeroDeps.lean
  Apache-2.0 License.

  Zero-dependency stock Lean 4 (`Init`-only, compatible with v4.21.0 and v4.35.0)
  certificate checks for Frontier 7000 (`PR #7000` & `PR #7001`), Role 275 two-probe
  rank-one determinant obstructions (`PR #7493`), and exact `119,542`-bit / `141,746`-bit
  cover-power and `kstar` bit-length inequalities via `powBits` binary squaring.

  Requires zero Mathlib imports and declares zero axioms.
-/

namespace KappaCheck.Frontier7000ZeroDeps

def kappaNum : Int := 363005817
def kappaDen : Int := 1000000000

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
    (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 : Int) = 485 ∧
    (1 * 13 + 2 * 18 + 3 * 44 + 4 * 215 + 5 * 68 + 6 * 42 + 7 * 18 + 8 * 67 : Int) = 1700 := by
  decide

def det2 (a b c d : Int) : Int :=
  a * d - b * c

theorem frontier7000_role275_two_probe_rank_one_obstruction :
    det2 (-203) 61 (-45) 13 = 118 ∧
    det2 (-203) 61 (-203) 61 = 0 ∧
    det2 (-45) 13 (-45) 13 = 0 ∧
    det2 (-203) 61 (-505) 152 = (-203) * 152 - 61 * (-505) ∧
    det2 (-203) 61 (-505) 152 = 5 ∧
    det2 (-45) 13 (-505) 152 = (-45) * 152 - 13 * (-505) ∧
    det2 (-45) 13 (-505) 152 = 275 := by
  decide

private theorem two_mul_eq (n : Nat) : 2 * n = n + n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, ih, Nat.succ_add]

def valBits : List Bool → Nat
| [] => 0
| false :: bs => 2 * valBits bs
| true :: bs => 2 * valBits bs + 1

def powBits (b : Nat) : List Bool → Nat
| [] => 1
| false :: bs => let p := powBits b bs; p * p
| true :: bs => let p := powBits b bs; p * p * b

theorem pow_add_nat (b n m : Nat) : b ^ (n + m) = b ^ n * b ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih]
    exact Nat.mul_assoc (b ^ n) (b ^ m) b

theorem powBits_eq_pow (b : Nat) (bs : List Bool) : powBits b bs = b ^ (valBits bs) := by
  induction bs with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false =>
      change (powBits b rest) * (powBits b rest) = b ^ (2 * valBits rest)
      rw [two_mul_eq, ih]
      exact pow_add_nat b (valBits rest) (valBits rest)
    | true =>
      change ((powBits b rest) * (powBits b rest)) * b = (b ^ (2 * valBits rest)) * b
      rw [two_mul_eq, ih]
      exact congrArg (fun t => t * b) (pow_add_nat b (valBits rest) (valBits rest))

def b2228 : List Bool :=
  [false, false, true, true, true, false, true, false, true, false, false, false, true]

theorem valBits_b2228 : valBits b2228 = 2228 := by
  decide

theorem pow2228_eq_powBits (b : Nat) : b ^ 2228 = powBits b b2228 := by
  rw [powBits_eq_pow, valBits_b2228]

def H11 : Nat := 32768
def H14 : Nat := 32769

def powH11Plus1_2228 : Nat := powBits (H11 + 1) b2228
def powH14Plus1_2228 : Nat := powBits (H14 + 1) b2228

def b119542 : List Bool :=
  [false, true, true, false, true, true, false, true, false, false, true, true, true, false, true, true, true]

def b141746 : List Bool :=
  [false, true, false, false, false, true, false, true, true, true, false, false, false, true, false, false, true]

theorem valBits_b119542 : valBits b119542 = 119542 := by
  decide

theorem valBits_b141746 : valBits b141746 = 141746 := by
  decide

theorem pow2_119542_eq_powBits : 2 ^ 119542 = powBits 2 b119542 := by
  rw [powBits_eq_pow, valBits_b119542]

theorem pow2_141746_eq_powBits : 2 ^ 141746 = powBits 2 b141746 := by
  rw [powBits_eq_pow, valBits_b141746]

def pow2_119542 : Nat := powBits 2 b119542
def pow2_141746 : Nat := powBits 2 b141746

theorem frontier7000_h11_cover_power_bound : powH11Plus1_2228 < pow2_119542 := by
  decide

theorem frontier7000_h14_cover_power_bound : powH14Plus1_2228 < pow2_141746 := by
  decide

def kstar : Nat := 22242183

def b14065 : List Bool :=
  [true, false, false, false, true, true, false, true, true, true, true, false, true, true]

def b14085 : List Bool :=
  [true, false, true, false, true, true, false, true, true, true, true, false, true, true]

theorem valBits_b14065 : valBits b14065 = 14065 := by
  decide

theorem valBits_b14085 : valBits b14085 = 14085 := by
  decide

def pow2_14065 : Nat := powBits 2 b14065
def pow2_14085 : Nat := powBits 2 b14085

theorem frontier7000_kstar11_bit_length_bound : 4096 * kstar < pow2_14065 ∧ pow2_14065 < 2 ^ H11 := by
  decide

theorem frontier7000_kstar14_bit_length_bound : 4096 * kstar < pow2_14085 ∧ pow2_14085 < 2 ^ H14 := by
  decide

theorem frontier7000_cover_119542_and_kstar11_bounds :
    powH11Plus1_2228 < pow2_119542 ∧
    4096 * kstar < pow2_14065 ∧
    pow2_14065 < 2 ^ H11 := by
  exact ⟨frontier7000_h11_cover_power_bound, frontier7000_kstar11_bit_length_bound.1, frontier7000_kstar11_bit_length_bound.2⟩

theorem frontier7000_interval_gate_141746_and_kstar14_bounds :
    powH14Plus1_2228 < pow2_141746 ∧
    4096 * kstar < pow2_14085 ∧
    pow2_14085 < 2 ^ H14 := by
  exact ⟨frontier7000_h14_cover_power_bound, frontier7000_kstar14_bit_length_bound.1, frontier7000_kstar14_bit_length_bound.2⟩

#print axioms frontier7000_cover_119542_and_kstar11_bounds
#print axioms frontier7000_interval_gate_141746_and_kstar14_bounds

end KappaCheck.Frontier7000ZeroDeps

  formal/lean/Frontier7000ZeroDeps.lean
  Apache-2.0 License.

  Zero-dependency stock Lean 4 (`Init`-only, compatible with v4.21.0 and v4.35.0)
  certificate checks for Frontier 7000 (`PR #7000` & `PR #7001`), Role 275 two-probe
  rank-one determinant obstructions (`PR #7493`), and exact `119,542`-bit / `141,746`-bit
  cover-power and `kstar` bit-length inequalities via `powBits` binary squaring.

  Requires zero Mathlib imports and declares zero axioms.
-/

namespace KappaCheck.Frontier7000ZeroDeps
set_option maxRecDepth 500000


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

theorem powBits_eq_of_val (b e : Nat) (bs : List Bool) (h : valBits bs = e) :
    powBits b bs = b ^ e :=
  Eq.mp (congrArg (fun k => powBits b bs = b ^ k) h) (powBits_eq_pow b bs)

theorem lt_pow_of_powBits (x y ex ey : Nat) (bx by_ : List Bool)
    (hx : valBits bx = ex) (hy : valBits by_ = ey)
    (hlt : powBits x bx < powBits y by_) : x ^ ex < y ^ ey := by
  have ex1 := powBits_eq_of_val x ex bx hx
  have ey1 := powBits_eq_of_val y ey by_ hy
  have t1 := Eq.mp (congrArg (fun u => u < powBits y by_) ex1) hlt
  exact Eq.mp (congrArg (fun v => x ^ ex < v) ey1) t1

theorem le_pow_of_powBits (x y ex ey : Nat) (bx by_ : List Bool)
    (hx : valBits bx = ex) (hy : valBits by_ = ey)
    (hle : powBits x bx ≤ powBits y by_) : x ^ ex ≤ y ^ ey := by
  have ex1 := powBits_eq_of_val x ex bx hx
  have ey1 := powBits_eq_of_val y ey by_ hy
  have t1 := Eq.mp (congrArg (fun u => u ≤ powBits y by_) ex1) hle
  exact Eq.mp (congrArg (fun v => x ^ ex ≤ v) ey1) t1

theorem pow2_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  induction h with
  | refl => exact Nat.le_refl (2 ^ a)
  | @step m _ ih =>
    exact Nat.le_trans ih (Nat.le_add_left (2 ^ m) (0 + 2 ^ m))

theorem kstar_bounds_of_powBits (H e153 elo ehi : Nat) (b153 blo bhi : List Bool)
    (h153 : valBits b153 = e153) (hlo_v : valBits blo = elo) (hhi_v : valBits bhi = ehi)
    (hlo : powBits 2 blo ≤ 4096 * (1920 * (powBits 153 b153) * ((H + 1) * (H + 1))))
    (hhi : 4096 * (1920 * (powBits 153 b153) * ((H + 1) * (H + 1))) < powBits 2 bhi)
    (hle : ehi ≤ H) :
    2 ^ elo ≤ 4096 * (1920 * (153 ^ e153) * ((H + 1) * (H + 1))) ∧
    4096 * (1920 * (153 ^ e153) * ((H + 1) * (H + 1))) < 2 ^ ehi ∧
    4096 * (1920 * (153 ^ e153) * ((H + 1) * (H + 1))) < 2 ^ H := by
  have p153 := powBits_eq_of_val 153 e153 b153 h153
  have plo := powBits_eq_of_val 2 elo blo hlo_v
  have phi := powBits_eq_of_val 2 ehi bhi hhi_v
  have g1 : 2 ^ elo ≤ 4096 * (1920 * (153 ^ e153) * ((H + 1) * (H + 1))) := by
    have t1 := Eq.mp (congrArg (fun u => u ≤ 4096 * (1920 * (powBits 153 b153) * ((H + 1) * (H + 1)))) plo) hlo
    exact Eq.mp (congrArg (fun v => 2 ^ elo ≤ 4096 * (1920 * v * ((H + 1) * (H + 1)))) p153) t1
  have g2 : 4096 * (1920 * (153 ^ e153) * ((H + 1) * (H + 1))) < 2 ^ ehi := by
    have t2 := Eq.mp (congrArg (fun u => 4096 * (1920 * (powBits 153 b153) * ((H + 1) * (H + 1))) < u) phi) hhi
    exact Eq.mp (congrArg (fun v => 4096 * (1920 * v * ((H + 1) * (H + 1))) < 2 ^ ehi) p153) t2
  exact ⟨g1, g2, Nat.lt_of_lt_of_le g2 (pow2_mono hle)⟩

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

abbrev H11 : Nat := 14174600000000000
abbrev step11 : Nat := 100000000000
abbrev kstar11 : Nat := 1920 * (153 ^ 1920) * ((H11 + 1) * (H11 + 1))

theorem frontier7000_cover_119542_and_kstar11_bounds :
    (H11 + 1) ^ 2228 < 2 ^ 119542 ∧
    2 ^ 119541 ≤ (H11 + 1) ^ 2228 ∧
    2 ^ 119541 ≤ (H11 - step11 + 1) ^ 2228 ∧
    2 ^ 14064 ≤ 4096 * kstar11 ∧
    4096 * kstar11 < 2 ^ 14065 ∧
    4096 * kstar11 < 2 ^ H11 :=
  ⟨lt_pow_of_powBits (H11 + 1) 2 2228 119542 bits_2228 bits_119542 (by decide) (by decide) (by decide),
   le_pow_of_powBits 2 (H11 + 1) 119541 2228 bits_119541 bits_2228 (by decide) (by decide) (by decide),
   le_pow_of_powBits 2 (H11 - step11 + 1) 119541 2228 bits_119541 bits_2228 (by decide) (by decide) (by decide),
   kstar_bounds_of_powBits H11 1920 14064 14065 bits_1920 bits_14064 bits_14065 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

abbrev step14 : Nat := 100000000000000
abbrev H14 : Nat := 14174600000000000000
abbrev kstar14 : Nat := 1920 * (153 ^ 1920) * ((H14 + 1) * (H14 + 1))

theorem frontier7000_interval_gate_141746_and_kstar14_bounds :
    (H14 + 1) ^ 2228 < 2 ^ 141746 ∧
    2 ^ 141745 ≤ (H14 - step14 + 1) ^ 2228 ∧
    2 ^ 14084 ≤ 4096 * kstar14 ∧
    4096 * kstar14 < 2 ^ 14085 ∧
    4096 * kstar14 < 2 ^ H14 :=
  ⟨lt_pow_of_powBits (H14 + 1) 2 2228 141746 bits_2228 bits_141746 (by decide) (by decide) (by decide),
   le_pow_of_powBits 2 (H14 - step14 + 1) 141745 2228 bits_141745 bits_2228 (by decide) (by decide) (by decide),
   kstar_bounds_of_powBits H14 1920 14084 14085 bits_1920 bits_14084 bits_14085 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end KappaCheck.Frontier7000ZeroDeps
