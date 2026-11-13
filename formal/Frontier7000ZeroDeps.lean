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
def kappaDen : Int := 1000000000

theorem frontier7000_kappa_hierarchy_and_supplier_margin :
    kappaNum * 32768 > 118 * kappaDen /\
    kappaNum * 32768 < 119 * kappaDen /\
    kappaNum * 1000000000 > 3125804 * kappaDen /\
    385248 * 1000 - kappaNum = 22242183 /\
    (22242183 : Int) > 0 /\
    (826790496 : Int) < 1000000000 /\
    ¬ (kappaNum ≥ 385248 * 1000) := by
  decide

theorem frontier7000_unit_job_and_rank_mass_ledger :
    (4075 + 828 + 811 + 241 + 320 + 17 + 12 + 6 : Int) = 6310 /\
    (1 * 4075 + 2 * 828 + 3 * 811 + 4 * 241 + 5 * 320 + 6 * 17 + 7 * 12 + 8 * 6 : Int) = 10962 /\
    (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 + 595 : Int) = 1080 /\
    (1 * 13 + 2 * 18 + 3 * 44 + 4 * 215 + 5 * 68 + 6 * 42 + 7 * 18 + 8 * 67 + 9 * 595 : Int) = 7650 /\
    (13 + 18 + 44 + 215 + 68 + 42 + 18 + 67 : Int) = 485 /\
    (1 * 13 + 2 * 18 + 3 * 44 + 4 * 215 + 5 * 68 + 6 * 42 + 7 * 18 + 8 * 67 : Int) = 1700 := by
  decide

def det2 (a b c d : Int) : Int := a * d - b * c

theorem frontier7000_role275_two_probe_rank_one_obstruction :
    det2 (-203) 61 (-45) 13 = 118 /\
    det2 (-203) 61 (-203) 61 = 0 /\
    det2 (-45) 13 (-45) 13 = 0 /\
    det2 (-203) 61 (-505) 152 = (-203) * 152 - 61 * (-505) /\
    det2 (-203) 61 (-505) 152 = 5 /\
    det2 (-45) 13 (-505) 152 = (-45) * 152 - 13 * (-505) /\
    det2 (-45) 13 (-505) 152 = 275 := by
  decide

def powBits (base : Nat) : List Bool → Nat
  | [] => 1
  | true :: bs => base * (powBits base bs)^2
  | false :: bs => (powBits base bs)^2

theorem powBits_nil (base : Nat) : powBits base [] = 1 := rfl

theorem powBits_cons (base : Nat) (b : Bool) (bs : List Bool) :
    powBits base (b :: bs) = if b then base * (powBits base bs)^2 else (powBits base bs)^2 := by
  cases b <;> rfl

def valBits : List Bool → Nat
  | [] => 0
  | true :: bs => 1 + 2 * valBits bs
  | false :: bs => 2 * valBits bs

theorem powBits_eq_pow (base : Nat) (bs : List Bool) :
    powBits base bs = base ^ valBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · change (powBits base bs)^2 = base ^ (2 * valBits bs)
      rw [ih, Nat.pow_mul]
    · change base * (powBits base bs)^2 = base ^ (1 + 2 * valBits bs)
      rw [ih, Nat.pow_add, Nat.pow_one, Nat.pow_mul]

def b2228 : List Bool :=
  [false, true, true, true, true, false, true, false, true, false, false, true]

theorem valBits_b2228 : valBits b2228 = 2228 := by
  decide

theorem powHPlus1_2228_eq_powBits (H : Nat) :
    (H + 1) ^ 2228 = powBits (H + 1) b2228 := by
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

theorem frontier7000_kstar11_bit_length_bound : 4096 * kstar < pow2_14065 /\ pow2_14065 < 2 ^ H11 := by
  decide

theorem frontier7000_kstar14_bit_length_bound : 4096 * kstar < pow2_14085 /\ pow2_14085 < 2 ^ H14 := by
  decide

theorem frontier7000_cover_119542_and_kstar11_bounds :
    powH11Plus1_2228 < pow2_119542 /\
    4096 * kstar < pow2_14065 /\
    pow2_14065 < 2 ^ H11 := by
  exact ⟨frontier7000_h11_cover_power_bound, frontier7000_kstar11_bit_length_bound.1, frontier7000_kstar11_bit_length_bound.2⟩

theorem frontier7000_interval_gate_141746_and_kstar14_bounds :
    powH14Plus1_2228 < pow2_141746 /\
    4096 * kstar < pow2_14085 /\
    pow2_14085 < 2 ^ H14 := by
  exact ⟨frontier7000_h14_cover_power_bound, frontier7000_kstar14_bit_length_bound.1, frontier7000_kstar14_bit_length_bound.2⟩

#print axioms frontier7000_cover_119542_and_kstar11_bounds
#print axioms frontier7000_interval_gate_141746_and_kstar14_bounds

end KappaCheck.Frontier7000ZeroDeps
