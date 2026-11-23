import ReciprocityTheory.DualLattices.SubMemOfCompat

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem surjective_ainfTower_zero : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y

theorem ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)

theorem ainf_zeta0 (h2 : p = 2) :
    (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = -1 := by
  have hz : (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt := by
    show zetaV p O ε 0 = _
    simp [zetaV, root, fontaineTheta_teichmuller]
  rw [hz]
  clear hz
  haveI : NoZeroDivisors O :=
    hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  set z := ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt with hzdef
  clear_value z
  rw [h2] at hε
  exact hε.eq_neg_one_of_two_right

end ReciprocityTheory.PGsh.Be2
