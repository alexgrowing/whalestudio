import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.QkRationalExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkNumberField

theorem exists_ringHom_extend {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed F] (M : IntermediateField K L) (f : M →+* F) : ∃ σ : L →+* F, σ.comp M.val.toRingHom = f := by
  letI : Algebra M F := f.toAlgebra
  have : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.tower_top (K := K) M
  have : Module.IsTorsionFree M F := DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree M L := DivisionSemiring.to_moduleIsTorsionFree
  let σ : L →ₐ[M] F := IsAlgClosed.lift
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.commutes x⟩

section Ext

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem qkExt_g (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).g = gtExt D f hf z.g := by
  unfold qkExt qkMk
  rfl

theorem qkExt_y (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).y = z.y := ((qkExt_iff hB f hf z _).2 rfl).1

theorem qkExt_qkExt (hB : D.TauBimult) {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (f' : F' →+* F'')
    (hf' : f'.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') (f'' : F →+* F'')
    (hf'' : f''.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'') (e : f'.comp f = f'')
    {k : ℕ} (z : QkPt D F k) : qkExt hB f' hf' (qkExt hB f hf z) = qkExt hB f'' hf'' z := by
  refine qk_ext ?_ ?_
  · rw [qkExt_y, qkExt_y, qkExt_y]
  · rw [qkExt_g, qkExt_g, qkExt_g]
    exact gtExt_gtExt f hf f' hf' f'' hf'' e z.g

theorem qkExt_pullQk (hD : IsPullDeg φ D D') (hG : GlobalFnsSt) (hB : D.TauBimult) (hB' : D'.TauBimult)
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] [Field F']
    [Algebra (FractionRing R) F'] [Algebra (FractionRing R') F'] (hF : Compat φ F) (hF' : Compat φ F') (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hf' : f.comp (algebraMap (FractionRing R') F) = algebraMap (FractionRing R') F') {k : ℕ} (z : QkPt D F k) :
    QkExt f (pullQk hD hG hF hB hB' z) (pullQk hD hG hF' hB hB' (qkExt hB f hf z)) := by
  have h₁ : QkExt f z (qkExt hB f hf z) := (qkExt_iff hB f hf _ _).2 rfl
  have h₂ : QkExt f (pullQk hD hG hF hB hB' z) (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)) :=
    (qkExt_iff hB' f hf' _ _).2 rfl
  have h₃ : IsPullGtF φ hD F z.g (pullQk hD hG hF hB hB' z).g := ((eq_pullQk_iff hD hG hF hB hB' z _).1 rfl).2
  have h₄ := isPullGtF_ext hD hF' f hf' h₃ h₁ h₂
  have h₅ : (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)).y = hD.xe.symm (qkExt hB f hf z).y := by
    rw [h₂.1, h₁.1, pullQk_y]
  rw [← (eq_pullQk_iff hD hG hF' hB hB' _ _).2 ⟨h₅, h₄⟩]
  exact h₂

end Ext

theorem exists_rational_of_finite (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (hB : D.TauBimult) (hB' : D'.TauBimult) {L : Type} [Field L] [Algebra (FractionRing R) L]
    [Algebra.IsAlgebraic (FractionRing R) L] [IsAlgClosed L] [CharZero L]
    (M : IntermediateField (FractionRing R) L) (j : M →+* FractionRing R')
    (hj : ∀ r : R, j (algebraMap (FractionRing R) M (algebraMap R _ r)) = algebraMap R' _ (φ r))
    {k : ℕ} (hk : k ≠ 0)
    (H : ∀ q : QkPt D L k, ∃ z : QkPt D M k, qkExt hB M.val.toRingHom (val_comp M) z = q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R') F] (q : QkPt D' F k) :
    ∃ p : QkPt D' (FractionRing R') k, QkExt (algebraMap (FractionRing R') F) p q := by
  have hG := hL.globalFns
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (fracMap hφ)).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hF : Compat φ F := fun r => congrArg (algebraMap (FractionRing R') F) (fracMap_algebraMap hφ r)
  obtain ⟨q₀, rfl⟩ := pullQk_surjective hD hG hF hB hB' q
  have hjf : j.comp (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) (FractionRing R') :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (hj r).trans (fracMap_algebraMap hφ r).symm)
  obtain ⟨σ, e⟩ := exists_ringHom_extend M ((algebraMap (FractionRing R') F).comp j)
  have hh : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := rfl
  have hc : ((algebraMap (FractionRing R') F).comp j).comp
      (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) F := by
    rw [RingHom.comp_assoc, hjf, hh]
  have hσ : σ.comp (algebraMap (FractionRing R) L) = algebraMap (FractionRing R) F := by
    rw [← val_comp M, ← RingHom.comp_assoc, e, hc]
  obtain ⟨x, rfl⟩ := GlobalTheory.ArcExt.exists_qkExt σ hσ hB hL (Nat.cast_ne_zero.2 hk) q₀
  obtain ⟨z, rfl⟩ := H x
  refine ⟨pullQk hD hG hK hB hB' (qkExt hB j hjf z), ?_⟩
  rw [qkExt_qkExt hB _ (val_comp M) σ hσ _ hc e z, ← qkExt_qkExt hB j hjf _ hh _ hc rfl z]
  exact qkExt_pullQk hD hG hB hB' hK hF _ hh (RingHom.comp_id _) _

theorem exists_cdvr_ext_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  intro T D hB N hN ϖ hϖ
  have hL : Laws := GlobalTheory.allSixLaws.1
  have : CharZero (FractionRing T.V) := charZero_of_injective_algebraMap (IsFractionRing.injective T.V _)
  obtain ⟨M, hM, H⟩ := exists_finite_qk (D := D) (L := AlgebraicClosure (FractionRing T.V)) hL hB
    (Nat.cast_ne_zero.2 hN.ne')
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))
    (algebraMap T.V _ ϖ)) hN
  have h₁ : FiniteDimensional (FractionRing T.V) (IntermediateField.adjoin (FractionRing T.V) {π}) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let M₂ := M ⊔ IntermediateField.adjoin (FractionRing T.V) {π}
  have h₂ : FiniteDimensional (FractionRing T.V) M₂ := inferInstance
  let π₂ : M₂ := ⟨π, (le_sup_right : _ ≤ M₂) (IntermediateField.mem_adjoin_simple_self _ π)⟩
  have hπ₂ : π₂ ^ N = algebraMap (FractionRing T.V) M₂ (algebraMap T.V _ ϖ) := Subtype.ext hπ
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, -, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V (FractionRing T.V) M₂
  have : CharZero W := charZero_of_injective_algebraMap hinj
  obtain ⟨w, hw⟩ := hint π₂ ⟨Polynomial.X ^ N - Polynomial.C ϖ, Polynomial.monic_X_pow_sub_C _ hN.ne', by
    simp [hπ₂]⟩
  have hwN : w ^ N = algebraMap T.V W ϖ := IsFractionRing.injective W M₂ (by
    rw [map_pow, hw, hπ₂]; exact (RingHom.congr_fun hc ϖ).symm)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hwN
    exact hϖ.ne_zero (hinj (hwN.symm.trans (map_zero _).symm))
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ'
  let ε := FractionRing.algEquiv W M₂
  let j : M →+* FractionRing W := ε.symm.toRingEquiv.toRingHom.comp
    (IntermediateField.inclusion (le_sup_left : M ≤ M₂)).toRingHom
  have hj : ∀ r : T.V, j (algebraMap (FractionRing T.V) M (algebraMap T.V _ r)) =
      algebraMap W _ (algebraMap T.V W r) := fun r => ε.injective (by
    refine (ε.apply_symm_apply _).trans (Eq.trans ?_ (ε.commutes _).symm)
    exact (RingHom.congr_fun hc r).symm)
  refine ⟨Formalism.L2.Pj.CDVR.mk W, algebraMap T.V W, ϖ', m * N, hinj, RingHom.finite_algebraMap.2 hfin, hϖ',
    Dvd.intro_left m rfl, ?_, ?_⟩
  · rw [← hwN, pow_mul]
    exact hm.pow_pow
  · intro D' hD hB' k hk q
    have hk0 : k ≠ 0 := by rintro rfl; exact hN.ne' (Nat.eq_zero_of_zero_dvd hk)
    exact exists_rational_of_finite hL hinj hD hB hB' M j hj hk0 (H k hk) q

end GlobalTheory.QkRationalExt
