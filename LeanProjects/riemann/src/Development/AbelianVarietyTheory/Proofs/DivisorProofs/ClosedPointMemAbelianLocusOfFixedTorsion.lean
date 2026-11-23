import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FixedTorsionTrait

theorem abLocus_of_retract {S : Scheme.{0}} (G H : Over S) (i : G ⟶ H) (r : H ⟶ G) (h : i ≫ r = 𝟙 G) :
    ∀ x ∈ abLocus H, x ∈ abLocus G := by
  intro x hx K _ _ t ht
  have hp : IsProper ((Over.pullback t).obj H).hom := hx K t ht
  exact GlobalTheory.Mum.RetractGeneric.isProper_of_retract ((Over.pullback t).map i) ((Over.pullback t).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]) hp

theorem closedPoint_mem_abLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  intro R _ _ _ hR D A G _ _ hG U V _ _ _ φ hV hφ n hn hu H
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj G) := Functor.isCommMonObj_obj
  obtain ⟨A', ψ, hψ⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback R A G U.gen U.gen_hom V φ hφ
  obtain ⟨W, _, _, _, io, em, D₈, Q, H₈, _, _, U₈, i, r, hW, hfin, hinj, hem, hc, hH₈, htot, hr, hir, hmono⟩ :=
    GlobalTheory.T.degeneration_extension_local_domain V hV A' _ hG' ψ hψ
  have hem' : ∀ w : W, w ≠ 0 → IsUnit (em w) := fun w hw =>
    IsUnit.mk0 _ ((map_ne_zero_iff em hem).2 hw)
  letI : Algebra (FractionRing W) (AlgebraicClosure (FractionRing V)) :=
    (IsFractionRing.lift (A := W) (K := FractionRing W) (g := em) hem).toAlgebra
  have hlift : ∀ w : W, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ w) = em w :=
    fun w => IsFractionRing.lift_algebraMap _ _
  have hcompat : ∀ v, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ (io v)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v) := fun v => (hlift _).trans (hc v)
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension V W hV hW io hfin hinj (AlgebraicClosure (FractionRing V)) hcompat
  have hsub : Subsingleton D₈.toPre.X := by
    refine GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification W hW D₈ Q H₈ hH₈ U₈ htot (AlgebraicClosure (FractionRing V)) n N hn fun j => ?_
    obtain ⟨T', hT', f, hf, hirr, hfix⟩ := H j
    obtain ⟨T'', hT'', g, e, hle, hg, he1, heN, hπ⟩ := hN T' hT' f hf hirr
    refine ⟨T'', hT'', g, e, hg, he1, heN, hπ, fun σ hσ x hx => ?_⟩
    exact GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs V W io _ hcompat _ H₈ r hr hmono σ (fun w => hσ _ (by rw [← hg w]; exact (g w).2)) (n ^ j)
      (fun y hy => hfix σ (fun z hz => hσ z (hle hz)) y hy) x hx
  have := hW.1
  have := hW.2.2
  have hab : IsAbelianScheme H₈ := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ W hW.2.1 D₈ Q H₈ hH₈ U₈ hsub
  have h₈ : closedPoint W ∈ abLocus H₈ := fun K _ _ t _ => by
    have := hab.proper
    infer_instance
  have h₁ : closedPoint W ∈ abLocus ((Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) :=
    abLocus_of_retract _ H₈ i (r 0) hir _ h₈
  have h₂ := (abLocus_pullback (G' := (Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) abLocusOne hG'
    (IsPullback.of_hasPullback ((Over.pullback (spMap φ)).obj G).hom (spMap io)) (closedPoint W)).2 h₁
  letI : Algebra V W := io.toAlgebra
  have : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  have hm : (maximalIdeal W).comap io = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (maximalIdeal W))
  have : IsLocalHom io := ((IsLocalRing.local_hom_TFAE io).out 4 0).1 hm
  have e : spMap io (closedPoint W) = closedPoint V := by
    have h : ⇑(spMap io) = PrimeSpectrum.comap io := by
      ext x : 1
      simp [spMap, Spec.map_base]
      rfl
    rw [h]
    exact IsLocalRing.comap_closedPoint io
  rw [← e]
  exact h₂

end GlobalTheory.FixedTorsionTrait

end
