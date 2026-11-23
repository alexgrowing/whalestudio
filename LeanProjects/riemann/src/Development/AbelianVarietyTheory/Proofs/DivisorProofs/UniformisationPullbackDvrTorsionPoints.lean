import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.TorusExt GlobalTheory.Balanced

attribute [local instance] gtGroup

set_option maxHeartbeats 2000000 in

theorem pull_unif_tors : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  intro R _ _ _ J hR D₀ A₀ G₀ _ _ U₀ hG V _ _ _ _ hV f hf hJ
  have hL := GlobalTheory.firstFiveLaws
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D, hD, A, U, hG', hU, hpt, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R J hR D₀ A₀ G₀ hG U₀ V f hV hf hJ
  refine ⟨D, hD, A, U, hG', hU, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := D₀.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  let p₁ : QkPt D₀.toPre F k := qkExt hB σ.toRingHom (hom_comp σ) p₀
  let x₁ : TFK (R := R) F ⟶ A₀.A := extPt σ x₀
  have hx₁ : QkToAkU U₀.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R J hR D₀ A₀ G₀ hG U₀ F₀ F σ k hk p₀ p₁ x₀ x₁
    ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) rfl).1 hx₀
  obtain ⟨ex, -, io, ns⟩ := hpt F hF
  obtain ⟨g, hg, -⟩ := ex p₁.g
  let p : QkPt D.toPre F k := ⟨hD.xe.symm p₁.y, g, by
    obtain ⟨s, h1, h2⟩ := p₁.eq
    obtain ⟨s', hs', -⟩ := ex s
    exact ⟨s', (ns k _ _ _ _ hg hs').1 h1, (io _ _ _ hs').1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x, hx⟩ := exists_toG_pull f U₀.toUnifPre U.toUnifPre hF x₁
  refine ⟨p, x, rfl, ⟨p₁.g, (eq_gtExt_iff σ.toRingHom (hom_comp σ) _ _).1 rfl, hg⟩, ?_, ?_⟩
  · exact hL.2.2.2.2.qkBaseChange R V J _ hR hR' f D₀ A₀ G₀ U₀ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A D
      hD U hU F hF k hk p₁ x₁ p x rfl hg
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx) hx₁
  · simpa only [toG, Category.assoc, x₁, extPt, Over.homMk_left] using hx

end GlobalTheory.TInj
