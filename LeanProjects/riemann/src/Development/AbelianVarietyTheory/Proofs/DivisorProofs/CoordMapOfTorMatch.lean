import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOrdSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorCoord

theorem coordMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∀ ρ, TorMatch U U' g β ρ → CoordMap D.toPre D'.toPre g ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hVb hV G' _ _ hG' D' A' U' g β hg hβ hL ρ hT
  haveI := hV
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  refine GlobalTheory.PsiFromTauEven.main R V hV g gK hgK D.toPre D'.toPre D.tau_bimult D.psi_even D'.tau_bimult D'.psi_even ρ ?_
  intro a b x x' hx hx'
  obtain ⟨⟨-, -, -, hVc⟩, hV0⟩ := id hVb
  haveI := hVc
  haveI := hV0
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ y, algebraMap (FractionRing R) F y = algebraMap (FractionRing V) F (gK y) := fun _ => rfl
  have hFr : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => (hF _).trans (congrArg _ (hgK r))
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois R hR G hG D A U V hVb hV g hg G' β hβ hG' D' A' U' hL F hFr
  have hm : ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a' := by
    intro k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8
    have h := (hT F hFr k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8).trans (he3 a').symm
    simp only [genMap] at h
    have hs : ∀ z : TFK (R := R) F ⟶ A.A, z.left ≫ U.gen.inv.left ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F).hom := by
      intro z
      have := Over.w U.gen.inv
      rw [← Over.w z, ← this]
      rfl
    have h' : a.left ≫ U.gen.inv.left = (e a').left ≫ U.gen.inv.left :=
      pullback.hom_ext (by simpa only [Category.assoc] using h) (by simpa only [Category.assoc] using (hs a).trans (hs (e a')).symm)
    ext1
    have hi : Mono U.gen.inv.left := inferInstance
    exact (cancel_mono _).1 h'
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' :=
    fun k hk => by
      obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root V F ϖ hϖ k (by simpa using hk.map g)
      exact GlobalTheory.TauFormGen.dvd_ord_sub R hR G hG D A U V hVb G' hG' D' A' U' g gK hgK F hF k hk ϖ hϖ O φ σ π h₁ h₂ h₃ h₄ h₅ ρ e
        (he1 k) (he2 σ) (hm k hk) a b x x' hx hx'
  obtain ⟨u, hu⟩ := GlobalTheory.TauForm.exists_unit_of_ord_eq (W := V) (x := Units.map gK.toMonoidHom x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x'))
      (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))
  exact ⟨u, hu⟩

end GlobalTheory.Poinc.TorCoord
