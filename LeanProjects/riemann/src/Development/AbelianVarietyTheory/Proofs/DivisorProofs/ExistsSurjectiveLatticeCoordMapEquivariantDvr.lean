import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfTorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivMapOfTorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadOfTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjectiveAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkForms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.GenRestrict

theorem exists_surjective_coordMap_equivMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (p : ℕ), p.Prime → (p : R) ∈ maximalIdeal R → ∀ (Wo : Set (Sp R)), IsOpen Wo → (∀ y, PsiUnitOn D.toPre y Wo) → (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) ∈ Wo → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∃ ρ : D.toPre.X →+ D'.toPre.X, Function.Surjective ρ ∧ CoordMap D.toPre D'.toPre g ρ ∧ EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hVd G' _ _ hG' D' A' U' g β p _ _ Wo hWo hψ hker gp hL
  obtain ⟨⟨hRN, -, -, hRA⟩, -⟩ := id hR
  obtain ⟨⟨-, -, hVI, -⟩, hV0⟩ := id hV
  obtain ⟨N, _, _, _, φ, g', hN, hφ, hg', hfac⟩ := GlobalTheory.FarTrait.exists_factor g
  obtain ⟨hNN, hNI, hNA, hN0⟩ := hN
  have hNb : GlobalTheory.Mum.Base N := ⟨⟨hNN, inferInstance, hNI, hNA⟩, hN0⟩
  have hsp : spMap g' ≫ spMap φ = spMap g := by
    rw [← Spec.map_comp]
    exact congrArg spMap (RingHom.ext hfac)
  have hgen : spMap φ (genericPoint (Sp N)) ∈ (⟨Wo, hWo⟩ : (Sp R).Opens) := by
    have e : spMap φ (genericPoint (Sp N)) = (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
      change φ r ∈ (⊥ : Ideal N) ↔ r ∈ RingHom.ker g
      rw [Ideal.mem_bot, RingHom.mem_ker, ← hfac, map_eq_zero_iff g' hg']
    rw [e]
    exact hker
  have hG₂ : IsSemiAbelian ((Over.pullback (specOf φ)).obj G) := Geo.Tor.IsSemiAbelian.pullback _ G hG
  haveI : IsCommMonObj ((Over.pullback (specOf φ)).obj G) := hG₂.comm
  have hbc : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom :=
    inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (specOf φ)).obj G)))
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U N hNb.1 φ hφ ⟨Wo, hWo⟩ hψ hgen
    ((Over.pullback (specOf φ)).obj G) (Iso.refl _) hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U N hNb _ hG₂ D₂ A₂ U₂ φ (pullback.fst G.hom (specOf φ)) hφ
    (Iso.refl _) hbc (Category.id_comp _).symm hD hU
  have sq : β ≫ G.hom = (G'.hom ≫ spMap g') ≫ specOf φ := by
    rw [Category.assoc, gp.1.w, ← hsp]
  let β₂ : G'.left ⟶ ((Over.pullback (specOf φ)).obj G).left := pullback.lift β (G'.hom ≫ spMap g') sq
  have hβ : β₂ ≫ pullback.fst G.hom (specOf φ) = β := pullback.lift_fst _ _ _
  have hβ' : β₂ ≫ pullback.snd G.hom (specOf φ) = G'.hom ≫ spMap g' := pullback.lift_snd _ _ _
  have gp₂ : IsGrpPullback G' ((Over.pullback (specOf φ)).obj G) (spMap g') β₂ :=
    (isGrpPullback_pullback G (specOf φ)).cancel (gp.congr hsp.symm hβ.symm) hβ'
  have hL₂ : LBIso U'.LG.L (U₂.LG.L.pull β₂) :=
    LBIso.trans U'.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hL
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ β₂ hβ.symm).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂
  have hs := GlobalTheory.TorusOntoSpread.restrict_surjective N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hT := GlobalTheory.SpreadTorMatch.torMatch_of_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hC₂ := TorCoord.coordMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV hVd G' hG' D' A' U' g' β₂ hg' gp₂ hL₂ ρ hT
  have hE₂ := equivMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ hg' ρ hT
  refine ⟨ρ.comp hD.xe.symm.toAddMonoidHom, hs.comp hD.xe.symm.surjective, fun y r r' hr hr' => ?_,
    fun f f' hf hf' hff m m' hm hm' y => ?_⟩
  · obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm.toAddMonoidHom y)
    rw [← hfac]
    exact ((hC₁ y r r₂ hr hr₂).map g').trans (hC₂ _ r₂ r' hr₂ hr')
  · have hf₂ : IsMonHom ((Over.pullback (specOf φ)).map f) := inferInstance
    have e₁ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst G.hom (specOf φ) =
        pullback.fst G.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
    have e₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.snd G.hom (specOf φ) =
        pullback.snd G.hom (specOf φ) := Over.w ((Over.pullback (specOf φ)).map f)
    have e₃ : f'.left ≫ β₂ = β₂ ≫ ((Over.pullback (specOf φ)).map f).left := by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₁, hβ, ← Category.assoc, hβ, hff]
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₂, hβ', ← Category.assoc, Over.w f']
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom N hNb _ hG₂ D₂ A₂ U₂ _ hf₂
    have h₁ := hE₁ f _ hf hf₂ e₁ m m₂ hm hm₂ y
    exact (congrArg ρ h₁).trans (hE₂ _ f' hf₂ hf' e₃ m₂ m' hm₂ hm' _)

end GlobalTheory.Poinc.Eq8.GenRestrict
