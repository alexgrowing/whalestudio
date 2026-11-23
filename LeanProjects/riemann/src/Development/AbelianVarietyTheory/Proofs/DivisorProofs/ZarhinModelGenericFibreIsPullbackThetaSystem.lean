import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

noncomputable section
namespace GlobalTheory.ZH.GenFib

theorem genFib_pullback : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE), X₁.S.Over₀ Y U₀ → ∃ ψ : ((Over.pullback Y.pt).obj O.G).left ⟶ X₁.ρ.P.A.left, IsGrpPullback ((Over.pullback Y.pt).obj O.G) X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) ψ ∧ LBIso (O.L.L.pull (pullback.fst O.G.hom Y.pt)) (X₁.ρ.P.L.pull ψ) ∧ ∀ f : X₁.ρ.P.A ⟶ X₁.ρ.P.A, IsMonHom f → ∃ F : O.G ⟶ O.G, IsMonHom F ∧ ((Over.pullback Y.pt).map F).left ≫ ψ = ψ ≫ f.left := by
  intro X₁ Y U₀ EE O hO
  have hcov := (top_le_preimage_iff _ _).1 (Y.top_le_preimage_pt hO.ne)
  let x : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt (by rw [Scheme.Opens.range_ι]; exact hcov)
  have hx : x ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ O.u₀ = spMap X₁.S.R.val.toRingHom := O.u₀_gen x hx
  have hc : pullback.fst O.G.hom Y.pt ≫ O.G.hom = (pullback.snd O.G.hom Y.pt ≫ x) ≫ U₀.ι := by
    rw [pullback.condition, Category.assoc, hx]
  let κ : pullback O.G.hom Y.pt ⟶ pullback X₁.ρ.P.A.hom O.u₀ := O.cart.1.lift _ _ hc
  have hκ₁ : κ ≫ O.φ = pullback.fst O.G.hom Y.pt := O.cart.1.lift_fst _ _ hc
  have hκ₂ : κ ≫ ((Over.pullback O.u₀).obj X₁.ρ.P.A).hom = ((Over.pullback Y.pt).obj O.G).hom ≫ x :=
    O.cart.1.lift_snd _ _ hc
  have n : IsGrpPullback ((Over.pullback Y.pt).obj O.G) O.G (x ≫ U₀.ι) (κ ≫ O.φ) :=
    (isGrpPullback_pullback O.G Y.pt).congr hx.symm hκ₁.symm
  have h₁ : IsGrpPullback ((Over.pullback Y.pt).obj O.G) ((Over.pullback O.u₀).obj X₁.ρ.P.A) x κ :=
    O.cart.cancel n hκ₂
  have hP : IsGrpPullback ((Over.pullback Y.pt).obj O.G) X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom)
      (κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀) :=
    (h₁.comp (isGrpPullback_pullback X₁.ρ.P.A O.u₀)).congr hxu rfl
  refine ⟨κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀, hP, ?_, ?_⟩
  · exact GlobalTheory.GenSpread.lbIso_pull_comp κ hκ₁.symm rfl ⟨O.w, O.w_gen⟩
  · intro f hf
    obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom))
    let f' := e.hom ≫ (Over.pullback (spMap X₁.S.R.val.toRingHom)).map f ≫ e.inv
    have hf' : IsMonHom f' := by infer_instance
    obtain ⟨F, ⟨hF, hFf⟩, -⟩ := O.endo f' hf'
    refine ⟨F, hF, ?_⟩
    rw [hFf]
    show (e.hom ≫ (Over.pullback (spMap X₁.S.R.val.toRingHom)).map f ≫ e.inv).left ≫ (κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀) = _
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    rw [← he']
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie]
    congr 1
    exact pullback.lift_fst _ _ _

end GlobalTheory.ZH.GenFib
