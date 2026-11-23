import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem latEmb_model_of_eq (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ) (hj : InR D j)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) (V : HSp D) (hV : V = D.sp.W j) (r : ℕ)
    (hr : V.rank = r) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hL : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (hI : LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀)) :
    Function.Injective ι₀ ∧ Submodule.span D.host.E (Set.range ι₀) = ⊤ ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
        herm (GlobalTheory.RecDict.gmW V hr) (ι₀ x) (ι₀ y)) := by
  subst hV
  subst hr
  have hL' : LatEmb (D.sp.W j) ι₀ := hL
  obtain ⟨ε, hε⟩ : LatIsom (D.sp.W j) Dw.EF ι₀ := hI
  have hsp : Submodule.span D.host.E (Set.range ι₀) = ⊤ := by
    rw [← LinearMap.coe_range, hL'.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D (D.sp.W j) 1).2.1
  let f := ((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hsp' : Submodule.span D.host.E (Set.range (f ∘ₗ ι₀)) = ⊤ := by
    have : Set.range (f ∘ₗ ι₀) = (D.sp.W j).frame.equivFun.symm.toLinearMap '' Set.range ι₀ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  have h1 : ε = 1 := GlobalTheory.Member.sign_eq_one D H Dw j hj hrt hrt0 hp hq (f ∘ₗ ι₀) ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL'.1) hsp' hε
  subst h1
  refine ⟨hL'.1, hsp, (GlobalTheory.Member.isom_iff_model Dw (D.sp.W j) rfl ι₀).1 fun x y => ?_⟩
  rw [hε x y, Units.val_one, Int.cast_one, _root_.one_mul]

set_option maxHeartbeats 2000000 in

theorem model_space_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∀ τ : D.host.E →+* ℂ, τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 → (τ ((T.U j σ).X k).ξ0).im < 0) ∧ ∃ φD : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), Function.Injective φD ∧ Submodule.span D.host.E (Set.range φD) = ⊤ ∧ ∀ x y, (((T.Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm (φD x) (φD y)) := by
  intro D T h j hj σ hσ k
  obtain ⟨hr, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨-, hrt, hrt0, -⟩ := h.pins.1
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨hr', -, -, -, -, -, -, hL, hI, -⟩ := h.adPin j hj σ hσ
  refine ⟨fun τ hτ => ?_, T.iota j, ?_⟩
  · rw [(hW k).2]
    exact GlobalTheory.Member.hostCMType_neg_constant_im_neg D τ (by rw [← hrt0, ← hrt, hτ])
  · rw [(hW k).1, (hW k).2]
    exact latEmb_model_of_eq D T.Q.H (T.Q.Dw j) j hj hrt hrt0 hp hq (T.V j σ) (h.spaceW j hj σ hσ) D.R.r hr
      (T.iota j) hL hI

end GlobalTheory.GeoLevel
