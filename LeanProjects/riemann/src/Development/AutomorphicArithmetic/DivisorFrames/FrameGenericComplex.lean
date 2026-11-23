import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem chg_cancel {r : ℕ} (dual : Bool) {T H N : Matrix (Fin r) (Fin r) ℂ} (hT : IsUnit T.det)
    (h : Tᵀ * H * Tᴴᵀ = cond dual ((lieMat dual T)ᴴ * N * lieMat dual T)⁻¹ ((lieMat dual T)ᴴ * N * lieMat dual T)ᵀ) :
    H = cond dual N⁻¹ Nᵀ := by
  have h₁ : IsUnit Tᵀ := (isUnit_iff_isUnit_det _).2 (by rwa [det_transpose])
  have h₂ : IsUnit Tᴴᵀ := (isUnit_iff_isUnit_det _).2 (by rw [det_transpose, det_conjTranspose]; exact hT.star)
  have key : Tᵀ * H * Tᴴᵀ = Tᵀ * cond dual N⁻¹ Nᵀ * Tᴴᵀ := by
    rw [h]
    cases dual
    · simp only [lieMat, cond_false, transpose_mul, Matrix.mul_assoc]
    · have e : (T⁻¹ᵀ)⁻¹ = Tᵀ := by rw [← transpose_nonsing_inv, nonsing_inv_nonsing_inv _ hT]
      simp only [lieMat, cond_true, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, e, Matrix.mul_assoc]
      rfl
  exact h₁.mul_right_inj.1 (h₂.mul_left_inj.1 key)

theorem UpperTheory.frame_generic_complex :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (X : Scheme.{0}) (j : Y.X ⟶ X) (M : X.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) (q : X ⟶ Sp (𝓞 F)) (G : ∀ σ : c.F →+* ℂ, EigMet Z σ) (h : VMetric q M (Dw.mult τ)), IsLie g₀ τ j dual A → (∀ z : X, ∃ ch : Chart M (Dw.mult τ), z ∈ ch.U ∧ MetOn g₀ τ j dual A G h ch) → IsMet g₀ τ j dual A G h := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ hρ g₀ τ X j M hM dual A q G h hL hloc ch σ p z hz hzU φ f hf yc hyc g hg
  obtain ⟨ch₀, h₀, hm⟩ := hloc (z.1 (IsLocalRing.closedPoint ℂ))
  have hz₀ : z ∈ CxPts.ptsIn q _ ch₀.U := CxPts.mem_ptsIn.2 h₀
  have hb : z.1 (IsLocalRing.closedPoint ℂ) = j (Var.base p) := by rw [hz]; rfl
  have hj₀ : j (Var.base p) ∈ ch₀.U := hb ▸ h₀
  have hj : j (Var.base p) ∈ ch.U := hb ▸ CxPts.mem_ptsIn.1 hzU
  obtain ⟨f₀, hco, hf₀⟩ := hf.change hL.1 hj hj₀
  have hp : spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) = p.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk p.1
  have hφ : embOf e σ = (Var.evStalk p).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ Y.X.functionField
      ((RingHom.congr_fun hf.1 a).symm.trans ((Y.stalkIncl (Var.base p)).commutes _).symm)
    rw [RingHom.comp_apply, RingHom.comp_apply, h3]
    exact ((Var.evStalk_germ (U := ⊤) trivial _).trans (CxPts.ev_algX CxPts.mem_ptsIn_top _)).symm
  have hx : yc.1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) ≫ ρ ≫ genι Z := by
    rw [← Category.assoc, hp, hyc]; exact Category.assoc _ _ _
  obtain ⟨g₁, hg₁⟩ := f₀.exists_isMap (Var.evStalk p) hφ hx
  have e₀ := hm σ p z hz hz₀ φ f₀ hf₀ yc hyc g₁ hg₁
  have hu := isUnit_det_trAt ch ch₀ (stalk_le j hj) (stalk_le j hj₀)
  have hT : (trAt (stalkPt Y (Var.base p) ≫ j) ch ch₀).map (Var.evStalk p) = ch.tr q _ ch₀ z := by
    rw [← trAt_spMap _ ch ch₀ (stalk_le j hj) (stalk_le j hj₀), ← Category.assoc, hp, ← hz, trAt_cx z ch ch₀ hzU hz₀]
  have hc : g.co g₁ τ = lieMat dual (ch.tr q _ ch₀ z) := by
    rw [hg.co τ hg₁ hx, hco, ← lieMat_map _ _ hu, hT]
  have hTu : IsUnit (ch.tr q _ ch₀ z).det := by
    rw [← hT, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hu.map _
  have ht := (h.met (σ.comp (algebraMap (𝓞 F) F))).trans ch ch₀ z hzU
  rw [ht, (G _).change yc g g₁ τ, hc] at e₀
  exact chg_cancel dual hTu e₀
