import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannFormFramePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtPtFOfEigFrame
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.HodgeLoc

open GlobalTheory.ArcQ

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R]
  {w w' : Sp R ⟶ Z.oF.t.G.left} (h : w ≫ Z.m.φ = w' ≫ Z.m.φ) : w = w' := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  haveI : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    unfold spMap
    infer_instance
  have := Z.jQ_open
  refine Z.m.cart.1.hom_ext h ?_
  rw [← cancel_mono (Z.jQ ≫ pullback.fst _ _)]
  have hw := Z.m.cart.1.w
  simp only [Category.assoc] at hw ⊢
  rw [← hw, reassoc_of% h]

theorem hermForm_pull {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

def imBil {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem eq_of_im_hermForm {g r : ℕ} {v : Fin r → Fin g → ℂ} (hv : Submodule.span ℝ (Set.range v) = ⊤)
    {H₁ H₂ : Matrix (Fin g) (Fin g) ℂ} (h : ∀ m m', (hermForm H₁ (v m) (v m')).im = (hermForm H₂ (v m) (v m')).im) :
    H₁ = H₂ := by
  have hE : imBil H₁ = imBil H₂ :=
    LinearMap.ext_on_range hv fun m => LinearMap.ext_on_range hv fun m' => h m m'
  have e : ∀ z w, (hermForm H₁ z w).im = (hermForm H₂ z w).im := fun z w =>
    congrArg (fun F : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ => F z w) hE
  ext p q
  apply Complex.ext
  · have := e (Complex.I • Pi.single p 1) (Pi.single q 1)
    simpa [hermForm, Matrix.mulVec_single, Pi.star_single] using this
  · have := e (Pi.single p 1) (Pi.single q 1)
    simpa [hermForm, Matrix.mulVec_single, Pi.star_single] using this

theorem hodge_eq_riem_chart : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (n g r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ M : Matrix (Fin r) (Fin r) ℝ, ∀ t ∈ logDom n k, LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) ∧ (∀ i i', (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam t i) (lam t i')).im = M i i') ∧ ∀ (f : EigFrame s.T.Z σ ((ch.symm (logExp k t)).1 ≫ genι s.T.Z)) (W : Letter S.Dw → Fin g → ℂ), Dirs (Z := s.T.Z) ⟨ch.symm (logExp k t), f⟩ (fun w => (ex (ch.symm (logExp k t)) w).left) W → ∀ τ : D.host.E →+* ℂ, (x.hodge σ).gram (ch.symm (logExp k t)) f τ = (Real.pi : ℂ) • Matrix.of fun b b' => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩) := by
  intro D A N j S κ s x σ hσ n g r k ch ex lam ρ hL
  obtain ⟨W₀⟩ := nonempty_unfWit_of_isUnf _ _ _ _ _ _ σ _ (s.U σ) (s.unf σ hσ).1
  obtain ⟨i, T₀, hT⟩ := GlobalTheory.ShFam.Hor.Mark.exists_marking_const _ _ _ _ _ _ _ _ s.T.Z σ _ W₀.e W₀.F n g r k ch ex lam ρ hL
  let M : Matrix (Fin r) (Fin r) ℝ :=
    fun m m' => (((W₀.F.Di i).EF (T₀.symm (Pi.single m 1)) (T₀.symm (Pi.single m' 1)) : ℤ) : ℝ)
  have key : ∀ t ∈ logDom n k, ∀ (f : EigFrame s.T.Z σ ((ch.symm (logExp k t)).1 ≫ genι s.T.Z))
      (Wd : Letter S.Dw → Fin g → ℂ),
      Dirs (Z := s.T.Z) ⟨ch.symm (logExp k t), f⟩ (fun w => (ex (ch.symm (logExp k t)) w).left) Wd →
      LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        (∀ m m', (hermForm Hm (lam t m) (lam t m')).im = M m m') ∧
        ∀ τ : D.host.E →+* ℂ, (x.hodge σ).gram (ch.symm (logExp k t)) f τ =
          (Real.pi : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩) := by
    intro t ht f Wd hW
    obtain ⟨-, hsrc, hin⟩ := Mark.pt_mem hL ht
    obtain ⟨Q, gm, hPer, hiso, hsum⟩ := hT t ht ⟨ch.symm (logExp k t), f⟩ Wd rfl hW
    obtain ⟨P, W', y', hP, hu, hy, hv, hQ⟩ := hPer
    choose e₁ h₁ using fun z => Mark.exists_up s.T.Z.m0.toSABMap.cart hu (W₀.F.ex i P z)
    choose e₂ h₂ using fun z => Mark.exists_up s.T.Z.m.cart (x := (ch.symm (logExp k t)).1 ≫ genι s.T.Z) (y := y')
      (by rw [← Category.assoc, hy]) (ex (ch.symm (logExp k t)) z)
    obtain ⟨-, L, hML, -⟩ := Mark.exists_match_of_lifts hL.1 hsrc hP hu hy h₁ h₂
    have hWW : ∀ z, L (W' z) = Wd z := fun z => by
      obtain ⟨v, h1, h2, h3⟩ := hv z
      exact ((hL.1.2.2.2.2.2 _ hsrc).2 _ (f.tan z.1 z.2)).unique (h2 ▸ (hML.2 _ v h1).1 h3) (hW z)
    obtain ⟨hind, T, hTL⟩ := Mark.exists_marking hP hML (hL.2.2.2.1 t ht).1 (hL.2.2.2.1 t ht).2.1
    have hLP : ∀ v, L (P v) = ∑ z, Q v z • Wd z := fun v => by
      rw [hQ v, map_sum]
      simp only [map_smul, hWW]
    have hlam : ∀ m, lam t m = L (P (gm (T₀.symm (Pi.single m 1)))) := fun m => by
      rw [hLP, hsum, AddEquiv.apply_symm_apply]
      simp [Pi.single_apply]
    have hspan : Submodule.span ℝ (Set.range (lam t)) = ⊤ := by
      refine eq_top_iff.2 fun w _ => ?_
      obtain ⟨w, rfl⟩ := L.surjective w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1.ge trivial
      refine (Submodule.span_le (p := (Submodule.span ℝ (Set.range (lam t))).comap
        (L.toLinearMap.restrictScalars ℝ))).2 ?_ hw
      rintro _ ⟨v, rfl⟩
      change L (P v) ∈ Submodule.span ℝ (Set.range (lam t))
      rw [← hTL v]
      exact Submodule.sum_mem _ fun m _ => by
        rw [← Int.cast_smul_eq_zsmul ℝ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    obtain ⟨Hm', hH1, hH2, hH3⟩ := hP.2.2.2.2
    obtain ⟨q, hq, hqv⟩ : ∃ q : FrPt (S.Xo κ.l) κ.c (CAt σ), GlobalTheory.AllWt.ptF q = y' ∧ ∀ τ b,
        ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ b ∧ w ≫ s.T.Z.m.φ = f.v τ b :=
      exists_frPt_ptF_of_eigFrame _ _ _ _ _ _ _ _ s.T.Z ℂ σ y'
      ((ch.symm (logExp k t)).1 ≫ genι s.T.Z) f
      (by have h2 := (ch.symm (logExp k t)).2; rw [← hy, Category.assoc, s.T.Z.jQ_over] at h2; exact h2)
      (by rw [← Category.assoc, hy])
    have hqx : q.x = W₀.F.u i P := by rw [← hu, ← hq]; exact (pullback.lift_fst _ _ _).symm
    have hqy : cxPt s.T.Z q = ch.symm (logExp k t) := Subtype.ext ((congrArg (· ≫ s.T.Z.jQ) hq).trans hy)
    have hAn : AnLie W₀.F i P q (fun τ b => W' ⟨τ, b⟩) := ⟨hqx, fun τ b => by
      obtain ⟨w, hw0, hw⟩ := hqv τ b
      obtain ⟨v, h1, h2, h3⟩ := hv ⟨τ, b⟩
      rw [← hw0, base_eq (hw.trans h2.symm)]
      exact h3⟩
    have hgram := ToroidalCompactificationData.hodge_gram_of_sameVec D A N j S κ s x σ hσ W₀ i P hP Hm' ⟨hH1, hH2, hH3⟩ q _ hAn _ hqy f hqv
    let B := LinearMap.toMatrix' L.symm.toLinearMap
    have hB : ∀ u, B *ᵥ u = L.symm u := fun u => LinearMap.toMatrix'_mulVec _ _
    have hF : ∀ u u', hermForm (Bᵀ * Hm' * Bᵀᴴ) u u' = hermForm Hm' (L.symm u) (L.symm u') := fun u u' => by
      rw [hermForm_pull, hB, hB]
    refine ⟨hind, hspan, Bᵀ * Hm' * Bᵀᴴ, Matrix.isHermitian_mul_mul_conjTranspose _ hH1, fun z hz => ?_,
      fun m m' => ?_, fun τ => ?_⟩
    · rw [hF]
      exact hH2 _ ((LinearEquiv.map_ne_zero_iff _).2 hz)
    · rw [hF, hlam, hlam, L.symm_apply_apply, L.symm_apply_apply, hH3, hiso]
    · ext a b
      rw [hgram τ a b, Matrix.smul_apply, Matrix.of_apply, hF, smul_eq_mul, ← hWW, ← hWW, L.symm_apply_apply,
        L.symm_apply_apply]
  refine ⟨M, fun t ht => ?_⟩
  obtain ⟨-, hsrc, -⟩ := Mark.pt_mem hL ht
  obtain ⟨f₀⟩ := EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ s.T.Z ℂ σ _ (ch.symm (logExp k t)).2
  choose W0 hW0 _ using fun z : Letter S.Dw => (hL.1.2.2.2.2.2 _ hsrc).2 _ (f₀.tan z.1 z.2)
  obtain ⟨hind, hspan, Hm, h1, h2, h3, -⟩ := key t ht f₀ W0 hW0
  refine ⟨hind, hspan, Hm, h1, h2, h3, fun f Wd hW τ => ?_⟩
  obtain ⟨-, -, Hm₂, -, -, g3, g4⟩ := key t ht f Wd hW
  rw [g4 τ, eq_of_im_hermForm hspan (fun m m' => (g3 m m').trans (h3 m m').symm)]

end GlobalTheory.ShFam.Hor.HodgeLoc
