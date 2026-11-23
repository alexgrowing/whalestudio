import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphic

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC GlobalTheory.LevModel GlobalTheory.CovTop

noncomputable section

namespace UpperTheory.Dv.Thin

open AlgebraicGeometry CategoryTheory in
set_option maxHeartbeats 1600000 in

theorem over_comp_lat : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ (∀ v, v ∈ ((U₂ σ₂).X k₂).Λ ↔ (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Λ) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d σ₂ hσ₂
  set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hU := hL.unf σ hσ
  have hU₂ := hL₂.unf σ₂ hσ₂
  obtain ⟨hr₀, hW⟩ := hL.modelW σ hσ
  obtain ⟨hr₂, hW₂⟩ := hL₂.modelW σ₂ hσ₂
  have hpq : Dw.p ≠ Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
  have hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp
      (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)
  have hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ := fun τ => by
    ext a
    exact congrArg σ₂ (Subtype.ext rfl)
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := id hU
  obtain ⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩ := id hU₂
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)
  obtain ⟨P₀, hP₀, hp₀, hu₀, -⟩ := hper₂ k₂ ⟨x₀, hx₀⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle,
      ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := CAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) hy
  obtain ⟨k, x₁, t₁, hb⟩ := hU.2.2.1 y
  obtain ⟨P₁, hP₁, hp₁, hu₁, -⟩ := hper k x₁
  have hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁ := by
    rw [← hu₁, ← hb.1]
    exact hyx.symm
  obtain ⟨gam, hl, hg, hh, hx⟩ := GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu
  have gM := mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx
  obtain ⟨a, ε, hε, hξ, hmul, hlat, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r
    ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm)
    ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by
      have e₁ := hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))
      have e₂ := hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)
      rw [hg] at e₁
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e₂
      exact e₁.symm.trans e₂)
  have hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0 := (hW k).2.trans (hW₂ k₂).2.symm
  obtain rfl : ε = 1 := mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])
  have hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm := (hW k).1.trans (hW₂ k₂).1.symm
  have hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ := fun τ =>
    ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm
  have hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0 := (hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm
  have hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w := fun v w => by
    rw [hiso, one_mul]
  have hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) =
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E) := fun b => by
    rw [hmul (φ₂ k₂ b)]
    simp
  refine ⟨k, a, hG.symm, fun v w => ?_, hlat, ?_⟩
  · have h' := hiso' v w
    rwa [hG] at h'
  intro x hx x' hmv
  have hx' : x' ∈ ((U σ).X k).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv
  refine ⟨hx', ?_⟩
  obtain ⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩ := hper k ⟨x', hx'⟩
  obtain ⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩ := hper₂ k₂ ⟨x, hx⟩
  obtain ⟨c₁, c₂⟩ := GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM
    (fun b i => by
      rw [hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]
      exact GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)
  have hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x := by
    rw [hqu₁, hqu₂]
    exact c₁
  have hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i :=
    fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)
  letI : Algebra c.F (CAt σ₂) := σ.toAlgebra
  obtain ⟨z, hzx, hzu, ho⟩ := exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu
  have hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1 := by
    intro hn τ i
    obtain ⟨τ, h₁⟩ := τ
    have h₂ := (hΨ τ).1 h₁
    have e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i := by
      unfold dmin
      rw [hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]
    rw [e']
    exact hn _ _
  refine ⟨t, fun hn => ?_, z, ?_, ho⟩
  · exact GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩)
      ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht
  · have e' : genScal (Dw := Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _
    exact e'.symm ▸ ht

open scoped Matrix in

theorem firstMinimumSq_eq_of_rationalIsometry_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X X₂ : Data E r)
    (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) (γ : GL (Fin r) E)
    (hΛ : ∀ v, v ∈ X₂.Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X.Λ)
    (hγ : ∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) =
      herm X₂.Gm v w) (hp : X.p0 = X₂.p0) (t : ℝ) (hc : ∀ τ, X.c τ = t) (hc₂ : ∀ τ, X₂.c τ = t)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (hrel : Moved X₂ X γ x x') : X.firstMinimumSq x' = X₂.firstMinimumSq x := by
  have hre : ∀ w, ∑ τ : X.Ψ, X.c τ * X.maj x' τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) =
      ∑ τ : X₂.Ψ, X₂.c τ * X₂.maj x τ (Data.emb τ.1 w) := fun w => by
    refine (Fintype.sum_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)).symm
    show X₂.c τ * X₂.maj x τ (Data.emb τ.1 w) = X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ *
      X.maj x' ⟨τ.1, (hΨ τ.1).1 τ.2⟩ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w))
    rw [GlobalTheory.CoverHol.maj_move X X₂ hγ hp x x' τ.1 τ.2 ((hΨ τ.1).1 τ.2) (hrel τ.1 τ.2 _), hc, hc₂]
  have e₁ : ∀ w, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = w :=
    fun w => by rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e₂ : ∀ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) = w :=
    fun w => by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine congrArg sInf (Set.ext fun s => ⟨?_, ?_⟩)
  · rintro ⟨v, hv, hv0, rfl⟩
    refine ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, (hΛ _).2 (by rwa [e₂]), fun h0 => hv0 ?_, ?_⟩
    · rw [← e₂ v, h0, Matrix.mulVec_zero]
    · rw [← hre, e₂]
  · rintro ⟨w, hw, hw0, rfl⟩
    refine ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ w, (hΛ _).1 hw, fun h0 => hw0 ?_, (hre w).symm⟩
    rw [← e₁ w, h0, Matrix.mulVec_zero]

set_option maxHeartbeats 1600000 in

theorem level_transport (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H)
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0)
    (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r)
    (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r)
    (hL : Laws D j Xo c U dict) (hL₂ : Laws D j d.Xo₂ d.c₂ U₂ dict₂) (hd : d.IsLev)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : Dom a n) (τ : d.c₂.F →+* ℂ) (hτ : GoodEmb d.c₂ τ) :
    ∃ φ : (Σ k, Frame ((U₂ τ).X k).Ψ D.R.r) → Σ k, Frame ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r,
      (∀ y : Σ k, Frame ((U₂ τ).X k).Ψ D.R.r, y.2 ∈ ((U₂ τ).X y.1).dom →
        (φ y).2 ∈ ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (φ y).1).dom ∧
        ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (φ y).1).firstMinimumSq (φ y).2 = ((U₂ τ).X y.1).firstMinimumSq y.2) ∧
      ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g →
        ∀ y : Σ k, Frame ((U₂ τ).X k).Ψ D.R.r, y.2 ∈ ((U₂ τ).X y.1).dom →
          ptN (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) y =
            ptN (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n))
              (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) (φ y) ∧
          (rdU (U₂ τ) g y.1 y.2 ≠ 0 ↔ rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (φ y).1 (φ y).2 ≠ 0) := by
  have hσ : GoodEmb c (τ.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d τ hτ
  choose π δ hGm hIso hLat hOv using over_comp_lat D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd τ hτ
  choose t ht hread using fun k₂ => GlobalTheory.T.levelCover_pullback_reading_eq_unitConst_pow_mul D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd τ hτ k₂ (π k₂) (δ k₂)
    (hGm k₂) (hIso k₂) (hOv k₂)
  have hΨ' : ∀ k₂ ρ, ρ ∈ ((U₂ τ).X k₂).Ψ ↔ ρ ∈ ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ := fun k₂ ρ =>
    (((hL₂.unf τ hτ).2.1 k₂).2 ρ).trans (((hL.unf _ hσ).2.1 (π k₂)).2 ρ).symm
  have hΨ : ∀ k₂, ((U₂ τ).X k₂).Ψ = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ := fun k₂ =>
    Finset.ext (hΨ' k₂)
  have hp0 : ∀ k₂, ((U₂ τ).X k₂).p0 = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).p0 := fun k₂ =>
    ((hL₂.unf τ hτ).2.1 k₂).1.trans ((hL.unf _ hσ).2.1 (π k₂)).1.symm
  have hu : ∀ k₂ v w, herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm
      ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ τ).X k₂).Gm v w := fun k₂ => by
    rw [← hGm k₂]; exact hIso k₂
  have hmv : ∀ k₂ x, Moved ((U₂ τ).X k₂) ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (δ k₂) x
      (lact (δ k₂) (hΨ k₂ ▸ x)) := fun k₂ x ρ h₂ h₁ => by
    show (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map ρ * mat (hΨ k₂ ▸ x) ⟨ρ, h₁⟩ = _
    congr 1
    unfold mat
    rw [GlobalTheory.LevPullNorm.frame_tr (hΨ k₂) x ρ h₁ h₂]
  refine ⟨fun y => ⟨π y.1, lact (δ y.1) (hΨ y.1 ▸ y.2)⟩, fun y hy => ⟨(hOv y.1 y.2 hy _ (hmv y.1 y.2)).1, ?_⟩,
    fun f hf g hg hp y hy => ?_⟩
  · exact firstMinimumSq_eq_of_rationalIsometry_lattice _ _ (hΨ' y.1) (δ y.1) (hLat y.1) (hu y.1) (hp0 y.1).symm (2 * xiR D)
      (fun ρ => congrArg (2 * ·) (hL.xiAbs _ hσ _ ρ.1)) (fun ρ => congrArg (2 * ·) (hL₂.xiAbs _ hτ _ ρ.1)) _ _
      (hmv y.1 y.2)
  · have hv := hread y.1 a n ha f hf g hg hp y.2 _ hy (hmv y.1 y.2) ha.2
    have hn : ‖t y.1 ^ n‖ = 1 := by rw [norm_pow, ht, one_pow]
    refine ⟨GlobalTheory.CoverHol.pnorm_move _ _ (hΨ' y.1) (hu y.1) _ _
      (fun ρ h₂ h₁ i => by simp only [modelWt, hp0 y.1, GlobalTheory.LevPullNorm.relab_eF]) _ _ _ _ (hmv y.1 y.2) _ hn hv, ?_⟩
    rw [hv, mul_ne_zero_iff_left (norm_ne_zero_iff.1 (by rw [hn]; exact one_ne_zero))]

set_option maxHeartbeats 1600000 in

theorem cover_transport (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hT : LawsJ T)
    (hj : InR D j) (hG : Y.Good e o) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : Dom a n)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    ∃ φ : (Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) → Σ k, Frame ((T.U j (Y.resEmb σ)).X k).Ψ D.R.r,
      (∀ y : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r, y.2 ∈ ((Y.U σ).X y.1).dom →
        (φ y).2 ∈ ((T.U j (Y.resEmb σ)).X (φ y).1).dom ∧
        ((T.U j (Y.resEmb σ)).X (φ y).1).firstMinimumSq (φ y).2 = ((Y.U σ).X y.1).firstMinimumSq y.2) ∧
      ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃ g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtZ a n),
        ∀ y : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r, y.2 ∈ ((Y.U σ).X y.1).dom →
          ptN (modelWt (Y.U σ) (wtZ a n)) (rdU (Y.U σ) g) y =
            ptN (modelWt (T.U j (Y.resEmb σ)) (wtZ a n)) (rdU (T.U j (Y.resEmb σ)) f) (φ y) ∧
          (rdU (Y.U σ) g y.1 y.2 ≠ 0 ↔ rdU (T.U j (Y.resEmb σ)) f (φ y).1 (φ y).2 ≠ 0) := by
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', -⟩ := GlobalTheory.T.moduliLaws_coefficientFieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hG.unit hG.modelW
  obtain ⟨φ, h1, h2⟩ := level_transport D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n ha σ hσ
  refine ⟨φ, h1, fun f hf => ?_⟩
  obtain ⟨g, ⟨hg, hgP⟩, -⟩ := GlobalTheory.CoverPull.cusp_pullback_existsUnique D T j Y e o hT hj hG hG.unit hG.modelW a n ha f hf
  have hs : f ∈ sec (T.Q.Xo j) T.Q.c a n := by
    rw [cuspW_wtZ] at hf
    exact cusp_le_sec _ _ _ a n hf
  have hgs : g ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have h := hg
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h
  have hV := (rulBC_sec_val_linear D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f hs
  have hrd : rdU (unfBC Y.hle (T.U j) (σ.comp (Y.d.eF : Y.c'.F →+* Y.d.c₂.F))) (rulBC Y.hle f) =
      rdU (T.U j (Y.resEmb σ)) f := by
    funext k x
    by_cases hx : x ∈ ((T.U j (Y.resEmb σ)).X k).dom
    · refine (dif_pos hx).trans (Eq.trans ?_ (dif_pos hx).symm)
      letI : Algebra T.Q.c.F (CAt (σ.comp (Y.d.eF : Y.c'.F →+* Y.d.c₂.F))) := (Y.resEmb σ).toAlgebra
      exact hV.2 (CAt (σ.comp (Y.d.eF : Y.c'.F →+* Y.d.c₂.F))) (fun _ => rfl) _
    · have e₂ : rdU (T.U j (Y.resEmb σ)) f k x = 0 := dif_neg hx
      exact (dif_neg hx).trans e₂.symm
  refine ⟨g, hg, fun y hy => ?_⟩
  have h3 := h2 _ hV.1 g hgs ((hP a n f hs g).1 hgP) y hy
  rw [hrd] at h3
  exact h3

end UpperTheory.Dv.Thin
