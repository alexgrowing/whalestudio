import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

theorem dense_of_span_real {g : ℕ} (S : Submodule ℚ (Fin g → ℂ))
    (hS : Submodule.span ℝ (S : Set (Fin g → ℂ)) = ⊤) : Dense (S : Set (Fin g → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hz : z ∈ Submodule.span ℝ (S : Set (Fin g → ℂ)) := hS ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem w hw => exact subset_closure hw
  | zero => exact subset_closure S.zero_mem
  | add a b _ _ ha hb => exact map_mem_closure₂ continuous_add ha hb fun c hc d hd => S.add_mem hc hd
  | smul t w _ hw =>

    have hq : ∀ q : ℚ, (q : ℝ) • w ∈ closure (S : Set (Fin g → ℂ)) := fun q =>
      map_mem_closure (continuous_const_smul (q : ℝ)) hw fun u hu => by
        rw [SetLike.mem_coe, Rat.cast_smul_eq_qsmul ℝ q u]
        exact S.smul_mem q hu
    have hcl : IsClosed {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    have hsub : closure (Set.range fun q : ℚ => (q : ℝ)) ⊆ {s : ℝ | s • w ∈ closure (S : Set (Fin g → ℂ))} :=
      hcl.closure_subset_iff.2 (by rintro _ ⟨q, rfl⟩; exact hq q)
    exact hsub ((Rat.denseRange_cast (𝕜 := ℝ)).closure_range ▸ Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

noncomputable def zRLin (x : Frame X.Ψ r) : WR X n →ₗ[ℝ] (Fin n → Fin g → ℂ) where
  toFun := zR X idx x
  map_add' u v := by
    funext k i
    simp only [zR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' t v := by
    funext k i
    simp only [zR, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

theorem denseRange_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (pv X idx x) := by

  have hrange : ((LinearMap.range ((LinearMap.funLeft ℚ ℂ idx).comp (perLin X x)) :
      Submodule ℚ (Fin g → ℂ)) : Set (Fin g → ℂ)) = Set.range (pv X idx x) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    exact Iff.rfl
  unfold DenseRange
  rw [← hrange]
  apply dense_of_span_real
  rw [hrange]
  exact GlobalTheory.Dict.span_range_pv idx hs hx

theorem denseRange_zR_embR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    DenseRange (zR X idx x ∘ embR X (n := n)) := by
  have h : zR X idx x ∘ embR X (n := n) = fun y k => pv X idx x (y k) := by
    funext y k
    exact zR_embR X idx x y k
  rw [h]
  exact DenseRange.piMap fun _ => denseRange_pv X idx hs hx

theorem exists_equiv_zR (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v := by

  have hsurj : Function.Surjective (zRLin X idx x (n := n)) := by
    have hcl : IsClosed (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      refine (denseRange_zR_embR X idx hs hx (n := n)).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨embR X y, rfl⟩
    have huniv := hcl.closure_eq.symm.trans hd.closure_eq
    intro z
    have hz : z ∈ (LinearMap.range (zRLin X idx x (n := n)) : Set (Fin n → Fin g → ℂ)) := by
      rw [huniv]
      trivial
    exact LinearMap.mem_range.1 hz

  have hg : g = Fintype.card X.Ψ * r := by
    simpa [Fintype.card_prod] using Fintype.card_congr idx
  have hdim : Module.finrank ℝ (WR X n) = Module.finrank ℝ (Fin n → Fin g → ℂ) := by
    simp only [WR, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hg]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun v => rfl⟩

theorem EFR_embR (y y' : Matrix (Fin n) (Fin r) E) :
    EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ) := by
  have key : ∀ (τ : X.Ψ) (k : Fin n),
      hermC τ.1 X.Gm (embR X y τ k) (embR X y' τ k) = τ.1 (herm X.Gm (y k) (y' k)) :=
    fun τ k => ReciprocityTheory.ChartRestriction.G.FD.hermC_emb τ.1 X.Gm (y k) (y' k)
  rw [EFR, Rat.cast_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EF_def, GlobalTheory.UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [key, map_mul]

theorem zR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn x hxd
  obtain ⟨L, hL⟩ := exists_equiv_zR X idx (n := n) hs hxd
  have hlaws := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd

  have hD : DenseRange (embR X (n := n)) := by
    have h1 : embR X (n := n) = L.symm ∘ (zR X idx x ∘ embR X) := by
      funext y
      simp only [Function.comp_apply, ← hL, ContinuousLinearEquiv.symm_apply_apply]
    rw [h1]
    exact L.symm.surjective.denseRange.comp (denseRange_zR_embR X idx hs hxd) L.symm.continuous

  have hB : ∀ v v' : WR X n,
      (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v' := by
    have hc1 : Continuous fun p : WR X n × WR X n =>
        (∑ k, hx X bas idx x (zR X idx x p.1 k) (zR X idx x p.2 k)).im := by
      simp only [← hL, GlobalTheory.Dict.hx]
      fun_prop
    have hc2 : Continuous fun p : WR X n × WR X n => EFR X p.1 p.2 := by
      simp only [EFR, hermC]
      fun_prop
    have heq := (hD.prodMap hD).equalizer hc1 hc2 (by
      funext ⟨y, y'⟩
      simp only [Function.comp_apply, Prod.map_apply]
      rw [EFR_embR X y y', Complex.im_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zR_embR, zR_embR]
      exact hlaws.2.2.1 (y k) (y' k))
    exact fun v v' => congrFun heq (v, v')

  have hF : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n,
      zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) =
        zR X idx x v := by
    intro γ hγ
    have hA : Continuous fun v : WR X n =>
        (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k : WR X n) := by
      fun_prop
    have hc1 : Continuous fun v : WR X n =>
        zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) :=
      (LinearMap.continuous_of_finiteDimensional (zRLin X idx (lact γ x) (n := n))).comp hA
    have hc2 : Continuous fun v : WR X n => zR X idx x v := by
      simp only [← hL]
      exact L.continuous
    have heq := hD.equalizer hc1 hc2 (by
      funext y
      simp only [Function.comp_apply]
      have hemb : (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ embR X y τ k : WR X n) =
          embR X (Matrix.of fun k => (γ : Matrix (Fin r) (Fin r) E) *ᵥ y k) := by
        funext τ k
        exact (GlobalTheory.PerMove.emb_mulVec τ.1 _ (y k)).symm
      rw [hemb]
      funext k
      rw [zR_embR, zR_embR]
      exact (hlaws.2.2.2.2.2.2.2 γ hγ).2.1 (y k))
    exact fun v => congrFun heq v
  exact ⟨⟨L, hL⟩, hB, fun y y' => EFR_embR X y y', hD, hF⟩

end GlobalTheory.Ker
