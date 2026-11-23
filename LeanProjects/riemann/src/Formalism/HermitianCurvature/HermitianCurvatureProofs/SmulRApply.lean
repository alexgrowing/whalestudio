import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

noncomputable section

open Finset Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.NFRO

open Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

def JetR {M : Type*} [AddCommGroup M] [Module ℝ M] (U : Set ℂ) (ζ0 : ℂ) (Λ : (ℂ → ℂ) → M) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (L : ι → ℂ →ₗ[ℝ] M),
    ∀ f, ContDiffOn ℝ ∞ f U → Λ f = ∑ i, L i (wd (w i) f ζ0)

theorem wn_cmono (ζ0 c : ℂ) (j l a b : ℕ) :
    wn a b (fun x => c * mono ζ0 j l x) ζ0 = c * wn a b (mono ζ0 j l) ζ0 := by
  have e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x := by funext x; ring
  have h1 : wn a b (fun x => c * mono ζ0 j l x) ζ0 =
      (c * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, iter_dZb_cmono, iter_dZ_cmono]
  have h2 : wn a b (mono ζ0 j l) ζ0 =
      (1 * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, e, iter_dZb_cmono, iter_dZ_cmono]
  rw [h1, h2]
  ring

section Zero

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_zero (hU : IsOpen U) (h0 : ζ0 ∈ U) {Λ : (ℂ → ℂ) → M} (hΛ : JetR U ζ0 Λ)
    (hP : ∀ (c : ℂ) (j l : ℕ), Λ (fun x => c * mono ζ0 j l x) = 0) : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = 0 := by
  classical
  obtain ⟨ι, _, w, L, h⟩ := hΛ
  let cnt : ι → ℕ × ℕ := fun i => ((w i).count false, (w i).count true)
  have hS : ∀ (c : ℕ × ℕ) (x : ℂ), ∑ i ∈ univ.filter (fun i => cnt i = c), L i x = 0 := by
    intro c x
    have hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y * ((c.1.factorial * c.2.factorial : ℕ) : ℂ) = x :=
      ⟨x / _, div_mul_cancel₀ x hne⟩
    have hsm : ContDiffOn ℝ ∞ (fun t => y * mono ζ0 c.1 c.2 t) U :=
      contDiffOn_const.mul (contDiff_mono ζ0 c.1 c.2).contDiffOn
    have hc := h _ hsm
    rw [hP] at hc
    have e1 : ∀ i, L i (wd (w i) (fun t => y * mono ζ0 c.1 c.2 t) ζ0) =
        if cnt i = c then L i x else 0 := by
      intro i
      rw [wd_eq hU hsm (w i) h0, wn_cmono, wn_mono]
      by_cases hi : cnt i = c
      · rw [if_pos hi, if_pos (by rw [← hi]), hy]
      · rw [if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), mul_zero, map_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter] at hc
    exact hc.symm
  intro f hf
  rw [h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]),
    ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt)
      (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e2 : ∀ i ∈ univ.filter (fun i => cnt i = c),
      L i (wn ((w i).count false) ((w i).count true) f ζ0) = L i (wn c.1 c.2 f ζ0) := by
    intro i hi
    have hi' : cnt i = c := (Finset.mem_filter.1 hi).2
    rw [← hi']
  rw [Finset.sum_congr rfl e2, hS c]

end Zero

section Deriv

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def smulR {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) : E →L[ℝ] (X →L[ℝ] E) :=
  ((ContinuousLinearMap.compL ℝ X ℂ E).flip c).comp (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

theorem smulR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) (e : E) (v : X) : smulR c e v = c v • e := by
  first
  | rfl
  | simp [smulR]

theorem jetR_iter (p : X →L[ℝ] ℂ) {U : Set ℂ} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : ∀ x ∈ V, p x ∈ U) {q : X} (hq : q ∈ V) (j : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (φ : X → E),
      ContDiffOn ℝ ∞ φ V → JetR U (p q) (fun f => iteratedFDeriv ℝ j (fun x => f (p x) • φ x) q) := by
  induction j with
  | zero =>
    intro E _ _ _ _ φ _
    let L0 : ℂ →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) E :=
      { toFun := fun c => (continuousMultilinearCurryFin0 ℝ X E).symm (c • φ q)
        map_add' := fun a b => by rw [add_smul, map_add]
        map_smul' := fun s a => by
          rw [RingHom.id_apply, smul_assoc, LinearIsometryEquiv.map_smul] }
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => L0, fun f _ => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | succ j ih =>
    intro E _ _ _ _ φ hφ
    let c2 : X →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp p
    have hφ' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ φ y) V := hφ.fderiv_of_isOpen hV (by simp)
    have hM1 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) p (φ y)) V :=
      (smulR (E := E) p).contDiff.comp_contDiffOn hφ
    have hM2 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) c2 (φ y)) V :=
      (smulR (E := E) c2).contDiff.comp_contDiffOn hφ
    obtain ⟨ι1, _, w1, L1, e1⟩ := ih (X →L[ℝ] E) _ hφ'
    obtain ⟨ι2, _, w2, L2, e2⟩ := ih (X →L[ℝ] E) _ hM1
    obtain ⟨ι3, _, w3, L3, e3⟩ := ih (X →L[ℝ] E) _ hM2
    let K : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (X →L[ℝ] E) →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) E :=
      (continuousMultilinearCurryRightEquiv' ℝ j X E).symm.toLinearEquiv.toLinearMap
    refine ⟨ι1 ⊕ ι2 ⊕ ι3, inferInstance,
      Sum.elim w1 (Sum.elim (fun i => w2 i ++ [false]) (fun i => w3 i ++ [true])),
      Sum.elim (fun i => K ∘ₗ L1 i) (Sum.elim (fun i => K ∘ₗ L2 i) (fun i => K ∘ₗ L3 i)), fun f hf => ?_⟩
    have hsm : ∀ {g : ℂ → ℂ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
        [IsScalarTower ℝ ℂ F] {ψ : X → F}, ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ ψ V →
        ContDiffAt ℝ j (fun y => g (p y) • ψ y) q := by
      intro g F _ _ _ _ ψ hg hψ
      exact (((hg.comp p.contDiff.contDiffOn hVU).smul hψ).contDiffAt (hV.mem_nhds hq)).of_le (inf_ge j)
    have hD : ∀ y ∈ V, fderiv ℝ (fun x => f (p x) • φ x) y =
        (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y) := by
      intro y hy
      have hfd : HasFDerivAt f (fderiv ℝ f (p y)) (p y) :=
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hVU y hy))).hasFDerivAt
      have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
        ((hφ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)).hasFDerivAt
      have hc : HasFDerivAt (fun x => f (p x)) ((fderiv ℝ f (p y)).comp p) y := hfd.comp y p.hasFDerivAt
      rw [(hc.fun_smul hφd).fderiv]
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smulR_apply, fderiv_wirt, add_smul,
        mul_smul, c2]
      simp [add_assoc]
    have hev : (fun y => fderiv ℝ (fun x => f (p x) • φ x) y) =ᶠ[𝓝 q]
        (fun y => (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y)) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) hD
    beta_reduce at e1 e2 e3 ⊢
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_add_apply ((hsm hf hφ').add (hsm (contDiffOn_dZ hU hf) hM1))
        (hsm (contDiffOn_dZb hU hf) hM2),
      fun_iteratedFDeriv_add_apply (hsm hf hφ') (hsm (contDiffOn_dZ hU hf) hM1),
      e1 f hf, e2 _ (contDiffOn_dZ hU hf), e3 _ (contDiffOn_dZb hU hf)]
    simp only [map_add, map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, wd_append]
    simp only [wd, Bool.false_eq_true, ↓reduceIte, add_assoc]
    rfl

end Deriv

section Closure

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_congr {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (e : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = Λ' f) :
    JetR U ζ0 Λ' := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, L, fun f hf => (e f hf).symm.trans (hL f hf)⟩

theorem jetR_map (Lm : M →ₗ[ℝ] N) {Λ : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) : JetR U ζ0 (fun f => Lm (Λ f)) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, fun i => Lm ∘ₗ L i, fun f hf => by simp only [hL f hf, map_sum, LinearMap.comp_apply]⟩

theorem jetR_add {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f + Λ' f) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  obtain ⟨ι', hι', w', L', hL'⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim L L', fun f hf => by
    simp only [hL f hf, hL' f hf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]⟩

theorem jetR_sub {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f - Λ' f) := by
  refine jetR_congr (jetR_add h (jetR_map (-LinearMap.id) h')) fun f _ => ?_
  simp [sub_eq_add_neg]

theorem jetR_sum {κ : Type*} (s : Finset κ) {Λ : κ → (ℂ → ℂ) → M} (h : ∀ j ∈ s, JetR U ζ0 (Λ j)) :
    JetR U ζ0 (fun f => ∑ j ∈ s, Λ j f) := by
  have h0 : JetR U ζ0 (fun _ : ℂ → ℂ => (0 : M)) :=
    ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun f _ => by simp⟩
  have hs := Finset.sum_induction Λ (JetR U ζ0) (fun a b ha hb => jetR_add ha hb) h0 h
  refine jetR_congr hs fun f _ => ?_
  simp [Finset.sum_apply]

theorem jetR_word (w : List Bool) (L : ℂ →ₗ[ℝ] M) : JetR U ζ0 (fun f => L (wd w f ζ0)) := by
  exact ⟨Unit, inferInstance, fun _ => w, fun _ => L, fun f _ => by simp⟩

def cl {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E) :
    ℂ →ₗ[ℝ] E where
  toFun c := (α * c) • e
  map_add' x y := by rw [mul_add, add_smul]
  map_smul' s c := by rw [RingHom.id_apply, mul_smul_comm, smul_assoc]

theorem cl_apply {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E)
    (c : ℂ) : cl α e c = (α * c) • e := rfl

end Closure

end Formalism.FourierDecayAlt.P.NFRO
