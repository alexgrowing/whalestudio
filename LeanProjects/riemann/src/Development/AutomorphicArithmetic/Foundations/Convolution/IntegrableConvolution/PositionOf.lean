import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory Matrix
open scoped ComplexConjugate NumberField.LiesOver

namespace UpperTheory.ConvolutionTheory.L1

section co
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

private theorem cpx (w : InfinitePlace K) : IsComplex w := IsTotallyComplex.isComplex w

open Classical in

private def co (τ : K →+* ℂ) : mixedSpace K →+* ℂ :=
  if (mk τ).embedding = τ then complexComp ⟨mk τ, cpx _⟩
  else (starRingEnd ℂ).comp (complexComp ⟨mk τ, cpx _⟩)

private theorem co_cases (τ : K →+* ℂ) :
    (∀ a, co τ a = a.2 ⟨mk τ, cpx _⟩) ∨ (∀ a, co τ a = conj (a.2 ⟨mk τ, cpx _⟩)) := by
  by_cases h : (mk τ).embedding = τ
  · left; intro a; simp [co, h]
  · right; intro a; simp [co, h]

private theorem co_along (τ : K →+* ℂ) (z : ℂ) : co τ (along τ z) = z := by
  by_cases h : (mk τ).embedding = τ
  · simp [co, h, along]
  · simp [co, h, along]

private theorem along_mul (τ : K →+* ℂ) (a : mixedSpace K) : along τ 1 * a = along τ (co τ a) := by
  refine Prod.ext ?_ ?_
  · simp [along]
  · funext ⟨w, hw⟩
    by_cases h : w = mk τ
    · subst h
      by_cases h : (mk τ).embedding = τ
      · simp [co, h, along]
      · simp [co, h, along]
    · simp [along, h]

private theorem along_zero (τ : K →+* ℂ) : along τ 0 = 0 := by
  refine Prod.ext rfl ?_
  funext ⟨w, hw⟩
  simp [along]

private theorem ne_zero_co {a : mixedSpace K} (ha : a ≠ 0) : ∃ τ : K →+* ℂ, co τ a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply ha
  refine Prod.ext ?_ ?_
  · funext ⟨w, hw⟩
    exact absurd hw (not_isReal_iff_isComplex.2 (cpx w))
  · funext ⟨w, hw⟩
    have h := hc w.embedding
    have hm : mk w.embedding = w := mk_embedding w
    rcases co_cases w.embedding with h1 | h1
    · rw [h1] at h
      simpa [hm] using h
    · rw [h1] at h
      simpa [hm] using h

private theorem mk_eq_of_co_along {τ τ₀ : K →+* ℂ} {z : ℂ} (h : co τ (along τ₀ z) ≠ 0) : mk τ = mk τ₀ := by
  by_contra hc
  apply h
  rcases co_cases τ with h1 | h1 <;> simp [h1, along, hc]

open Classical in

private def cc (w : InfinitePlace K) (τ : K →+* ℂ) : w.Completion →+* ℂ :=
  if w.embedding = τ then Completion.extensionEmbedding w
  else (starRingEnd ℂ).comp (Completion.extensionEmbedding w)

private theorem continuous_cc (w : InfinitePlace K) (τ : K →+* ℂ) : Continuous (cc w τ) := by
  have h0 : Continuous (Completion.extensionEmbedding w) := (Completion.isometry_extensionEmbedding w).continuous
  by_cases h : w.embedding = τ
  · simpa [cc, h] using h0
  · simpa [cc, h] using Complex.continuous_conj.comp h0

private theorem cc_alg (τ : K →+* ℂ) (w : InfinitePlace K) (h : mk τ = w) (x : K) :
    cc w τ (algebraMap K w.Completion x) = τ x := by
  subst h
  have e : Completion.extensionEmbedding (mk τ) (algebraMap K _ x) = (mk τ).embedding x := by
    rw [Completion.algebraMap_apply]
    exact Completion.extensionEmbedding_coe _ _
  by_cases h1 : (mk τ).embedding = τ
  · rw [cc, if_pos h1, e, h1]
  · have h := (embedding_mk_eq τ).resolve_left h1
    rw [cc, if_neg h1, RingHom.comp_apply, e, h]
    simp [ComplexEmbedding.conjugate_coe_eq]

private theorem co_psi (τ : K →+* ℂ) (y : InfiniteAdeleRing K) :
    co τ (InfiniteAdeleRing.ringEquiv_mixedSpace K y) = cc (mk τ) τ (y (mk τ)) := by
  by_cases h : (mk τ).embedding = τ
  · simp [co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]
  · simp [co, cc, h, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, complexComp]

private theorem cc_unique (w : InfinitePlace K) (f g : w.Completion →+* ℂ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K _ x) = g (algebraMap K _ x)) : f = g := by
  have hd : DenseRange (algebraMap K w.Completion) := by
    refine Dense.mono ?_ (Completion.denseRange_coe w)
    rintro _ ⟨x, rfl⟩
    exact ⟨WithAbs.equiv _ x, Completion.algebraMap_apply _ _⟩
  exact DFunLike.coe_injective (hd.equalizer hf hg (funext h))

private theorem conj_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M ∈ unitaryGroup (Fin n) ℂ) :
    M.map (starRingEnd ℂ) ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at h ⊢
  have h2 := congrArg (RingHom.mapMatrix (starRingEnd ℂ)) h
  rw [map_mul, map_one] at h2
  have e : star (M.map (starRingEnd ℂ)) = RingHom.mapMatrix (starRingEnd ℂ) (star M) := by
    ext i j
    simp [Matrix.star_apply]
  rw [e]
  exact h2

private theorem co_unitary {n : ℕ} (τ : K →+* ℂ) (M : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    M.map (co τ) ∈ unitaryGroup (Fin n) ℂ ↔ M.map (complexComp ⟨mk τ, cpx _⟩) ∈ unitaryGroup (Fin n) ℂ := by
  rcases co_cases τ with h1 | h1
  · have e : M.map (co τ) = M.map (complexComp ⟨mk τ, cpx _⟩) := by ext i j; simp [h1]
    rw [e]
  · have e : M.map (co τ) = (M.map (complexComp ⟨mk τ, cpx _⟩)).map (starRingEnd ℂ) := by ext i j; simp [h1]
    have e2 : M.map (complexComp ⟨mk τ, cpx _⟩) = (M.map (co τ)).map (starRingEnd ℂ) := by ext i j; simp [h1]
    exact ⟨fun h => e2 ▸ conj_unitary h, fun h => e ▸ conj_unitary h⟩

private theorem co_unitary_of_mk {n : ℕ} {τ τ₀ : K →+* ℂ} (h : mk τ = mk τ₀) (M : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    M.map (co τ) ∈ unitaryGroup (Fin n) ℂ ↔ M.map (co τ₀) ∈ unitaryGroup (Fin n) ℂ := by
  have e : (⟨mk τ, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = ⟨mk τ₀, cpx _⟩ := Subtype.ext h
  rw [co_unitary, co_unitary, e]

private theorem archC_iff {n : ℕ} (x : archGroup K n) :
    x ∈ archCompact K n ↔
      ∀ τ : K →+* ℂ, (mat ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n)).map (co τ) ∈ unitaryGroup (Fin n) ℂ := by
  constructor
  · intro hx τ
    rw [co_unitary]
    exact complexCompM_mem_unitaryGroup hx ⟨mk τ, cpx _⟩
  · intro h
    refine mem_archCompact_of_unitary x (fun v => absurd v.2 (not_isReal_iff_isComplex.2 (cpx _))) fun v => ?_
    have h1 := (co_unitary _ _).1 (h v.1.embedding)
    have e : (⟨mk v.1.embedding, cpx _⟩ : {w : InfinitePlace K // IsComplex w}) = v := Subtype.ext (mk_embedding _)
    rw [e] at h1
    exact h1

end co

section ext
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]

private theorem totC (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] :
    IsTotallyComplex E := ⟨fun w => by
  rw [← not_isReal_iff_isComplex]
  intro h
  have h1 := isReal_iff.1 h
  have h2 := ComplexEmbedding.IsReal.comp (algebraMap F E) h1
  exact not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (mk (w.embedding.comp (algebraMap F E))))
    (isReal_mk_iff.2 h2)⟩

variable [IsTotallyComplex E]

private theorem co_iota (τ : E →+* ℂ) (y : InfiniteAdeleRing F) :
    co τ (InfiniteAdeleRing.ringEquiv_mixedSpace E (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) y)) =
      co (τ.comp (algebraMap F E)) (InfiniteAdeleRing.ringEquiv_mixedSpace F y) := by
  rw [co_psi, co_psi]
  have key : ∀ (v : InfinitePlace F), mk (τ.comp (algebraMap F E)) = v →
      cc (mk (τ.comp (algebraMap F E))) (τ.comp (algebraMap F E)) (y (mk (τ.comp (algebraMap F E)))) =
        cc v (τ.comp (algebraMap F E)) (y v) := by
    rintro _ rfl
    rfl
  have hv : mk (τ.comp (algebraMap F E)) = (mk τ).comap (algebraMap F E) := (comap_mk _ _).symm
  rw [key _ hv, GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply]
  have hcont : Continuous (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion) :=
    NumberField.LiesOver.continuous_completionMap (v := (mk τ).comap (algebraMap F E)) (w := mk τ)
  have h : (cc (mk τ) τ).comp (algebraMap ((mk τ).comap (algebraMap F E)).Completion (mk τ).Completion) =
      cc ((mk τ).comap (algebraMap F E)) (τ.comp (algebraMap F E)) := by
    refine cc_unique _ _ _ ((continuous_cc _ _).comp hcont) (continuous_cc _ _) fun x => ?_
    rw [cc_alg _ _ hv, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply F E, cc_alg _ _ rfl]
    rfl
  exact congrArg (fun f => f (y ((mk τ).comap (algebraMap F E)))) h

end ext

section intersection_update_fsHerm_neg_one
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

private def P (τ : K →+* ℂ) (z : ℂ) : InfiniteAdeleRing K := (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (along τ z)

private def cq (τ : K →+* ℂ) : InfiniteAdeleRing K →+* ℂ :=
  (co τ).comp (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedSpace K)

private theorem cq_apply (τ : K →+* ℂ) (x : InfiniteAdeleRing K) :
    cq τ x = co τ (InfiniteAdeleRing.ringEquiv_mixedSpace K x) := rfl

private theorem cq_P (τ : K →+* ℂ) (z : ℂ) : cq τ (P τ z) = z := by
  rw [cq_apply, P, RingEquiv.apply_symm_apply, co_along]

private theorem twoPow_mul_twoPow (τ : K →+* ℂ) (x : InfiniteAdeleRing K) : P τ 1 * x = P τ (cq τ x) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
  rw [map_mul, P, P, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, along_mul, cq_apply]

private theorem P_zero (τ : K →+* ℂ) : P τ 0 = 0 := by
  rw [P, along_zero, map_zero]

private theorem P_one_ne (τ : K →+* ℂ) : P τ 1 ≠ 0 := by
  intro h
  have := cq_P τ 1
  rw [h, map_zero] at this
  exact zero_ne_one this

private theorem idem_eq (τ : K →+* ℂ) {x : InfiniteAdeleRing K} (hx : P τ 1 * x = x) (hi : x * x = x) (h0 : x ≠ 0) :
    x = P τ 1 := by
  have hc : cq τ x * cq τ x = cq τ x := by rw [← map_mul, hi]
  have e : x = P τ (cq τ x) := by rw [← twoPow_mul_twoPow, hx]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hc with h | h
  · rw [h, P_zero] at e
    exact absurd e h0
  · rwa [h] at e

end intersection_update_fsHerm_neg_one

section main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
  [IsTotallyComplex E] {σ : E ≃ₐ[F] E} {m : ℕ}

private theorem cq_iota (τ : E →+* ℂ) (y : InfiniteAdeleRing F) :
    cq τ (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) y) = cq (τ.comp (algebraMap F E)) y :=
  co_iota τ y

private theorem exists_continuousLinearMap_tens_update (D : InfD σ m) (τ : E →+* ℂ) :
    ∃ k : Fin (m + 1), D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1) := by
  set τ' := τ.comp (algebraMap F E) with hτ'
  set π : InfiniteAdeleRing E := P τ 1 with hπ
  set πF : InfiniteAdeleRing F := P τ' 1 with hπF
  have hidem : π * π = π := by rw [hπ, twoPow_mul_twoPow, cq_P]
  have hidemF : πF * πF = πF := by rw [hπF, twoPow_mul_twoPow, cq_P]
  have h1 : π * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) πF = π := by
    rw [hπ, twoPow_mul_twoPow, cq_iota, ← hτ', hπF, cq_P]
  have h2 : ∀ i, πF * D.e π i = D.e π i := by
    intro i
    have h := congrFun (congrArg D.e h1) i
    rw [map_mul, Pi.mul_apply, D.map_diag, mul_comm] at h
    exact h
  have hne : D.e π ≠ 0 := fun h => P_one_ne τ (D.e.injective (h.trans (map_zero _).symm))
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  have hidemk : D.e π k * D.e π k = D.e π k := by
    have h := congrFun (congrArg D.e hidem) k
    rwa [map_mul, Pi.mul_apply] at h
  have hk1 : D.e π k = πF := idem_eq τ' (h2 k) hidemk hk
  refine ⟨k, ?_⟩
  have hs : D.e.symm (Pi.single k πF) = π := by
    refine idem_eq τ ?_ ?_ ?_
    · apply D.e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      funext j
      by_cases hj : j = k
      · subst hj
        have hk1' : D.e (P τ 1) j = πF := hk1
        simp [hk1', hidemF]
      · simp [Pi.single_eq_of_ne hj]
    · apply D.e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hidemF]
      · simp [Pi.single_eq_of_ne hj]
    · intro h
      have h' := congrArg D.e h
      rw [RingEquiv.apply_symm_apply, map_zero] at h'
      have := congrFun h' k
      simp only [Pi.single_eq_same, Pi.zero_apply] at this
      exact P_one_ne τ' this
  rw [← hs, RingEquiv.apply_symm_apply]

private theorem position_P (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1))
    (hk : D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1)) (z : ℂ) :
    D.e (P τ z) = Pi.single k (P (τ.comp (algebraMap F E)) z) := by
  have h : P τ z = P τ 1 * GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (P (τ.comp (algebraMap F E)) z) := by
    rw [twoPow_mul_twoPow, cq_iota, cq_P]
  rw [h, map_mul, hk]
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Pi.mul_apply, D.map_diag, Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow, cq_P]
  · simp [Pi.single_eq_of_ne hj]

private theorem position_cq (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1))
    (hk : D.e (P τ 1) = Pi.single k (P (τ.comp (algebraMap F E)) 1)) (x : InfiniteAdeleRing E) :
    cq (τ.comp (algebraMap F E)) (D.e x k) = cq τ x := by
  have h := congrFun (congrArg D.e (twoPow_mul_twoPow τ x)) k
  rw [map_mul, Pi.mul_apply, hk, position_P D τ k hk (cq τ x), Pi.single_eq_same, Pi.single_eq_same, twoPow_mul_twoPow] at h
  have h' := congrArg (cq (τ.comp (algebraMap F E))) h
  rwa [cq_P, cq_P] at h'

private theorem exists_over (D : InfD σ m) (i : Fin (m + 1)) (τ₀ : F →+* ℂ) :
    ∃ τ : E →+* ℂ, D.e (P τ 1) = Pi.single i (P (τ.comp (algebraMap F E)) 1) ∧ mk (τ.comp (algebraMap F E)) = mk τ₀ := by
  set e : InfiniteAdeleRing E := D.e.symm (Pi.single i (P τ₀ 1)) with he
  have hDe : D.e e = Pi.single i (P τ₀ 1) := RingEquiv.apply_symm_apply _ _
  have hne : InfiniteAdeleRing.ringEquiv_mixedSpace E e ≠ 0 := by
    intro h
    have h0 : e = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective (h.trans (map_zero _).symm)
    rw [h0, map_zero] at hDe
    have := congrFun hDe i
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact P_one_ne τ₀ this.symm
  obtain ⟨τ, hτ⟩ := ne_zero_co hne
  obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
  have h1 := position_cq D τ k hk e
  rw [hDe] at h1
  by_cases hki : k = i
  · subst hki
    refine ⟨τ, hk, ?_⟩
    rw [Pi.single_eq_same] at h1
    refine mk_eq_of_co_along (z := 1) ?_
    have h2 : co (τ.comp (algebraMap F E)) (along τ₀ 1) = cq (τ.comp (algebraMap F E)) (P τ₀ 1) := by
      rw [cq_apply, P, RingEquiv.apply_symm_apply]
    rw [h2, h1]
    exact hτ
  · rw [Pi.single_eq_of_ne hki, map_zero] at h1
    exact absurd h1.symm hτ

end main

theorem _root_.UpperTheory.ConvolutionTheory.L1.positionOf :
    UpperTheory.ConvolutionTheory.L1.PositionOf := by
  intro F E _ _ _ _ _ _ σ m D
  haveI : IsTotallyComplex E := totC F E
  have entry : ∀ (n : ℕ) (g : archGroup E n) (i : Fin (m + 1)) (τ : E →+* ℂ),
      D.e (P τ 1) = Pi.single i (P (τ.comp (algebraMap F E)) 1) →
      (mat (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n)).map (co (τ.comp (algebraMap F E))) =
        (mat ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)).map (co τ) := by
    intro n g i τ hk
    ext a b
    have h := position_cq D τ i hk ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (mat ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) a b))
    rw [cq_apply, cq_apply, RingEquiv.apply_symm_apply] at h
    exact h
  refine ⟨fun τ => ?_, fun n g => ?_⟩
  · obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
    refine ⟨k, fun z => ?_⟩
    have h := position_P D τ k hk z
    exact (D.e.symm_apply_apply (P τ z)).symm.trans (congrArg D.e.symm h)
  · rw [archC_iff]
    constructor
    · intro h i
      rw [archC_iff]
      intro τ₀
      obtain ⟨τ, hτ, hm⟩ := exists_over D i τ₀
      rw [← co_unitary_of_mk hm, entry n g i τ hτ]
      exact h τ
    · intro h τ
      obtain ⟨k, hk⟩ := exists_continuousLinearMap_tens_update D τ
      have h1 := (archC_iff _).1 (h k) (τ.comp (algebraMap F E))
      rwa [entry n g k τ hk] at h1

end UpperTheory.ConvolutionTheory.L1
