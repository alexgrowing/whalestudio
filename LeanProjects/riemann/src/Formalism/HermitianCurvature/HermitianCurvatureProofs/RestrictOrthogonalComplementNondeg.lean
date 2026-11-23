import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x6
open Module

structure Inv {K : Type} [Field K] (σ : K →+* K) : Prop where
  invol : ∀ x, σ (σ x) = x
  norm_surj : ∀ c, σ c = c → ∃ y, σ y * y = c
  trace_one : ∃ l, l + σ l = 1

variable {K : Type} [Field K] {σ : K →+* K}

def Herm {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) : Prop :=
  ∀ u v, σ (h u v) = h v u

def Nondeg {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) : Prop :=
  ∀ u, (∀ v, h u v = 0) → u = 0

def Ortho {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [DecidableEq ι]
    (b : ι → V) : Prop := ∀ i j, h (b i) (b j) = if i = j then 1 else 0

section A1
variable {V : Type} [AddCommGroup V] [Module K V]

def restrictFormAlt (h : V →ₛₗ[σ] V →ₗ[K] K) (W : Submodule K V) : W →ₛₗ[σ] W →ₗ[K] K :=
  h.domRestrict₁₂ W W

lemma restrict_form_apply (h : V →ₛₗ[σ] V →ₗ[K] K) (W : Submodule K V) (u v : W) :
    restrictFormAlt h W u v = h u v := rfl

lemma restrict_form_hermitian {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) (W : Submodule K V) :
    Herm (restrictFormAlt h W) := fun u v => hh u v

lemma restrict_orthogonal_complement_nondeg {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) (hn : Nondeg h) (v : V)
    (hv : h v v = 1) : Nondeg (restrictFormAlt h (LinearMap.ker (h v))) := by
  intro w hw
  apply Subtype.ext
  apply hn
  intro z
  have hz : z - h v z • v ∈ LinearMap.ker (h v) := by
    simp [LinearMap.mem_ker, hv]
  have h1 := hw ⟨_, hz⟩
  have h2 : h w v = 0 := by
    rw [← hh v w]
    have := w.2
    rw [LinearMap.mem_ker] at this
    rw [this, map_zero]
  rw [restrict_form_apply] at h1
  simpa [map_sub, h2] using h1

lemma finrank_orthogonal_unit_add_one [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (v : V) (hv : h v v = 1) :
    finrank K (LinearMap.ker (h v)) + 1 = finrank K V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (h v)
  have hr : LinearMap.range (h v) = ⊤ :=
    LinearMap.range_eq_top.2 (fun c => ⟨c • v, by simp [hv]⟩)
  rw [hr, finrank_top, finrank_self] at h1
  omega

lemma exists_unit_norm_vector (hσ : Inv σ) {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h)
    (hne : ∃ u v, h u v ≠ 0) : ∃ v, h v v = 1 := by
  have h1 : ∃ v, h v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, v, huv⟩ := hne
    obtain ⟨l, hl⟩ := hσ.trace_one
    have h2 := hcon (u + (l / h u v) • v)
    have h3 : h (u + (l / h u v) • v) (u + (l / h u v) • v) =
        h u u + (l / h u v) * h u v + σ (l / h u v) * h v u + σ (l / h u v) * ((l / h u v) * h v v) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring
    rw [h3, hcon u, hcon v, ← hh u v, ← map_mul, div_mul_cancel₀ _ huv] at h2
    simp only [mul_zero, add_zero, zero_add] at h2
    rw [hl] at h2
    exact one_ne_zero h2
  obtain ⟨v, hv⟩ := h1
  obtain ⟨y, hy⟩ := hσ.norm_surj (h v v) (hh v v)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hv
    rw [← hy]
    simp
  refine ⟨y⁻¹ • v, ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [← hy, map_inv₀]
  have : σ y ≠ 0 := by
    intro h0
    apply hv
    rw [← hy, h0, zero_mul]
  field_simp

lemma orthonormal_cons_iff {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) {n : ℕ} (v : V) (c : Fin n → V) :
    Ortho h (Fin.cons v c : Fin (n + 1) → V) ↔ h v v = 1 ∧ (∀ i, h v (c i) = 0) ∧ Ortho h c := by
  constructor
  · intro H
    refine ⟨by simpa using H 0 0, fun i => ?_, fun i j => ?_⟩
    · have := H 0 i.succ
      simpa [(Fin.succ_ne_zero i).symm] using this
    · have := H i.succ j.succ
      simpa using this
  · rintro ⟨h1, h2, h3⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h1
    · simpa [(Fin.succ_ne_zero j).symm] using h2 j
    · have : h (c i) v = 0 := by rw [← hh v (c i), h2 i, map_zero]
      simpa [Fin.succ_ne_zero i] using this
    · simpa using h3 i j

end A1

theorem exists_orthonormal (hσ : Inv σ) (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K), Herm h → Nondeg h → finrank K V = n →
    ∃ b : Basis (Fin n) K V, Ortho h b := by
  induction n with
  | zero =>
    intro V _ _ _ h _ _ hfin
    exact ⟨finBasisOfFinrankEq K V hfin, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hh hn hfin
    have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hne : ∃ u v, h u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hn u (hcon u))
    obtain ⟨v, hv⟩ := exists_unit_norm_vector hσ hh hne
    have hW := finrank_orthogonal_unit_add_one h v hv
    obtain ⟨bW, hbW⟩ := ih (LinearMap.ker (h v)) (restrictFormAlt h _) (restrict_form_hermitian hh _)
      (restrict_orthogonal_complement_nondeg hh hn v hv) (by omega)
    refine ⟨Basis.mkFinCons v bW ?_ ?_, ?_⟩
    · intro c x hx hc
      have := congrArg (h v) hc
      rw [LinearMap.mem_ker] at hx
      simpa [hv, hx] using this
    · intro z
      exact ⟨-(h v z), by simp [LinearMap.mem_ker, hv]⟩
    · rw [Basis.coe_mkFinCons, orthonormal_cons_iff hh]
      refine ⟨hv, fun i => ?_, fun i j => hbW i j⟩
      exact LinearMap.mem_ker.1 (bW i).2

lemma form_norm_orthonormal_coords {V : Type} [AddCommGroup V] [Module K V] {h : V →ₛₗ[σ] V →ₗ[K] K} {n : ℕ}
    (b : Basis (Fin n) K V) (hb : Ortho h b) (v : V) :
    h v v = ∑ i, σ (b.equivFun v i) * b.equivFun v i := by
  conv_lhs => rw [← b.sum_equivFun v]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, hb _ _]
  simp [mul_comm]

lemma card_unit_norm_vectors (hσ : Inv σ) [Finite K] (s : ℕ → ℕ)
    (hs : ∀ n, Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1} = s n) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K)
    (hh : Herm h) (hn : Nondeg h) (hfin : finrank K V = n) :
    Nat.card {v : V // h v v = 1} = s n := by
  obtain ⟨b, hb⟩ := exists_orthonormal hσ n V h hh hn hfin
  rw [← hs n]
  exact Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv (fun v => by
    rw [form_norm_orthonormal_coords b hb v]; rfl))

def orthonormalFrameEquiv {V : Type} [AddCommGroup V] [Module K V] {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h)
    (n : ℕ) : {b : Fin (n + 1) → V // Ortho h b} ≃
      Σ v : {v : V // h v v = 1},
        {c : Fin n → LinearMap.ker (h v.1) // Ortho (restrictFormAlt h (LinearMap.ker (h v.1))) c} where
  toFun b :=
    have H : Ortho h (Fin.cons (b.1 0) (fun i => b.1 i.succ) : Fin (n + 1) → V) := by
      have : (Fin.cons (b.1 0) (fun i => b.1 i.succ) : Fin (n + 1) → V) = b.1 :=
        Fin.cons_self_tail b.1
      rw [this]; exact b.2
    ⟨⟨b.1 0, ((orthonormal_cons_iff hh _ _).1 H).1⟩,
      ⟨fun i => ⟨b.1 i.succ, LinearMap.mem_ker.2 (((orthonormal_cons_iff hh _ _).1 H).2.1 i)⟩,
        fun i j => ((orthonormal_cons_iff hh _ _).1 H).2.2 i j⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun i => ((p.2.1 i : LinearMap.ker (h p.1.1)) : V)),
    (orthonormal_cons_iff hh _ _).2 ⟨p.1.2, fun i => LinearMap.mem_ker.1 (p.2.1 i).2,
      fun i j => p.2.2 i j⟩⟩
  left_inv b := Subtype.ext (Fin.cons_self_tail b.1)
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, ⟨c, hc⟩⟩
    rfl

theorem card_frames (hσ : Inv σ) [Finite K] (s : ℕ → ℕ)
    (hs : ∀ n, Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1} = s n) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K),
    Herm h → Nondeg h → finrank K V = n →
    Nat.card {b : Fin n → V // Ortho h b} = ∏ j ∈ Finset.range n, s (j + 1) := by
  induction n with
  | zero =>
    intro V _ _ _ h _ _ _
    rw [Finset.prod_range_zero, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨Fin.elim0, fun i => i.elim0⟩⟩⟩
  | succ n ih =>
    intro V _ _ _ h hh hn hfin
    have : Finite V := Module.finite_of_finite K
    let _ : Fintype {v : V // h v v = 1} := Fintype.ofFinite _
    rw [Nat.card_congr (orthonormalFrameEquiv hh n), Nat.card_sigma]
    have h1 : ∀ v : {v : V // h v v = 1},
        Nat.card {c : Fin n → LinearMap.ker (h v.1) // Ortho (restrictFormAlt h (LinearMap.ker (h v.1))) c} =
          ∏ j ∈ Finset.range n, s (j + 1) := by
      intro v
      have hW := finrank_orthogonal_unit_add_one h v.1 v.2
      exact ih (LinearMap.ker (h v.1)) (restrictFormAlt h _) (restrict_form_hermitian hh _)
        (restrict_orthogonal_complement_nondeg hh hn v.1 v.2) (by omega)
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_unit_norm_vectors hσ s hs (n + 1) V h hh hn hfin,
      Finset.prod_range_succ, smul_eq_mul, mul_comm]

section A2
variable {V : Type} [AddCommGroup V] [Module K V]

lemma form_sum_right_alt (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (u : V) (c : ι → K)
    (x : ι → V) : h u (∑ j, c j • x j) = ∑ j, c j * h u (x j) := by
  simp [map_sum]

lemma form_sum_left_alt (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (u : V) (c : ι → K)
    (x : ι → V) : h (∑ j, c j • x j) u = ∑ j, σ (c j) * h (x j) u := by
  simp [map_sum, LinearMap.sum_apply]

def gramMatrix (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} (x : ι → V) : Matrix ι ι K :=
  Matrix.of fun i j => h (x i) (x j)

lemma gram_mulVec_eq (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (x : ι → V) (c : ι → K)
    (i : ι) : (gramMatrix h x).mulVec c i = h (x i) (∑ j, c j • x j) := by
  rw [form_sum_right_alt]
  simp [gramMatrix, Matrix.mulVec, dotProduct, mul_comm]

lemma form_functionals_surjective (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hn : Nondeg h) {ι : Type} [Fintype ι]
    [DecidableEq ι] (x : ι → V) (hx : LinearIndependent K x) (r : ι → K) :
    ∃ m, ∀ i, h (x i) m = r i := by
  let Φ : V →ₗ[K] (ι → K) := LinearMap.pi (fun i => h (x i))
  have htop : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have key : ∀ v, ∑ i, h (x i) v * f (fun j => if i = j then 1 else 0) = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hf ⟨v, rfl⟩
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ] using h1
    have h2 : ∑ i, σ (f (fun j => if i = j then 1 else 0)) • x i = 0 := by
      apply hn
      intro v
      rw [form_sum_left_alt]
      simp only [hσ.invol]
      refine Eq.trans ?_ (key v)
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hc := Fintype.linearIndependent_iff.1 hx _ h2
    apply hf0
    refine LinearMap.ext (fun w => ?_)
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h3 := hc i
    rw [map_eq_zero] at h3
    rw [h3, smul_zero]
  have : r ∈ LinearMap.range Φ := by rw [htop]; trivial
  obtain ⟨m, hm⟩ := this
  exact ⟨m, fun i => by rw [← hm]; rfl⟩

lemma linearIndependent_of_gram_unit (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] [DecidableEq κ] (z : κ → V)
    (hG : IsUnit (gramMatrix h z).det) : LinearIndependent K z := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : (gramMatrix h z).mulVec c = 0 := by
    ext i
    rw [gram_mulVec_eq, hc]
    simp
  have h2 : Function.Injective (gramMatrix h z).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hG)
  have h3 : c = 0 := h2 (by rw [h1, Matrix.mulVec_zero])
  intro i
  rw [h3]; rfl

lemma form_sum_expand (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] (b : κ → V) (c d : κ → K) :
    h (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, σ (c i) * (d j * h (b i) (b j)) := by
  rw [form_sum_left_alt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [form_sum_right_alt, Finset.mul_sum]

lemma extend_to_orthogonal_basis (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) {a : ℕ} (x : Fin a → V) (hG : IsUnit (gramMatrix h x).det) :
    ∃ b : Basis (Fin a ⊕ Fin (finrank K V - a)) K V, (∀ i, b (Sum.inl i) = x i) ∧
      (∀ i j, h (b (Sum.inl i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, h (b (Sum.inr j)) (b (Sum.inl i)) = 0) ∧
      ∀ j k, h (b (Sum.inr j)) (b (Sum.inr k)) = if j = k then 1 else 0 := by
  have hx : LinearIndependent K x := linearIndependent_of_gram_unit h x hG
  let Φ : V →ₗ[K] (Fin a → K) := LinearMap.pi (fun i => h (x i))
  have hΦ : ∀ v i, Φ v i = h (x i) v := fun v i => rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    obtain ⟨m, hm⟩ := form_functionals_surjective hσ h hn x hx r
    exact ⟨m, funext hm⟩
  let W : Submodule K V := LinearMap.ker Φ
  have hWmem : ∀ w, w ∈ W ↔ ∀ i, h (x i) w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker]
    constructor
    · intro hw i
      rw [← hΦ, hw]; rfl
    · intro hw
      funext i
      exact hw i
  have hfr : finrank K W = finrank K V - a := by
    have h1 : finrank K (LinearMap.range Φ) + finrank K W = finrank K V :=
      LinearMap.finrank_range_add_finrank_ker Φ
    rw [hsurj, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hdec : ∀ v, ∃ c : Fin a → K, v - ∑ j, c j • x j ∈ W := by
    intro v
    refine ⟨(gramMatrix h x)⁻¹.mulVec (Φ v), ?_⟩
    rw [hWmem]
    intro i
    rw [map_sub, ← gram_mulVec_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mulVec, hΦ, sub_self]
  let hW : W →ₛₗ[σ] W →ₗ[K] K := h.domRestrict₁₂ W W
  have hWh : Herm hW := fun u v => hh u v
  have hWn : Nondeg hW := by
    intro w hw
    apply Subtype.ext
    apply hn
    intro v
    obtain ⟨c, hc⟩ := hdec v
    have h1 : h w (v - ∑ j, c j • x j) = 0 := hw ⟨_, hc⟩
    have h2 : h w (∑ j, c j • x j) = 0 := by
      rw [form_sum_right_alt]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [← hh (x j) w, (hWmem w).1 w.2 j]
      simp
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  obtain ⟨c, hc⟩ := exists_orthonormal hσ _ W hW hWh hWn hfr
  let z : Fin a ⊕ Fin (finrank K V - a) → V := Sum.elim x (fun j => (c j : V))
  have h12 : ∀ i j, h (x i) (c j : V) = 0 := fun i j => (hWmem _).1 (c j).2 i
  have h21 : ∀ i j, h (c j : V) (x i) = 0 := by
    intro i j
    rw [← hh, h12]; simp
  have h22 : ∀ j k, h (c j : V) (c k : V) = if j = k then 1 else 0 := fun j k => hc j k
  have hzG : gramMatrix h z = Matrix.fromBlocks (gramMatrix h x) 0 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · simp [gramMatrix, z, h12]
    · simp [gramMatrix, z, h21]
    · simp [gramMatrix, z, h22, Matrix.one_apply]
  have hzli : LinearIndependent K z := by
    apply linearIndependent_of_gram_unit h
    rw [hzG, Matrix.det_fromBlocks_zero₂₁]
    simpa using hG
  have hcard : Fintype.card (Fin a ⊕ Fin (finrank K V - a)) = finrank K V := by
    have h1 := hx.fintype_card_le_finrank
    simp only [Fintype.card_fin] at h1
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hsp := hzli.span_eq_top_of_card_eq_finrank' hcard
  refine ⟨Basis.mk hzli hsp.ge, ?_, ?_, ?_, ?_⟩
  · intro i; simp [z]
  · intro i j; simp [z, h12]
  · intro i j; simp [z, h21]
  · intro j k; simp [z, h22]

lemma witt_extension_of_nondeg_gram (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) {a : ℕ} (x y : Fin a → V) (hG : IsUnit (gramMatrix h x).det)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  have hGy : IsUnit (gramMatrix h y).det := by
    have : gramMatrix h y = gramMatrix h x := by
      ext i j
      exact (hxy i j).symm
    rw [this]; exact hG
  obtain ⟨bx, hx1, hx2, hx3, hx4⟩ := extend_to_orthogonal_basis hσ h hh hn x hG
  obtain ⟨bY, hy1, hy2, hy3, hy4⟩ := extend_to_orthogonal_basis hσ h hh hn y hGy
  have hb : ∀ i j, h (bx i) (bx j) = h (bY i) (bY j) := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rw [hx1, hx1, hy1, hy1, hxy]
    · rw [hx2, hy2]
    · rw [hx3, hy3]
    · rw [hx4, hy4]
  refine ⟨bx.equiv bY (Equiv.refl _), ?_, ?_⟩
  · intro u v
    have hg : ∀ w, bx.equiv bY (Equiv.refl _) w = ∑ i, bx.repr w i • bY i := by
      intro w
      calc bx.equiv bY (Equiv.refl _) w
          = bx.equiv bY (Equiv.refl _) (∑ i, bx.repr w i • bx i) := by rw [bx.sum_repr]
        _ = ∑ i, bx.repr w i • bY i := by
            rw [map_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_smul, Basis.equiv_apply]
            rfl
    rw [hg, hg, form_sum_expand]
    conv_rhs => rw [← bx.sum_repr u, ← bx.sum_repr v, form_sum_expand]
    simp only [hb]
  · intro i
    rw [← hx1, Basis.equiv_apply, ← hy1]
    rfl

lemma exists_isotropic_completion (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (N : Fin a → K) (i0 : Fin a) (hN : N i0 ≠ 0)
    (hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0) :
    ∃ m, (∀ i, h (x i) m = if i = i0 then 1 else 0) ∧ h m m = 0 ∧
      m ∉ Submodule.span K (Set.range x) := by
  obtain ⟨m0, hm0⟩ := form_functionals_surjective hσ h hn x hx (fun i => if i = i0 then 1 else 0)
  obtain ⟨l, hl⟩ := hσ.trace_one
  set u := ∑ j, N j • x j with hu
  have hux : ∀ i, h u (x i) = 0 := by
    intro i
    rw [← hh, hGN]; simp
  have huu : h u u = 0 := by
    conv_lhs => rw [hu]
    rw [form_sum_left_alt]
    exact Finset.sum_eq_zero (fun j _ => by rw [hGN, mul_zero])
  have hum : h u m0 = σ (N i0) := by
    rw [hu, form_sum_left_alt]
    simp [hm0]
  have hs : σ (N i0) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hN
  have hmu : h m0 u = N i0 := by
    rw [← hh u m0, hum, hσ.invol]
  have ht : σ (h m0 m0) = h m0 m0 := hh m0 m0
  refine ⟨m0 + (-(l * h m0 m0) / N i0) • u, ?_, ?_, ?_⟩
  · intro i
    rw [map_add, map_smul, hGN, smul_zero, add_zero, hm0]
  · simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, huu, hum,
      hmu, smul_eq_mul, map_div₀, map_neg, map_mul, ht]
    have hl' : σ l = 1 - l := by rw [← hl]; ring
    rw [hl']
    field_simp
    ring
  · intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    have h1 : h u (∑ i, c i • x i) = 0 := by
      rw [form_sum_right_alt]
      exact Finset.sum_eq_zero (fun j _ => by rw [hux, mul_zero])
    rw [hc, map_add, map_smul, huu, smul_zero, add_zero, hum] at h1
    exact hs h1

lemma witt_extension_induction (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) : ∀ (d a : ℕ) (x y : Fin a → V), a + d = finrank K V →
    LinearIndependent K x → LinearIndependent K y →
    (∀ i j, h (x i) (x j) = h (y i) (y j)) →
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  intro d
  induction d with
  | zero =>
    intro a x y had hx hy hxy
    by_cases hG : IsUnit (gramMatrix h x).det
    · exact witt_extension_of_nondeg_gram hσ h hh hn x y hG hxy
    · exfalso
      rw [isUnit_iff_ne_zero, not_not] at hG
      obtain ⟨N, hN0, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
      obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hN0
      have hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0 := by
        intro i
        rw [← gram_mulVec_eq, hN]; rfl
      obtain ⟨m, -, -, hm⟩ := exists_isotropic_completion hσ h hh hn x hx N i0 hi0 hGN
      have hli : LinearIndependent K (Fin.snoc x m : Fin (a + 1) → V) :=
        linearIndependent_finSnoc.2 ⟨hx, hm⟩
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      omega
  | succ d ih =>
    intro a x y had hx hy hxy
    by_cases hG : IsUnit (gramMatrix h x).det
    · exact witt_extension_of_nondeg_gram hσ h hh hn x y hG hxy
    · rw [isUnit_iff_ne_zero, not_not] at hG
      obtain ⟨N, hN0, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
      obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hN0
      have hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0 := by
        intro i
        rw [← gram_mulVec_eq, hN]; rfl
      have hGN' : ∀ i, h (y i) (∑ j, N j • y j) = 0 := by
        intro i
        rw [form_sum_right_alt]
        have h1 := hGN i
        rw [form_sum_right_alt] at h1
        simpa only [hxy] using h1
      obtain ⟨m, hm1, hm2, hm3⟩ := exists_isotropic_completion hσ h hh hn x hx N i0 hi0 hGN
      obtain ⟨m', hm1', hm2', hm3'⟩ := exists_isotropic_completion hσ h hh hn y hy N i0 hi0 hGN'
      obtain ⟨g, hg1, hg2⟩ := ih (a + 1) (Fin.snoc x m : Fin (a + 1) → V)
        (Fin.snoc y m' : Fin (a + 1) → V) (by omega)
        (linearIndependent_finSnoc.2 ⟨hx, hm3⟩) (linearIndependent_finSnoc.2 ⟨hy, hm3'⟩) (by
          intro i j
          refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
          · simp only [Fin.snoc_last, hm2, hm2']
          · simp only [Fin.snoc_last, Fin.snoc_castSucc]
            rw [← hh, hm1, ← hh (y j), hm1']
          · simp only [Fin.snoc_last, Fin.snoc_castSucc, hm1, hm1']
          · simp only [Fin.snoc_castSucc, hxy])
      refine ⟨g, hg1, fun i => ?_⟩
      have := hg2 i.castSucc
      simpa only [Fin.snoc_castSucc] using this

end A2

theorem witt (hσ : Inv σ) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ} (x y : Fin a → V)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  have h1 := hx.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h1
  exact witt_extension_induction hσ h hh hn (finrank K V - a) a x y (by omega) hx hy hxy

section PartC
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)

theorem c_two_le (hq : Fintype.card K = q ^ 2) : 2 ≤ q := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  rw [hq] at h1
  by_contra h
  interval_cases q <;> simp at h1

theorem c_exists_frob (hq : Fintype.card K = q ^ 2) : ∃ σ : K →+* K, ∀ x, σ x = x ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have : ExpChar K p := ExpChar.prime hpp
  have hdvd : q ∣ p ^ (n : ℕ) := by rw [← hn, hq]; exact Dvd.intro_left q (by ring)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hpp).1 hdvd
  refine ⟨iterateFrobenius K p m, fun x => ?_⟩
  rw [iterateFrobenius_def, hm]

theorem c_pow_pow (hq : Fintype.card K = q ^ 2) (x : K) : (x ^ q) ^ q = x := by
  rw [← pow_mul, ← sq, ← hq, FiniteField.pow_card]

theorem c_card_pow_le [DecidableEq K] (n : ℕ) (hn : 0 < n) (a : K) :
    (univ.filter (fun x : K => x ^ n = a)).card ≤ n := by
  calc (univ.filter (fun x : K => x ^ n = a)).card ≤ (Polynomial.nthRoots n a).toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [Polynomial.mem_nthRoots hn, hx]
    _ ≤ Multiset.card (Polynomial.nthRoots n a) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n a

theorem c_fibre [DecidableEq K] (hq : Fintype.card K = q ^ 2) (c : K) (hc : c ^ q = c) (hc0 : c ≠ 0) :
    (univ.filter (fun x : K => x ^ (q + 1) = c)).card = q + 1 := by
  have h2 := c_two_le K q hq
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  set G := univ.filter (fun c : K => c ^ (k + 1) = 1) with hG
  have hGc : G.card ≤ k + 1 := c_card_pow_le K (k + 1) (by omega) 1
  set s := univ.filter (fun x : K => x ≠ 0) with hs
  have hsc : s.card = (k + 2) ^ 2 - 1 := by
    rw [hs, Finset.filter_ne', Finset.card_erase_of_mem (mem_univ _), card_univ, hq]
  have hmaps : ∀ x ∈ s, x ^ (k + 2 + 1) ∈ G := by
    intro x hx
    simp only [hs, hG, mem_filter, mem_univ, true_and] at hx ⊢
    rw [← pow_mul]
    have h3 : (k + 2 + 1) * (k + 1) = Fintype.card K - 1 := by
      rw [hq]
      have : (k + 2) ^ 2 = (k + 2 + 1) * (k + 1) + 1 := by ring
      omega
    rw [h3]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∀ b ∈ G, (s.filter (fun x => x ^ (k + 2 + 1) = b)).card ≤ k + 2 + 1 := fun b _ =>
    le_trans (card_le_card (by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.2)) (c_card_pow_le K (k + 2 + 1) (by omega) b)
  have hcG : c ∈ G := by
    simp only [hG, mem_filter, mem_univ, true_and]
    have : c * c ^ (k + 1) = c * 1 := by rw [mul_one, ← pow_succ']; exact hc
    exact mul_left_cancel₀ hc0 this
  have heq : s.filter (fun x => x ^ (k + 2 + 1) = c) = univ.filter (fun x => x ^ (k + 2 + 1) = c) := by
    ext x
    simp only [hs, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hx h0
    subst h0
    simp at hx
    exact hc0 hx.symm
  rw [← heq]
  by_contra hne
  have hlt : (s.filter (fun x => x ^ (k + 2 + 1) = c)).card < k + 2 + 1 := lt_of_le_of_ne (hle c hcG) hne
  have h4 : ∑ b ∈ G, (s.filter (fun x => x ^ (k + 2 + 1) = b)).card < ∑ b ∈ G, (k + 2 + 1) :=
    Finset.sum_lt_sum hle ⟨c, hcG, hlt⟩
  rw [← hsum, hsc, sum_const, smul_eq_mul] at h4
  have h5 : G.card * (k + 2 + 1) ≤ (k + 1) * (k + 2 + 1) := Nat.mul_le_mul_right _ hGc
  have h6 : (k + 2) ^ 2 = (k + 1) * (k + 2 + 1) + 1 := by ring
  omega

theorem c_fixed_card_le [DecidableEq K] (hq : Fintype.card K = q ^ 2) :
    (univ.filter (fun x : K => x ^ q = x)).card ≤ q := by
  have h2 := c_two_le K q hq
  have hsub : univ.filter (fun x : K => x ^ q = x) ⊆ insert 0 (univ.filter (fun x : K => x ^ (q - 1) = 1)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_insert] at hx ⊢
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      have : x * x ^ (q - 1) = x * 1 := by
        rw [mul_one, ← pow_succ']
        have : q - 1 + 1 = q := by omega
        rw [this]; exact hx
      exact mul_left_cancel₀ h0 this
  have h3 := c_card_pow_le K (q - 1) (by omega) 1
  have h4 := Finset.card_le_card hsub
  have h5 := Finset.card_insert_le (0 : K) (univ.filter (fun x : K => x ^ (q - 1) = 1))
  omega

theorem exists_sigma (hq : Fintype.card K = q ^ 2) :
    ∃ σ : K →+* K, (∀ x, σ x = x ^ q) ∧ Inv σ := by
  classical
  have h2 := c_two_le K q hq
  obtain ⟨σ, hσ⟩ := c_exists_frob K q hq
  have hinv : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ, c_pow_pow K q hq]
  refine ⟨σ, hσ, hinv, ?_, ?_⟩
  · intro c hc
    by_cases hc0 : c = 0
    · exact ⟨0, by simp [hc0]⟩
    · have h3 := c_fibre K q hq c (by rw [← hσ]; exact hc) hc0
      have h4 : (univ.filter (fun x : K => x ^ (q + 1) = c)).Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨y, hy⟩ := h4
      simp only [mem_filter, mem_univ, true_and] at hy
      exact ⟨y, by rw [hσ, ← pow_succ]; exact hy⟩
  · have h3 : ∃ t : K, t + σ t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h11 : (1 : K) + 1 = 0 := by simpa using hcon 1
      have hall : ∀ t : K, t ^ q = t := by
        intro t
        have h5 := hcon t
        rw [hσ] at h5
        have h6 : t + t = 0 := by
          have : t + t = t * (1 + 1) := by ring
          rw [this, h11, mul_zero]
        have : t ^ q - t = (t + t ^ q) - (t + t) := by ring
        rw [h5, h6, sub_zero] at this
        exact sub_eq_zero.1 this
      have h7 := c_fixed_card_le K q hq
      rw [Finset.filter_true_of_mem (fun x _ => hall x), card_univ, hq] at h7
      nlinarith
    obtain ⟨t, ht⟩ := h3
    refine ⟨t / (t + σ t), ?_⟩
    rw [map_div₀, map_add, hinv, add_comm (σ t) t, ← add_div, div_self ht]

theorem c_count_succ [DecidableEq K] (n : ℕ) (c : K) :
    (univ.filter (fun w : Fin (n + 1) → K => ∑ i, w i ^ q * w i = c)).card =
      ∑ x : K, (univ.filter (fun w : Fin n → K => ∑ i, w i ^ q * w i = c - x ^ q * x)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w 0) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  refine Finset.card_bij (fun w _ => Fin.cons x w) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine ⟨?_, by simp⟩
    rw [Fin.sum_univ_succ]
    simp [hw]
  · intro w _ w' _ h
    funext i
    have h1 := congrFun h i.succ
    simpa using h1
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    refine ⟨Fin.tail w, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have h1 := hw.1
      rw [Fin.sum_univ_succ, hw.2] at h1
      rw [← h1]
      simp [Fin.tail]
    · rw [← hw.2]
      exact Fin.cons_self_tail w

theorem c_nu [DecidableEq K] (hq : Fintype.card K = q ^ 2) (c : K) (hc : c ^ q = c) :
    (univ.filter (fun x : K => c - x ^ q * x = 0)).card = if c = 0 then 1 else q + 1 := by
  have h1 : univ.filter (fun x : K => c - x ^ q * x = 0) = univ.filter (fun x : K => x ^ (q + 1) = c) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, pow_succ, sub_eq_zero]
    exact eq_comm
  rw [h1]
  by_cases h0 : c = 0
  · rw [if_pos h0, h0]
    have : univ.filter (fun x : K => x ^ (q + 1) = 0) = {0} := by
      ext x
      simp
    rw [this, card_singleton]
  · rw [if_neg h0]
    exact c_fibre K q hq c hc h0

theorem c_count [DecidableEq K] (hq : Fintype.card K = q ^ 2) (n : ℕ) : ∀ c : K, c ^ q = c →
    (q : ℤ) * (univ.filter (fun w : Fin n → K => ∑ i, w i ^ q * w i = c)).card =
      if c = 0 then (q : ℤ) ^ (2 * n) + (-1) ^ n * (q - 1) * q ^ n else q ^ n * (q ^ n - (-1) ^ n) := by
  obtain ⟨σ, hσ⟩ := c_exists_frob K q hq
  induction n with
  | zero =>
    intro c _
    by_cases h0 : c = 0
    · simp [h0]
    · simp [h0, Ne.symm h0]
  | succ n ih =>
    intro c hc
    have hfix : ∀ x : K, (c - x ^ q * x) ^ q = c - x ^ q * x := by
      intro x
      rw [← hσ, map_sub, map_mul, hσ, hσ, hσ, hc, c_pow_pow K q hq, mul_comm]
    rw [c_count_succ, Nat.cast_sum, Finset.mul_sum, Finset.sum_congr rfl (fun x _ => ih _ (hfix x)),
      Finset.sum_ite, sum_const, sum_const, c_nu K q hq c hc]
    have h3 : ((univ.filter (fun x : K => ¬ (c - x ^ q * x = 0))).card : ℤ) =
        (q : ℤ) ^ 2 - (if c = 0 then 1 else q + 1 : ℕ) := by
      have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset K)) (fun x : K => c - x ^ q * x = 0)
      rw [c_nu K q hq c hc, card_univ, hq] at h4
      have h5 : (((if c = 0 then 1 else q + 1 : ℕ) + (univ.filter (fun x : K => ¬ (c - x ^ q * x = 0))).card : ℕ) : ℤ)
          = ((q ^ 2 : ℕ) : ℤ) := by rw [h4]
      push_cast at h5 ⊢
      linarith
    rw [nsmul_eq_mul, nsmul_eq_mul, h3]
    by_cases h0 : c = 0
    · simp only [h0, if_true]
      push_cast
      ring
    · simp only [h0, if_false]
      push_cast
      ring

theorem card_norm_one (hq : Fintype.card K = q ^ 2) (n : ℕ) :
    (q : ℤ) * Nat.card {w : Fin n → K // ∑ i, (w i) ^ q * w i = 1} = q ^ n * (q ^ n - (-1) ^ n) := by
  classical
  have h := c_count K q hq n 1 (one_pow q)
  rw [if_neg one_ne_zero] at h
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]

end PartC

section PartD
open Matrix Formalism.FourierDecayAlt.S3

noncomputable def hJ (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₛₗ[σ] (Fin n → K) →ₗ[K] K := Matrix.toLinearMapₛₗ₂' K σ (RingHom.id K) J

lemma hJ_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hJ σ J u v = ∑ i, ∑ j, σ (u i) * J i j * v j := by
  unfold hJ
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply, smul_eq_mul]
  ring

lemma d_gram_entry {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (J : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) α K) (Y : Matrix (Fin n) β K) (i : α) (j : β) :
    (fconj q X * J * Y) i j = hJ σ J (fun k => X k i) (fun k => Y k j) := by
  rw [hJ_apply]
  simp only [Matrix.mul_apply, fconj, Matrix.transpose_apply, Matrix.map_apply, hσ, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma d_fconj_eq {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β : Type} (X : Matrix α β K) :
    fconj q X = (X.map σ)ᵀ := by
  ext i j
  simp [fconj, hσ]

lemma d_fconj_mul {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β γ : Type} [Fintype β] (X : Matrix α β K)
    (Y : Matrix β γ K) : fconj q (X * Y) = fconj q Y * fconj q X := by
  rw [d_fconj_eq hσ, d_fconj_eq hσ, d_fconj_eq hσ, Matrix.map_mul, Matrix.transpose_mul]

lemma d_fconj_one {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α : Type} [DecidableEq α] :
    fconj q (1 : Matrix α α K) = 1 := by
  rw [d_fconj_eq hσ, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

lemma d_herm {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hi : Inv σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (hJh : fconj q J = J) : Herm (hJ σ J) := by
  intro u v
  rw [hJ_apply, hJ_apply, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : σ (J j i) = J i j := by
    have := congrFun (congrFun hJh i) j
    simpa [fconj, hσ] using this
  rw [map_mul, map_mul, hi.invol, h1]
  ring

lemma d_nondeg {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (hJu : IsUnit J.det) : Nondeg (hJ σ J) := by
  intro u hu
  have h1 : (fun i => σ (u i)) ᵥ* J = 0 := by
    ext j
    have := hu (Pi.single j 1)
    rw [hJ_apply] at this
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hJu.ne_zero h1
  ext i
  have := congrFun h2 i
  simpa using this

lemma d_li_of_rank {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    LinearIndependent K (fun (i : Fin a) (k : Fin n) => X k i) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  have h1 := Matrix.range_mulVecLin X
  unfold Matrix.rank at hX
  rw [h1] at hX
  exact hX.symm

theorem d_wittHerm : WittHerm := by
  intro K _ _ q n a J X Y hq hJh hJu hX hY hXY
  obtain ⟨σ, hσ, hi⟩ := exists_sigma K q hq
  obtain ⟨g, hg, hgx⟩ := witt hi (hJ σ J) (d_herm hσ hi J hJh) (d_nondeg J hJu)
    (fun (i : Fin a) (k : Fin n) => X k i) (fun (i : Fin a) (k : Fin n) => Y k i)
    (d_li_of_rank X hX) (d_li_of_rank Y hY) (by
      intro i j
      rw [← d_gram_entry hσ, ← d_gram_entry hσ, hXY])
  have hcol : ∀ (α : Type) [Fintype α] (Z : Matrix (Fin n) α K) (i : α),
      (fun k => (LinearMap.toMatrix' g.toLinearMap * Z) k i) = g (fun k => Z k i) := by
    intro α _ Z i
    have : g (fun k => Z k i) = LinearMap.toMatrix' g.toLinearMap *ᵥ (fun k => Z k i) := by
      rw [LinearMap.toMatrix'_mulVec]; rfl
    rw [this]
    ext k
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine ⟨LinearMap.toMatrix' g.toLinearMap, ?_, ?_⟩
  · ext i j
    have h1 := d_gram_entry hσ J (LinearMap.toMatrix' g.toLinearMap * 1)
      (LinearMap.toMatrix' g.toLinearMap * 1) i j
    rw [hcol, hcol, hg, ← d_gram_entry hσ, d_fconj_one hσ] at h1
    simpa using h1
  · ext k i
    have := congrFun (hcol _ X i) k
    rw [hgx] at this
    exact this

lemma d_densP (η : ℤ) (q b : ℕ) :
    densP η q 1 b = ∏ i ∈ Finset.range b, (1 - (η : ℝ) ^ (i + 1) * ((q : ℝ) ^ (i + 1))⁻¹) := by
  unfold densP
  have h1 : Finset.Icc (1 : ℤ) b = (Finset.range b).image (fun i : ℕ => ((i : ℤ) + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [h1, Finset.prod_image (by intro x _ y _ hxy; simpa using hxy)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h2, zpow_natCast, _root_.zpow_neg, zpow_natCast]

lemma d_arith (q : ℕ) (hq : 0 < q) (s : ℕ → ℕ)
    (hs : ∀ n, (q : ℤ) * s n = q ^ n * (q ^ n - (-1) ^ n)) (b : ℕ) :
    ((∏ j ∈ Finset.range b, s (j + 1) : ℕ) : ℝ) = (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b := by
  rw [d_densP]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    have h1 : (q : ℝ) * s (b + 1) = q ^ (b + 1) * (q ^ (b + 1) - (-1) ^ (b + 1)) := by
      exact_mod_cast hs (b + 1)
    have h2 : (s (b + 1) : ℝ) = q ^ b * (q ^ (b + 1) - (-1) ^ (b + 1)) := by
      apply mul_left_cancel₀ hq'
      rw [h1]; ring
    rw [h2]
    have h3 : (b + 1) ^ 2 = b ^ 2 + b + (b + 1) := by ring
    rw [h3, pow_add, pow_add]
    generalize (∏ i ∈ Finset.range b, (1 - ((-1 : ℤ) : ℝ) ^ (i + 1) * ((q : ℝ) ^ (i + 1))⁻¹)) = Q
    have h4 : (q : ℝ) ^ (b + 1) * (1 - ((-1 : ℤ) : ℝ) ^ (b + 1) * ((q : ℝ) ^ (b + 1))⁻¹) =
        q ^ (b + 1) - (-1) ^ (b + 1) := by
      push_cast
      field_simp
    linear_combination (-(q : ℝ) ^ (b ^ 2) * Q * q ^ b) * h4

theorem d_unitaryOrder : UnitaryOrder := by
  intro K _ _ q b J hq hJh hJu
  obtain ⟨σ, hσ, hi⟩ := exists_sigma K q hq
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have := Fintype.card_pos (α := K)
      omega
    · exact h
  have hH := d_herm hσ hi J hJh
  have hN : Nondeg (hJ σ J) := d_nondeg J hJu
  obtain ⟨bs, hbs⟩ := exists_orthonormal hi b (Fin b → K) (hJ σ J) hH hN (by simp)
  set P : Matrix (Fin b) (Fin b) K := Matrix.of fun k i => bs i k with hP
  have hPJ : fconj q P * J * P = 1 := by
    ext i j
    rw [d_gram_entry hσ, Matrix.one_apply]
    exact hbs i j
  have hPu : IsUnit P.det := by
    have := congrArg Matrix.det hPJ
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hJP : J = fconj q P⁻¹ * P⁻¹ := by
    calc J = fconj q (P * P⁻¹) * J * (P * P⁻¹) := by rw [hPP, d_fconj_one hσ]; simp
      _ = fconj q P⁻¹ * (fconj q P * J * P) * P⁻¹ := by
          rw [d_fconj_mul hσ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPJ]; simp
  let e1 : {g : Matrix (Fin b) (Fin b) K // fconj q g * J * g = J} ≃
      {Z : Matrix (Fin b) (Fin b) K // fconj q Z * J * Z = 1} :=
    { toFun := fun g => ⟨g.1 * P, by
        rw [d_fconj_mul hσ]
        calc fconj q P * fconj q g.1 * J * (g.1 * P) = fconj q P * (fconj q g.1 * J * g.1) * P := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [g.2, hPJ]⟩
      invFun := fun Z => ⟨Z.1 * P⁻¹, by
        rw [d_fconj_mul hσ]
        calc fconj q P⁻¹ * fconj q Z.1 * J * (Z.1 * P⁻¹)
            = fconj q P⁻¹ * (fconj q Z.1 * J * Z.1) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = J := by rw [Z.2, hJP]; simp⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp [Matrix.mul_assoc, hPP]
      right_inv := fun Z => by
        apply Subtype.ext
        simp [Matrix.mul_assoc, hPP'] }
  let e2 : {Z : Matrix (Fin b) (Fin b) K // fconj q Z * J * Z = 1} ≃
      {f : Fin b → (Fin b → K) // Ortho (hJ σ J) f} :=
    { toFun := fun Z => ⟨fun i k => Z.1 k i, by
        intro i j
        rw [← d_gram_entry hσ, Z.2, Matrix.one_apply]⟩
      invFun := fun f => ⟨Matrix.of fun k i => f.1 i k, by
        ext i j
        rw [d_gram_entry hσ, Matrix.one_apply]
        exact f.2 i j⟩
      left_inv := fun Z => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr (e1.trans e2),
    card_frames hi (fun n => Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1}) (fun _ => rfl) b
      (Fin b → K) (hJ σ J) hH hN (by simp)]
  refine d_arith q hq0 (fun n => Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1}) ?_ b
  intro n
  have := card_norm_one K q hq n
  simpa only [hσ] using this

end PartD

end Formalism.FourierDecayAlt.P.S3x6

namespace Formalism.FourierDecayAlt.P

theorem unitary_group_order : Formalism.FourierDecayAlt.S3.UnitaryOrder := S3x6.d_unitaryOrder

theorem witt_hermitian_frames : Formalism.FourierDecayAlt.S3.WittHerm := S3x6.d_wittHerm

end Formalism.FourierDecayAlt.P
