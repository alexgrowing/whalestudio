import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def VP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

open Classical in

def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => if j.1 = σ then v j else 0

def mulc {dim : (E →+* ℂ) → ℕ} (c : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => c j.1 * v j

theorem emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

theorem mulc_mem {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  classical
  set S := Submodule.span ℂ (I : Set (Vsp dim)) with hS

  have hact : ∀ (α : 𝓞 E), ∀ v ∈ S, act α v ∈ S := by
    intro α
    let A : Vsp dim →ₗ[ℂ] Vsp dim :=
      { toFun := act α
        map_add' := fun x y => by ext j; simp [act]; ring
        map_smul' := fun c x => by ext j; simp [act]; ring }
    have hle : S.map A ≤ S := by
      rw [hS, Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (hst α x hx)
    intro v hv
    exact hle ⟨v, hv, rfl⟩

  have hα : ∀ τ : E →+* ℂ, ∃ α : 𝓞 E, τ ≠ σ → σ (α : E) ≠ τ (α : E) := by
    intro τ
    by_cases h : τ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨α, hα⟩ := emb_sep (Ne.symm h)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hα
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ τ' =>
    (τ' (α τ : E) - τ (α τ : E)) * (σ (α τ : E) - τ (α τ : E))⁻¹
  have hstep : ∀ τ, ∀ v ∈ S, mulc (c τ) v ∈ S := by
    intro τ v hv
    have : mulc (c τ) v = (σ (α τ : E) - τ (α τ : E))⁻¹ • (act (α τ) v - (τ (α τ : E)) • v) := by
      ext j; simp [mulc, act, c]; ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (hact _ v hv) (S.smul_mem _ hv))
  have hprod : ∀ T : Finset (E →+* ℂ), ∀ v ∈ S, mulc (fun τ' => ∏ τ ∈ T, c τ τ') v ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v hv
      have : mulc (fun τ' => ∏ τ ∈ (∅ : Finset (E →+* ℂ)), c τ τ') v = v := by ext j; simp [mulc]
      rw [this]; exact hv
    | insert τ T hτ ih =>
      intro v hv
      have : mulc (fun τ' => ∏ t ∈ insert τ T, c t τ') v = mulc (c τ) (mulc (fun τ' => ∏ t ∈ T, c t τ') v) := by
        ext j; simp [mulc, Finset.prod_insert hτ]; ring
      rw [this]
      exact hstep τ _ (ih v hv)
  intro v hv
  have : prj σ v = mulc (fun τ' => ∏ τ ∈ Finset.univ.erase σ, c τ τ') v := by
    ext j
    simp only [prj, mulc, PiLp.toLp_apply]
    by_cases hj : j.1 = σ
    · rw [if_pos hj, hj, Finset.prod_eq_one, one_mul]
      intro τ hτ
      have hne := hα τ (Finset.ne_of_mem_erase hτ)
      simp only [c]
      exact mul_inv_cancel₀ (sub_ne_zero.2 hne)
    · rw [if_neg hj, Finset.prod_eq_zero (i := j.1) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), zero_mul]
      simp [c]
  rw [this]
  exact hprod _ v hv

theorem Hf_prj {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {ξ : Vsp dim} (hξ : InPart σ ξ) (a : Vsp dim) :
    Hf ξ a = Hf ξ (prj σ a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [prj, PiLp.toLp_apply]
  by_cases hj : j.1 = σ
  · rw [if_pos hj]
  · rw [if_neg hj, hξ j hj]; simp

theorem Hf_eq_inner' {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w :=
  lemS_Hf_eq_inner w v

theorem prj_inpart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (a : Vsp dim) : InPart σ (prj σ a) := by
  intro j hj; simp [prj, hj]

theorem onb_data (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by
  classical
  set N := Module.finrank ℂ (VP (dim := X.dim) σ) with hN
  have hw_inner : ∀ s s', inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0 := by
    intro s s'
    rw [← Hf_eq_inner', hon s' s]
    by_cases h : s = s' <;> simp [h, eq_comm]
  have hwo : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]; exact hw_inner
  have hρN : ρ ≤ N := hρ ▸ Submodule.finrank_mono inf_le_right
  have hNr : N ≤ X.r := by
    let f : VP (dim := X.dim) σ →ₗ[ℂ] (Fin (X.dim σ) → ℂ) :=
      { toFun := fun v a => (v : Vsp X.dim) ⟨σ, a⟩
        map_add' := fun x y => by funext a; simp
        map_smul' := fun c x => by funext a; simp }
    have hinj : Function.Injective f := by
      intro v v' h
      apply Subtype.ext
      ext j
      obtain ⟨τ, a⟩ := j
      by_cases hτ : τ = σ
      · subst hτ; exact congrFun h a
      · rw [(v.2 : InPart σ (v : Vsp X.dim)) ⟨τ, a⟩ hτ, (v'.2 : InPart σ (v' : Vsp X.dim)) ⟨τ, a⟩ hτ]
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at h1
    have h2 := X.dim_conj σ
    omega
  let vv : Fin N → VP (dim := X.dim) σ := fun k =>
    if h : k.val < ρ then ⟨w ⟨k, h⟩, (hw _).1⟩ else 0
  have hon' : Orthonormal ℂ (Set.domRestrict {k : Fin N | k.val < ρ} vv) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    have hk0 : k.val < ρ := hk
    have hk0' : k'.val < ρ := hk'
    show inner ℂ (vv k) (vv k') = if (⟨k, hk⟩ : {k : Fin N | k.val < ρ}) = ⟨k', hk'⟩ then 1 else 0
    simp only [vv, dif_pos hk0, dif_pos hk0', Submodule.coe_inner, hw_inner]
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := VP (dim := X.dim) σ) (ι := Fin N) (by simp [hN]) hon'
  have hbw : ∀ k (h : k.val < ρ), (bb k : Vsp X.dim) = w ⟨k, h⟩ := by
    intro k h
    rw [hbb k h]
    simp [vv, h]
  refine ⟨N, fun k => (bb k : Vsp X.dim), hNr, hρN, hbw, fun k => (bb k).2, ?_, ?_⟩
  · intro k hk
    constructor
    · exact bb.orthonormal.1 k
    · intro a ha
      rw [Hf_prj ((bb k).2 : InPart σ (bb k : Vsp X.dim)) a]
      have hpa : prj σ a ∈ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) :=
        ⟨mulc_mem I hst σ a (Submodule.subset_span ha), prj_inpart σ a⟩
      have hspan : Submodule.span ℂ (Set.range w) =
          (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]; rintro _ ⟨s, rfl⟩; exact ⟨(hw s).2, (hw s).1⟩
        · rw [finrank_span_eq_card hwo.linearIndependent, Fintype.card_fin, hρ]
      rw [← hspan] at hpa
      rw [Hf_eq_inner']
      refine Submodule.span_induction (p := fun z _ => inner ℂ z (bb k : Vsp X.dim) = 0) ?_ ?_ ?_ ?_ hpa
      · rintro _ ⟨s, rfl⟩
        have hs : (⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Fin N).val < ρ := s.2
        have e1 : w s = (bb ⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Vsp X.dim) := by
          rw [hbw _ hs]
        rw [e1, ← Submodule.coe_inner]
        refine bb.orthonormal.2 ?_
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
  · intro x y hx hy
    have := bb.sum_inner_mul_inner (⟨y, hy⟩ : VP (dim := X.dim) σ) ⟨x, hx⟩
    simp only [Submodule.coe_inner] at this
    rw [Hf_eq_inner', ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_eq_inner', Hf_eq_inner', mul_comm]

end

end ReciprocityTheory.ChartRestriction.G.I2
