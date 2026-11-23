import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cm_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem rId_zero : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

def formL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := form σ J x y
  map_add' a b := by simp [form, add_dotProduct]
  map_smul' c a := by simp [form, smul_dotProduct]

omit [NumberField F] [NumberField E] in
theorem formL_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) : formL σ J y x = form σ J x y := rfl

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ ε : E, ε * ε = 1 ∧ ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
  have key : ∀ ε : E, (∀ i j, σ (J j i) = ε * J i j) → ε * ε = 1 → ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
    intro ε h1 h2 x y
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_invol h, h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(y j * J j i * σ (x i))) * h2
  rcases hJ.1 with h1 | h1
  · exact ⟨1, by simp, key 1 (by simpa using h1) (by simp)⟩
  · exact ⟨-1, by simp, key (-1) (by simpa using h1) (by simp)⟩

theorem frameBasis_of : FrameBasis := by
  intro F E _ _ _ _ _ σ hσ n J hJ fr hfr
  classical
  obtain ⟨ε, hε, hsw⟩ := form_swap hσ hJ
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have yx : ∀ i j, form σ J (fr.y i) (fr.x j) = if i = j then ε else 0 := by
    intro i j
    rw [hsw, hfr.xy]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  let K : Submodule E (Fin n → E) := ⨅ i, (LinearMap.ker (formL σ J (fr.x i)) ⊓ LinearMap.ker (formL σ J (fr.y i)))
  have hK : ∀ u, u ∈ K ↔ ∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0 := by
    intro u
    simp [K, Submodule.mem_iInf, formL_apply]
  let bK := Module.finBasis E K
  let v : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → Fin n → E :=
    Sum.elim (Sum.elim fr.x fr.y) fun k => (bK k : Fin n → E)
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ j, g (.inl (.inl j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.y j)) hg
      simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xy, hfr.yy, ((hK _).1 (bK _).2 j).2] using this
    have h2 : ∀ j, g (.inl (.inr j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.x j)) hg
      simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xx, yx, ((hK _).1 (bK _).2 j).1, hε0] using this
    have h3 : ∑ k, g (.inr k) • bK k = 0 := by
      apply Subtype.ext
      simpa [Fintype.sum_sum_type, v, h1, h2] using hg
    have h4 := Fintype.linearIndependent_iff.1 bK.linearIndependent _ h3
    rintro ((j | j) | j)
    exacts [h1 j, h2 j, h4 j]
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro u _
    let a := ∑ i, form σ J u (fr.y i) • fr.x i + ∑ i, (ε * form σ J u (fr.x i)) • fr.y i
    have ha : a ∈ Submodule.span E (Set.range v) :=
      add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inl i), rfl⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inr i), rfl⟩))
    have hu : u - a ∈ K := by
      rw [hK]
      intro j
      constructor
      · rw [← formL_apply]
        simp only [a, map_sub, map_add, map_sum, map_smul, formL_apply, hfr.xx, yx, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination (-form σ J u (fr.x j)) * hε
      · rw [← formL_apply]
        simp only [a, map_sub, map_add, map_sum, map_smul]
        simp [formL_apply, hfr.xy, hfr.yy]
    have hb : u - a ∈ Submodule.span E (Set.range v) := by
      have : u - a = ∑ k, bK.repr ⟨_, hu⟩ k • (bK k : Fin n → E) := by
        have := congrArg Subtype.val (bK.sum_repr ⟨_, hu⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)
    simpa using add_mem hb ha
  let B := Module.Basis.mk hli hsp
  let e : ((Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K)) ≃ Fin n := B.indexEquiv (Pi.basisFun E (Fin n))
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun l k => v (e.symm k) l
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  let lam0 : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ :=
    Sum.elim (Sum.elim (fun i => LinearMap.proj i) fun i => -LinearMap.proj i) fun _ => 0
  refine ⟨hM.unit, fun k => lam0 (e.symm k), ⟨fun i => e (.inl (.inl i)), fun i j h => by simpa using h⟩,
    ⟨fun i => e (.inl (.inr i)), fun i j h => by simpa using h⟩, fun i j h => by simpa using e.injective h,
    fun i t => ⟨congrArg (fun z => lam0 z t) (e.symm_apply_apply _), congrArg (fun z => lam0 z t) (e.symm_apply_apply _)⟩,
    fun k hk => ?_, fun i => congrArg v (e.symm_apply_apply _), fun t => ?_⟩
  · obtain ⟨k, rfl⟩ := e.surjective k
    rcases k with (j | j) | j
    · exact absurd rfl (hk j).1
    · exact absurd rfl (hk j).2
    · simp [lam0]
  · have key : ∀ k, mat (fr.a t) *ᵥ incV F (v k) = rId F (lam0 k t) • incV F (v k) := by
      rintro ((j | j) | j)
      · exact hfr.ax t j
      · exact hfr.ay t j
      · have := hfr.a0 t _ ((hK _).1 (bK j).2)
        simpa [lam0, rId_zero, v] using this
    ext l k
    have := congrFun (key (e.symm k)) l
    rw [Matrix.mul_diagonal, mul_comm, ← Algebra.smul_def]
    exact this

end PositivityTheory.ThKEst

end
