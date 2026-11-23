import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaH

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_ph_inj (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : D} (hyG : y ∈ genSub E V) (hy0 : (y : H) ≠ 0) {g0 : Fin n → D} (hg0m : g0 ∈ tensSub (genSub E V))
    (h0 : tfPh dual ε σ (y : H) (fun i => ((g0 i : D) : H)) = 0) : g0 = 0 := by
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V :=
    fun f hf c => Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  set f2 : Fin n → D := fun c => tfSgn ε c • g0 c with hf2
  have hf2m : f2 ∈ tensSub (genSub E V) := by
    rw [tset_mem]; intro c; exact Submodule.smul_mem _ _ ((tset_mem.1 hg0m) c)
  have hT2b := tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC (hcoeC _ hf2m) (hcoeC _ hg0m)
    (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf2m) (tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hg0m)
  rw [h0, map_zero, inner_zero_right] at hT2b
  have hform : tfFormBH ε (fun i => ((f2 i : D) : H)) (fun i => ((g0 i : D) : H)) =
      ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) := by
    unfold tfFormBH
    push_cast
    refine sum_congr rfl fun c _ => ?_
    rw [hf2]
    simp only [Submodule.coe_smul, inner_smul_left, ← mul_assoc, inner_self_eq_norm_sq_to_K]
    rw [show (starRingEnd ℂ) (tfSgn ε c) = tfSgn ε c from tf_star_sgn ε c, tfSgn_mul_self, one_mul]
    rfl
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hN0 : inner ℂ (y : H) (y : H) ≠ 0 := inner_self_ne_zero.2 hy0
  rw [hform] at hT2b
  have hs0 : (∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) = 0 := by
    have h1 : ((∑ c, ‖((g0 c : D) : H)‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have h2 := hT2b.symm
      rw [mul_div_assoc] at h2
      exact (mul_eq_zero.1 h2).resolve_right (div_ne_zero hN0 hd0)
    exact_mod_cast h1
  funext c
  have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖((g0 i : D) : H)‖)).1 hs0 c (mem_univ _)
  have h2 : ((g0 c : D) : H) = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  exact Subtype.ext h2

theorem tf_trace_core (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ c0 = r ∧ (c0 = 0 → ∀ b, P (Pi.single b y) = 0) := by
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hc hVK (tf_sqInt_of_hW hσ hD hgap hV hc hVK hW)
  obtain ⟨HP, w, -, hHPeq, -, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hc hVK hW hP hPP hPB hEP hc0 hyV hy0 hd
  have hdpos : 0 < d := hd.1
  refine ⟨(∑ c, ‖w c‖ ^ 2) / d, div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hdpos.le, hc0eq, fun h0 b => ?_⟩
  have hT0 : ∑ c, ‖w c‖ ^ 2 = 0 := by
    rw [h0] at hc0eq
    have h1 : (∑ c, ‖w c‖ ^ 2) / d = 0 := by exact_mod_cast hc0eq.symm
    exact (div_eq_zero_iff.1 h1).resolve_right hdpos.ne'
  have hw0 : ∀ c, w c = 0 := by
    intro c
    have h1 := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖w i‖)).1 hT0 c (mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  have hHP0 : ∀ v ∈ HP, v = 0 := by
    intro v hv
    refine vectorL2_ext fun c => ?_
    have h1 := hrep v hv c
    simp only [hw0, inner_zero_left] at h1
    exact Lp.ext (h1.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)).symm)
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hsing : (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  have hmemHP : tfPh dual ε σ (y : H) (fun i => ((P (Pi.single b y) i : D) : H)) ∈ HP := by
    rw [hHPeq]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hsing, rfl⟩)
  exact tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hyG hy0 (hP.1 _ hsing) (hHP0 _ hmemHP)

end ReciprocityTheory.ChartRestriction.DS
