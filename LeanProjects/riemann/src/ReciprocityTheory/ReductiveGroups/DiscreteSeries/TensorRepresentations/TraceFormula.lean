import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Decomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaM

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

instance closGen_completeSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) : CompleteSpace (closGen E V) := by
  unfold closGen; infer_instance

def formB {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} (ε : Fin n → Bool)
    (f g : Fin n → D) : ℂ :=
  ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f c : D) : H) ((g c : D) : H)

theorem tfa_sign (ε : Fin n → Bool) (r s : Fin n) :
    (if ε s then (1 : ℂ) else -1) * adjSign ε r s = if ε r then (1 : ℂ) else -1 := by
  unfold adjSign
  rcases Bool.eq_false_or_eq_true (ε r) with h | h <;> rcases Bool.eq_false_or_eq_true (ε s) with h' | h' <;>
    simp [h, h']

theorem tfa_sign' (ε : Fin n → Bool) (r s : Fin n) :
    (if ε s then (1 : ℂ) else -1) * adjSign ε s r = if ε r then (1 : ℂ) else -1 := by
  unfold adjSign
  rcases Bool.eq_false_or_eq_true (ε r) with h | h <;> rcases Bool.eq_false_or_eq_true (ε s) with h' | h' <;>
    simp [h, h']

theorem tfa_inner_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (x : Fin n → D) (y : D) : inner ℂ (((∑ r, x r : D)) : H) (y : H) = ∑ r, inner ℂ ((x r : D) : H) (y : H) := by
  rw [Submodule.coe_sum, sum_inner]

theorem tfa_inner_sum' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (x : Fin n → D) (y : D) : inner ℂ (y : H) (((∑ r, x r : D)) : H) = ∑ r, inner ℂ (y : H) ((x r : D) : H) := by
  rw [Submodule.coe_sum, inner_sum]

section FormB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} {ε : Fin n → Bool}

theorem formB_conj (f g : Fin n → D) : starRingEnd ℂ (formB ε f g) = formB ε g f := by
  simp only [formB, map_sum, map_mul, inner_conj_symm]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem formB_add_right (f g g' : Fin n → D) : formB ε f (g + g') = formB ε f g + formB ε f g' := by
  simp only [formB, Pi.add_apply, Submodule.coe_add, inner_add_right, mul_add, sum_add_distrib]

theorem formB_smul_right (f g : Fin n → D) (a : ℂ) : formB ε f (a • g) = a * formB ε f g := by
  simp only [formB, Pi.smul_apply, Submodule.coe_smul, inner_smul_right, mul_sum]
  refine sum_congr rfl fun c _ => by ring

theorem formB_smul_left (f g : Fin n → D) (a : ℂ) : formB ε (a • f) g = starRingEnd ℂ a * formB ε f g := by
  simp only [formB, Pi.smul_apply, Submodule.coe_smul, inner_smul_left, mul_sum]
  refine sum_congr rfl fun c _ => by ring

theorem formB_zero_right (f : Fin n → D) : formB ε f 0 = 0 := by
  simp [formB]

theorem formB_zero_left (f : Fin n → D) : formB ε 0 f = 0 := by
  simp [formB]

theorem formB_sub_right (f g g' : Fin n → D) : formB ε f (g - g') = formB ε f g - formB ε f g' := by
  simp only [formB, Pi.sub_apply, Submodule.coe_sub, inner_sub_right, mul_sub, sum_sub_distrib]

theorem formB_sum_right {ι : Type*} (s : Finset ι) (f : Fin n → D) (g : ι → Fin n → D) :
    formB ε f (∑ i ∈ s, g i) = ∑ i ∈ s, formB ε f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [formB_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, formB_add_right, ih]

end FormB

def closRep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (g : Matrix (Fin n) (Fin n) ℂ) : S →L[ℂ] S :=
  S.orthogonalProjection ∘L σ g ∘L S.subtypeL

theorem trace_nonneg (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x) :
    c.im = 0 ∧ 0 ≤ c.re ∧ (c = 0 → ∀ f ∈ tensSub (genSub E V), P f = 0) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  have hcore : ∀ y ∈ V, (y : H) ≠ 0 → ∃ r : ℝ, 0 ≤ r ∧ c = r ∧ (c = 0 → ∀ b, P (Pi.single b y) = 0) :=
    fun y hy hy0 => tf_trace_core dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy hy0
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  obtain ⟨r, hr, hcr, -⟩ := hcore y0 hy0V hy0H
  refine ⟨by rw [hcr, Complex.ofReal_im], by rw [hcr, Complex.ofReal_re]; exact hr, fun h0 => ?_⟩
  have hV0 : ∀ y ∈ V, ∀ b, P (Pi.single b y) = 0 := by
    intro y hy b
    by_cases hyz : (y : H) = 0
    · have hy' : y = 0 := Subtype.ext hyz
      rw [hy', Pi.single_zero, map_zero]
    · obtain ⟨-, -, -, h⟩ := hcore y hy hyz
      exact h h0 b
  have hVt : ∀ f ∈ tensSub V, P f = 0 := by
    intro f hf
    rw [← Finset.univ_sum_single f, map_sum]
    exact sum_eq_zero fun b _ => hV0 _ ((tset_mem.1 hf) b) b
  have hle : tensSub (genSub E V) ≤ tensSub (genSub E V) ⊓ LinearMap.ker P := by
    refine tfg_gen dual E V _ (fun f hf => ⟨tset_mem.2 fun b => rorth_le_genSub ((tset_mem.1 hf) b), hVt f hf⟩) ?_
    intro a b f hf
    refine ⟨tensSub_stable dual a b f hf.1, ?_⟩
    show P (tensF dual E a b f) = 0
    rw [hP.2.1 a b f hf.1, show P f = 0 from hf.2, map_zero]
  intro f hf
  exact (hle hf).2

theorem trace_ge (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    (hSq : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V)))
    (hSq' : Formalism.MainNotions.S.IsSqIntOn ε (closRep σ (closGen E V')))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c : ℂ} (hc : ∀ x ∈ genSub E V, ptr P x = c • x)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι)
    (hιP : ∀ x ∈ genSub E V', P (ι x) = ι x) {w : closGen E V} (hw : w ≠ 0) {w' : closGen E V'} (hw' : w' ≠ 0) :
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
              Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w ≤ c.re ∧
      (c.re = Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' /
          Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w →
        ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x) := by
  rename_i hcas
  have hPB' : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)) := hPB
  obtain ⟨d, hd⟩ := tfClRep_fdeg hgap hσ hD hV hcas hVK hSq
  obtain ⟨d', hd'⟩ := tfClRep_fdeg hgap' hσ hD hV' hc' hVK' hSq'
  have hfd : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V)) w = d :=
    fdegOf_of_isFdeg' hd hw
  have hfd' : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep σ (closGen E V')) w' = d' :=
    fdegOf_of_isFdeg' hd' hw'
  rw [hfd, hfd']
  obtain ⟨y0, hy0V, hy00, -⟩ := hV.2.2.2
  have hy0H : (y0 : H) ≠ 0 := fun h => hy00 (Subtype.ext h)
  have hy0G : y0 ∈ genSub E V := rorth_le_genSub hy0V
  obtain ⟨HP, wv, hHPc, hHPeq, hst, hrep, hc0eq⟩ :=
    tf_trace_data dual hσ hD hsm hgap hV hcas hVK hW hP hPP hPB' hEP hc hy0V hy0H hd
  obtain ⟨V₂, hV₂, hc₂, hVK₂, hV₂0, hgen1, -⟩ :=
    tf_datum2 dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hV' hc' hVK' hι
  have hV'0 : V' ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV'.2.2.2
    intro h
    apply hu0
    have hub : u ∈ (⊥ : Submodule ℂ D) := h ▸ hu
    exact (Submodule.mem_bot ℂ).1 hub
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap' hσ hD hV' hc' hVK' hV'0 hR hDR hV₂ hc₂ hVK₂ hV₂0
  have hschur := tf_schur_transfer (closGen E V') (closGen (smE ε (tfRdiag ε)) V₂) U hU
    (closGen_stable hgap' hσ hD hV' hc' hVK') hd'
  have hH'c : IsClosed ((closGen (smE ε (tfRdiag ε)) V₂ : Submodule ℂ (tfL2n ε)) : Set (tfL2n ε)) :=
    Submodule.isClosed_topologicalClosure _
  have hst2 := closGen_stable hgap' hR hDR hV₂ hc₂ hVK₂
  have hH'P : closGen (smE ε (tfRdiag ε)) V₂ ≤ HP := by
    refine Submodule.topologicalClosure_minimal _ ?_ hHPc
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hgen1 v hv
    rw [hHPeq]
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ι x, hι.1 x hx, ?_⟩)
    show (v : tfL2n ε) = _
    rw [hxe, hιP x hx]
  have hH'0 : closGen (smE ε (tfRdiag ε)) V₂ ≠ ⊥ := by
    obtain ⟨u, hu, hu0, -⟩ := hV₂.2.2.2
    intro h
    apply hu0
    have h1 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ closGen (smE ε (tfRdiag ε)) V₂ :=
      Submodule.le_topologicalClosure _ ⟨u, Submodule.mem_sInf.mpr fun _ hT => hT.1 hu, rfl⟩
    have h2 : ((u : smD ε (tfRdiag ε)) : tfL2n ε) ∈ (⊥ : Submodule ℂ (tfL2n ε)) := h ▸ h1
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 h2)
  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := hR.1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    hR.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    hR.2.1 _ (umat_mem_UJset ε g) v
  obtain ⟨hge, heq⟩ := tf_ge_abstract (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso
    HP _ hH'c hH'P (fun g v hv => hst2 _ (umat_mem_UJset ε g) v hv) hH'0 wv hrep hd'.1 hschur
  have hdpos : 0 < d := hd.1
  have hre : c.re = (∑ i, ‖wv i‖ ^ 2) / d := by rw [hc0eq, Complex.ofReal_re]
  refine ⟨by rw [hre]; exact div_le_div_of_nonneg_right hge hdpos.le, fun h => ?_⟩
  have hT : ∑ i, ‖wv i‖ ^ 2 = d' := by
    rw [hre, div_left_inj' hdpos.ne'] at h
    exact h
  have hle := heq hT
  refine tf_eq_case dual hσ hD hsm hgap hV hcas hVK hW hd hy0G hy0H hP hι.1 hgap' hV₂ hc₂ hVK₂ hgen1 ?_
  intro f hf
  apply hle
  rw [hHPeq]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem eeF_formB_symm (dual : Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (f g : Fin n → D) :
    formB ε (eeF dual E f) g = formB ε f (eeF dual E g) := by
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hU' : ∀ a b (x y : D), inner ℂ ((E a b x : D) : H) (y : H) = adjSign ε a b * inner ℂ (x : H) ((E b a y : D) : H) := by
    intro a b x y
    have := hU a b x y
    simpa only [Submodule.coe_inner] using this
  cases dual
  · simp only [formB, eeF, cond_false, eeV_coord, tfa_inner_sum, tfa_inner_sum', mul_sum, hU']
    rw [sum_comm]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, tfa_sign]
  · simp only [formB, eeF, cond_true, eeVd_coord, Submodule.coe_neg, inner_neg_left, inner_neg_right,
      tfa_inner_sum, tfa_inner_sum', mul_neg, mul_sum, hU', sum_neg_distrib]
    rw [sum_comm]
    refine congrArg _ (sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_)
    rw [← mul_assoc, tfa_sign']

theorem eigenProj_formB (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) {P : Module.End ℂ (Fin n → D)}
    (hPM : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V)) (hPz : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    (hP1 : ∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0) :
    ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), formB ε (P f) g = formB ε f (P g) := by
  obtain ⟨Bs, hdec, hreal⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have horth : ∀ x y : Fin n → D, ∀ a b : ℂ, a.im = 0 → eeF dual E x = a • x → eeF dual E y = b • y → a ≠ b →
      formB ε x y = 0 := by
    intro x y a b ha hx hy hab
    have h := eeF_formB_symm dual hσ hD (ε := ε) x y
    rw [hx, hy, formB_smul_left, formB_smul_right] at h
    have hca : starRingEnd ℂ a = a := Complex.conj_eq_iff_im.mpr ha
    rw [hca] at h
    have h2 : (a - b) * formB ε x y = 0 := by rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hab
    · exact h3
  have hL : ∀ f ∈ tensSub (genSub E V), ∀ h ∈ tensSub (genSub E V), formB ε (P f) (h - P h) = 0 := by
    intro f hf h hh
    obtain ⟨hb, hbe, rfl⟩ := hdec h hh
    rw [map_sum, ← sum_sub_distrib, formB_sum_right]
    refine sum_eq_zero fun b _ => ?_
    by_cases hbz : ((b : ℝ) : ℂ) = z
    · rw [hP1 _ (hbe b).1 (by rw [(hbe b).2, hbz]), sub_self, formB_zero_right]
    · rw [hP0 _ (hbe b).1 _ hbz (hbe b).2, sub_zero]
      by_cases hPf : P f = 0
      · rw [hPf, formB_zero_left]
      · obtain ⟨b0, _, hb0⟩ := hreal z (P f) (hPM f hf) hPf (hPz f hf)
        exact horth _ _ z _ (by rw [hb0]; simp) (hPz f hf) (hbe b).2 (Ne.symm hbz)
  intro f hf g hg
  have e1 : formB ε (P f) g = formB ε (P f) (P g) := by
    have := hL f hf g hg
    rw [formB_sub_right, sub_eq_zero] at this
    exact this
  have e2 : formB ε f (P g) = formB ε (P f) (P g) := by
    have := hL g hg f hf
    rw [formB_sub_right, sub_eq_zero] at this
    rw [← formB_conj, this, formB_conj]
  rw [e1, e2]

end ReciprocityTheory.ChartRestriction.DS
