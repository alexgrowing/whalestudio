import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapValA

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h by simp only [Matrix.mul_assoc], hg]
  exact hh

lemma capelliC_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (u : ℂ) :
    ∀ y ∈ S, Capelli.capelliC E u y ∈ S := by
  have hprod : ∀ l : List (Module.End ℂ M), (∀ A ∈ l, ∀ y ∈ S, A y ∈ S) → ∀ y ∈ S, l.prod y ∈ S := by
    intro l
    induction l with
    | nil => intro _ y hy; simpa using hy
    | cons A l ih =>
      intro hl y hy
      rw [List.prod_cons, Module.End.mul_apply]
      exact hl A List.mem_cons_self _ (ih (fun B hB => hl B (List.mem_cons_of_mem _ hB)) y hy)
  intro y hy
  unfold Capelli.capelliC Capelli.cminor
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [LinearMap.smul_apply]
  refine zsmul_mem (hprod _ ?_ y hy) _
  intro A hA
  rw [List.mem_ofFn] at hA
  obtain ⟨j, rfl⟩ := hA
  intro z hz
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS _ _ z hz) ?_
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact S.smul_mem _ hz
  · simp

section Clos

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {D : Submodule ℂ H} {V : Submodule ℂ D} {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}

variable (ε σ V) in

def clo : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ g, inUJ ε g ∧ ∃ v : D, v ∈ V ∧ x = σ g (v : H)}).topologicalClosure

lemma sig_mem_clo (hσ : IsURepOn (UJset ε) σ) {h : Matrix (Fin n) (Fin n) ℂ} (hh : inUJ ε h) {x : H}
    (hx : x ∈ clo V ε σ) : σ h x ∈ clo V ε σ := by
  have hle : Submodule.span ℂ {x : H | ∃ g, inUJ ε g ∧ ∃ v : D, v ∈ V ∧ x = σ g (v : H)} ≤
      (clo V ε σ).comap (σ h : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro y ⟨g, hg, v, hv, rfl⟩
    show σ h (σ g (v : H)) ∈ clo V ε σ
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 h hh g hg]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨h * g, inUJ_mul hh hg, v, hv, rfl⟩)
  have hcl : IsClosed (((clo V ε σ).comap (σ h : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (σ h).continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hx

lemma mem_of_hasDerivAt {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) {f : ℝ → H} {f' : H}
    (hf : HasDerivAt f f' 0) (hm : ∀ t, f t ∈ K) : f' ∈ K := by
  refine hK.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hf) (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact Submodule.smul_of_tower_mem K _ (K.sub_mem (hm t) (hm 0))

lemma actM_mem_clo (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) {x : D} (hx : (x : H) ∈ clo V ε σ) : ((actM E X x : D) : H) ∈ clo V ε σ :=
  mem_of_hasDerivAt (Submodule.isClosed_topologicalClosure _) (hD.deriv X hX x)
    fun t => sig_mem_clo hσ (inUJ_exp ε hX t) hx

lemma E_mem_clo (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (a b : Fin n) {x : D}
    (hx : (x : H) ∈ clo V ε σ) : ((E a b x : D) : H) ∈ clo V ε σ := by
  have hs : S7.cpart1 ε (Matrix.single a b 1) + Complex.I • S7.cpart2 ε (Matrix.single a b 1) =
      Matrix.single a b 1 := LemK.ta_cpart_sum ε _
  rw [← SmDerA.actM_single E a b, ← hs, SmDerA.actM_add, SmDerA.actM_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul]
  exact add_mem (actM_mem_clo hσ hD (LemK.ta_inG_cpart1 ε _) hx)
    (Submodule.smul_mem _ _ (actM_mem_clo hσ hD (LemK.ta_inG_cpart2 ε _) hx))

end Clos

theorem capVal_main : CapValStatement := by
  intro n ε lam _h H _ _ _ σ D E V T μ ι hσ hD _hV _hcas _hVK hμ hcoef _hHC _hgap _hh _hq ω m hm
  set P : ℂ := ∏ t, (ω + ((LemK.thV lam t : ℝ) : ℂ)) with hP
  set C := Capelli.capelliC E ω with hC
  have hΨ : ∀ g, inUJ ε g → S7.PsiM T μ g = opC σ ι g 1 := by
    intro g hg
    refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun x' => ?_
    obtain ⟨v, rfl⟩ := ι.surjective x
    obtain ⟨v', rfl⟩ := ι.surjective x'
    rw [opC_coef σ ι g 1 v v', ← hcoef g hg v v']
    rfl
  have hval : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((C v : D) : H)⟫_ℂ = P * ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ := by
    intro g hg v v'
    have h1 := S7.psiM_capelli T μ hμ (ω - ((n : ℂ) - 1) / 2) hg
    rw [show ω - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 = ω by ring] at h1
    rw [show Formalism.QuantumDeterminants.capelli ε ω (S7.PsiM T μ) = Formalism.QuantumDeterminants.qdetOp (Formalism.REAL.EabV ε) ω (S7.PsiM T μ)
      from rfl, qdet_opC hσ hD ι hΨ hg ω] at h1
    have h3 : Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (ω - ((n : ℂ) - 1) / 2) = P := by
      unfold Formalism.QuantumDeterminants.capP
      rw [hP]
      refine Finset.prod_congr rfl fun t _ => ?_
      unfold LemK.thV
      push_cast
      ring
    rw [← opC_coef σ ι g C v v', ← mul_one C, h1, h3, hΨ g hg, _root_.smul_apply,
      inner_smul_right, opC_coef]
    rfl
  have hA : ∀ v : V, C v = P • (v : D) := by
    intro v
    set u : D := C v - P • (v : D) with hu
    have horth : ∀ g, inUJ ε g → ∀ v' : V, ⟪((v' : D) : H), σ g (u : H)⟫_ℂ = 0 := by
      intro g hg v'
      rw [hu, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, inner_sub_right,
        inner_smul_right, hval g hg v v', sub_self]
    let S : Submodule ℂ D := (clo V ε σ).comap D.subtype
    have hSE : ∀ a b, ∀ x ∈ S, E a b x ∈ S := fun a b x hx => E_mem_clo hσ hD a b hx
    have hvS : (v : D) ∈ S := by
      show ((v : D) : H) ∈ clo V ε σ
      refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, inUJ_one ε, v, v.2, ?_⟩)
      rw [hσ.1.1]
      rfl
    have huS : u ∈ S := S.sub_mem (capelliC_mem E S hSE ω _ hvS) (S.smul_mem P hvS)
    have hle : clo V ε σ ≤ (innerSL ℂ (u : H)).ker := by
      refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
      rw [Submodule.span_le]
      rintro y ⟨g, hg, w, hw, rfl⟩
      have h0 := horth _ (inUJ_jAdj hg) ⟨w, hw⟩
      have h1 : ⟪σ g (w : H), (u : H)⟫_ℂ = 0 := by
        rw [inner_sig_left hσ hg]
        exact h0
      show innerSL ℂ (u : H) (σ g (w : H)) = 0
      rw [innerSL_apply_apply, ← inner_conj_symm, h1, map_zero]
    have hin : innerSL ℂ (u : H) (u : H) = 0 := hle huS
    rw [innerSL_apply_apply] at hin
    have hu0 : u = 0 := by
      have : (u : H) = 0 := inner_self_eq_zero.mp hin
      exact_mod_cast this
    rw [hu, sub_eq_zero] at hu0
    exact hu0
  have hB : genSub E V ≤ LinearMap.ker (C - P • (1 : Module.End ℂ D)) := by
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
      exact hA ⟨x, hx⟩
    · intro a b x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hcomm := Capelli.capelliCentral (Module.End ℂ D) n E ω
        ((Capelli.isGlRep_iff_glRelR E).mp hD.glRep) a b
      have hce : C (E a b x) = E a b (C x) := by
        have := congrArg (fun A : Module.End ℂ D => A x) hcomm.eq
        simpa [Module.End.mul_apply] using this.symm
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
      rw [hce, ← map_smul, ← map_sub, hx, map_zero]
  have hm' := hB hm
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hm'
  exact hm'

end ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem capVal : CapValStatement := CapelliClosureMembership.capVal_main

end ReciprocityTheory.ChartRestriction.DS.Lap
