import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefEmbed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tfg_gen {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (S : Submodule ℂ (Fin n → M))
    (hV : tensSub V ≤ S) (hS : ∀ a b, ∀ f ∈ S, tensF dual E a b f ∈ S) : tensSub (genSub E V) ≤ S := by
  let T : Submodule ℂ M := ⨅ c, S.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hT : ∀ m, m ∈ T ↔ ∀ c, (Pi.single c m : Fin n → M) ∈ S := fun m => by simp [T, Submodule.mem_iInf]
  have hle : genSub E V ≤ T := sInf_le ⟨fun v hv => (hT v).2 fun c => hV (tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using hv
      · simp [h]),
    fun a b m hm => (hT _).2 fun c => by
      have hm' := (hT m).1 hm
      cases dual
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF false E a b (Pi.single c m) - if b = c then Pi.single a m else 0 := by
          funext d
          simp only [tensF, cond_false, Pi.sub_apply, tensV_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = a <;> by_cases h3 : b = c <;>
            simp_all
        rw [e]
        refine S.sub_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' a
        · exact S.zero_mem
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF true E a b (Pi.single c m) + if a = c then Pi.single b m else 0 := by
          funext d
          simp only [tensF, cond_true, Pi.add_apply, tensVd_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = b <;> by_cases h3 : a = c <;>
            simp_all
        rw [e]
        refine S.add_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' b
        · exact S.zero_mem⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact S.sum_mem fun c _ => (hT _).1 (hle (tset_mem.mp hf c)) c

theorem tfg_real {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ X} (hU : IsInfUnitary ε E) {c : ℂ} {v : X}
    (h : casimir E v = c • v) : casimir E v = ((c.re : ℝ) : ℂ) • v := by
  by_cases hv : v = 0
  · simp [hv]
  have h1 : inner ℂ (casimir E v) v = inner ℂ v (casimir E v) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have e1 := hU b a v (E b a v)
    have e2 := hU a b (E b a v) v
    have e3 : inner ℂ v (E a b (E b a v)) = starRingEnd ℂ (inner ℂ (E a b (E b a v)) v) :=
      (inner_conj_symm _ _).symm
    rw [e3, e2, map_mul, inner_conj_symm]
    congr 1
    unfold adjSign; split_ifs <;> simp
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 := mul_right_cancel₀ (inner_self_ne_zero.mpr hv) h1
  rw [h, Complex.conj_eq_iff_re.mp h2]

theorem tf_closure_stable (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {y : D} (hy : y ∈ genSub E V) :
    ∀ g ∈ UJset ε, ∀ v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure,
      tfRdiag ε g v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure := by
  have hη : ∀ c, (Pi.single c (tfSgn ε c • y) : Fin n → D) ∈ tensSub (genSub E V) := fun c =>
    tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using Submodule.smul_mem _ _ hy
      · simp [h]
  have hco : ∀ c, (fun d => (((Pi.single c (tfSgn ε c • y) : Fin n → D) d : D) : H)) =
      Pi.single c (tfSgn ε c • (y : H)) := fun c => funext fun d => by
    by_cases h : d = c
    · subst h; simp
    · simp [h]
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (hη c) f hf
  simp only [hco] at hce
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, mul_sum, mul_left_comm]) }
  have hΦE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
      Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f =>
    Subtype.ext (vectorL2_ext fun c => by
      refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
      refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
      exact (hce c f.1 f.2).2.1 a b g hg)
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let Ξ := Φ ∘ₗ P'
  have hΞE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Ξ f) =
      Ξ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f => by
    refine (hΦE a b (P' f)).trans (congrArg Φ (Subtype.ext ?_))
    exact (hP.2.1 a b f.1 f.2).symm
  let W : Submodule ℂ (tensSub (n := n) (genSub E V)) := (tensSub V).comap (tensSub (genSub E V)).subtype
  have := hV.1
  have hVle : tensSub (n := n) V ≤ tensSub (genSub E V) := fun f hf =>
    tset_mem.mpr fun c => Submodule.mem_sInf.mpr fun _ hT => hT.1 (tset_mem.mp hf c)
  have hfd : FiniteDimensional ℂ (tensSub (n := n) V) :=
    Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict V
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub V).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hW' : FiniteDimensional ℂ W := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hVle).symm
  have hkst : IsKStableSub ε (smE ε (tfRdiag ε)) (W.map Ξ) := by
    rintro a b hab _ ⟨f, hf, rfl⟩
    refine ⟨_, ?_, (hΞE a b f).symm⟩
    have hf' := tset_mem.mp (show f.1 ∈ tensSub V from hf)
    refine tset_mem.mpr fun c => ?_
    show tensF dual E a b f.1 c ∈ V
    cases dual
    · simp only [tensF, cond_false, tensV_coord]
      exact V.add_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' b, V.zero_mem])
    · simp only [tensF, cond_true, tensVd_coord]
      exact V.sub_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' a, V.zero_mem])
  have hcas : ∀ v ∈ W.map Ξ, casimir (smE ε (tfRdiag ε)) v =
      (((((casVal lam : ℝ) : ℂ) + n + 2 * z).re : ℝ) : ℂ) • v := by
    rintro _ ⟨f, -, rfl⟩
    refine tfg_real (isInfUnitary_of_isDerivedOn hR hDR) ?_
    have h3 : diagOp (casimir E) (P f.1) = ((casVal lam : ℝ) : ℂ) • P f.1 := funext fun c => by
      rw [diagOp_coord, casimir_genSub hD.glRep hc _ (tset_mem.mp (hP.1 _ f.2) c)]; rfl
    have h2 : casimir (tensF dual E) (P f.1) = (((casVal lam : ℝ) : ℂ) + n + 2 * z) • P f.1 := by
      rw [add_smul, add_smul, mul_smul, ← hEP f.1 f.2, ← h3]
      cases dual
      · exact LinearMap.congr_fun (casimir_tensV hD.glRep) _
      · exact LinearMap.congr_fun (casimir_tensVd hD.glRep) _
    show casimir _ (Φ (P' f)) = _ • Φ (P' f)
    rw [← map_smul]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hΦE, ← map_sum]
    refine congrArg Φ (Subtype.ext ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [show ((P' f : tensSub (n := n) (genSub E V)) : Fin n → D) = P f.1 from rfl, ← h2]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply]
  have hgen : genSub (smE ε (tfRdiag ε)) (W.map Ξ) = LinearMap.range Ξ := by
    refine le_antisymm (sInf_le ⟨LinearMap.map_le_range, ?_⟩) ?_
    · rintro a b _ ⟨f, rfl⟩
      exact ⟨_, (hΞE a b f).symm⟩
    · rintro _ ⟨f, rfl⟩
      have h1 := tfg_gen dual E V (((genSub (smE ε (tfRdiag ε)) (W.map Ξ)).comap Ξ).map
        (tensSub (genSub E V)).subtype)
        (fun f hf => ⟨⟨f, hVle hf⟩, Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨_, hf, rfl⟩, rfl⟩)
        (by
          rintro a b _ ⟨f, hf, rfl⟩
          refine ⟨⟨_, tensSub_stable dual a b f.1 f.2⟩, ?_, rfl⟩
          show Ξ _ ∈ genSub _ _
          rw [← hΞE]
          exact tset_genSub_E _ _ a b hf) f.2
      obtain ⟨f', hf', e⟩ := h1
      rwa [← Subtype.ext e]
  have hspan : Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
      v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} =
      (genSub (smE ε (tfRdiag ε)) (W.map Ξ)).map (smD ε (tfRdiag ε)).subtype := by
    rw [hgen, ← Submodule.span_eq (Submodule.map _ _)]
    congr 1
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  rw [hspan]
  exact closure_genSub_stable hR hDR inferInstance hkst hcas

end ReciprocityTheory.ChartRestriction.DS
