import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep

namespace PositivityTheory.Rg.BcB.CG.ReproA

section Fin

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem hasCompactSupport_prod {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha' : ∀ i, HasCompactSupport (a i))
    (f : (ι → G) → ℂ) : HasCompactSupport fun y : ι → G => (∏ i, a i (y i)) * f y := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun i => ha' i) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport (f := a i) hi), zero_mul]

theorem continuous_prod_mul {ι : Type} [Fintype ι] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (f : (ι → G) → ℂ) (hf : Continuous f) : Continuous fun y : ι → G => (∏ i, a i (y i)) * f y :=
  (continuous_finsetProd _ fun i _ => (ha i).comp (continuous_apply i)).mul hf

theorem cons_one_mul (n : ℕ) (z : Fin n → G) (j : Fin n) (t : G) :
    (Fin.cons 1 (z * Pi.mulSingle j t) : Fin (n + 1) → G) = Fin.cons 1 z * Pi.mulSingle j.succ t := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.succ_ne_zero]
  · simp only [Fin.cons_succ, Pi.mul_apply, Pi.mulSingle_apply, Fin.succ_inj]

theorem cons_mul_single (n : ℕ) (z : Fin n → G) (t : G) :
    (Fin.cons 1 z : Fin (n + 1) → G) * Pi.mulSingle 0 t = Fin.cons t z := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

variable (μ : Measure G) [μ.IsHaarMeasure]

theorem integral_fin_repro : ∀ (n : ℕ) (a : Fin n → G → ℂ), (∀ i, Continuous (a i)) → (∀ i, HasCompactSupport (a i)) →
    ∀ (f : (Fin n → G) → ℂ), Continuous f → ∀ (s : Fin n → ℂ),
    (∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) →
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1
  | 0, a, _, _, f, _, s, _ => by
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) 1, integral_dirac]
    simp
  | n + 1, a, ha, ha', f, hf, s, h => by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    set F : (Fin (n + 1) → G) → ℂ := fun y => (∏ i, a i (y i)) * f y with hF
    have hFi : Integrable F (Measure.pi fun _ => μ) :=
      (continuous_prod_mul a ha f hf).integrable_of_hasCompactSupport (hasCompactSupport_prod a ha' f)
    have e1 : ∫ y, F y ∂(Measure.pi fun _ => μ) = ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      rw [← hmp.integral_comp' (fun p => F (e.symm p))]
      simp
    have hsymm : ∀ p : G × (Fin n → G), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' _ _
    have hGi : Integrable (fun p => F (e.symm p)) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      have := (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding (g := F)
      exact this.2 hFi
    change ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    rw [e1, integral_prod_symm _ hGi]
    have e2 : ∀ z : Fin n → G, ∫ t, F (e.symm (t, z)) ∂μ =
        (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) := by
      intro z
      rw [← h 0 (Fin.cons 1 z), ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hsymm, hF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, cons_mul_single]
      ring
    simp_rw [e2]
    set a' : Fin n → G → ℂ := fun j => a j.succ
    set f' : (Fin n → G) → ℂ := fun z => f (Fin.cons 1 z)
    have hf' : Continuous f' := hf.comp (continuous_const.finCons continuous_id)
    have h' : ∀ j z, ∫ t, a' j t * f' (z * Pi.mulSingle j t) ∂μ = s j.succ * f' z := by
      intro j z
      simp only [a', f', cons_one_mul]
      exact h j.succ (Fin.cons 1 z)
    have ih := integral_fin_repro n a' (fun j => ha j.succ) (fun j => ha' j.succ) f' hf' (fun j => s j.succ) h'
    have e3 : ∀ z : Fin n → G, (∏ j, a j.succ (z j)) * (s 0 * f (Fin.cons 1 z)) =
        s 0 * ((∏ j, a' j (z j)) * f' z) := fun z => by simp only [a', f']; ring
    simp_rw [e3]
    rw [integral_const_mul, ih, Fin.prod_univ_succ]
    have e4 : f' 1 = f 1 := by
      simp only [f']
      congr 1
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [e4]
    ring

end Fin

theorem integral_pi_repro {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (a : ι → G → ℂ) (ha : ∀ i, Continuous (a i))
    (ha' : ∀ i, HasCompactSupport (a i)) (f : (ι → G) → ℂ) (hf : Continuous f) (s : ι → ℂ)
    (h : ∀ i y, ∫ t, a i t * f (y * Pi.mulSingle i t) ∂μ = s i * f y) :
    ∫ y, (∏ i, a i (y i)) * f y ∂(Measure.pi fun _ => μ) = (∏ i, s i) * f 1 := by
  set e := Fintype.equivFin ι
  set Φ := MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl G) with hΦ
  have hmp : MeasurePreserving Φ (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_arrowCongr' _ _ e.symm (MeasurableEquiv.refl G) fun _ => MeasurePreserving.id μ
  have hΦa : ∀ z : Fin (Fintype.card ι) → G, Φ z = fun i => z (e i) := by
    intro z; funext i; rfl
  rw [← hmp.integral_comp' (fun y => (∏ i, a i (y i)) * f y)]
  simp_rw [hΦa]
  set a' : Fin (Fintype.card ι) → G → ℂ := fun k => a (e.symm k)
  set f' : (Fin (Fintype.card ι) → G) → ℂ := fun z => f fun i => z (e i)
  have e1 : ∀ z : Fin (Fintype.card ι) → G, (∏ i, a i (z (e i))) * f (fun i => z (e i)) =
      (∏ k, a' k (z k)) * f' z := by
    intro z
    simp only [a', f']
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp
  simp_rw [e1]
  have hf' : Continuous f' := hf.comp (continuous_pi fun i => continuous_apply (e i))
  have hmul : ∀ (z : Fin (Fintype.card ι) → G) (k : Fin (Fintype.card ι)) (t : G),
      (fun i => (z * Pi.mulSingle k t : Fin (Fintype.card ι) → G) (e i)) =
        (fun i => z (e i)) * Pi.mulSingle (e.symm k) t := by
    intro z k t
    funext i
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hi : i = e.symm k
    · subst hi; simp
    · have : e i ≠ k := fun h' => hi (by rw [← h']; simp)
      simp [hi, this]
  have h' : ∀ k z, ∫ t, a' k t * f' (z * Pi.mulSingle k t) ∂μ = s (e.symm k) * f' z := by
    intro k z
    simp only [a', f', hmul]
    exact h (e.symm k) _
  rw [integral_fin_repro μ _ a' (fun k => ha _) (fun k => ha' _) f' hf' _ h']
  have e2 : f' 1 = f 1 := rfl
  rw [e2]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ fun k => rfl

theorem pi_isHaar {ι : Type} [Fintype ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : (Measure.pi fun _ : ι => μ).IsHaarMeasure := by
  infer_instance

theorem haar_restrict_eq {X A : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure X) [ν.IsHaarMeasure] (lam0 : Measure A) [lam0.IsHaarMeasure] (P : X →* A) (hP : Continuous P)
    (σ : A →* X) (hσ : ∀ a, P (σ a) = a) (U0 : Subgroup X) (hU0 : IsOpen (U0 : Set X)) (hσU : ∀ a, σ a ∈ U0)
    (hprop : ∀ C : Set A, IsCompact C → ∃ D : Set X, IsCompact D ∧ (U0 : Set X) ∩ P ⁻¹' C ⊆ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : A → ℂ, Continuous F → HasCompactSupport F →
      ∫ x, (U0 : Set X).indicator (fun x => F (P x)) x ∂ν = c * ∫ a, F a ∂lam0 := by
  have hPm : Measurable P := hP.measurable
  have hU0m : MeasurableSet (U0 : Set X) := hU0.measurableSet
  set lam : Measure A := Measure.map P (ν.restrict U0) with hlam
  have hinv : lam.IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hf : Measurable fun x : X => σ a * x := measurable_const_mul (σ a)
    have hpre : (fun x : X => σ a * x) ⁻¹' (U0 : Set X) = U0 := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using U0.mul_mem (U0.inv_mem (hσU a)) h, fun h => U0.mul_mem (hσU a) h⟩
    have e1 : Measure.map (fun x : X => σ a * x) (ν.restrict U0) = ν.restrict U0 := by
      conv_lhs => rw [← hpre]
      rw [← Measure.restrict_map hf hU0m, map_mul_left_eq_self]
    rw [hlam, Measure.map_map (measurable_const_mul a) hPm]
    have e2 : (fun x : A => a * x) ∘ P = P ∘ fun x : X => σ a * x := by
      funext x; simp [hσ]
    rw [e2, ← Measure.map_map hPm hf, e1]
  have hfin : IsFiniteMeasureOnCompacts lam := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨D, hD, hsub⟩ := hprop C hC
    rw [hlam, Measure.map_apply hPm hC.isClosed.measurableSet, Measure.restrict_apply (hPm hC.isClosed.measurableSet)]
    refine lt_of_le_of_lt (measure_mono ?_) hD.measure_lt_top
    intro x hx
    exact hsub ⟨hx.2, hx.1⟩
  have heq := Measure.isMulLeftInvariant_eq_smul lam lam0
  set c' := Measure.haarScalarFactor lam lam0 with hc'
  have hpos : c' ≠ 0 := by
    intro h0
    have h1 : lam Set.univ = 0 := by rw [heq, h0]; simp
    rw [hlam, Measure.map_apply hPm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter] at h1
    exact (hU0.measure_ne_zero ν ⟨1, U0.one_mem⟩) h1
  refine ⟨(c' : ℝ), lt_of_le_of_ne c'.2 (fun h => hpos (NNReal.coe_eq_zero.1 h.symm)), fun F hF _ => ?_⟩
  rw [integral_indicator hU0m, ← integral_map hPm.aemeasurable hF.aestronglyMeasurable, ← hlam]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem exists_compact_open_le (E : Type) [Field E] [NumberField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) :
    ∃ K0 : Subgroup (GL (Fin N) (Af E)), K0 ≤ K ∧ IsOpen (K0 : Set (GL (Fin N) (Af E))) ∧
      IsCompact (K0 : Set (GL (Fin N) (Af E))) := by
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E N
  refine ⟨K ⊓ U, inf_le_left, ?_, ?_⟩
  · exact hK.inter hUo
  · exact hUc.inter_left (K.isClosed_of_isOpen hK)

end PositivityTheory.Rg.BcB.CG.ReproA
