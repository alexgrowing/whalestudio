import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TotalDegreeLinear

noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace AvgPf

section
variable {ι A B : Type} [Fintype ι]

def actP (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (actP g h z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rcases s with x | y
    · simp [sub, actP, map_sum]
    · simp [sub, actP, map_sum]

theorem actP_actP (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actP g h (actP g' h' z) = actP (g * g') (h * h') z := by
  funext s
  rcases s with x | y
  · simp only [actP, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [actP, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem totalDegree_sub_le (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree :=
  _root_.UpperTheory.Reformulated.B.TotalDegreeLinear.main g h p

theorem continuous_coeff_sub {K : Type} [TopologicalSpace K] (g h : K → Matrix ι ι ℂ) (hg : Continuous g)
    (hh : Continuous h) (p : PV ι A B) : ∀ m, Continuous fun k => coeff m (sub (g k) (h k) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => intro m; simp only [sub, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro m; simp only [map_add, coeff_add]; exact (hp m).add (hq m)
  | mul_X p s hp =>
    intro m
    rcases s with x | y
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inl x))) =
          ∑ j, g k x.1 j * coeff m (sub (g k) (h k) p * X (Sum.inl (j, x.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inl, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply x.1).comp hg))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inr y))) =
          ∑ j, h k y.1 j * coeff m (sub (g k) (h k) p * X (Sum.inr (j, y.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inr, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply y.1).comp hh))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const

end

abbrev εT (N : ℕ) : Fin N → Bool := fun _ => true

theorem continuous_toMK (N : ℕ) : Continuous fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

theorem toMK_mul (N : ℕ) (k k' : Formalism.REAL.KG (εT N)) :
    Formalism.REAL.toMK (k * k') = Formalism.REAL.toMK k * Formalism.REAL.toMK k' := rfl

theorem map_star_mul {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp [Matrix.mul_apply]

theorem exists_toMK (N : ℕ) (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ k : Formalism.REAL.KG (εT N), Formalism.REAL.toMK k = u := by
  have hJ : Formalism.REAL.Jm (εT N) = 1 := by
    simp [Formalism.REAL.Jm, εT, Matrix.diagonal_one]
  have : u ∈ Formalism.REAL.Kset (εT N) := ⟨hu, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  rw [← Formalism.REAL.range_toMK] at this
  exact this

theorem isEmbedding_toMK (N : ℕ) : Topology.IsEmbedding (fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k) :=
  (Formalism.REAL.isClosedEmbeddingMatrix N (εT N)).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal

instance instSCKG (N : ℕ) : SecondCountableTopology (Formalism.REAL.KG (εT N)) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (isEmbedding_toMK N).isInducing.secondCountableTopology

theorem muK_univ (N : ℕ) : Formalism.REAL.muK (εT N) Set.univ = 1 := by
  have := Measure.haarMeasure_self (G := Formalism.REAL.KG (εT N)) (K₀ := ⊤)
  rw [TopologicalSpace.PositiveCompacts.coe_top] at this
  exact this

theorem map_mul_right_muK (N : ℕ) (g : Formalism.REAL.KG (εT N)) :
    Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N)) = Formalism.REAL.muK (εT N) := by
  have : (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_mul_right (Formalism.REAL.muK (εT N)) g
  have h := Measure.haarMeasure_unique (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))) ⊤
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
    Set.preimage_univ, muK_univ, one_smul]
  rfl

instance (N : ℕ) : (Formalism.REAL.muK (εT N)).IsMulRightInvariant := ⟨fun g => map_mul_right_muK N g⟩

end AvgPf

open AvgPf in
theorem avg : Avg := by
  classical
  intro N A B _ _ p
  set μ := Formalism.REAL.muK (εT N)
  let F : Formalism.REAL.KG (εT N) → PV (Fin N) A B := fun k =>
    sub (Formalism.REAL.toMK k) ((Formalism.REAL.toMK k).map star) p
  set d := p.totalDegree
  let S : Finset ((Fin N × A) ⊕ (Fin N × B) →₀ ℕ) :=
    ((Finset.univ : Finset ((Fin N × A) ⊕ (Fin N × B) → Fin (d + 1))).image
      (fun f => Finsupp.equivFunOnFinite.symm (fun s => (f s : ℕ)))).filter (fun m => (m.sum fun _ e => e) ≤ d)
  have hsupp : ∀ k, (F k).support ⊆ S := by
    intro k m hm
    have hdeg : (m.sum fun _ e => e) ≤ d := (le_totalDegree hm).trans (totalDegree_sub_le _ _ _)
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun s => ⟨m s, Nat.lt_succ_of_le ?_⟩, Finset.mem_univ _, ?_⟩, hdeg⟩
    · exact (Finsupp.le_degree ..).trans hdeg
    · ext s; simp
  have hcont : ∀ m, Continuous fun k => coeff m (F k) := fun m =>
    continuous_coeff_sub _ _ (continuous_toMK N)
      (continuous_pi fun i => continuous_pi fun j => continuous_star.comp
        ((continuous_apply j).comp ((continuous_apply i).comp (continuous_toMK N)))) p m
  have hint : ∀ m, Integrable (fun k => coeff m (F k)) μ := fun m =>
    integrableOn_univ.1 ((hcont m).continuousOn.integrableOn_compact isCompact_univ)
  let P : PV (Fin N) A B := ∑ m ∈ S, monomial m (∫ k, coeff m (F k) ∂μ)
  have hF : ∀ k, F k = ∑ m ∈ S, monomial m (coeff m (F k)) := by
    intro k
    conv_lhs => rw [(F k).as_sum]
    exact Finset.sum_subset (hsupp k) fun m _ hm => by rw [notMem_support_iff.1 hm, monomial_zero]
  have heval : ∀ z, eval z P = ∫ k, eval z (F k) ∂μ := by
    intro z
    have e : ∀ k, eval z (F k) = ∑ m ∈ S, coeff m (F k) * (m.prod fun n e => z n ^ e) := by
      intro k
      conv_lhs => rw [hF k]
      simp only [map_sum, eval_monomial]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_finsetSum _ (fun m _ => (hint m).mul_const _)]
    simp only [P, map_sum, eval_monomial, integral_mul_const]
  refine ⟨P, ?_, ?_, heval⟩
  · intro u hu
    obtain ⟨ku, hku⟩ := exists_toMK N u hu
    refine MvPolynomial.funext fun z => ?_
    rw [AvgPf.eval_sub, heval, heval]
    have e2 : ∀ k, eval (actP u (u.map star) z) (F k) = eval z (F (k * ku)) := by
      intro k
      simp only [F]
      rw [AvgPf.eval_sub, actP_actP, ← AvgPf.eval_sub, toMK_mul, hku, map_star_mul]
    simp only [e2]
    exact integral_mul_right_eq_self (fun k => eval z (F k)) ku
  · refine totalDegree_finsetSum_le fun m hm => (totalDegree_monomial_le _ _).trans ?_
    exact (Finset.mem_filter.1 hm).2

end PositivityTheory.Rg.Sw.FFTSteps
