import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

section Gen

variable {ι : Type} [Fintype ι] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

private theorem integ_of_cont {X : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {f : X → ℂ} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Fintype ι] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem single_mul_eq (i : ι) (h : G) (k : ι → G) :
    (Pi.mulSingle i h : ι → G) * k = Function.update k i (h * k i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

omit [Fintype ι] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem update_mul_single (i : ι) (y h : G) (k : ι → G) :
    Function.update k i y * (Pi.mulSingle i h : ι → G) = Function.update k i (y * h) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

private theorem integral_update [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (i : ι) {F : (ι → G) → ℂ}
    (hF : Continuous F) :
    ∫ k, F k ∂(Measure.pi fun _ : ι => μ) =
      ∫ k, ∫ h, F (Function.update k i h) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
  have h1 : ∀ k : ι → G, ∫ h, F (Function.update k i h) ∂μ = ∫ h, F ((Pi.mulSingle i h : ι → G) * k) ∂μ := by
    intro k
    simp only [single_mul_eq]
    exact (integral_mul_right_eq_self (fun h => F (Function.update k i h)) (k i)).symm
  simp only [h1]
  rw [integral_integral_swap]
  · have h2 : ∀ h : G, ∫ k, F ((Pi.mulSingle i h : ι → G) * k) ∂(Measure.pi fun _ : ι => μ) =
        ∫ k, F k ∂(Measure.pi fun _ : ι => μ) := fun h => integral_mul_left_eq_self F _
    simp [h2]
  · apply integ_of_cont
    exact hF.comp (((continuous_mulSingle i).comp continuous_snd).mul continuous_fst)

private theorem fix_prod [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {M : Type} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] (j : G → M) (hj : Continuous j) (t : ι → G → ℂ) (ht : ∀ i, Continuous (t i))
    (Ψ : (ι → M) → ℂ) (hΨ : Continuous Ψ)
    (h : ∀ i g, ∫ m, t i m * Ψ (g * (Pi.mulSingle i (j m) : ι → M)) ∂μ = Ψ g) (g : ι → M) :
    ∫ m : ι → G, (∏ i, t i (m i)) * Ψ (g * fun i => j (m i)) ∂(Measure.pi fun _ : ι => μ) = Ψ g := by
  have key : ∀ s : Finset ι, ∫ m : ι → G, (∏ i ∈ s, t i (m i)) * Ψ (g * fun i => if i ∈ s then j (m i) else 1)
      ∂(Measure.pi fun _ : ι => μ) = Ψ g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun _ : ι => (1 : M)) = 1 := rfl
      simp [this]
    | insert a s ha ih =>
      rw [integral_update μ a, ← ih]
      · refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        beta_reduce
        rw [← h a, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        have e1 : ∏ i ∈ s, t i (Function.update m a y i) = ∏ i ∈ s, t i (m i) :=
          Finset.prod_congr rfl fun i hi => by
            rw [Function.update_of_ne (show i ≠ a from fun hh => ha (by rwa [← hh]))]
        have e2 : (g * fun i => if i ∈ insert a s then j (Function.update m a y i) else 1) =
            (g * fun i => if i ∈ s then j (m i) else 1) * (Pi.mulSingle a (j y) : ι → M) := by
          funext i
          by_cases hi : i = a
          · subst hi; simp [ha]
          · simp [hi]
        rw [Finset.prod_insert ha, e1, e2, Function.update_self]
        ring
      · refine (continuous_finset_prod _ fun i _ => (ht i).comp (continuous_apply i)).mul
          (hΨ.comp (continuous_const.mul (continuous_pi fun i => ?_)))
        split_ifs
        · exact hj.comp (continuous_apply i)
        · exact continuous_const
  simpa using key Finset.univ

private theorem fix_slice [μ.IsMulLeftInvariant] (e : ι → G → ℂ) (he : ∀ i, Idem μ (e i)) (Φ : (ι → G) → ℂ)
    (hΦ : Continuous Φ) (hf : RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i)) Φ) (i : ι) (g₀ : ι → G) :
    RFix μ (e i) fun y => Φ (Function.update g₀ i y) := by
  intro y
  simp only [← update_mul_single]
  generalize Function.update g₀ i y = g
  have h1 : ∀ h : G, Φ (g * (Pi.mulSingle i h : ι → G)) =
      ∫ k, e i (h⁻¹ * k i) * ((∏ j ∈ Finset.univ.erase i, e j (k j)) * Φ (g * k)) ∂(Measure.pi fun _ : ι => μ) := by
    intro h
    rw [← hf (g * (Pi.mulSingle i h : ι → G)),
      ← integral_mul_left_eq_self _ (Pi.mulSingle i h⁻¹ : ι → G)]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    have e1 : ∏ j ∈ Finset.univ.erase i, e j (((Pi.mulSingle i h⁻¹ : ι → G) * k) j) =
        ∏ j ∈ Finset.univ.erase i, e j (k j) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    have e2 : g * (Pi.mulSingle i h : ι → G) * ((Pi.mulSingle i h⁻¹ : ι → G) * k) = g * k := by
      rw [mul_assoc, ← mul_assoc (Pi.mulSingle i h : ι → G), ← Pi.mulSingle_mul]; simp
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), e1, e2]
    simp [mul_assoc]
  simp only [h1, ← integral_const_mul]
  rw [integral_integral_swap]
  · rw [← hf g]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    simp only [← mul_assoc (e i _), mul_assoc (e i _ * _)]
    rw [integral_mul_const, (he i).idem, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc]
  · apply integ_of_cont
    refine ((he i).cont.comp continuous_fst).mul (((he i).cont.comp
      (continuous_fst.inv.mul ((continuous_apply i).comp continuous_snd))).mul
      ((continuous_finset_prod _ fun j _ => (he j).cont.comp ((continuous_apply j).comp continuous_snd)).mul
        (hΦ.comp (continuous_const.mul continuous_snd))))

private theorem aboveSlice {ι : Type} {j : U2 → U4} {n : ℕ} {q : ℤ} {Φ : (ι → U4) → ℂ} (c : ι) (k : ι → U4)
    (h : LAbove (fun m => (Pi.mulSingle c (j m) : ι → U4)) n q Φ) :
    LAbove j n q fun y => Φ (Function.update k c y) := by
  intro n' q' hn l y
  have := h n' q' hn l (Function.update k c y)
  simpa only [single_mul_eq, Function.update_self, Function.update_idem] using this

end Gen

private theorem continuous_alt (n : ℕ) (q : ℤ) : Continuous (T n q) := by
  unfold T
  exact continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.extPi :
    ∀ (ι : Type) [Fintype ι] (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ →
      (∀ i, Ext μ (e i) (n i) (q i) (n' i) (q' i) (x i)) → ExtP μ e n q n' q' x := by
  intro ι _ μ e n q n' q' x hμ hE
  haveI : IsProbabilityMeasure μ := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun g => (hμ.left g).map_eq⟩
  haveI : μ.IsMulRightInvariant := ⟨fun g => (hμ.right g).map_eq⟩
  obtain ⟨-, -, -, -, hbd, -, -, -, -, -, -, hcpt, -⟩ := u4
  haveI : CompactSpace U4 := hcpt
  have hb1 : Continuous fun m : U2 => bd m 1 := hbd.comp (continuous_id.prodMk continuous_const)
  have hb2 : Continuous fun m : U2 => bd 1 m := hbd.comp (continuous_const.prodMk continuous_id)
  have hcontS : ∀ (Φ : (ι → U4) → ℂ), Continuous Φ → ∀ (i : ι) (k : ι → U4),
      Continuous fun y => Φ (Function.update k i y) := fun Φ hΦ i k =>
    hΦ.comp (continuous_const.update i continuous_id)
  have hsl : ∀ (Φ : (ι → U4) → ℂ) (i : ι) (g : ι → U4) (h : U4),
      Φ (g * (Pi.mulSingle i h : ι → U4) * x) =
        (fun y => Φ (Function.update (g * x) i y)) (g i * h * x i) := by
    intro Φ i g h
    beta_reduce
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hsl0 : ∀ (Φ : (ι → U4) → ℂ) (i : ι) (g : ι → U4),
      Φ (g * x) = (fun y => Φ (Function.update (g * x) i y)) (g i * x i) := by
    intro Φ i g
    beta_reduce
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hidem : ∀ i, Idem μ (e i) := fun i => (hE i).idem
  refine ⟨⟨continuous_finset_prod _ fun i _ => (hE i).idem.cont.comp (continuous_apply i), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.inv_apply, (hE _).idem.star, map_prod]
  · intro k
    have h1 : ∀ h : ι → U4, (∏ i, e i (h i)) * ∏ i, e i ((h⁻¹ * k) i) = ∏ i, e i (h i) * e i ((h i)⁻¹ * k i) := by
      intro h
      simp only [Pi.mul_apply, Pi.inv_apply, Finset.prod_mul_distrib]
    simp only [h1]
    rw [integral_fintype_prod_eq_prod (fun i h => e i h * e i (h⁻¹ * k i))]
    exact Finset.prod_congr rfl fun i _ => (hE i).idem.idem (k i)
  · intro Φ hΦ hR g
    constructor
    · refine fix_prod μK (fun m => bd m 1) hb1 (fun i => T (n i) (q i)) (fun i => continuous_alt _ _)
        (fun y => Φ (y * x)) (hΦ.comp (continuous_id.mul continuous_const)) ?_ g
      intro i g
      beta_reduce
      simp only [hsl Φ i g]
      rw [hsl0 Φ i g]
      exact ((hE i).fix _ (hcontS Φ hΦ i _) (fix_slice μ e hidem Φ hΦ hR i _) (g i)).1
    · refine fix_prod μK (fun m => bd 1 m) hb2 (fun i => T (n' i) (q' i)) (fun i => continuous_alt _ _)
        (fun y => Φ (y * x)) (hΦ.comp (continuous_id.mul continuous_const)) ?_ g
      intro i g
      beta_reduce
      simp only [hsl Φ i g]
      rw [hsl0 Φ i g]
      exact ((hE i).fix _ (hcontS Φ hΦ i _) (fix_slice μ e hidem Φ hΦ hR i _) (g i)).2
  · intro Φ hΦ hR hL hL' h0
    have key : ∀ s : Finset ι, ∀ k : ι → U4, (∀ i, i ∉ s → ∃ a b, k i = bd a b * x i) → Φ k = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro k hk
        choose a b hab using fun i => hk i (Finset.notMem_empty i)
        have : k = (fun i => bd (a i) (b i)) * x := funext hab
        rw [this]
        exact h0 a b
      | insert c s hc ih =>
        intro k hk
        have hz := (hE c).inj (fun y => Φ (Function.update k c y)) (hcontS Φ hΦ c k)
          (fix_slice μ e hidem Φ hΦ hR c k) (aboveSlice c k (hL c)) (aboveSlice c k (hL' c)) ?_
        · have := congrFun hz (k c)
          simpa using this
        · intro a b
          refine ih _ fun i hi => ?_
          by_cases hic : i = c
          · subst hic
            exact ⟨a, b, Function.update_self ..⟩
          · rw [Function.update_of_ne hic]
            exact hk i (by simp [hic, hi])
    funext k
    exact key Finset.univ k fun i hi => absurd (Finset.mem_univ i) hi
  · choose ψ hc hfix hval using fun i => (hE i).ex
    refine ⟨fun k => ∏ i, ψ i (k i), continuous_finset_prod _ fun i _ => (hc i).comp (continuous_apply i), ?_, ?_⟩
    · intro g
      have h1 : ∀ k : ι → U4, (∏ i, e i (k i)) * ∏ i, ψ i ((g * k) i) = ∏ i, e i (k i) * ψ i (g i * k i) := by
        intro k
        simp only [Pi.mul_apply, Finset.prod_mul_distrib]
      simp only [h1]
      rw [integral_fintype_prod_eq_prod (fun i h => e i h * ψ i (g i * h))]
      exact Finset.prod_congr rfl fun i _ => hfix i (g i)
    · intro a b
      simp only [Pi.mul_apply, hval, map_prod, Finset.prod_mul_distrib]
