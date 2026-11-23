import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingOfNormSqEqSumComplexCoords

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.CovPi

open GlobalTheory.HomCovolume

theorem hasCov_pi {β : Type} [Fintype β] {V : β → Type} [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [∀ b, FiniteDimensional ℝ (V b)] [∀ b, MeasurableSpace (V b)]
    [∀ b, BorelSpace (V b)] {μ : ∀ b, Measure (V b)} [∀ b, (μ b).IsAddHaarMeasure]
    {L : ∀ b, Submodule ℤ (V b)} {c : β → ℝ} (h : ∀ i, HasCov (μ i) (L i) (c i)) :
    HasCov (Measure.pi μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  classical
  have hd : ∀ i, DiscreteTopology (L i) := fun i => (h i).1
  have hz : ∀ i, IsZLattice ℝ (L i) := fun i => (h i).2.1
  have hc : ∀ i, ZLattice.covolume (L i) (μ i) = c i := fun i => (h i).2.2
  let B : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℝ (V i) := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis ℝ
  have hBmem : ∀ i j, B i j ∈ L i := fun i j => by
    simp only [B, Module.Basis.ofZLatticeBasis_apply]
    exact (Module.Free.chooseBasis ℤ (L i) j).2
  have hBspan : ∀ i, Submodule.span ℤ (Set.range (B i)) = L i := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis_span ℝ
  have hspan : Submodule.pi Set.univ L = Submodule.span ℤ (Set.range (Pi.basis B)) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_pi] at hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hxi : x i ∈ Submodule.span ℤ (Set.range (B i)) := by
        rw [hBspan]; exact hx i (Set.mem_univ i)
      refine Submodule.span_induction
        (p := fun y _ => Pi.single i y ∈ Submodule.span ℤ (Set.range (Pi.basis B))) ?_ ?_ ?_ ?_ hxi
      · rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨⟨i, j⟩, by simp⟩
      · simp
      · intro y z _ _ hy hz
        rw [Pi.single_add]; exact add_mem hy hz
      · intro a y _ hy
        rw [Pi.single_smul]; exact Submodule.smul_mem _ a hy
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_pi]
      intro i' _
      rw [Pi.basis_apply]
      by_cases hi : i' = i
      · subst hi; simpa using hBmem i' j
      · simp [hi]
  rw [hspan]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (Pi.basis B) _)]
  have hfd : ZSpan.fundamentalDomain (Pi.basis B) = Set.univ.pi fun i => ZSpan.fundamentalDomain (B i) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall]
  rw [hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hc i, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (L i)) (μ i)), measureReal_def]

theorem measurePreserving_of_sum_sq {κ σ : Type} [Fintype κ] [Fintype σ]
    (e : (κ → ℂ) ≃L[ℝ] (σ → ℂ)) (he : ∀ z, ∑ j, ‖e z j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    MeasurePreserving e volume volume := by
  let T : EuclideanSpace ℂ κ ≃L[ℝ] (κ → ℂ) := ((EuclideanSpace.equiv κ ℂ).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hnorm : ∀ v : EuclideanSpace ℂ κ, ‖v‖ ^ 2 = ∑ i, ‖T v i‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hT : MeasurePreserving T volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ κ T hnorm
  have hTe : MeasurePreserving (T.trans e) volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ σ (T.trans e) fun v => by
      rw [hnorm v, ContinuousLinearEquiv.trans_apply, he]
  have hTs := MeasurePreserving.symm T.toHomeomorph.toMeasurableEquiv hT
  have hfun : (⇑e) = (T.trans e) ∘ T.toHomeomorph.toMeasurableEquiv.symm := by
    funext z
    simp
  rw [hfun]
  exact hTe.comp hTs

private theorem measurePreserving_piCurry_complex {I : Type} [Fintype I] {K : I → Type} [∀ i, Fintype (K i)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
  symm
  show Measure.pi (fun i : I => Measure.pi fun _ : K i => (volume : Measure ℂ)) = _
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ fun _ : K i => {s : Set ℂ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℂ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  obtain rfl : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) ⁻¹'
      Set.univ.pi (fun i => Set.univ.pi (t i)) = Set.univ.pi fun p : (Σ i, K i) => t p.1 p.2 := by
    ext f
    simp [MeasurableEquiv.coe_piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  simp only [Measure.pi_pi]

attribute [local instance] haar_two haar_three

theorem covolume_pi_unitary : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  intro ι κ β _ _ _ r s Φ hΦ M hM L hL
  classical
  let Ψ : (ι → κ → ℂ) ≃ₗ[ℂ] (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun z b v => Φ v (z v) b
      invFun := fun w v => (Φ v).symm fun b => w b v
      map_add' := fun x y => by funext b v; simp
      map_smul' := fun c x => by funext b v; simp
      left_inv := fun z => by funext v; simp
      right_inv := fun w => by funext b v; simp }
  let F : ((Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)) → ℂ) ≃ₗ[ℂ]
      (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun w b v p q => w ⟨b, v, p, q⟩
      invFun := fun u x => u x.1 x.2.1 x.2.2.1 x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := LinearEquiv.piCurry ℂ fun (_ : ι) (_ : κ) => ℂ
  let E := G.trans (Ψ.trans F.symm)
  have hE : MeasurePreserving (E.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    apply measurePreserving_of_sum_sq
    intro z
    have hz : ∀ j : (Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)),
        (E.restrictScalars ℝ).toContinuousLinearEquiv z j =
          Φ j.2.1 (fun k => z ⟨j.2.1, k⟩) j.1 j.2.2.1 j.2.2.2 := fun j => rfl
    simp only [hz, Fintype.sum_sigma]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => hΦ v _
  have hG : MeasurePreserving (MeasurableEquiv.piCurry fun (_ : ι) (_ : κ) => ℂ) volume volume :=
    measurePreserving_piCurry_complex
  have hF : MeasurePreserving F volume volume := by
    have h := (volume_preserving_pi fun b => volume_preserving_pi fun (_ : ι) =>
        measurePreserving_piCurry_complex (I := Fin (r b)) (K := fun _ => Fin (s b))).comp
      ((volume_preserving_pi fun b =>
        measurePreserving_piCurry_complex (I := ι) (K := fun _ => Σ _ : Fin (r b), Fin (s b))).comp
        (measurePreserving_piCurry_complex (I := β) (K := fun b => Σ _ : ι, Σ _ : Fin (r b), Fin (s b))))
    exact h
  have hΨ : MeasurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    have h := hF.comp (hE.comp (MeasurePreserving.symm _ hG))
    convert h using 1
    funext z
    rfl
  have := haar_two ι κ
  have hB3 : ∀ b, (volume : Measure (ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure :=
    fun b => haar_three ι _ _
  have : (volume : Measure (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure := by
    rw [← hΨ.map_eq]; infer_instance
  show HasCov volume L _
  refine HasCov.of_measurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv hΨ
    (L' := Submodule.pi Set.univ M) ?_ ?_
  · intro z
    rw [hL, Submodule.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact Iff.rfl
  · exact hasCov_pi (μ := fun _ => volume) fun b => by
      obtain ⟨hd, hz⟩ := hM b
      exact ⟨hd, hz, rfl⟩

end GlobalTheory.CovPi
