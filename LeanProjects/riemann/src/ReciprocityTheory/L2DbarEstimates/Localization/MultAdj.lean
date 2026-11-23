import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.Localization.IntegrableOnCompactOfLocL2

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem multAdj (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultAdjStatement n M := by
  intro z hz ph₁ ph₂ η f w h1s h2s hηs hf hw hW g hg
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hgs : ReciprocityTheory.L2DbarEstimates.Smooth n z g := hg.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * g y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hgs
  have hψ : IsTest n z (fun y => (η y : ℂ) * g y) := ⟨hψs, hg.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hc1 : Continuous ph₁ := multA_contR z hz ph₁ h1s
  have hc2 : Continuous ph₂ := multA_contR z hz ph₂ h2s
  have hcη : Continuous η := multA_contR z hz η hηs
  have hcg : Continuous g := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz g hgs
  have hgc : HasCompactSupport (fun x => conj (g x)) := hg.2.comp_left (map_zero _)
  have hin : ∀ (h : M → ℂ) (x : M) (v : V n),
      ⟪dbarF n z h x, v⟫_ℂ = ∑ j, conj (db n z j h x) * v j := by
    intro h x v
    simp [dbarF, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hdbψ : ∀ j x, db n z j (fun y => (η y : ℂ) * g y) x =
      db n z j (fun y => (η y : ℂ)) x * g x + (η x : ℂ) * db n z j g x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.db_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hgs) j x
  have hconj : ∀ j x, conj (db n z j (fun y => (η y : ℂ)) x) = d n z j (fun y => (η y : ℂ)) x :=
    fun j x => by rw [ReciprocityTheory.L2DbarEstimates.db_ofReal, Complex.conj_conj]
  have hcomp : ∀ (v : V n) (j : Fin n), ‖v j‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v j => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hE1 : Continuous (fun x => (Real.exp (-ph₁ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc1.neg)
  have hE2 : Continuous (fun x => (Real.exp (-ph₂ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc2.neg)
  have hfj : ∀ j, AEStronglyMeasurable (fun x => f x j) (vol n z) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hf.1
  have hfb : ∀ j, ∫⁻ x, ENNReal.ofReal (‖f x j‖ ^ 2 * Real.exp (-ph₂ x)) ∂vol n z < ⊤ :=
    fun j => lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hcomp (f x) j) (Real.exp_pos _).le)) hf.2
  have hfE : ∀ j K, IsCompact K →
      IntegrableOn (fun x => f x j * (Real.exp (-ph₂ x) : ℂ)) K (vol n z) := fun j K hK =>
    (multA_intOn_w _ _ ph₂ hc2 (hfj j) (hfb j) K hK).mul_continuousOn hE2.continuousOn hK
  have hwE : ∀ K, IsCompact K →
      IntegrableOn (fun x => w x * (Real.exp (-ph₁ x) : ℂ)) K (vol n z) := fun K hK =>
    (multA_intOn_w _ w ph₁ hc1 hw.1 hw.2 K hK).mul_continuousOn hE1.continuousOn hK
  have hP : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      conj (db n z j (fun y => (η y : ℂ) * g y) x)) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      (Complex.continuous_conj.comp (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _
        (ReciprocityTheory.L2DbarEstimates.Smooth.db n z j _ hψs)))
      ((hψ.2.mono' ((subset_tsupport _).trans
        (ReciprocityTheory.L2DbarEstimates.tsupport_db_subset n z j _))).comp_left (map_zero _))
  have hR : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      (d n z j (fun y => (η y : ℂ)) x * conj (g x))) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul
        (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hQ : Integrable (fun x => w x * (Real.exp (-ph₁ x) : ℂ) *
      ((η x : ℂ) * conj (g x))) (vol n z) :=
    multA_int_mul _ _ _ hwE ((Complex.continuous_ofReal.comp hcη).mul
      (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hE : ∀ x, (Real.exp (ph₁ x - ph₂ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) =
      (Real.exp (-ph₂ x) : ℂ) := fun x => by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have eA : ∀ x, ⟪dbarF n z g x, (η x : ℂ) • f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      (∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [hin, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdbψ, map_add, map_mul, map_mul, hconj, Complex.conj_ofReal]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eB : ∀ x, conj (g x) * ((η x : ℂ) * w x - (Real.exp (ph₁ x - ph₂ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [← hE x, mul_sub, sub_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  have eP : ∀ x, ⟪dbarF n z (fun y => (η y : ℂ) * g y) x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x) := by
    intro x
    rw [hin, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have eQ : ∀ x, conj ((η x : ℂ) * g x) * w x * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [funext eP, funext eQ] at h1
  rw [funext eA, funext eB, integral_sub hP hR, integral_sub hQ hR, h1]

theorem multS (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultSStatement n M := by
  intro z hz η f σ hηs hf hσ hW φ hφ j k
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hφs : ReciprocityTheory.L2DbarEstimates.Smooth n z φ := hφ.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * φ y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hφs
  have hψ : IsTest n z (fun y => (η y : ℂ) * φ y) := ⟨hψs, hφ.2.mul_left⟩
  have h1 := hW _ hψ j k
  beta_reduce at h1
  have hcφ : Continuous φ := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz φ hφs
  have hdbψ : ∀ i x, db n z i (fun y => (η y : ℂ) * φ y) x =
      db n z i (fun y => (η y : ℂ)) x * φ x + (η x : ℂ) * db n z i φ x := fun i x =>
    ReciprocityTheory.L2DbarEstimates.db_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hφs) i x
  have hint : ∀ (a : Fin n) (c : M → ℂ), Continuous c → HasCompactSupport c →
      Integrable (fun x => f x a * c x) (vol n z) := fun a c hc hcs =>
    multA_int_mul _ _ c (fun K hK => integrableOn_compact_of_locL2 _ _ (locL2_form_component _ f hf a) K hK) hc hcs
  have hcψ : ∀ i, Continuous (db n z i (fun y => (η y : ℂ) * φ y)) := fun i =>
    ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.db n z i _ hψs)
  have hsψ : ∀ i, HasCompactSupport (db n z i (fun y => (η y : ℂ) * φ y)) := fun i =>
    hψ.2.mono' ((subset_tsupport _).trans (ReciprocityTheory.L2DbarEstimates.tsupport_db_subset n z i _))
  have hcη : ∀ i, Continuous (fun x => db n z i (fun y => (η y : ℂ)) x * φ x) := fun i =>
    (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.db n z i _ he)).mul hcφ
  have hH : Integrable (fun x => f x k * db n z j (fun y => (η y : ℂ) * φ y) x -
      f x j * db n z k (fun y => (η y : ℂ) * φ y) x) (vol n z) :=
    (hint k _ (hcψ j) (hsψ j)).sub (hint j _ (hcψ k) (hsψ k))
  have hW' : Integrable (fun x => f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
      f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) (vol n z) :=
    (hint k _ (hcη j) hφ.2.mul_left).sub (hint j _ (hcη k) hφ.2.mul_left)
  have hS : Integrable (fun x => σ x j k * ((η x : ℂ) * φ x)) (vol n z) :=
    multA_int_mul _ _ _ (fun K hK => integrableOn_compact_of_locL2 _ _ (locL2_two_form_component _ σ hσ j k) K hK)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ hψs) hψ.2
  have eL : ∀ x, ((η x : ℂ) • f x) k * db n z j φ x - ((η x : ℂ) • f x) j * db n z k φ x =
      (f x k * db n z j (fun y => (η y : ℂ) * φ y) x -
        f x j * db n z k (fun y => (η y : ℂ) * φ y) x) -
      (f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
        f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) := by
    intro x
    rw [hdbψ, hdbψ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eR : ∀ x, ((η x : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k) * φ x =
      σ x j k * ((η x : ℂ) * φ x) +
      (f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
        f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) := by
    intro x
    simp only [wedge]
    ring
  rw [funext eL, funext eR, integral_sub hH hW', integral_add hS hW', h1]
  ring

theorem multDiv (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultDivStatement n M := by
  intro z hz η G D hηs hG hD hW φ hφ
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hφs : ReciprocityTheory.L2DbarEstimates.Smooth n z φ := hφ.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * φ y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hφs
  have hψ : IsTest n z (fun y => (η y : ℂ) * φ y) := ⟨hψs, hφ.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hcφ : Continuous φ := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz φ hφs
  have hdψ : ∀ j x, d n z j (fun y => (η y : ℂ) * φ y) x =
      d n z j (fun y => (η y : ℂ)) x * φ x + (η x : ℂ) * d n z j φ x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.d_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hφs) j x
  have hGj : ∀ j K, IsCompact K → IntegrableOn (fun x => G x j) K (vol n z) := fun j K hK =>
    integrableOn_compact_of_locL2 _ _ (locL2_form_component _ G hG j) K hK
  have hI1 : Integrable (fun x => ∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ hψs))
      (hψ.2.mono' ((subset_tsupport _).trans (ReciprocityTheory.L2DbarEstimates.tsupport_d_subset n z j _)))
  have hI2 : Integrable (fun x => ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x))
      (vol n z) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul hcφ)
      hφ.2.mul_left
  have hI3 : Integrable (fun x => D x * ((η x : ℂ) * φ x)) (vol n z) :=
    multA_int_mul _ _ _ (fun K hK => integrableOn_compact_of_locL2 _ _ hD K hK)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ hψs) hψ.2
  have hL : ∀ x, ∑ j, ((η x : ℂ) • G x) j * d n z j φ x =
      (∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) -
      ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdψ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hR : ∀ x, ((η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) * φ x =
      D x * ((η x : ℂ) * φ x) + ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [funext hL, funext hR, integral_sub hI1 hI2, integral_add hI3 hI2, h1]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
