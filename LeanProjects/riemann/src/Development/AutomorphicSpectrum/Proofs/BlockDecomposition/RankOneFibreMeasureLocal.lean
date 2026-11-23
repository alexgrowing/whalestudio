import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos

section Alg

variable {A : Type} [CommRing A] (s : A →+* A) {ι : Type} [Fintype ι] (J : Matrix ι ι A)

theorem hf_add_right (x y z : ι → A) : hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_add_left (x y z : ι → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hf_smul_right (a : A) (x y : ι → A) : hform s J x (a • y) = a * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_smul_left (a : A) (x y : ι → A) : hform s J (a • x) y = s a * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : ι → A) : hform s J x 0 = 0 := by
  simp [hform]

theorem hf_swap (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : ι → A) :
    s (hform s J x y) = hform s J y x := by
  simp only [hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_shift (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (u x : ι → A) (c : A)
    (hxx : hform s J x x = 0) :
    hform s J (u + c • x) (u + c • x) =
      hform s J u u + c * s (hform s J x u) + s c * hform s J x u := by
  rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
    hf_smul_right, hxx, hf_swap s J hs hJ x u]
  ring

end Alg

section Shift

variable {K : Type} [CommRing K] (s : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
  (x : Fin M → K)

def bet (Y : Fin 1 → Fin M → K) : K := hform s J x (Y 0)

def jx : K →+ (Fin 1 → Fin M → K) where
  toFun a := fun _ => a • x
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_mul]

def cS (h r : K) (Y : Fin 1 → Fin M → K) : K := h * r * Ring.inverse (s (bet s J x Y))

def Tm (h r : K) (Y : Fin 1 → Fin M → K) : Fin 1 → Fin M → K := Y + jx x (cS s J x h r Y)

variable {s J x}

theorem bet_add_jx (hxx : hform s J x x = 0) (Y : Fin 1 → Fin M → K) (a : K) :
    bet s J x (Y + jx x a) = bet s J x Y := by
  show hform s J x (Y 0 + a • x) = hform s J x (Y 0)
  rw [hf_add_right, hf_smul_right, hxx, mul_zero, add_zero]

theorem cS_add_jx (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) (a : K) :
    cS s J x h r (Y + jx x a) = cS s J x h r Y := by
  simp only [cS, bet_add_jx hxx]

theorem bet_Tm (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) :
    bet s J x (Tm s J x h r Y) = bet s J x Y :=
  bet_add_jx hxx _ _

theorem Tm_neg (hxx : hform s J x x = 0) (h r : K) (Y : Fin 1 → Fin M → K) :
    Tm s J x h (-r) (Tm s J x h r Y) = Y := by
  have h1 : cS s J x h (-r) (Tm s J x h r Y) = -cS s J x h r Y := by
    simp only [cS, bet_Tm hxx]
    ring
  rw [Tm, h1, Tm, map_neg, add_neg_cancel_right]

theorem hf_Tm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hxx : hform s J x x = 0) {h r : K} (h2 : h + h = 1) (hh : s h = h) (hr : s r = r)
    {Y : Fin 1 → Fin M → K} (hY : IsUnit (bet s J x Y)) :
    hform s J (Tm s J x h r Y 0) (Tm s J x h r Y 0) = hform s J (Y 0) (Y 0) + r := by
  have hT : Tm s J x h r Y 0 = Y 0 + cS s J x h r Y • x := rfl
  have hsb : IsUnit (s (bet s J x Y)) := hY.map s
  have e1 : Ring.inverse (s (bet s J x Y)) * s (bet s J x Y) = 1 :=
    Ring.inverse_mul_cancel _ hsb
  have e2 : s (Ring.inverse (s (bet s J x Y))) * bet s J x Y = 1 := by
    have := congrArg s e1
    rwa [map_mul, hs, map_one] at this
  have hb : hform s J x (Y 0) = bet s J x Y := rfl
  rw [hT, hf_shift s J hs hJ _ _ _ hxx, hb]
  simp only [cS, map_mul, hh, hr]
  linear_combination (h * r) * e1 + (h * r) * e2 + r * h2

theorem linIndep_of_isUnit {Y : Fin 1 → Fin M → K} (hY : IsUnit (bet s J x Y)) :
    LinearIndependent K Y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : c 0 • Y 0 = 0 := by simpa using hc
  have h1 : c 0 * bet s J x Y = 0 := by
    have := congrArg (hform s J x) h0
    rwa [hf_smul_right, hf_zero_right] at this
  rw [Subsingleton.elim i 0]
  exact hY.mul_left_eq_zero.1 h1

end Shift

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_bet (s : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    Continuous (bet s J x) := by
  unfold bet hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply 0))

theorem continuous_jx {M : ℕ} (x : Fin M → K) : Continuous (jx x) := by
  refine continuous_pi fun _ => continuous_pi fun i => ?_
  exact continuous_id.mul continuous_const

theorem isOpen_isUnit (hU : IsOpenEmbedding (Units.val : Kˣ → K)) : IsOpen {r : K | IsUnit r} := by
  have := hU.isOpen_range
  convert this using 1
  ext r
  simp [IsUnit]

theorem continuousOn_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    ContinuousOn (Tm s J x h r) {Y | IsUnit (bet s J x Y)} := by
  have h1 : ContinuousOn (fun Y => Ring.inverse (s (bet s J x Y))) {Y | IsUnit (bet s J x Y)} :=
    (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hU).comp
      (hsc.comp (continuous_bet s J x)).continuousOn (fun Y hY => IsUnit.map s hY)
  have h2 : ContinuousOn (cS s J x h r) {Y | IsUnit (bet s J x Y)} :=
    continuousOn_const.mul h1
  exact continuousOn_id.add ((continuous_jx x).comp_continuousOn h2)

variable [MeasurableSpace K] [BorelSpace K]

theorem measurable_ringInverse (hU : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Measurable (Ring.inverse : K → K) := by
  classical
  have h1 : Measurable (({r : K | IsUnit r}).piecewise (Ring.inverse : K → K) (fun _ => 0)) :=
    (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hU).measurable_piecewise continuousOn_const
      (isOpen_isUnit hU).measurableSet
  convert h1 using 1
  funext r
  by_cases hr : IsUnit r
  · simp [Set.piecewise, hr]
  · simp [Set.piecewise, hr, Ring.inverse_non_unit]

end Top

theorem map_shift_eq {V A : Type} [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V) (hj : Measurable j) (f : V → A) (hf : Measurable f)
    (hinv : ∀ v a, f (v + j a) = f v) (C : Set A) (hC : MeasurableSet C) (h0 : lam C ≠ 0)
    (h1 : lam C ≠ ⊤) : μ.map (fun v => v + j (f v)) = μ := by
  have hT : Measurable fun v => v + j (f v) := measurable_id.add (hj.comp hf)
  ext B hB
  rw [Measure.map_apply hT hB]
  have key := GlobalTheory.T.quotient_measure_by_invariant_subgroup V A μ lam j hj f hf hinv C hC h0 h1 (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at key
  rw [← key, ← lintegral_indicator_one (hT hB)]
  refine lintegral_congr fun v => ?_
  by_cases hv : v + j (f v) ∈ B
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show v ∈ (fun v => v + j (f v)) ⁻¹' B from hv)]
    rfl
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (show v ∉ (fun v => v + j (f v)) ⁻¹' B from hv)]

section Meas

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem measurable_cS (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    Measurable (cS s J x h r) :=
  ((measurable_ringInverse hU).comp (hsc.comp (continuous_bet s J x)).measurable).const_mul _

theorem measurable_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K) (h r : K) :
    Measurable (Tm s J x h r) :=
  measurable_id.add ((continuous_jx x).measurable.comp (measurable_cS hU hsc J x h r))

theorem map_Tm (hU : IsOpenEmbedding (Units.val : Kˣ → K)) {s : K →+* K}
    (hsc : Continuous s) {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (hxx : hform s J x x = 0) (h r : K) (μ : Measure (Fin 1 → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (Tm s J x h r) = μ := by
  obtain ⟨C, hCc, hC0⟩ := exists_compact_mem_nhds (0 : K)
  let lam : Measure K := Measure.addHaar
  exact map_shift_eq μ lam (jx x) (continuous_jx x).measurable (cS s J x h r)
    (measurable_cS hU hsc J x h r) (fun Y a => cS_add_jx hxx h r Y a) C hCc.measurableSet
    (Measure.measure_pos_of_mem_nhds lam hC0).ne' hCc.measure_lt_top.ne

end Meas

theorem fibre_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J 1 μ ν m → ∀ X : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ J X = 0 → ∀ S : HermR R σ 1, m S ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL μ ν m hμ hν hm X hX hX0 S
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, tsc, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin 1 → Fin M → R ⊗[F] E) := tK8 1 M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R 1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hL
  have hss : ∀ a, sigR R σ (sigR R σ a) = a := HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hJJ : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    simp only [JR, Matrix.map_apply, HermTop.sigR_inclR, hJ.1]
  obtain ⟨hf, hf2, hfs⟩ : ∃ hf : R ⊗[F] E, hf + hf = 1 ∧ sigR R σ hf = hf := by
    refine ⟨inclR R (algebraMap F E (1 / 2)), ?_, ?_⟩
    · rw [← map_add, ← map_add]
      norm_num
    · rw [HermTop.sigR_inclR, σ.commutes]
  have hxx : hform (sigR R σ) (JR R J) (X 0) (X 0) = 0 := congrFun (congrFun hX0 0) 0
  have hXeq : (fun _ : Fin 1 => X 0) = X := by
    funext a
    rw [Subsingleton.elim a 0]
  obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (X 0) (by rw [hXeq]; exact hX)
  have hgen := GlobalTheory.T.disintegration_haar_base (Fin 1 → Fin M → R ⊗[F] E) (HermR R σ 1)
    (Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hg
    {Y | LinearIndependent (R ⊗[F] E) Y} {Y | IsUnit (bet (sigR R σ) (JR R J) (X 0) Y)}
    ((isOpen_isUnit hU).preimage (continuous_bet _ _ _))
    (fun Y hY => linIndep_of_isUnit hY)
    ⟨fun _ => y, by
      show IsUnit (hR R σ J (X 0) y)
      rw [hy]
      exact isUnit_one⟩
    m hm (fun S Y => Tm (sigR R σ) (JR R J) (X 0) hf ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) Y)
    (fun S => measurable_Tm hU tsc _ _ _ _)
    (fun S => map_Tm hU tsc _ _ hxx _ _ μ)
    (fun S => continuousOn_Tm hU tsc _ _ _ _)
    (fun S Y => by
      show IsUnit (bet _ _ _ _) ↔ IsUnit (bet _ _ _ _)
      rw [bet_Tm hxx])
    (fun S Y _ => Tm_neg hxx _ _ Y)
    (fun S Y hY => by
      apply Subtype.ext
      rw [← hg, AddSubgroup.coe_add, ← hg]
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      exact hf_Tm hss hJJ hxx hf2 hfs (S.2 0 0) hY)
  exact hgen S

end GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos
