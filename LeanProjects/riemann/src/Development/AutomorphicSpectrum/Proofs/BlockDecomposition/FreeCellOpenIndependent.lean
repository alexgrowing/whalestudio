import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell

section Alg

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_yPart (X : Fin (n + 1) → Fin (M + 2) → K) (g : Fin n → K) (i : Fin M) :
    ∑ j, g j * yPart X j i = ∑ j, g j * X j.succ i.succ.succ -
      (∑ j, g j * X j.succ 0) * (Ring.inverse (X 0 0) * X 0 i.succ.succ) := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [yPart]; ring

theorem linearIndependent_of_yPart (X : Fin (n + 1) → Fin (M + 2) → K)
    (hu : IsUnit (X 0 0)) (hy : LinearIndependent K (yPart X)) : LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff] at hy ⊢
  intro g hg
  have hc : ∀ i, g 0 * X 0 i + ∑ j : Fin n, g j.succ * X j.succ i = 0 := fun i => by
    have := congrFun hg i
    simpa [Fin.sum_univ_succ, Finset.sum_apply] using this
  have hinv : X 0 0 * Ring.inverse (X 0 0) = 1 := Ring.mul_inverse_cancel _ hu
  have h1 : ∀ j : Fin n, g j.succ = 0 := by
    apply hy (fun j => g j.succ)
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [sum_yPart]
    have a1 : ∑ j : Fin n, g j.succ * X j.succ 0 = -(g 0 * X 0 0) :=
      eq_neg_of_add_eq_zero_right (hc 0)
    have a2 : ∑ j : Fin n, g j.succ * X j.succ i.succ.succ = -(g 0 * X 0 i.succ.succ) :=
      eq_neg_of_add_eq_zero_right (hc i.succ.succ)
    rw [a1, a2]
    linear_combination (g 0 * X 0 i.succ.succ) * hinv
  have h0 : g 0 = 0 := by
    have := hc 0
    simp only [h1, zero_mul, Finset.sum_const_zero, add_zero] at this
    calc g 0 = g 0 * X 0 0 * Ring.inverse (X 0 0) := by rw [mul_assoc, hinv, mul_one]
      _ = 0 := by rw [this, zero_mul]
  intro i
  exact Fin.cases h0 h1 i

end Alg

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hR R σ J x y
  map_add' y z := by
    simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin (M + 2) → R ⊗[F] E) :
    hR R σ (hypOne J) x y = sigR R σ (x 0) * y 1 + sigR R σ (x 1) * y 0 +
      hR R σ J (tailH x) (tailH y) := by
  simp only [hR, hform, JR, Matrix.map_apply, Fin.sum_univ_succ, Fin.succ_zero_eq_one, tailH,
    hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest,
    hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, map_zero, map_one, mul_zero, zero_mul, mul_one,
    Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem yPart_linearIndependent (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X)
    (hg : gramR R σ (hypOne J) X = 0) (hu : IsUnit (X 0 0)) :
    LinearIndependent (R ⊗[F] E) (yPart X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hrel
  have hinv : X 0 0 * Ring.inverse (X 0 0) = 1 := Ring.mul_inverse_cancel _ hu
  set c : R ⊗[F] E := (∑ j, g j * X j.succ 0) * Ring.inverse (X 0 0) with hc
  set w : Fin (M + 2) → R ⊗[F] E := (∑ j, g j • X j.succ) - c • X 0 with hw
  have hwi : ∀ i, w i = ∑ j, g j * X j.succ i - c * X 0 i := fun i => by
    simp [hw, Finset.sum_apply]
  have hw0 : w 0 = 0 := by
    rw [hwi, hc]
    linear_combination (-(∑ j, g j * X j.succ 0)) * hinv
  have hwr : ∀ k : Fin M, w k.succ.succ = 0 := fun k => by
    have := congrFun hrel k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [sum_yPart] at this
    rw [hwi, hc, ← this]
    ring
  have htail : tailH w = 0 := funext hwr
  have hx0 : ∀ y, hR R σ (hypOne J) (X 0) y = hLin R σ (hypOne J) (X 0) y := fun _ => rfl
  have hzero : hR R σ (hypOne J) (X 0) w = 0 := by
    rw [hx0, hw, map_sub, map_sum, map_smul]
    have h1 : ∀ j : Fin n, hLin R σ (hypOne J) (X 0) (g j • X j.succ) = 0 := fun j => by
      rw [map_smul, ← hx0]
      have := congrFun (congrFun hg 0) j.succ
      simp only [gramR, Matrix.zero_apply] at this
      rw [this, smul_zero]
    have h2 : hLin R σ (hypOne J) (X 0) (X 0) = 0 := by
      rw [← hx0]
      simpa only [gramR, Matrix.zero_apply] using congrFun (congrFun hg 0) 0
    rw [h2, smul_zero, sub_zero]
    exact Finset.sum_eq_zero fun j _ => h1 j
  have hw1 : w 1 = 0 := by
    have hz : hR R σ J (tailH (X 0)) (tailH w) = 0 := by
      rw [htail]
      simp [hR, hform]
    rw [hR_hypOne, hw0, hz, mul_zero, add_zero, add_zero] at hzero
    have hsu : IsUnit (sigR R σ (X 0 0)) := hu.map (sigR R σ)
    exact (hsu.mul_right_eq_zero).1 hzero
  have hall : w = 0 := by
    funext i
    refine Fin.cases hw0 (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · simpa using hw1
    · exact hwr k
  have hfin := hX (Fin.cons (-c) g) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [neg_smul, neg_add_eq_sub]
    exact hall)
  intro j
  simpa using hfin j.succ

theorem yPart_chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E)
    (Y : Fin n → Fin M → R ⊗[F] E) (hu : IsUnit (x 0 0)) :
    yPart (chartS R σ J x a s Y) = Y := by
  funext j i
  have hinv : x 0 0 * Ring.inverse (x 0 0) = 1 := Ring.mul_inverse_cancel _ hu
  simp only [yPart, chartS, Fin.cons_zero, Fin.cons_succ, cvec, vH, Fin.cons_succ, Fin.cons_zero]
  linear_combination (-(a 0 j * x 0 i.succ.succ)) * hinv

end Form

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] {α : Type} [MeasurableSpace α]
  [MeasurableMul₂ (R ⊗[F] E)] [MeasurableAdd₂ (R ⊗[F] E)] [MeasurableSub₂ (R ⊗[F] E)]

theorem measurable_vH {M : ℕ} {a s : α → R ⊗[F] E} {Y : α → Fin M → R ⊗[F] E}
    (ha : Measurable a) (hs : Measurable s) (hY : Measurable Y) :
    Measurable fun p => (vH (a p) (s p) (Y p) : Fin (M + 2) → R ⊗[F] E) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simpa [vH] using ha
  · simpa [vH] using hs
  · simpa [vH, Function.comp_def] using (measurable_pi_apply k).comp hY

theorem measurable_tailH {M : ℕ} {x : α → Fin (M + 2) → R ⊗[F] E} (hx : Measurable x) :
    Measurable fun p => tailH (x p) :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply i.succ.succ).comp hx

theorem measurable_hR (σ : E →ₐ[F] E) (hsig : Measurable (sigR R σ)) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {x y : α → Fin M → R ⊗[F] E} (hx : Measurable x) (hy : Measurable y) :
    Measurable fun p => hR R σ J (x p) (y p) := by
  simp only [hR, hform]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((hsig.comp ((measurable_pi_apply i).comp hx)).mul_const _).mul ((measurable_pi_apply j).comp hy)

theorem measurable_tHalf (σ : E →ₐ[F] E) (hsig : Measurable (sigR R σ)) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {x : α → Fin (M + 2) → R ⊗[F] E} (hx : Measurable x) :
    Measurable fun p => tHalf R σ J (x p) :=
  (measurable_hR R σ hsig (hypOne J) hx hx).const_mul _

theorem measurable_cvec (σ : E →ₐ[F] E) (hsig : Measurable (sigR R σ))
    (hinv : Measurable (Ring.inverse : R ⊗[F] E → R ⊗[F] E)) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {x v : α → Fin (M + 2) → R ⊗[F] E} (hx : Measurable x) (hv : Measurable v) :
    Measurable fun p => cvec R σ J (x p) (v p) := by
  have c : ∀ i : Fin (M + 2), Measurable fun p => x p i := fun i => (measurable_pi_apply i).comp hx
  have d : ∀ i : Fin (M + 2), Measurable fun p => v p i := fun i => (measurable_pi_apply i).comp hv
  refine measurable_vH R ((c 0).mul (d 0)) (((d 0).mul (c 1)).add
    ((hinv.comp (hsig.comp (c 0))).mul (((d 1).sub ((measurable_tHalf R σ hsig J hx).mul (d 0))).sub
      (measurable_hR R σ hsig J (measurable_tailH R hx) (measurable_tailH R hv))))) ?_
  exact measurable_pi_lambda _ fun i => ((d 0).mul (c i.succ.succ)).add (d i.succ.succ)

theorem measurable_chartS (σ : E →ₐ[F] E) (hsig : Measurable (sigR R σ))
    (hinv : Measurable (Ring.inverse : R ⊗[F] E → R ⊗[F] E)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Measurable (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hx : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [chartS] using hx
  · simp only [chartS, Fin.cons_succ]
    have ha : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.1 0 j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd))
    have hs : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.1 0 j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply 0).comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    have hY : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.2 j :=
      (measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact measurable_cvec R σ hsig hinv J hx
      (measurable_vH R ha (hs.sub ((measurable_tHalf R σ hsig J hx).mul ha)) hY)

end Meas

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem measurable_ringInverse [MeasurableSpace K] [BorelSpace K] (h : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Measurable (Ring.inverse : K → K) := by
  have hU : IsOpen {r : K | IsUnit r} := by
    convert h.isOpen_range using 1
    ext r
    simp [IsUnit]
  refine measurable_of_restrict_of_restrict_compl hU.measurableSet ?_ ?_
  · exact (continuousOn_iff_continuous_restrict.1
      (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse h)).measurable
  · have : ({r : K | IsUnit r}ᶜ).domRestrict (Ring.inverse : K → K) = fun _ => 0 := by
      funext r
      exact Ring.inverse_non_unit _ r.2
    rw [this]
    exact measurable_const

theorem isOpen_freeCell {M n : ℕ} (h : IsOpenEmbedding (Units.val : Kˣ → K))
    (hfree : IsOpen {X : Fin n → Fin M → K | LinearIndependent K X}) :
    IsOpen (freeCell K M n) := by
  have hU : IsOpen {r : K | IsUnit r} := by
    convert h.isOpen_range using 1
    ext r
    simp [IsUnit]
  have hev : ∀ (a : Fin (n + 1)) (i : Fin (M + 2)),
      Continuous fun X : Fin (n + 1) → Fin (M + 2) → K => X a i := fun a i =>
    (continuous_apply i).comp (continuous_apply a)
  have hUo : IsOpen {X : Fin (n + 1) → Fin (M + 2) → K | IsUnit (X 0 0)} := hU.preimage (hev 0 0)
  have hinv : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → K => Ring.inverse (X 0 0))
      {X | IsUnit (X 0 0)} :=
    (GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse h).comp (hev 0 0).continuousOn fun _ hX => hX
  have hy : ContinuousOn (yPart : (Fin (n + 1) → Fin (M + 2) → K) → Fin n → Fin M → K)
      {X | IsUnit (X 0 0)} := by
    refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun i => ?_
    exact (hev _ _).continuousOn.sub
      (((hev _ _).continuousOn.mul hinv).mul (hev _ _).continuousOn)
  exact hy.isOpen_inter_preimage hUo hfree

end Top

theorem freeCell_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, IsOpen (freeCell (R ⊗[F] E) M n) ∧ (∀ X ∈ freeCell (R ⊗[F] E) M n, LinearIndependent (R ⊗[F] E) X) ∧ (∀ X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ (hypOne J) X = 0 → IsUnit (X 0 0) → X ∈ freeCell (R ⊗[F] E) M n) ∧ (∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) Y → chartS R σ J x a s Y ∈ freeCell (R ⊗[F] E) M n) ∧ Measurable (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ hR n
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, ksig, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hU := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hR
  refine ⟨isOpen_freeCell hU (GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n M),
    fun X hX => linearIndependent_of_yPart X hX.1 hX.2,
    fun X hX hg hu => ⟨hu, yPart_linearIndependent R σ J X hX hg hu⟩,
    fun x a s Y hu hY => ?_,
    measurable_chartS R σ ksig.measurable (measurable_ringInverse hU) J⟩
  refine ⟨by simpa [chartS] using hu, ?_⟩
  rw [yPart_chartS R σ J x a s Y hu]
  exact hY

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell
