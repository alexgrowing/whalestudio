import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def aPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin 1 → Fin n → K :=
  fun _ j => X j.succ 0 * Ring.inverse (X 0 0)

def sPart (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) :
    Fin 1 → Fin n → R ⊗[F] E :=
  fun _ j => sigR R σ (X 0 0) * (X j.succ 1 - aPart X 0 j * X 0 1) + tHalf R σ J (X 0) * aPart X 0 j +
    hR R σ J (tailH (X 0)) (yPart X j) + tHalf R σ J (X 0) * aPart X 0 j

def thetaS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) :
    (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin n → Fin M → R ⊗[F] E) :=
  (fun _ => X 0, aPart X, sPart R σ J X, yPart X)

variable (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
  (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E)

theorem chartS_zero : chartS R σ J x a s Y 0 = x 0 := rfl

theorem chartS_succ_zero (j : Fin n) : chartS R σ J x a s Y j.succ 0 = x 0 0 * a 0 j := rfl

theorem chartS_succ_one (j : Fin n) : chartS R σ J x a s Y j.succ 1 = a 0 j * x 0 1 +
    Ring.inverse (sigR R σ (x 0 0)) * (s 0 j - tHalf R σ J (x 0) * a 0 j - tHalf R σ J (x 0) * a 0 j -
      hR R σ J (tailH (x 0)) (Y j)) := rfl

theorem chartS_succ_rest (j : Fin n) (i : Fin M) :
    chartS R σ J x a s Y j.succ i.succ.succ = a 0 j * x 0 i.succ.succ + Y j i := rfl

variable {R σ J x a s Y}

theorem aPart_chartS (hx : IsUnit (x 0 0)) : aPart (chartS R σ J x a s Y) = a := by
  funext u j
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  show chartS R σ J x a s Y j.succ 0 * Ring.inverse (chartS R σ J x a s Y 0 0) = a 0 j
  rw [chartS_succ_zero, chartS_zero, mul_comm (x 0 0), mul_assoc, Ring.mul_inverse_cancel _ hx, mul_one]

theorem yPart_chartS (hx : IsUnit (x 0 0)) : yPart (chartS R σ J x a s Y) = Y := by
  funext j i
  show chartS R σ J x a s Y j.succ i.succ.succ -
    chartS R σ J x a s Y j.succ 0 * Ring.inverse (chartS R σ J x a s Y 0 0) * chartS R σ J x a s Y 0 i.succ.succ = Y j i
  rw [chartS_succ_rest, chartS_succ_zero, chartS_zero, mul_comm (x 0 0), mul_assoc (a 0 j),
    Ring.mul_inverse_cancel _ hx, mul_one]
  ring

theorem sPart_chartS (hx : IsUnit (x 0 0)) : sPart R σ J (chartS R σ J x a s Y) = s := by
  funext u j
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  have hs : IsUnit (sigR R σ (x 0 0)) := hx.map _
  have ha := aPart_chartS (R := R) (σ := σ) (J := J) (a := a) (s := s) (Y := Y) hx
  have hy := yPart_chartS (R := R) (σ := σ) (J := J) (a := a) (s := s) (Y := Y) hx
  show sigR R σ (chartS R σ J x a s Y 0 0) * (chartS R σ J x a s Y j.succ 1 -
      aPart (chartS R σ J x a s Y) 0 j * chartS R σ J x a s Y 0 1) +
      tHalf R σ J (chartS R σ J x a s Y 0) * aPart (chartS R σ J x a s Y) 0 j +
      hR R σ J (tailH (chartS R σ J x a s Y 0)) (yPart (chartS R σ J x a s Y) j) +
      tHalf R σ J (chartS R σ J x a s Y 0) * aPart (chartS R σ J x a s Y) 0 j = s 0 j
  rw [ha, hy, chartS_succ_one, chartS_zero, add_sub_cancel_left, ← mul_assoc, Ring.mul_inverse_cancel _ hs, one_mul]
  ring

theorem thetaS_chartS (hx : IsUnit (x 0 0)) : thetaS R σ J (chartS R σ J x a s Y) = (x, a, s, Y) := by
  have h0 : (fun _ : Fin 1 => chartS R σ J x a s Y 0) = x := by
    funext u
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    rfl
  simp only [thetaS, h0, aPart_chartS hx, sPart_chartS hx, yPart_chartS hx]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem continuous_hR [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type} [TopologicalSpace A]
    {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {u v : A → Fin m → R ⊗[F] E} (hu : Continuous u) (hv : Continuous v) :
    Continuous fun p => hR R σ J (u p) (v p) := by
  unfold hR hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hsig.comp ((continuous_apply i).comp hu)).mul continuous_const).mul ((continuous_apply j).comp hv)

theorem continuousOn_hR [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type}
    [TopologicalSpace A] {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {S : Set A} {u v : A → Fin m → R ⊗[F] E}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) : ContinuousOn (fun p => hR R σ J (u p) (v p)) S := by
  unfold hR hform
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  exact ((hsig.comp_continuousOn ((continuous_apply i).comp_continuousOn hu)).mul continuousOn_const).mul
    ((continuous_apply j).comp_continuousOn hv)

theorem continuous_tHalf [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type}
    [TopologicalSpace A] {u : A → Fin (M + 2) → R ⊗[F] E} (hu : Continuous u) :
    Continuous fun p => tHalf R σ J (u p) :=
  continuous_const.mul (continuous_hR hsig _ hu hu)

theorem continuous_tailH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {u : A → Fin (M + 2) → K}
    (hu : Continuous u) : Continuous fun p => tailH (u p) :=
  continuous_pi fun i => (continuous_apply i.succ.succ).comp hu

theorem continuousOn_vH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {S : Set A} {a s : A → K}
    {Y : A → Fin M → K} (ha : ContinuousOn a S) (hs : ContinuousOn s S) (hY : ContinuousOn Y S) :
    ContinuousOn (fun p => vH (a p) (s p) (Y p)) S := by
  refine continuousOn_pi.2 fun i => ?_
  refine Fin.cases ha (fun i => ?_) i
  refine Fin.cases hs (fun i => ?_) i
  exact (continuous_apply i).comp_continuousOn hY

theorem continuousOn_cvec [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) {A : Type} [TopologicalSpace A]
    {S : Set A} {u v : A → Fin (M + 2) → R ⊗[F] E} (hu : Continuous u) (hv : Continuous v)
    (hunit : ∀ p ∈ S, IsUnit (u p 0)) : ContinuousOn (fun p => cvec R σ J (u p) (v p)) S := by
  have c {w : A → Fin (M + 2) → R ⊗[F] E} (hw : Continuous w) (i : Fin (M + 2)) : Continuous fun p => w p i :=
    (continuous_apply i).comp hw
  have hI : ContinuousOn (fun p => Ring.inverse (sigR R σ (u p 0))) S :=
    hinv.comp (hsig.comp (c hu 0)).continuousOn fun p hp => (hunit p hp).map _
  refine continuousOn_vH ((c hu 0).mul (c hv 0)).continuousOn ?_ ?_
  · refine ((c hv 0).mul (c hu 1)).continuousOn.add (hI.mul (Continuous.continuousOn ?_))
    exact ((c hv 1).sub ((continuous_tHalf hsig hu).mul (c hv 0))).sub
      (continuous_hR hsig J (continuous_tailH hu) (continuous_tailH hv))
  · exact (continuous_pi fun i : Fin M => ((c hv 0).mul (c hu i.succ.succ)).add (c hv i.succ.succ)).continuousOn

theorem continuous_vH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {a s : A → K}
    {Y : A → Fin M → K} (ha : Continuous a) (hs : Continuous s) (hY : Continuous Y) :
    Continuous (fun p => vH (a p) (s p) (Y p)) :=
  continuousOn_univ.1 (continuousOn_vH ha.continuousOn hs.continuousOn hY.continuousOn)

theorem continuousOn_chartS [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) :
    ContinuousOn (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) {p | IsUnit (p.1 0 0)} := by
  have hx : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.1 0 := by fun_prop
  refine continuousOn_pi.2 fun j => ?_
  cases j using Fin.cases with
  | zero => exact hx.continuousOn
  | succ j =>
    have ha : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.1 0 j := by fun_prop
    have hs : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.1 0 j := by fun_prop
    have hY : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.2 j := by fun_prop
    exact continuousOn_cvec hsig hinv hx
      (continuous_vH ha (hs.sub ((continuous_tHalf hsig hx).mul ha)) hY) fun p hp => hp

theorem continuousOn_thetaS [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) :
    ContinuousOn (thetaS R σ J : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → _) {X | IsUnit (X 0 0)} := by
  have c (j : Fin (n + 1)) (i : Fin (M + 2)) :
      Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => X j i := by fun_prop
  have hI : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => Ring.inverse (X 0 0))
      {X | IsUnit (X 0 0)} := hinv.comp (c 0 0).continuousOn fun X hX => hX
  have h0 : Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => X 0 := continuous_apply 0
  have hA (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => aPart X 0 j)
      {X | IsUnit (X 0 0)} := (c j.succ 0).continuousOn.mul hI
  have hY (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => yPart X j)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 fun i =>
    (c j.succ i.succ.succ).continuousOn.sub (((c j.succ 0).continuousOn.mul hI).mul (c 0 i.succ.succ).continuousOn)
  have ht : Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => tHalf R σ J (X 0) :=
    continuous_tHalf hsig h0
  have hh (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
      hR R σ J (tailH (X 0)) (yPart X j)) {X | IsUnit (X 0 0)} :=
    continuousOn_hR hsig J (continuous_tailH h0).continuousOn (hY j)
  have h1 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => (fun _ : Fin 1 => X 0))
      {X | IsUnit (X 0 0)} := (continuous_pi fun _ => h0).continuousOn
  have h2 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => aPart X)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 fun u => continuousOn_pi.2 fun j => by
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    exact hA j
  have h3 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => sPart R σ J X)
      {X | IsUnit (X 0 0)} := by
    refine continuousOn_pi.2 fun _ => continuousOn_pi.2 fun j => ?_
    have hs : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
        sigR R σ (X 0 0) * (X j.succ 1 - aPart X 0 j * X 0 1) + tHalf R σ J (X 0) * aPart X 0 j +
          hR R σ J (tailH (X 0)) (yPart X j) + tHalf R σ J (X 0) * aPart X 0 j) {X | IsUnit (X 0 0)} :=
      (((((hsig.comp (c 0 0)).continuousOn).mul ((c j.succ 1).continuousOn.sub
        ((hA j).mul (c 0 1).continuousOn))).add (ht.continuousOn.mul (hA j))).add (hh j)).add
          (ht.continuousOn.mul (hA j))
    exact hs
  have h4 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => yPart X)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 hY
  exact h1.prodMk (h2.prodMk (h3.prodMk h4))

end Top

theorem test_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ hLoc n φ hφ hφc hφs
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hLoc
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨i1, -, -, i4, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := i1
  haveI := i4
  have hinv := GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hKu
  set ψ := fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
    (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) with hψ
  have hCu : tsupport φ ⊆ {X | IsUnit (X 0 0)} := fun X hX => (hφs hX).1
  let T := thetaS R σ J '' tsupport φ
  have hTc : IsCompact T := hφc.isCompact.image_of_continuousOn ((continuousOn_thetaS hsig hinv).mono hCu)
  have hTcl : IsClosed T := hTc.isClosed
  have hsupp : Function.support ψ ⊆ T := by
    rintro ⟨x, a, s, Y⟩ hp
    have hC : chartS R σ J x a s Y ∈ tsupport φ := subset_tsupport φ hp
    have hx : IsUnit (x 0 0) := hCu hC
    exact ⟨_, hC, thetaS_chartS hx⟩
  have hts : tsupport ψ ⊆ T := closure_minimal hsupp hTcl
  refine ⟨?_, hTc.of_isClosed_subset (isClosed_tsupport ψ) hts, ?_⟩
  · refine continuous_iff_continuousAt.2 fun p => ?_
    by_cases hp : p ∈ T
    · obtain ⟨X, hX, rfl⟩ := hp
      have hU : IsOpen {q : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
          (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) | IsUnit (q.1 0 0)} := by
        have h1 : IsOpen {r : R ⊗[F] E | IsUnit r} := by
          have h2 : {r : R ⊗[F] E | IsUnit r} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) :=
            Set.ext fun r => Iff.rfl
          rw [h2]
          exact hKu.isOpen_range
        exact h1.preimage (by fun_prop)
      have hmem : thetaS R σ J X ∈ {q : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
          (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) | IsUnit (q.1 0 0)} := hCu hX
      exact hφ.continuousAt.comp ((continuousOn_chartS hsig hinv).continuousAt (hU.mem_nhds hmem))
    · have : ψ =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [hTcl.isOpen_compl.mem_nhds hp] with q hq
        by_contra h
        exact hq (hsupp h)
      exact continuousAt_const.congr this.symm
  · intro p hp
    obtain ⟨X, hX, rfl⟩ := hts hp
    exact hφs hX

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest
