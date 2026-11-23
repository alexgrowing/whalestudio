import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt

noncomputable section

namespace GlobalTheory.GaugeEx

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Inst

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

scoped instance modTopTens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
scoped instance borelTens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
scoped instance borelHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

variable [FiniteDimensional F E] [IsTopologicalRing R]

scoped instance topRingTens : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _

scoped instance lcTens [LocallyCompactSpace R] : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.isClosedEmbedding.locallyCompactSpace

scoped instance scTens [SecondCountableTopology R] : SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.secondCountableTopology

scoped instance t2Space_scalarTensorExt [T2Space R] : T2Space (R ⊗[F] E) := by
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  exact e.isEmbedding.t2Space

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

scoped instance topGroupHA : IsTopologicalGroup (HA R σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem continuous_mat : Continuous fun g : HA R σ J =>
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  Units.continuous_val.comp continuous_subtype_val

scoped instance contSMulHA (n : ℕ) : ContinuousSMul (HA R σ J) (Fin n → Fin M → R ⊗[F] E) where
  continuous_smul := continuous_pi fun a =>
    ((continuous_mat R σ J).comp continuous_fst).matrix_mulVec
      ((continuous_apply a).comp continuous_snd)

variable [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]

scoped instance lcHA : LocallyCompactSpace (HA R σ J) := (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).1
scoped instance scHA : SecondCountableTopology (HA R σ J) :=
  (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).2.1
scoped instance t2HA : T2Space (HA R σ J) := (GlobalTheory.AdelicUnitaryTop.lcsc_HA R σ M J).2.2

end Inst

section AdeleInst

variable (F : Type) [Field F] [NumberField F]

scoped instance borelAF : BorelSpace (AF F) := ⟨rfl⟩
scoped instance borelAinf : BorelSpace (Ainf F) := ⟨rfl⟩
scoped instance borelAf : BorelSpace (Af F) := ⟨rfl⟩
scoped instance borelFv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
scoped instance lcAF : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
scoped instance scAF : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
scoped instance t2AF : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
scoped instance lcAf : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
scoped instance scAf : SecondCountableTopology (Af F) :=
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
scoped instance t2Af : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
scoped instance scAinf : SecondCountableTopology (Ainf F) :=
  GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
scoped instance t2Space_numberFieldInfiniteAdeles : T2Space (Ainf F) := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
scoped instance properFv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) :=
  GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v

end AdeleInst

def Nice (R : Type) [CommRing R] [TopologicalSpace R] : Prop :=
  IsArtinianRing R ∧ IsReduced R ∧ IsOpenUnits R ∧
    ∃ U : Set R, IsOpen U ∧ (1 : R) ∈ U ∧ ∃ s : R → R, ContinuousOn s U ∧ s 1 = 1 ∧ ∀ u ∈ U, s u * s u = u

open Classical in

def modu (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]
    (u : S) : ℝ≥0 :=
  if h : IsUnit u then distribHaarChar S h.unit else 0

def tupMeas {S : Type} [MeasurableSpace S] (lam : Measure S) (n M : ℕ) : Measure (Fin n → Fin M → S) :=
  Measure.pi fun _ => Measure.pi fun _ => lam

def lrAct {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : Fin n → Fin M → S :=
  fun a => g.mulVec fun i => ∑ c, X c i * γ c a

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def FibAt [TopologicalSpace R] [MeasurableSpace R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R)
    (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) : Prop :=
  ∃ fib : R → Measure (Fin 1 → Fin M → R ⊗[F] E),
    IsFibreFamily μ (fun X => qR R σ J (X 0)) id Set.univ ν {c | IsUnit c} fib ∧ fib β = m

def IsInvTup [TopologicalSpace R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  ∀ g : HA R σ J, m.map (fun X => g • X) = m

def OnOrbit [TopologicalSpace R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E)
    (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) : Prop :=
  m {y | ¬ ∃ g : HA R σ J, g • ratTup (F := F) R x = y} = 0

def IsSec {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E)
    (s : (Fin 1 → Fin M → R ⊗[F] E) → HA R σ J) : Prop :=
  ∀ y, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y • ratTup (F := F) R x = y

def pairOf {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g : HA R σ J) (y' : Fin 1 → Fin M → R ⊗[F] E) :
    Fin 2 → Fin (M + 1) → R ⊗[F] E :=
  ![y 0, ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix _ _ (R ⊗[F] E)).mulVec
    ((B.map (inclR R)).mulVec (y' 0))]

def TwoStep [TopologicalSpace R] {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E)
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)) : Prop :=
  ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∀ s, IsSec R σ J x s →
    ∫⁻ X, f X ∂N = ∫⁻ y, ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' ∂m

def gram3 {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin 2 → Fin M → R ⊗[F] E) : R × (R ⊗[F] E) × R :=
  (qR R σ J (X 0), hR R σ J (X 0) (X 1), qR R σ J (X 1))

def StepData {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) : Prop :=
  IsHermND σ J ∧ β ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β ∧
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) ∧
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B ∧ IsHermND σ J'

def consCol {M : ℕ} (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) E :=
  Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i)

def FrameRelR {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E)
    (B : Matrix (Fin M) (Fin M') E) (g : HA R σ J) (g' : HA R σ J') : Prop :=
  ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * B.map (inclR R) =
    B.map (inclR R) *
      ((HA.mat R σ J' g' : GL (Fin M') (R ⊗[F] E)) : Matrix (Fin M') (Fin M') (R ⊗[F] E))

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def prInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def prV (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem projInf_apply {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) :
    projInf X a i = prInf (X a i) := rfl

theorem projV_apply (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) : projV v (projFin X) a i = prV v (X a i) := rfl

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

def intV (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

theorem mem_latV_iff (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV b v ↔ ∀ a i, Y a i ∈ intV b v := Iff.rfl

structure StdMeas where

  lamI : Measure (Ainf F ⊗[F] E)

  lamV : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v ⊗[F] E)

  nuI : Measure (Ainf F)

  nuV : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)
  haar_lamI : lamI.IsAddHaarMeasure
  haar_lamV : ∀ v, (lamV v).IsAddHaarMeasure
  haar_nuI : nuI.IsAddHaarMeasure
  haar_nuV : ∀ v, (nuV v).IsAddHaarMeasure
  lamV_int : ∀ v, lamV v (intV b v) = 1
  nuV_int : ∀ v, nuV v (v.adicCompletionIntegers F : Set (Fv F v)) = 1

def tailProd {n M : ℕ} (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  ENNReal.ofReal (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (mv v.1 (latV b v.1)).toReal)

def Conv {n M : ℕ} (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFiniteMeasureOnCompacts mi ∧ (∀ v, IsFiniteMeasureOnCompacts (mv v)) ∧
    Summable fun v => |(mv v (latV b v)).toReal - 1|

def IsProd {n M : ℕ} (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  Conv b mi mv ∧
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
    Measurable fi → (∀ v, Measurable (fv v)) →
    ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v},
        fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν =
      (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S

variable {b} (s : StdMeas b) (σ : E →ₐ[F] E)

def IsStdX {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (β : F)
    (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ∃ (mi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
    FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi ∧
    (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) (mv v)) ∧
    IsProd b ν mi mv

def StepRel {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')) : Prop :=
  ∀ ν, IsStdX s σ J β ν → ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
    (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
    IsCompatible F E σ (M + 1) J x μ (μ'.map e.symm) ν

end Global

end GlobalTheory.GaugeEx
