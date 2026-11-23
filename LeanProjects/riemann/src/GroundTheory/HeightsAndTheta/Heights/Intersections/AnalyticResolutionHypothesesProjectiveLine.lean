import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineHomogeneousLift
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IfaceInh
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ

def tsmul (c : K → ℂ) (z : MCone ι) : MCone ι := fun q => c q.1 * z q

def zPts (P : Ideal (MRing ι ℂ)) : Set (MCone ι) :=
  ReciprocityTheory.AnForm.R.conePts P

def IsProjVar (P : Ideal (MRing ι ℂ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P ∧ ringKrullDim (MRing ι ℂ ⧸ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

def IsLocSmooth (P : Ideal (MRing ι ℂ)) (g : MCone ι → ℝ) : Prop :=
  ∀ z ∈ zPts P, ∃ U ∈ 𝓝 z, ∃ G : MCone ι → ℝ, ContDiffOn ℝ ∞ G U ∧ ∀ w ∈ U ∩ zPts P, g w = G w

def IsSmoothFn (P : Ideal (MRing ι ℂ)) (g : MCone ι → ℝ) : Prop :=
  (∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P, g (tsmul c z) = g z) ∧ IsLocSmooth P g

def logH (L : HLine ι) : MCone ι → ℝ := fun z => Real.log (L.h z)

def IsSmoothMetric (P : Ideal (MRing ι ℂ)) (L : HLine ι) : Prop :=
  IsLocSmooth P (logH L)

def IsSmoothPot (P : Ideal (MRing ι ℂ)) (φ : MCone ι → ℝ) : Prop :=
  (∃ a : K → ℤ, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P,
    φ (tsmul c z) = φ z + ∑ k, (a k : ℝ) * Real.log ‖c k‖) ∧ IsLocSmooth P φ

def secNorm (A : HLine ι) (s : MRing ι ℂ) : MCone ι → ℝ :=
  fun z => Real.log (‖eval z s‖ / A.h z)

def IsFormSec {R : Type} [CommRing R] (P : Ideal (MRing ι R)) (A : HLine ι) (s : MRing ι R) : Prop :=
  ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P

def comps {R : Type} [CommRing R] (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Set (Ideal (MRing ι R)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}

variable (ι) in

structure Res (P : Ideal (MRing ι ℂ)) (e : ℕ) where

  D : Ideal (MRing ι ℂ)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e

namespace Res

variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)

def idx (x : R.R.M) : Fin R.R.n := (R.R.cover x).choose

theorem mem_src_idx (x : R.R.M) : x ∈ R.R.src (R.idx x) := (R.R.cover x).choose_spec

def liftAt (x y : R.R.M) : MCone ι :=
  fun q => eval (R.R.coord (R.idx x) y) (R.R.lift (R.idx x) q)

def pt (x : R.R.M) : MCone ι := R.liftAt x x

def atlas : FinHolAtlas e R.R.M := R.R.exists_atlas.choose

def pot (φ : MCone ι → ℝ) : LocPot R.R.M where
  U x := R.R.src (R.idx x)
  isOpen_U _ := R.R.isOpen_alt_bis _
  mem_U x := R.mem_src_idx x
  φ x y := φ (R.liftAt x y)

def int (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  mInt R.atlas (fun j => R.pot (φ j)) (fun x => g (R.pt x))

end Res

open Classical in

def zInt (P : Ideal (MRing ι ℂ)) (e : ℕ) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  if h : Nonempty (Res ι P e) then h.some.int φ g else 0

def extC (P0 : Ideal (MRing ι ℚ)) : Ideal (MRing ι ℂ) :=
  ReciprocityTheory.AnForm.R.extC P0

def sC (s : MRing ι ℚ) : MRing ι ℂ := MvPolynomial.map (algebraMap ℚ ℂ) s

def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

def zIntQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  ∑ᶠ Z ∈ (extC P0).minimalPrimes, zInt Z e φ g

end Objects

def projectiveLineZeroForm_holds.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) (W : Set X) (B : FinHolAtlas e W),
    IsPotential A L → IsSection A L s → IsSNC A L s ![1] ![W] → HoloMap B A Subtype.val →
    ∀ v : X → ℝ, A.Smooth v → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
        mInt B (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) -
          mInt A (Fin.cons L Φ) v

def ResIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (R R' : Res ι P e) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ),
    IsProjVar P e → (∀ j, IsSmoothPot P (φ j)) →
    (IsSmoothFn P g ∨ ∃ (A : HLine ι) (s : MRing ι ℂ), IsSmoothMetric P A ∧ IsFormSec P A s ∧
      g = secNorm A s) →
    R.int φ g = R'.int φ g

def S3.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (v w : MCone ι → ℝ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothFn P v → IsSmoothFn P w →
    zInt P (e + 1) (Fin.cons w fun j => logH (L j)) v =
      zInt P (e + 1) (Fin.cons v fun j => logH (L j)) w

def ThreeSphereMass.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L L' : Fin e → HLine ι),
    IsProjVar P e → Nonempty (Res ι P e) → (∀ j, IsSmoothMetric P (L j)) →
    (∀ j, IsSmoothMetric P (L' j)) → (∀ j, (L j).a = (L' j).a) →
    zInt P e (fun j => logH (L j)) (fun _ => 1) = zInt P e (fun j => logH (L' j)) (fun _ => 1)

def S4.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (R : Res ι P e) (φ : Fin e → MCone ι → ℝ) (A : HLine ι)
    (s : MRing ι ℂ),
    IsProjVar P e → (∀ j, IsSmoothPot P (φ j)) → IsSmoothMetric P A → IsFormSec P A s →
    MIntegrable R.atlas (fun j => R.pot (φ j)) (fun x => secNorm A s (R.pt x))

def PoincareLelongAlt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A : HLine ι) (s : MRing ι ℂ)
    (v : MCone ι → ℝ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ W ∈ comps P s, Nonempty (Res ι W e)) →
    (∀ j, IsSmoothMetric P (L j)) → IsSmoothMetric P A → IsFormSec P A s → IsSmoothFn P v →
    zInt P (e + 1) (Fin.cons v fun j => logH (L j)) (secNorm A s) =
      (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) v) -
        zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) v

def Degrees.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι),
    IsProjVar P e → Nonempty (Res ι P e) → (∀ j, IsSmoothMetric P (L j)) →
    zInt P e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ P (fun j => (L j).a) : ℝ)

def ProjectiveLineTwo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A A' : HLine ι) (s s' : MRing ι ℂ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ W ∈ comps P s, Nonempty (Res ι W e)) →
    (∀ W ∈ comps P s', Nonempty (Res ι W e)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P A' → IsFormSec P A s → IsFormSec P A' s' →
    (∀ W ∈ comps P s, W ∉ comps P s') →
    (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (secNorm A' s')) +
        zInt P (e + 1) (Fin.cons (logH A') fun j => logH (L j)) (secNorm A s) =
      (∑ᶠ W ∈ comps P s', (divCycle P s' W : ℝ) * zInt W e (fun j => logH (L j)) (secNorm A s)) +
        zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (secNorm A' s')

def BCMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (s : MRing ι ℚ) (a : K → ℕ) (W : Ideal (MRing ι ℚ))
    (Wa : Ideal (MRing ι ℂ)),
    IsProjVarQ P0 (e + 1) → IsMultiHomog s a → s ∉ P0 → W ∈ comps P0 s →
    Wa ∈ (extC W).minimalPrimes →
    divCycle P0 s W = ∑ᶠ Z ∈ (extC P0).minimalPrimes, divCycle Z (sC s) Wa

def BCCommon.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (s s' : MRing ι ℚ) (a a' : K → ℕ) (Z Wa : Ideal (MRing ι ℂ)),
    IsProjVarQ P0 (e + 1) → IsMultiHomog s a → s ∉ P0 → IsMultiHomog s' a' → s' ∉ P0 →
    Z ∈ (extC P0).minimalPrimes → Wa ∈ comps Z (sC s) → Wa ∈ comps Z (sC s') →
    Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ∈ comps P0 s ∩ comps P0 s'

def BCDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (bs : Fin e → K → ℤ),
    IsProjVarQ P0 e →
    intNum ℚ P0 bs = ∑ᶠ Z ∈ (extC P0).minimalPrimes, intNum ℂ Z bs

def DegreesQ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι),
    IsProjVarQ P0 e → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) →
    zIntQ P0 e (fun j => logH (L j)) (fun _ => 1) = (intNum ℚ P0 (fun j => (L j).a) : ℝ)

def ProjectiveLineOverRationals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι) (A : HLine ι) (s : MRing ι ℚ)
    (v : MCone ι → ℝ),
    IsProjVarQ P0 (e + 1) → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z (e + 1))) →
    (∀ W ∈ comps P0 s, ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) → IsSmoothMetric (extC P0) A → IsFormSec P0 A s →
    IsSmoothFn (extC P0) v →
    zIntQ P0 (e + 1) (Fin.cons v fun j => logH (L j)) (secNorm A (sC s)) =
      (∑ᶠ W ∈ comps P0 s, (divCycle P0 s W : ℝ) * zIntQ W e (fun j => logH (L j)) v) -
        zIntQ P0 (e + 1) (Fin.cons (logH A) fun j => logH (L j)) v

def ProjectivePlaneOverRationals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι) (A A' : HLine ι) (s s' : MRing ι ℚ),
    IsProjVarQ P0 (e + 1) → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z (e + 1))) →
    (∀ W ∈ comps P0 s, ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ W ∈ comps P0 s', ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) → IsSmoothMetric (extC P0) A →
    IsSmoothMetric (extC P0) A' → IsFormSec P0 A s → IsFormSec P0 A' s' →
    (∀ W ∈ comps P0 s, W ∉ comps P0 s') →
    (∑ᶠ W ∈ comps P0 s, (divCycle P0 s W : ℝ) *
        zIntQ W e (fun j => logH (L j)) (secNorm A' (sC s'))) +
        zIntQ P0 (e + 1) (Fin.cons (logH A') fun j => logH (L j)) (secNorm A (sC s)) =
      (∑ᶠ W ∈ comps P0 s', (divCycle P0 s' W : ℝ) *
        zIntQ W e (fun j => logH (L j)) (secNorm A (sC s))) +
        zIntQ P0 (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (secNorm A' (sC s'))

section Ring

variable {K : Type} {ι : K → Type}

theorem mem_span_X_iff {R : Type} [CommRing R] (q : Σ k, ι k) (f : MRing ι R) :
    f ∈ Ideal.span {(X q : MRing ι R)} ↔ ∀ m ∈ f.support, m q ≠ 0 := by
  rw [← Set.image_singleton, mem_ideal_span_X_image]
  simp

theorem isMultiHomogIdeal_span_X [Fintype K] [DecidableEq K] {R : Type} [CommRing R] (q : Σ k, ι k) :
    IsMultiHomogIdeal (Ideal.span {(X q : MRing ι R)}) := by
  intro f hf b
  rw [mem_span_X_iff] at hf ⊢
  intro m hm
  apply hf m
  rw [mem_support_iff] at hm ⊢
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact hm
  · exact absurd rfl hm

theorem X_not_mem_span_X {R : Type} [CommRing R] [Nontrivial R] {q q' : Σ k, ι k} (h : q ≠ q') :
    (X q' : MRing ι R) ∉ Ideal.span {(X q : MRing ι R)} := by
  rw [mem_span_X_iff]
  intro hm
  have := hm (Finsupp.single q' 1) (by simp [support_X])
  simp [h.symm] at this

theorem isPrime_span_X {R : Type} [CommRing R] [IsDomain R] (q : Σ k, ι k) :
    (Ideal.span {(X q : MRing ι R)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero q)).mpr X_prime

theorem X_ne_bot {R : Type} [CommRing R] [Nontrivial R] (q : Σ k, ι k) :
    (X q : MRing ι R) ∉ (⊥ : Ideal (MRing ι R)) := by
  rw [Submodule.mem_bot]
  exact X_ne_zero q

end Ring

abbrev ι1 : Unit → Type := fun _ => Fin 2

abbrev Xj {R : Type} [CommRing R] (j : Fin 2) : MRing ι1 R := X ⟨(), j⟩

abbrev ptI {R : Type} [CommRing R] (j : Fin 2) : Ideal (MRing ι1 R) := Ideal.span {Xj j}

theorem fin_two_add_one_ne (j : Fin 2) : j + 1 ≠ j := by
  fin_cases j <;> decide

theorem fin_two_eq_or_eq_add_one (j i : Fin 2) : i = j ∨ i = j + 1 := by
  fin_cases j <;> fin_cases i <;> decide

theorem isRelevant_ptI {R : Type} [CommRing R] [Nontrivial R] (j : Fin 2) :
    IsRelevant (ptI (R := R) j) := by
  intro k
  refine ⟨j + 1, X_not_mem_span_X ?_⟩
  intro h
  have := congrArg Sigma.snd h
  exact fin_two_add_one_ne j (by simpa using this.symm)

theorem comps_bot_X {R : Type} [CommRing R] [IsDomain R] (j : Fin 2) :
    comps (⊥ : Ideal (MRing ι1 R)) (Xj j) = {ptI j} := by
  have := isPrime_span_X (R := R) (⟨(), j⟩ : Σ _ : Unit, Fin 2)
  ext W
  simp only [comps, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant_ptI j⟩

theorem ptI_ne {R : Type} [CommRing R] [Nontrivial R] : ptI (R := R) 0 ≠ ptI 1 := by
  intro h
  have h0 : (Xj 0 : MRing ι1 R) ∈ ptI 0 := Ideal.subset_span rfl
  rw [h] at h0
  exact X_not_mem_span_X (by decide) h0

theorem extC_bot : extC (⊥ : Ideal (MRing ι1 ℚ)) = ⊥ := Ideal.map_bot

theorem extC_ptI (j : Fin 2) : extC (ptI (R := ℚ) j) = ptI j := by
  simp [extC, ReciprocityTheory.AnForm.R.extC, Ideal.map_span]

theorem minimalPrimes_bot_C : (⊥ : Ideal (MRing ι1 ℂ)).minimalPrimes = {⊥} :=
  IsDomain.minimalPrimes_eq_singleton_bot _

theorem minimalPrimes_ptI (j : Fin 2) : (ptI (R := ℂ) j).minimalPrimes = {ptI j} := by
  have := isPrime_span_X (R := ℂ) (⟨(), j⟩ : Σ _ : Unit, Fin 2)
  exact Ideal.minimalPrimes_eq_subsingleton_self

theorem dim_bot (k : Type) [Field k] :
    ringKrullDim (MRing ι1 k ⧸ (⊥ : Ideal (MRing ι1 k))) = ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.height_add_ringKrullDim_quotient_fintype
    (σ := Σ _ : Unit, Fin 2) k ⊥
  rw [Ideal.height_bot] at h
  simpa using h

theorem isProjVar_bot : IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 :=
  ⟨GroundTheory.Heights₂.Heights.NumbersDVR.isMultiProjPrime_bot, dim_bot ℂ⟩

theorem isProjVarQ_bot : IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) 1 :=
  ⟨GroundTheory.Heights₂.Heights.NumbersDVR.isMultiProjPrime_bot, dim_bot ℚ⟩

theorem isMultiHomog_Xj {R : Type} [CommRing R] (j : Fin 2) :
    IsMultiHomog (Xj (R := R) j) (fun _ => 1) := by
  have h := isWeightedHomogeneous_X R (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι1)
    (⟨(), j⟩ : Σ _ : Unit, Fin 2)
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι1 (⟨(), j⟩ : Σ _ : Unit, Fin 2) =
      fun _ => 1 := by
    funext u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  rw [hw] at h
  exact h

def projLineResolution : Res ι1 (⊥ : Ideal (MRing ι1 ℂ)) 1 where
  D := ptI 0
  homog := isMultiHomogIdeal_span_X _
  not_le h := X_ne_bot (R := ℂ) (⟨(), 0⟩ : Σ _ : Unit, Fin 2) (h (Ideal.subset_span rfl))
  R := ReciprocityTheory.AnForm.R.projectiveLineAlgRes

def ptVec (j : Fin 2) : MCone ι1 := fun q => if q.2 = j then 0 else 1

def ptLift (j : Fin 2) : (Σ _ : Unit, Fin 2) → MvPolynomial (Fin 0) ℂ :=
  fun q => if q.2 = j then 0 else 1

theorem eval_ptLift (j : Fin 2) (y : Fin 0 → ℂ) (q : Σ _ : Unit, Fin 2) :
    eval y (ptLift j q) = ptVec j q := by
  unfold ptLift ptVec
  split_ifs <;> simp

theorem ptVec_mem (j : Fin 2) : ptVec j ∈ ReciprocityTheory.AnForm.R.conePts (ptI (R := ℂ) j) := by
  refine ⟨fun k => ⟨j + 1, ?_⟩, fun f hf => ?_⟩
  · simp [ptVec]
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [ptVec]

theorem not_mem_conePts_top (z : MCone ι1) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MRing ι1 ℂ)) := by
  rintro ⟨-, h⟩
  simpa using h 1 Submodule.mem_top

def ptSnc (p : Fin 0 → ℂ) :
    ReciprocityTheory.AnForm.R.SncData (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) ⊤ p 0 0 where
  r l := l.elim0
  J := ∅
  h := 1
  σ l := l.elim0
  σ_injOn := by simp
  σ_eq_none l := l.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    conv_rhs => arg 2; rw [ReciprocityTheory.AnForm.R.ptIdeal_fin_zero]
    exact Ideal.map_bot.symm
  eval_h := by simp
  mem_bd := Submodule.mem_top
  le_span g _ := by simp

theorem bind₁_ptLift_isUnit (j : Fin 2) (f : MvPolynomial (Σ _ : Unit, Fin 2) ℂ)
    (hf : eval (ptVec j) f ≠ 0) : IsUnit (bind₁ (ptLift j) f) := by
  have key2 : eval (0 : Fin 0 → ℂ) (bind₁ (ptLift j) f) = eval (ptVec j) f := by
    have h := hom_bind₁ (eval (0 : Fin 0 → ℂ)) (ptLift j) f
    have hc : (eval (0 : Fin 0 → ℂ)).comp C = RingHom.id ℂ := RingHom.ext fun c => by simp
    have hv : (fun i => eval (0 : Fin 0 → ℂ) (ptLift j i)) = ptVec j := funext (eval_ptLift j 0)
    rw [hc, hv, coe_eval₂Hom, eval₂_id] at h
    exact h
  have hC := eq_C_of_isEmpty (bind₁ (ptLift j) f)
  have hc : coeff 0 (bind₁ (ptLift j) f) ≠ 0 := by
    intro h0
    apply hf
    rw [← key2, hC, h0]
    simp
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

def ptAlgRes (j : Fin 2) : ReciprocityTheory.AnForm.R.AlgRes ι1 (ptI j) ⊤ 0 where
  M := Unit
  n := 1
  amb _ := 0
  ideal _ := ⊥
  src _ := Set.univ
  isOpen_alt_bis _ := isOpen_univ
  cover _ := ⟨0, Set.mem_univ _⟩
  coord _ _ := 0
  isEmbedding _ := Topology.IsEmbedding.of_subsingleton _
  image _ := by
    ext y
    constructor
    · rintro - h hh
      rw [Ideal.mem_bot] at hh
      simp [hh]
    · intro _
      exact ⟨(), Set.mem_univ _, Subsingleton.elim _ _⟩
  trans _ _ _ _ := ⟨1, fun l => l.elim0, by simp, fun _ _ _ l => l.elim0⟩
  regular _ _ _ := ReciprocityTheory.AnForm.R.locRing_bot_regular _
  dim _ _ _ := by
    rw [ReciprocityTheory.AnForm.R.locRing_bot_dim]
    rfl
  lift _ := ptLift j
  lift_one _ := ⟨fun _ => j + 1, fun _ => by simp [ptLift]⟩
  lift_mem _ _ _ := by
    convert ptVec_mem j using 1
    funext q
    exact eval_ptLift j _ q
  compat _ _ _ _ := ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩
  surj z hz _ := by
    have hzj : z ⟨(), j⟩ = 0 := by simpa using hz.2 _ (Ideal.subset_span rfl)
    have hz1 : z ⟨(), j + 1⟩ ≠ 0 := by
      obtain ⟨i, hi⟩ := hz.1 ()
      rcases fin_two_eq_or_eq_add_one j i with rfl | rfl
      · exact absurd hzj hi
      · exact hi
    refine ⟨0, (), Set.mem_univ _, fun _ => (z ⟨(), j + 1⟩)⁻¹, fun _ => inv_ne_zero hz1, ?_⟩
    funext q
    rcases q with ⟨⟨⟩, i⟩
    rw [eval_ptLift]
    rcases fin_two_eq_or_eq_add_one j i with rfl | rfl
    · simp [ptVec, hzj]
    · simp [ptVec, hz1]
  inj _ _ x _ x' _ _ _ := Subsingleton.elim x x'
  inv _ _ _ _ _ hp := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, 1, fun l => l.elim0,
    fun _ _ => ⟨hp, by simp, fun l => l.elim0⟩⟩
  bd _ := ⊤
  le_bd _ := le_top
  zero_bd _ _ _ := ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp),
    fun h => absurd h (not_mem_conePts_top _)⟩
  rc := 0
  comp k := k.elim0
  sncAt _ _ _ := ptSnc _
  comp_eq _ _ _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, fun k => k.elim0⟩
  mult f _ _ _ hz := by
    have hf : eval (ptVec j) f ≠ 0 := fun h0 => not_mem_conePts_top _ (hz _ (ptVec_mem j) h0)
    refine ⟨fun k => k.elim0, fun i x hx => ?_⟩
    refine ⟨algebraMap _ _ (bind₁ (ptLift j) f), (bind₁_ptLift_isUnit j f hf).map _, ?_⟩
    simp only [ptSnc, Finset.prod_empty, mul_one]

def ptRes (j : Fin 2) : Res ι1 (ptI (R := ℂ) j) 0 where
  D := ⊤
  homog _ _ _ := Submodule.mem_top
  not_le h := (isPrime_span_X (R := ℂ) (⟨(), j⟩ : Σ _ : Unit, Fin 2)).ne_top (top_le_iff.mp h)
  R := ptAlgRes j

def qn (z : MCone ι1) : ℝ := ‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2

theorem contDiff_normSq_coord (i : Fin 2) :
    ContDiff ℝ ∞ (fun z : MCone ι1 => ‖z ⟨(), i⟩‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨(), i⟩ : Σ _ : Unit, Fin 2))

theorem contDiff_qn : ContDiff ℝ ∞ qn :=
  (contDiff_normSq_coord 0).add (contDiff_normSq_coord 1)

theorem qn_pos {z : MCone ι1} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < qn z := by
  obtain ⟨i, hi⟩ := hz ()
  have h := pow_pos (norm_pos_iff.mpr hi) 2
  unfold qn
  fin_cases i
  · exact add_pos_of_pos_of_nonneg h (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) h

theorem qn_tsmul (c : Unit → ℂ) (z : MCone ι1) : qn (tsmul c z) = ‖c ()‖ ^ 2 * qn z := by
  simp only [qn, tsmul, norm_mul, mul_pow]
  ring

theorem isOpen_qn_pos : IsOpen {w : MCone ι1 | 0 < qn w} :=
  isOpen_lt continuous_const contDiff_qn.continuous

def fubiniStudyLine : HLine ι1 := ReciprocityTheory.ChartRestriction.G.Geo.fsLine 2

theorem logH_fubiniStudyLine (z : MCone ι1) : logH fubiniStudyLine z = Real.log (qn z) / 2 := by
  have h : fubiniStudyLine.h z = Real.sqrt (qn z) := by
    simp [fubiniStudyLine, ReciprocityTheory.ChartRestriction.G.Geo.fsLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics,
      ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, EuclideanSpace.norm_eq, Fin.sum_univ_two, qn]
  rw [logH, h, Real.log_sqrt (by unfold qn; positivity)]

theorem isSmoothMetric_fubiniStudyLine (P : Ideal (MRing ι1 ℂ)) : IsSmoothMetric P fubiniStudyLine := by
  intro z hz
  refine ⟨{w | 0 < qn w}, isOpen_qn_pos.mem_nhds (qn_pos hz.1), fun w => Real.log (qn w) / 2,
    ?_, fun w _ => logH_fubiniStudyLine w⟩
  exact (contDiff_qn.contDiffOn.log fun w hw => ne_of_gt hw).div_const 2

def projectiveLineCoordinates (j : Fin 2) (z : MCone ι1) : ℝ := ‖z ⟨(), j⟩‖ ^ 2 / qn z

theorem projLineRatio_torus_smul (j : Fin 2) (c : Unit → ℂ) (hc : ∀ k, c k ≠ 0) (z : MCone ι1) :
    projectiveLineCoordinates j (tsmul c z) = projectiveLineCoordinates j z := by
  rw [projectiveLineCoordinates, projectiveLineCoordinates, qn_tsmul]
  simp only [tsmul, norm_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hc ())))

theorem isSmoothFn_projLineRatio (P : Ideal (MRing ι1 ℂ)) (j : Fin 2) : IsSmoothFn P (projectiveLineCoordinates j) := by
  refine ⟨fun c hc z _ => projLineRatio_torus_smul j c hc z, fun z hz => ?_⟩
  refine ⟨{w | 0 < qn w}, isOpen_qn_pos.mem_nhds (qn_pos hz.1), projectiveLineCoordinates j, ?_, fun w _ => rfl⟩
  exact (contDiff_normSq_coord j).contDiffOn.div contDiff_qn.contDiffOn fun w hw => ne_of_gt hw

theorem isSmoothPot_logH {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι ℂ)} {L : HLine ι} (h : IsSmoothMetric P L) :
    IsSmoothPot P (logH L) := by
  refine ⟨⟨L.a, fun c hc z hz => ?_⟩, h⟩
  have hL := L.pos z hz.1
  have hp : ∀ k ∈ Finset.univ, ‖c k‖ ^ L.a k ≠ 0 := fun k _ =>
    zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  unfold logH tsmul
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr hp) hL.ne', Real.log_prod hp,
    add_comm]
  simp only [Real.log_zpow]

theorem isSmoothPot_of_fn {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι ℂ)} {g : MCone ι → ℝ} (h : IsSmoothFn P g) :
    IsSmoothPot P g :=
  ⟨⟨0, fun c hc z hz => by simp [h.1 c hc z hz]⟩, h.2⟩

theorem isSec_bot_X {R : Type} [CommRing R] [IsDomain R] (j : Fin 2) :
    IsFormSec (⊥ : Ideal (MRing ι1 R)) fubiniStudyLine (Xj j) :=
  ⟨fun _ => 1, fun k => by simp [fubiniStudyLine, ReciprocityTheory.ChartRestriction.G.Geo.fsLine,
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics], isMultiHomog_Xj j, X_ne_bot _⟩

def fsTw : HLine ι1 :=
  ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor fubiniStudyLine
    (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (projectiveLineCoordinates 0) fun c z hc => projLineRatio_torus_smul 0 c hc z)

theorem isSmoothMetric_fsTw (P : Ideal (MRing ι1 ℂ)) : IsSmoothMetric P fsTw := by
  intro z hz
  refine ⟨{w | 0 < qn w}, isOpen_qn_pos.mem_nhds (qn_pos hz.1),
    fun w => Real.log (qn w) / 2 - projectiveLineCoordinates 0 w, ?_, fun w hw => ?_⟩
  · exact ((contDiff_qn.contDiffOn.log fun w hw => ne_of_gt hw).div_const 2).sub
      ((contDiff_normSq_coord 0).contDiffOn.div contDiff_qn.contDiffOn fun w hw => ne_of_gt hw)
  · have hp := fubiniStudyLine.pos w hw.2.1
    show Real.log (fubiniStudyLine.h w * Real.exp (-projectiveLineCoordinates 0 w)) = _
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, ← logH, logH_fubiniStudyLine]
    ring

theorem fsTw_a : fsTw.a = fubiniStudyLine.a := by
  show fubiniStudyLine.a + 0 = fubiniStudyLine.a
  exact add_zero _

def projLineFubiniStudyMass : ℝ := zInt (⊥ : Ideal (MRing ι1 ℂ)) 1 ![logH fubiniStudyLine] (fun _ => 1)

theorem nonempty_resolution_projLine : Nonempty (Res ι1 (⊥ : Ideal (MRing ι1 ℂ)) 1) := ⟨projLineResolution⟩

theorem holoMap_infty :
    HoloMap (ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))) ReciprocityTheory.AnForm.M.p1
      Subtype.val := by
  refine ⟨continuous_subtype_val, fun j k y _ => ?_⟩
  have hc : (ReciprocityTheory.AnForm.M.p1.chart k ∘ Subtype.val ∘
      ((ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))).chart j).symm) =
      fun _ => (ReciprocityTheory.AnForm.M.p1.chart k ∘ Subtype.val ∘
        ((ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))).chart j).symm) y :=
    funext fun y' => congrArg _ (Subsingleton.elim y' y)
  rw [hc]
  exact analyticAt_const

theorem projectiveLineZeroForm_holds.analyticResolution_hypotheses_projectiveLine :
    IsPotential ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ∧
    IsSection ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ∧
    IsSNC ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ![1]
      ![({OnePoint.infty} : Set (OnePoint ℂ))] ∧
    HoloMap (ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))) ReciprocityTheory.AnForm.M.p1
      Subtype.val ∧
    ReciprocityTheory.AnForm.M.p1.Smooth ReciprocityTheory.AnForm.M.fsH ∧
    ∀ i : Fin 0, IsPotential ReciprocityTheory.AnForm.M.p1 ((Fin.elim0 : Fin 0 → LocPot (OnePoint ℂ)) i) :=
  ⟨ReciprocityTheory.AnForm.M.projLine_isSmoothPotential, ReciprocityTheory.AnForm.M.projLine_isHolomorphicSection, ReciprocityTheory.AnForm.M.projLine_isSimpleNormalCrossing,
    holoMap_infty, ReciprocityTheory.AnForm.M.projLine_smooth_of_charts ReciprocityTheory.AnForm.M.contDiff_fubiniStudyRatio_comp_chart0
      ReciprocityTheory.AnForm.M.contDiff_fubiniStudyRatio_comp_chart1, fun i => i.elim0⟩

theorem ResIndep.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ (∀ j, IsSmoothPot ⊥ ((![logH fubiniStudyLine] : Fin 1 → _) j)) ∧
    (IsSmoothFn ⊥ (secNorm fubiniStudyLine (Xj 0)) ∨ ∃ (A : HLine ι1) (s : MRing ι1 ℂ),
      IsSmoothMetric ⊥ A ∧ IsFormSec ⊥ A s ∧ secNorm fubiniStudyLine (Xj 0) = secNorm A s) :=
  ⟨isProjVar_bot, fun j => by fin_cases j; exact isSmoothPot_logH (isSmoothMetric_fubiniStudyLine ⊥),
    Or.inr ⟨fubiniStudyLine, Xj 0, isSmoothMetric_fubiniStudyLine ⊥, isSec_bot_X 0, rfl⟩⟩

theorem S3.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) (0 + 1) ∧ Nonempty (Res ι1 ⊥ (0 + 1)) ∧
    (∀ j, IsSmoothMetric ⊥ ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothFn ⊥ (projectiveLineCoordinates 0) ∧
    IsSmoothFn ⊥ (projectiveLineCoordinates 1) :=
  ⟨isProjVar_bot, nonempty_resolution_projLine, fun j => j.elim0, isSmoothFn_projLineRatio ⊥ 0, isSmoothFn_projLineRatio ⊥ 1⟩

theorem ThreeSphereMass.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ Nonempty (Res ι1 ⊥ 1) ∧
    (∀ j, IsSmoothMetric ⊥ ((![fubiniStudyLine] : Fin 1 → HLine ι1) j)) ∧
    (∀ j, IsSmoothMetric ⊥ ((![fsTw] : Fin 1 → HLine ι1) j)) ∧
    (∀ j, ((![fubiniStudyLine] : Fin 1 → HLine ι1) j).a = ((![fsTw] : Fin 1 → HLine ι1) j).a) :=
  ⟨isProjVar_bot, nonempty_resolution_projLine, fun j => by fin_cases j; exact isSmoothMetric_fubiniStudyLine ⊥,
    fun j => by fin_cases j; exact isSmoothMetric_fsTw ⊥, fun j => by fin_cases j; exact fsTw_a.symm⟩

theorem S4.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ (∀ j, IsSmoothPot ⊥ ((![logH fubiniStudyLine] : Fin 1 → _) j)) ∧
    IsSmoothMetric ⊥ fubiniStudyLine ∧ IsFormSec (⊥ : Ideal (MRing ι1 ℂ)) fubiniStudyLine (Xj 0) :=
  ⟨isProjVar_bot, fun j => by fin_cases j; exact isSmoothPot_logH (isSmoothMetric_fubiniStudyLine ⊥),
    isSmoothMetric_fubiniStudyLine ⊥, isSec_bot_X 0⟩

theorem res_comps_bot (j : Fin 2) :
    ∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (Xj j), Nonempty (Res ι1 W 0) := by
  rw [comps_bot_X]
  rintro W rfl
  exact ⟨ptRes j⟩

theorem PoincareLelongAlt.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) (0 + 1) ∧ Nonempty (Res ι1 ⊥ (0 + 1)) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (Xj 0), Nonempty (Res ι1 W 0)) ∧
    (∀ j, IsSmoothMetric ⊥ ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothMetric ⊥ fubiniStudyLine ∧
    IsFormSec (⊥ : Ideal (MRing ι1 ℂ)) fubiniStudyLine (Xj 0) ∧ IsSmoothFn ⊥ (projectiveLineCoordinates 1) :=
  ⟨isProjVar_bot, nonempty_resolution_projLine, res_comps_bot 0, fun j => j.elim0, isSmoothMetric_fubiniStudyLine ⊥,
    isSec_bot_X 0, isSmoothFn_projLineRatio ⊥ 1⟩

theorem Degrees.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ Nonempty (Res ι1 ⊥ 1) ∧
    (∀ j, IsSmoothMetric ⊥ ((![fubiniStudyLine] : Fin 1 → HLine ι1) j)) :=
  ⟨isProjVar_bot, nonempty_resolution_projLine, fun j => by fin_cases j; exact isSmoothMetric_fubiniStudyLine ⊥⟩

theorem comps_disjoint {R : Type} [CommRing R] [IsDomain R] :
    ∀ W ∈ comps (⊥ : Ideal (MRing ι1 R)) (Xj 0), W ∉ comps ⊥ (Xj 1) := by
  rw [comps_bot_X, comps_bot_X]
  rintro W rfl h
  exact ptI_ne h

theorem ProjectiveLineTwo.analyticResolution_hypotheses_projectiveLine :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) (0 + 1) ∧ Nonempty (Res ι1 ⊥ (0 + 1)) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (Xj 0), Nonempty (Res ι1 W 0)) ∧ (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (Xj 1), Nonempty (Res ι1 W 0)) ∧
    (∀ j, IsSmoothMetric ⊥ ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothMetric ⊥ fubiniStudyLine ∧
    IsSmoothMetric ⊥ fsTw ∧ IsFormSec (⊥ : Ideal (MRing ι1 ℂ)) fubiniStudyLine (Xj 0) ∧ IsFormSec (⊥ : Ideal (MRing ι1 ℂ)) fsTw (Xj 1) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (Xj 0), W ∉ comps ⊥ (Xj 1)) :=
  ⟨isProjVar_bot, nonempty_resolution_projLine, res_comps_bot 0, res_comps_bot 1, fun j => j.elim0,
    isSmoothMetric_fubiniStudyLine ⊥, isSmoothMetric_fsTw ⊥, isSec_bot_X 0,
    by obtain ⟨a, ha, hs, hn⟩ := isSec_bot_X (R := ℂ) 1; exact ⟨a, fun k => by rw [fsTw_a]; exact ha k, hs, hn⟩,
    comps_disjoint⟩

theorem sC_Xj (j : Fin 2) : sC (Xj (R := ℚ) j) = Xj j := by
  simp [sC]

theorem BCMult.analyticResolution_hypotheses_projectiveLine :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧ IsMultiHomog (Xj (R := ℚ) 0) (fun _ => 1) ∧
    Xj 0 ∉ (⊥ : Ideal (MRing ι1 ℚ)) ∧ ptI 0 ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0) ∧
    ptI (R := ℂ) 0 ∈ (extC (ptI (R := ℚ) 0)).minimalPrimes :=
  ⟨isProjVarQ_bot, isMultiHomog_Xj 0, X_ne_bot _, by rw [comps_bot_X]; rfl,
    by rw [extC_ptI, minimalPrimes_ptI]; rfl⟩

theorem BCCommon.analyticResolution_hypotheses_projectiveLine :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧ IsMultiHomog (Xj (R := ℚ) 0) (fun _ => 1) ∧
    Xj 0 ∉ (⊥ : Ideal (MRing ι1 ℚ)) ∧ (⊥ : Ideal (MRing ι1 ℂ)) ∈ (extC ⊥).minimalPrimes ∧
    ptI 0 ∈ comps (⊥ : Ideal (MRing ι1 ℂ)) (sC (Xj 0)) :=
  ⟨isProjVarQ_bot, isMultiHomog_Xj 0, X_ne_bot _, by rw [extC_bot, minimalPrimes_bot_C]; rfl,
    by rw [sC_Xj, comps_bot_X]; rfl⟩

theorem BCDeg.analyticResolution_hypotheses_projectiveLine : IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) 1 := isProjVarQ_bot

theorem res_min_extC_bot (e : ℕ) (R : Res ι1 (⊥ : Ideal (MRing ι1 ℂ)) e) :
    ∀ Z ∈ (extC (⊥ : Ideal (MRing ι1 ℚ))).minimalPrimes, Nonempty (Res ι1 Z e) := by
  rw [extC_bot, minimalPrimes_bot_C]
  rintro Z rfl
  exact ⟨R⟩

theorem res_comps_extC (j : Fin 2) :
    ∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj j), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0) := by
  rw [comps_bot_X]
  rintro W rfl Z hZ
  rw [extC_ptI, minimalPrimes_ptI] at hZ
  rw [hZ]
  exact ⟨ptRes j⟩

theorem DegreesQ.analyticResolution_hypotheses_projectiveLine :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) 1 ∧
    (∀ Z ∈ (extC (⊥ : Ideal (MRing ι1 ℚ))).minimalPrimes, Nonempty (Res ι1 Z 1)) ∧
    (∀ j, IsSmoothMetric (extC ⊥) ((![fubiniStudyLine] : Fin 1 → HLine ι1) j)) :=
  ⟨isProjVarQ_bot, res_min_extC_bot 1 projLineResolution, fun j => by fin_cases j; exact isSmoothMetric_fubiniStudyLine _⟩

theorem ProjectiveLineOverRationals.analyticResolution_hypotheses_projectiveLine :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧
    (∀ Z ∈ (extC (⊥ : Ideal (MRing ι1 ℚ))).minimalPrimes, Nonempty (Res ι1 Z (0 + 1))) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0)) ∧
    (∀ j, IsSmoothMetric (extC ⊥) ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothMetric (extC ⊥) fubiniStudyLine ∧
    IsFormSec (⊥ : Ideal (MRing ι1 ℚ)) fubiniStudyLine (Xj 0) ∧ IsSmoothFn (extC ⊥) (projectiveLineCoordinates 1) :=
  ⟨isProjVarQ_bot, res_min_extC_bot 1 projLineResolution, res_comps_extC 0, fun j => j.elim0,
    isSmoothMetric_fubiniStudyLine _, isSec_bot_X 0, isSmoothFn_projLineRatio _ 1⟩

theorem ProjectivePlaneOverRationals.analyticResolution_hypotheses_projectiveLine :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧
    (∀ Z ∈ (extC (⊥ : Ideal (MRing ι1 ℚ))).minimalPrimes, Nonempty (Res ι1 Z (0 + 1))) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0)) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 1), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0)) ∧
    (∀ j, IsSmoothMetric (extC ⊥) ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothMetric (extC ⊥) fubiniStudyLine ∧
    IsSmoothMetric (extC ⊥) fubiniStudyLine ∧ IsFormSec (⊥ : Ideal (MRing ι1 ℚ)) fubiniStudyLine (Xj 0) ∧
    IsFormSec (⊥ : Ideal (MRing ι1 ℚ)) fubiniStudyLine (Xj 1) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0), W ∉ comps ⊥ (Xj 1)) :=
  ⟨isProjVarQ_bot, res_min_extC_bot 1 projLineResolution, res_comps_extC 0, res_comps_extC 1, fun j => j.elim0,
    isSmoothMetric_fubiniStudyLine _, isSmoothMetric_fubiniStudyLine _, isSec_bot_X 0, isSec_bot_X 1, comps_disjoint⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
