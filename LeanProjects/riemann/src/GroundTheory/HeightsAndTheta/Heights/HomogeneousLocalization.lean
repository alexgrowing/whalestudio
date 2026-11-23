import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory MeasureTheory
  NumberField TensorProduct GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

lemma point_self {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) :
    (self A N).point x = projPoint ρ x.1 :=
  (self A N).ι_point x

def selfPoint (ρ : A →+* ℂ) (v : CP N) : (self A N).complexPoints ρ :=
  ⟨v, by rw [complexPoints_self]; trivial⟩

lemma rep_chartIndex_ne_zero (v : CP N) : v.rep (CP.chartIndex v) ≠ 0 := by
  have h := CP.mk_mem_chartDomain (CP.chartIndex v) v.rep v.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h.mp (CP.mem_chartDomain_chartIndex v)

lemma point_mem_stdOpen {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) {j : Fin (N + 1)}
    (hj : x.1.rep j ≠ 0) : (self A N).point x ∈ ProjSpace.stdOpen A N j := by
  rw [point_self]
  change (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∉ (projPoint ρ x.1).asHomogeneousIdeal
  intro h
  have := (isOver_projPoint ρ x.1 1 (MvPolynomial.X j) (ProjSpace.X_mem j)).1 h
  simp [evalAt] at this
  exact hj this

variable (A N) in

def twistN (n : ℕ) : (self A N).X.Modules :=
  twistingSheaf (ProjSpace.grading A N) (n : ℤ)

theorem isInvertibleSheaf_twistN (n : ℕ) : IsInvertibleSheaf (twistN A N n) :=
  ProjSpace.isInvertibleSheaf_twistingSheaf _

variable (A) in

def stdFrame (j : Fin (N + 1)) (n : ℕ) :
    ((preMod (self A N).X).obj (twistN A N n)).obj (op (ProjSpace.stdOpen A N j)) :=
  ProjTwist.upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)

theorem isBasisOn_frame (j : Fin (N + 1)) (n : ℕ) :
    IsBasisOn ((preMod (self A N).X).obj (twistN A N n)) (ProjSpace.stdOpen A N j) (stdFrame A j n) :=
  ProjTwist.isBasisOn_upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)

def fsFrameCoord (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ) :
    (self A N).Fibre (twistN A N n) x ≃ₗ[ℂ] ℂ :=
  fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x (rep_chartIndex_ne_zero x.1))
    (isBasisOn_frame (A := A) (CP.chartIndex x.1) n)

def fsFibreNorm (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (s : (self A N).Fibre (twistN A N n) x) : ℝ :=
  ‖fsFrameCoord n ρ x s‖ * ‖x.1.rep (CP.chartIndex x.1)‖ ^ n / norm2 x.1.rep ^ n

theorem fsFibreNorm_smul (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ) (c : ℂ)
    (s : (self A N).Fibre (twistN A N n) x) :
    fsFibreNorm n ρ x (c • s) = ‖c‖ * fsFibreNorm n ρ x s := by
  rw [fsFibreNorm, fsFibreNorm, LinearEquiv.map_smul, smul_eq_mul, norm_mul]
  ring

theorem fsFibreNorm_pos (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (s : (self A N).Fibre (twistN A N n) x) (hs : s ≠ 0) : 0 < fsFibreNorm n ρ x s := by
  have h1 : 0 < ‖fsFrameCoord n ρ x s‖ :=
    norm_pos_iff.mpr fun h => hs ((fsFrameCoord n ρ x).map_eq_zero_iff.mp h)
  have h2 := norm_pos_iff.mpr (rep_chartIndex_ne_zero x.1)
  have h3 := euclideanNorm_pos x.1.rep_nonzero
  unfold fsFibreNorm
  positivity

def polyFun (P : MvPolynomial (Fin (N + 1)) A) (U : Opens (ProjectiveSpectrum.top (ProjSpace.grading A N))) :
    ∀ x : U, ProjTwist.Loc (ProjSpace.grading A N) x.1 :=
  fun _ => Localization.mk P 1

lemma isLocallyFraction_polyFun {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (U : Opens (ProjectiveSpectrum.top (ProjSpace.grading A N))) :
    (ProjTwist.isLocallyFraction (ProjSpace.grading A N) (n : ℤ)).pred (polyFun P U) := fun x =>
  ⟨U, x.2, 𝟙 _, 0, n, by simp, P, 1, hP, SetLike.GradedOne.one_mem,
    fun y h => y.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), fun _ => rfl⟩

def polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n) :
    (self A N).H0 (twistN A N n) :=
  ProjTwist.mkSection (polyFun P ⊤) (isLocallyFraction_polyFun hP ⊤)

lemma monomial_mem_grading (a : Fin (N + 1) →₀ ℕ) {n : ℕ} (ha : a.degree = n) :
    MvPolynomial.monomial a (1 : A) ∈ ProjSpace.grading A N n :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_monomial 1 ha)

theorem polySection_ne_zero [IsDomain A] {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (hP0 : P ≠ 0)
    (x : ProjectiveSpectrum (ProjSpace.grading A N)) : polySection hP ≠ 0 := by
  intro h
  have h1 : (Localization.mk P 1 : ProjTwist.Loc (ProjSpace.grading A N) x) = 0 :=
    congrArg (fun s : (self A N).H0 (twistN A N n) =>
      (show Γ(twistingSheaf (ProjSpace.grading A N) (n : ℤ), ⊤) from s).1 ⟨x, trivial⟩) h
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h1
  obtain ⟨⟨c, hc⟩, hcP⟩ := h1
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ Ideal.zero_mem _)
  exact hP0 ((mul_eq_zero.mp hcP).resolve_left hc0)

end ProjScheme

namespace SectionsLatticeFS

open ProjScheme

def PNFlat.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ), Flat (self A N).toBase

def PNReduced.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsReduced A] (N : ℕ), IsReduced (self A N).X

def FSContinuousFrame.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (U : (self A N).X.Opens)
    (e : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)),
    IsBasisOn ((preMod (self A N).X).obj (twistN A N n)) U e →
      Continuous fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} =>
        fsFibreNorm n ρ y.1 ((self A N).sectionValue y.1 y.2 e)

def FSNormConj.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (U : (self A N).X.Opens)
    (s : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)) (x : (self A N).complexPoints ρ)
    (hx : (self A N).point x ∈ U) (hx' : (self A N).point ((self A N).conjPoint ρ x) ∈ U),
      fsFibreNorm n ((starRingEnd ℂ).comp ρ) ((self A N).conjPoint ρ x)
          ((self A N).sectionValue _ hx' s) =
        fsFibreNorm n ρ x ((self A N).sectionValue x hx s)

def FSValue.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (P : MvPolynomial (Fin (N + 1)) A)
    (hP : P ∈ ProjSpace.grading A N n) (x : (self A N).complexPoints ρ),
      fsFibreNorm n ρ x ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) =
        CP.fsNormPoly n (MvPolynomial.map ρ P) x.1

def FSFullSupport.Statement : Prop :=
  ∀ (N : ℕ) (U : Set (CP N)), IsOpen U → U.Nonempty → 0 < CP.fsMeasure N U

def FSConjInvariant.Statement : Prop :=
  ∀ N : ℕ, (CP.fsMeasure N).map CP.conj = CP.fsMeasure N

def PolySections.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ),
    ∃ e : ProjSpace.grading A N n ≃ₗ[A] (self A N).H0 (twistN A N n),
      ∀ P : ProjSpace.grading A N n, e P = polySection P.2

def MonomialBasis.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ),
    ∃ b : Module.Basis {a : Fin (N + 1) →₀ ℕ // a.degree = n} A ((self A N).H0 (twistN A N n)),
      ∀ a, b a = polySection (monomial_mem_grading (A := A) a.1 a.2)

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

variable {A : Type u} [CommRing A] {N : ℕ}

def fsMetric (hf : FSContinuousFrame.Statement.{u}) (hc : FSNormConj.Statement.{u}) (n : ℕ) :
    (self A N).ContinuousMetric (twistN A N n) where
  norm ρ x s := fsFibreNorm n ρ x s
  norm_smul ρ x c s := fsFibreNorm_smul n ρ x c s
  norm_pos ρ x s hs := fsFibreNorm_pos n ρ x s hs
  continuous_frame ρ U e he := hf A N n ρ U e he
  norm_conj ρ U s x hx hx' := hc A N n ρ U s x hx hx'

def fsBundle (hf : FSContinuousFrame.Statement.{u}) (hc : FSNormConj.Statement.{u}) (n : ℕ) :
    (self A N).HermitianLineBundle :=
  ⟨twistN A N n, isInvertibleSheaf_twistN n, fsMetric hf hc n⟩

variable (K : Type) [Field K] [NumberField K]

def fsPointMeasures (N : ℕ) (hs : FSFullSupport.Statement) (hc : FSConjInvariant.Statement) :
    (self (𝓞 K) N).PointMeasures where
  μ _ := CP.fsMeasure N
  isFinite _ := inferInstance
  null_compl σ := by rw [complexPoints_self, Set.compl_univ, measure_empty]
  pos_of_isOpen σ U hU hne := hs N U hU (hne.mono Set.inter_subset_left)
  map_conj σ := (hc N).symm

def fsSupNorm (n : ℕ) (σ : K →+* ℂ) (t : Heights.Fibre σ ((self (𝓞 K) N).H0 (twistN (𝓞 K) N n))) : ℝ :=
  ⨆ x : (self (𝓞 K) N).complexPoints (intEmb σ),
    fsFibreNorm n (intEmb σ) x ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N n) σ x t)

variable {K} in

def fsFibreInner (n : ℕ) {ρ : 𝓞 K →+* ℂ} (x : (self (𝓞 K) N).complexPoints ρ)
    (v w : (self (𝓞 K) N).Fibre (twistN (𝓞 K) N n) x) : ℂ :=
  ((((fsFibreNorm n ρ x (v + w)) ^ 2 - (fsFibreNorm n ρ x (v - w)) ^ 2 : ℝ) : ℂ) +
    (((fsFibreNorm n ρ x (v - Complex.I • w)) ^ 2 -
      (fsFibreNorm n ρ x (v + Complex.I • w)) ^ 2 : ℝ) : ℂ) * Complex.I) / 4

open Classical in

def fubiniStudyL2Inner (n : ℕ) (μ : Measure (CP N)) (σ : K →+* ℂ)
    (t u : Heights.Fibre σ ((self (𝓞 K) N).H0 (twistN (𝓞 K) N n))) : ℂ :=
  ∫ v, (if h : v ∈ (self (𝓞 K) N).complexPoints (intEmb σ) then
      fsFibreInner n ⟨v, h⟩ ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N n) σ ⟨v, h⟩ t)
        ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N n) σ ⟨v, h⟩ u)
    else 0) ∂μ

variable {K}

omit [NumberField K] in

theorem l2Inner_eq_fubiniStudyL2Inner {n : ℕ} (m : (self (𝓞 K) N).ContinuousMetric (twistN (𝓞 K) N n))
    (hm : ∀ ρ x s, m.norm ρ x s = fsFibreNorm n ρ x s) (μ : Measure (CP N)) (σ : K →+* ℂ) (t u) :
    (self (𝓞 K) N).l2Inner ⟨twistN (𝓞 K) N n, isInvertibleSheaf_twistN n, m⟩ μ σ t u =
      fubiniStudyL2Inner K n μ σ t u := by
  simp only [l2Inner, fibreInner, fubiniStudyL2Inner, fsFibreInner, hm]

omit [NumberField K] in

theorem l2Inner_fubiniStudyBundle (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0})
    (n : ℕ) (μ : Measure (CP N)) (σ : K →+* ℂ) (t u) :
    (self (𝓞 K) N).l2Inner (fsBundle hf hc n) μ σ t u = fubiniStudyL2Inner K n μ σ t u :=
  l2Inner_eq_fubiniStudyL2Inner _ (fun _ _ _ => rfl) μ σ t u

end ProjScheme

namespace SectionsLatticeFS

open ProjScheme

def SupMonomial.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (σ : K →+* ℂ) (a : Fin (N + 1) →₀ ℕ),
    fsSupNorm K a.degree σ
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl)) =
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree)

def L2MonomialOrthogonality.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (σ : K →+* ℂ) (a b : Fin (N + 1) →₀ ℕ)
    (hb : b.degree = a.degree),
    fubiniStudyL2Inner K a.degree (CP.fsMeasure N) σ
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl))
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) b hb)) =
      if a = b then
        (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial : ℝ) : ℂ)
      else 0

variable {K : Type} [Field K] [NumberField K] {N : ℕ}

def fsSectionsHermitian (hfin : SectionsLattice.Finite.Statement) (hl2 : SectionsLattice.L2.Statement)
    (hflat : PNFlat.Statement.{0}) (hred : PNReduced.Statement.{0})
    (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0})
    (hs : FSFullSupport.Statement) (hci : FSConjInvariant.Statement) (n : ℕ) : HermitianBundle K :=
  SectionsLattice.sectionsHermitian hfin hl2 (self (𝓞 K) N) (hflat (𝓞 K) N) (hred (𝓞 K) N)
    (fsBundle hf hc n) (fsPointMeasures K N hs hci)

def fsSectionsNormed (hfin : SectionsLattice.Finite.Statement) (hsup : SectionsLattice.SupNorm.Statement)
    (hflat : PNFlat.Statement.{0}) (hred : PNReduced.Statement.{0})
    (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0}) (n : ℕ) : NormedBundle K :=
  SectionsLattice.sectionsNormed hfin hsup (self (𝓞 K) N) (hflat (𝓞 K) N) (hred (𝓞 K) N)
    (fsBundle hf hc n)

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

def pointQ : (self (𝓞 ℚ) 1).complexPoints (intEmb (Rat.castHom ℂ)) :=
  selfPoint _ (basePoint 1)

lemma pointQ_mem : (self (𝓞 ℚ) 1).point pointQ ∈ ProjSpace.stdOpen (𝓞 ℚ) 1 0 := by
  refine point_mem_stdOpen pointQ ?_
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ)
    (by simp [funext_iff, Pi.single_apply])
  change (basePoint 1).rep 0 ≠ 0
  rw [basePoint, ← ha]
  simp [Units.smul_def]

example : IsInvertibleSheaf (twistN (𝓞 ℚ) 1 1) := isInvertibleSheaf_twistN 1

example : 0 < fsFibreNorm 1 _ pointQ
    ((self (𝓞 ℚ) 1).sectionValue pointQ pointQ_mem (stdFrame (𝓞 ℚ) 0 1)) :=
  fsFibreNorm_pos _ _ _ _ (value_ne_zero _ (isBasisOn_frame 0 1))

example : polySection (N := 1) (ProjSpace.X_mem (A := 𝓞 ℚ) 0) ≠ 0 :=
  polySection_ne_zero _ (MvPolynomial.X_ne_zero 0) (projPoint (intEmb (Rat.castHom ℂ)) (basePoint 1))

example : IsBasisOn ((preMod (self (𝓞 ℚ) 1).X).obj (twistN (𝓞 ℚ) 1 1)) (ProjSpace.stdOpen (𝓞 ℚ) 1 0)
    (stdFrame (𝓞 ℚ) 0 1) :=
  isBasisOn_frame 0 1

example : (Finsupp.single (0 : Fin 2) 1).degree = 1 := by simp

example : IsOpen (Set.univ : Set (CP 1)) ∧ (Set.univ : Set (CP 1)).Nonempty :=
  ⟨isOpen_univ, Set.univ_nonempty⟩

end ProjScheme

end

end GroundTheory.Heights₂.Heights
