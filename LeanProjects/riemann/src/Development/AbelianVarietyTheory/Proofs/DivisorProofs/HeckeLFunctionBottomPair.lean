import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeVacuumReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTransversalCongruenceMulNormEqLocalNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIndexLocalNormNormalizingFactorEqPartialStatement

noncomputable section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type}
    (s : Finset ι) (G : ι → Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ) (f : ι → WO S T → ℂ) (h : ∀ i ∈ s, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ip_eq (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) : ip S T ν 𝓕 f g = GlobalTheory.Ker.ipO ν 𝓕 f g := rfl

theorem ip_sum_left (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 (∑ i ∈ s, f i) g = ∑ i ∈ s, ip S T ν 𝓕 (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_left hψ hν.1 hν.2.1 (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j) hg

theorem ip_sum_right (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 g (∑ i ∈ s, f i) = ∑ i ∈ s, ip S T ν 𝓕 g (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_right hψ hν.1 hν.2.1 hg (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j)

theorem isSphOff_sum {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i ∈ s, IsSphOff ψ S T LS LT Sf (f i)) : IsSphOff ψ S T LS LT Sf (∑ i ∈ s, f i) := by
  have key : ∀ u, (∀ i ∈ s, heisO ψ S T u (f i) = f i) → heisO ψ S T u (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    intro u hu
    funext w
    simp only [heisO, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => congrFun (hu i hi) w
  exact ⟨fun u hu => key _ fun i hi => (hf i hi).1 u hu, fun e he u hu hh => key _ fun i hi => (hf i hi).2 e he u hu hh⟩

theorem isSphOff_pure (hθ : IsInfFam θ) {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {f : WO S T → ℂ}
    (hf : IsSphOff ψ S T LS LT Sf f) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (p : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f p) :=
  ⟨fun u hu => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any (nsmul_mem hu 2)), hf.1 u hu],
   fun e he u hu hh => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any hu), hf.2 e he u hu hh]⟩

theorem volQ_eq_mass (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V) (h2 : Function.Injective ι) (h3 : ι.range = GfC V)
    (h4 : ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n)
    (h5 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K) (h6 : ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ intG D n)
    (h7 : Links.IsMeasDef V K μ 𝓕) : (volQ V μ : ℂ) = mass D n := by
  have h := (GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum V n ι (intG D n) K μ 𝓕 h1 h2 h3 h4 h5 h6 h7 (fun _ => 1)
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩).2.2
  simpa [GlobalTheory.AutomorphicL2Unitary.descend, volQ, mass] using h

theorem openOff_conj {V : HSp D} {L : Lat V} {Sf : Finset (FinPl D)} {a g b : GA D V} (ha : a ∈ openOff V L ∅)
    (hg : g ∈ openOff V L Sf) (hb : b ∈ openOff V L ∅) : a⁻¹ * g * b ∈ openOff V L Sf := fun v hv => by
  rw [map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem (ha v (Finset.notMem_empty v))) (hg v hv)) (hb v (Finset.notMem_empty v))

end General

section Translates

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)

theorem om_mul_one (om : GlobalTheory.Core.Rk.IP.WRep S T) (g g' : GA D S) (f : WO S T → ℂ) :
    om (g * g', 1) f = om (g, 1) (om (g', 1) f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem coef_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G) (x : G) :
    ip S T ν 𝓕 (om (ι x, 1) (∑ y ∈ R, om (ι y, 1) φ)) (∑ y ∈ R, om (ι y, 1) φ) =
      ∑ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * x * y), 1) φ) φ := by
  have hth : ∀ g : GA D S, IsThetaFunO ψ S T (om (g, 1) φ) := fun g => hom.om_pres _ _ hφ
  rw [map_sum]
  simp only [← om_mul_one]
  rw [ip_sum_left hom.std hν R _ (fun _ => hth _) ((GlobalTheory.FinWeilO.thetaSub _ _ _).sum_mem fun j _ => hth _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ip_sum_right hom.std hν R _ (fun _ => hth _) (hth _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have e : ι x * ι y = ι y' * ι (y'⁻¹ * x * y) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [ip_eq, ip_eq, ← GlobalTheory.Size.ipO_om hom hν.1 hν.2.1 (hth (ι (y'⁻¹ * x * y))) hφ (ι y', 1), ← om_mul_one, e]

theorem norm_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G)
    (h : ∀ y ∈ R, ∀ y' ∈ R, y' ≠ y → ip S T ν 𝓕 (om (ι (y'⁻¹ * y), 1) φ) φ = 0) :
    ip S T ν 𝓕 (∑ y ∈ R, om (ι y, 1) φ) (∑ y ∈ R, om (ι y, 1) φ) = (R.card : ℂ) * ip S T ν 𝓕 φ φ := by
  have h1 := coef_sum ι hom hν hφ R 1
  rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  have h2 : ∀ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * 1 * y), 1) φ) φ = ip S T ν 𝓕 φ φ := by
    intro y hy
    rw [Finset.sum_eq_single_of_mem y hy]
    · rw [mul_one, inv_mul_cancel, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    · intro y' hy' hne
      rw [mul_one]
      exact h y hy y' hy' hne
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]

theorem mem_of_conj_mem {H : Subgroup G} {a b x : G} (ha : a ∈ H) (hb : b ∈ H) (h : a⁻¹ * x * b ∈ H) : x ∈ H := by
  have := mul_mem (mul_mem ha h) (inv_mem hb)
  rwa [show a * (a⁻¹ * x * b) * b⁻¹ = x by group] at this

theorem openOff_conj_hom {L : Lat S} {Sf : Finset (FinPl D)} {a g b : G} (ha : ι a ∈ openOff S L ∅)
    (hg : ι g ∈ openOff S L Sf) (hb : ι b ∈ openOff S L ∅) : ι (a⁻¹ * g * b) ∈ openOff S L Sf := by
  rw [map_mul, map_mul, map_inv]
  exact openOff_conj ha hg hb

theorem norm_arith {A B C : ℂ} {c N e : ℕ} {n v L : ℝ} (h1 : A = (c : ℂ) * B) (h2 : B = ((N : ℂ) ^ e)⁻¹ * C) (h3 : C = n)
    (h4 : n = v) (h5 : (c : ℝ) * ((N : ℝ) ^ e)⁻¹ = L) : A = (L : ℂ) * (v : ℂ) := by
  rw [h1, h2, h3, h4, ← h5]
  push_cast
  ring

end Translates

section Exact

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D N) := fun i j => by simp

theorem vac_eq_of_reads (h : IsExact P X r) {G : Formalism.MainNotions.TaylorLogMetric.VC D P.a P.d → ℂ} {f : WO X.A X.B → ℂ} (hF : P.F = G)
    (h1 : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r G f) : X.vac = f := by
  subst hF
  exact h.read.unique h1

theorem vac_eq_sum (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) {o : ℕ}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hF : P.F = ∑ y ∈ R, P.W.Om y 1 (cosetVec P 𝔪 o)) {φ : WO X.A X.B → ℂ}
    (hφ : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ) : X.vac = ∑ y ∈ R, X.om (X.ιA y, 1) φ := by
  have h1 : ∀ y, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (P.W.Om y 1 (cosetVec P 𝔪 o)) (X.om (X.ιA y, 1) φ) := fun y => by
    have := h.reads_om hI y 1 (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o) hφ
    rwa [X.ιB.map_one] at this
  exact vac_eq_of_reads h hF (reads_sum R (fun y => P.W.Om y 1 (cosetVec P 𝔪 o)) (fun y => X.om (X.ιA y, 1) φ) fun y _ => h1 y)

theorem exists_reads_coset (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) (o : ℕ) :
    ∃ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup (cosetVec P 𝔪 o) (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o)

theorem exists_reads_vacuum (h : IsExact P X r) : ∃ f₀, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)

theorem mem_openOff (h : IsExact P X r) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∈ intG D P.a) (Sf : Finset (FinPl D)) :
    X.ιA x ∈ openOff X.A (stdLat X.A) Sf := fun v _ =>
  (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)).2.1 hx v (Finset.notMem_empty v)

theorem norm_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a)
    (hRu : ∀ k ∈ intG D P.a, ∃! y, y ∈ R ∧ CongOne D 𝔪 (y⁻¹ * k)) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) :
    ip X.A X.B ν 𝓕 (∑ y ∈ R, X.om (X.ιA y, 1) φ) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = (R.card : ℂ) * ip X.A X.B ν 𝓕 φ φ := by
  refine norm_sum X.ιA h.weil hν hφ R fun y hy y' hy' hne =>
    horth _ (mem_openOff h (mul_mem (inv_mem (hR y' hy')) (hR y hy)) Sf) fun hc => hne ?_
  have h1 : CongOne D 𝔪 (y⁻¹ * y) := by rw [inv_mul_cancel]; exact congOne_one 𝔪 _
  exact (hRu y (hR y hy)).unique ⟨hy', hc.2⟩ ⟨hy, h1⟩

theorem supp_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∉ intG D P.a)
    (hx' : X.ιA x ∈ openOff X.A (stdLat X.A) Sf) :
    ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) (∑ y ∈ R, X.om (X.ιA y, 1) φ)) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = 0 := by
  refine (coef_sum X.ιA h.weil hν hφ R x).trans ?_
  refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun y' hy' => horth _ ?_ fun hc => hx ?_
  · exact openOff_conj_hom X.ιA (mem_openOff h (hR y' hy') ∅) hx' (mem_openOff h (hR y hy) ∅)
  · exact mem_of_conj_mem (hR y' hy') (hR y hy) hc.1

theorem finite_data (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ}
    (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o) (ho : o + P.a ≤ P.d) :
    (∃ LB : Lat X.B, IsSelfDualC X.B LB ∧ IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf X.vac) ∧
    ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
      ip X.A X.B ν 𝓕 X.vac X.vac = (locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ) ∧
      ∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) X.vac) X.vac = 0 := by
  obtain ⟨R, hR, hRu, hF⟩ := hstd
  refine (exists_reads_coset h hm.1 o).elim fun φ hφ => ?_
  refine (exists_reads_vacuum h).elim fun f₀ hf₀ => ?_
  refine (GlobalTheory.T.exists_selfDualLattice_vacuumReading X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup).elim fun LB ⟨hLB, hz, hsph⟩ => ?_
  have hs₀ := hsph P.e0 P.vac.1 f₀ hf₀
  have hsd := (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA 1) 1 h.std.frame.gramA X.rkA (h.std.ptA 1)).1
  have hv := vac_eq_sum hI h hm.1 hF hφ
  have hsφ := GlobalTheory.T.thetaCosetIndicatorReading_spherical_off_modulus P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ
  have hs := isSphOff_sum R (fun y => X.om (X.ιA y, 1) φ) fun y hy =>
    GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer X.ψ X.A X.B X.χA X.χB X.om h.weil _ _ hsd hLB Sf _ (mem_openOff h (hR y hy) Sf) φ hφ.1 hsφ
  refine ⟨⟨LB, hLB, by rw [hv]; exact hs⟩, fun ν 𝓕 hν => ?_⟩
  have horth := GlobalTheory.T.cosetVector_orthogonal_translate_finite_point P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ho ν 𝓕 hν
  refine ⟨?_, fun x hx hx' => by rw [hv]; exact supp_transl h hR hφ.1 hν horth hx hx'⟩
  have h3 := GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ν 𝓕 hν
  have h4 := GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup LB hLB hz P.e0 P.vac.1 f₀ hf₀ hs₀ ν 𝓕 hν
  have h5 := GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm D 𝔪 hm.1 hm.2.1 P.a (P.d - P.a) R hR hRu
  rw [Nat.add_sub_cancel' P.a_le] at h5
  have h6 := norm_transl h hR hRu hφ.1 hν horth
  exact norm_arith (by rw [hv]; exact h6) h3 h4 P.vac.2.2.1 h5

end Exact

section Fock

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem var_injective (X : Data P) : Function.Injective X.var := by
  rintro ⟨τ, i, j⟩ ⟨τ', i', j'⟩ e
  simp only [Data.var, Prod.mk.injEq, Fin.cast_inj] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

theorem ip_fock (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) : ip X.A X.B ν 𝓕 (X.fock T) (X.fock T) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) * ip X.A X.B ν 𝓕 X.vac X.vac := by
  have h := GlobalTheory.FockIsometry.ipO_pureTensorO D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank) (fun _ => le_rfl) (fun _ => le_rfl)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) X.vac hX.2.vac_theta hX.2.vac_fock
    ν 𝓕 hν (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T)) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) := by
    rw [GlobalTheory.FockCoefReal.fockIp_eq_fock, GlobalTheory.LowRowFock.fock_rename_inj (var_injective X), ← GlobalTheory.FockCoefReal.fockIp_eq_fock]
  have e2 : ip X.A X.B ν 𝓕 X.vac X.vac = (nrm2 ν 𝓕 X.vac : ℂ) := GlobalTheory.Size.ipO_self ν 𝓕 X.vac
  exact h.trans (by rw [e, e2])

theorem ip_fock_zero (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) {g : GA D X.A} (hg : g ∈ GfC X.A) (h0 : ip X.A X.B ν 𝓕 (X.om (g, 1) X.vac) X.vac = 0) :
    ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) = 0 := by
  refine (GlobalTheory.FockCoefSplit.pair_eq_inf D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) ν 𝓕 hν 1 (one_mem _) 1 (one_mem _)
    (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))).elim fun c hc => ?_
  have h1 := hc X.vac (X.om (g, 1) X.vac) hX.2.vac_theta (hX.2.weil.om_pres _ _ hX.2.vac_theta) hX.2.vac_fock
    fun τ => GlobalTheory.FockCoefSplit.fockVac_om_fin hX.2.weil hX.2.inf hg (one_mem _) τ _ hX.2.vac_theta (hX.2.vac_fock τ)
  have h2 := GlobalTheory.FockCoefSplit.om_fin_pureTensorO hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) hg
    (one_mem (GfC X.B)) hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  rw [GlobalTheory.VacPairSchur.thetaIP_eq_ipO, GlobalTheory.VacPairSchur.thetaIP_eq_ipO, ← h2, Prod.mk_one_one, X.om.map_one,
    Module.End.one_apply, ← ip_eq, ← ip_eq, h0, mul_zero] at h1
  exact h1

theorem isFockVec_fock (hX : IsDict P X) (T : Tup D P.a P.d P.n) :
    IsFockVec X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (X.fock T) :=
  GlobalTheory.FockSph.isFockVec_pureTensorO (sS := fun _ => 1) (sT := fun _ => 1) hX.2.weil.std hX.2.inf
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB) (fun _ => 1) (fun _ => 1)
    hX.2.vac_theta hX.2.vac_fock _

theorem wcoef_fock (hX : IsDict P X) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)) (T : Tup D P.a P.d P.n)
    (g : GA D X.A) {k : GA D X.A} (hk : k ∈ GinfC X.A) : wcoef X.om ν 𝓕 (X.fock T) (X.fock T) (g * k) =
      ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) := by
  rw [wcoef, om_mul_one, GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors P X hX hX.2.infB k hk T]

end Fock

section Norm

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem petersson_eq (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (hX : IsDict P X)
    {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))} {μ₀ : Measure (GA D X.B)} (hK : IsMaxLevel X.toFrame K₀ μ₀)
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ} (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o)
    (ho : o + P.a ≤ P.d) (ha : 1 ≤ P.a) (had : P.a < P.d) (hu : GlobalTheory.LFun.UnrOff X.χB (Sf : Set (FinPl D))) (Λ : ℂ → ℂ)
    (hΛ : ∀ s, GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL X.χB⁻¹ (Sf : Set (FinPl D))) s (Λ s)) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) =
      mass D P.d * mass D P.a * ((∏ i ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - i)) /
        GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) P.a P.d (((P.d - P.a : ℕ) : ℂ) / 2)) *
        (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) *
          ((locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ))) := by
  refine (GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan P X hX ha had).elim fun cA h1 => h1.elim fun a h2 => h2.elim fun ν h3 => h3.elim fun 𝓕 hPair => ?_
  have hfd := finite_data hI h hm hstd ho
  refine hfd.1.elim fun LB hLB => ?_
  have hn := (hfd.2 ν 𝓕 hPair.covol).1
  have hs := (hfd.2 ν 𝓕 hPair.covol).2
  have hlev := fun x => GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)
  have hsph : IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf (X.fock T) := isSphOff_pure hX.2.inf hLB.2 _ _ _ _ _
  have hU : GlobalTheory.Core.Rk.IP.Unram X.ψ X.A X.B X.χB (stdLat X.A) LB Sf (X.fock T) (X.fock T) :=
    ⟨(hlev 1).1, hLB.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2, hu, hsph, hsph⟩
  have hint := GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact P X hX (hlev 1).1 (fun x => (hlev x).2) a ν 𝓕 hPair.maj Sf (X.fock T)
    (ip X.A X.B ν 𝓕 (X.fock T) (X.fock T))
    (fun x hx k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (by rw [hX.2.fixA x hx T]))
    (fun x hx hx' k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (ip_fock_zero hX hPair.covol T (h.std.ptA x).1 (hs x hx hx')))
  refine hK.meas.elim fun 𝓕₀ h𝓕₀ => hX.1.measA.elim fun 𝓕A h𝓕A => ?_
  haveI := hX.1.haarA
  haveI : μ₀.IsHaarMeasure := h𝓕₀.1.1
  have hA : GlobalTheory.Cusp.wittIndex X.A = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramA)
  have hB : GlobalTheory.Cusp.wittIndex X.B = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramB)
  have key := GlobalTheory.BottomRallis.norm_eq hP hPair hA hB (isFockVec_fock hX T) hU X.m μ₀
    ⟨((P.d - P.a : ℕ) : ℝ) / 2 - 1, by linarith, hint.1 _⟩
    (fun i => Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (X.A.rank : ℂ) / 2 - i)) fun i _ => hΛ _
  have vA := volQ_eq_mass X.A P.a X.ιA X.KA X.m 𝓕A hX.1.defA hX.1.injA hX.1.rangeA hX.1.ratA hX.1.levA hX.1.levA_iff h𝓕A
  have vB := volQ_eq_mass X.B P.d X.ιB K₀ μ₀ 𝓕₀ hX.1.defB hX.1.injB hX.1.rangeB hX.1.ratB hK.lev hK.mem_iff h𝓕₀
  have e1 := hint.2.trans ((ip_fock hX hPair.covol T).trans (congrArg _ hn))
  refine key.trans ?_
  rw [vA, vB, e1, X.rkA, X.rkB]

def normFactor (D : D7) (δ t0 : ℂ) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  (normConst D ⊤ δ a n : ℂ) * mass D d * mass D a * fockSum D a d n * (vacNorm D ⊤ δ t0 a d : ℂ) /
    GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a d (((d - a : ℕ) : ℂ) / 2)

theorem collect {c I mB mA L dS d0 F l v : ℂ} (h : I * l * d0 = dS) (h0 : d0 ≠ 0) (hS : dS ≠ 0) :
    c * I * (mB * mA * (L / dS) * (F * (l * v))) = c * mB * mA * F * v / d0 * L := by
  rw [← h] at hS ⊢
  have h1 : I ≠ 0 := fun e => hS (by rw [e]; simp)
  have h2 : l ≠ 0 := fun e => hS (by rw [e]; simp)
  field_simp

theorem norm_bottom (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) {T : Type}
    {L : LevCh D T} {sc : Consts} {μ : T} (hL : L.Is μ) (G : GridData L sc) {t : T} {i j : Fin D.R.m}
    {P' : Pair D ⊤ δ t0 Q} (hb : IsBottom G t i j (modT G t) P P') {Λ : ℂ → ℂ} (hΛ : GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ) :
    (P.norm : ℂ) = normFactor D δ t0 P.a P.d P.n *
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  have hm := goodMod_modT hL (GlobalTheory.SqTop.BotT.pde_ne_q hR).1 (GlobalTheory.SqTop.BotT.pde_ne_q hR).2 G t
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hdict := exact_dictionary P hI (isCongLevel_of_isBlockLevel hm.1 hb.lev.1)
  refine hdict.2.1.elim fun X h1 => h1.elim fun r h2 => h2.elim fun K₀ h3 => h3.elim fun μ₀ h4 => ?_
  have h5 := hdict.2.2 X r K₀ μ₀ h4.1 h4.2
  have hX := h5.1.1
  have hχ := GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse X.χB P.W.chV' P.W.ep' (nuH G t i j) hX.2.weil.hecT h4.1.chB hb.chars.2
  have hl := GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive hL hR.hF G t i j X.χB hχ
  have hT := petersson_eq hP hI h4.1 hX h4.2 hm hb.std (by rw [zero_add]; exact P.a_le) (by omega) (by omega) hl.1 Λ
    (hl.2 Λ hΛ)
  have hidx : ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = locIdx D (modT G t) P.a (P.d - P.a) :=
    GlobalTheory.StdLoc.relIndex_blockLevel P (modT G t) P.a hm.1 hm.2.1 P.a_le (hPa.symm ▸ hb.lev.1)
  have hidx' : ((P.J.relIndex (intG D P.d) : ℕ) : ℂ) = (locIdx D (modT G t) P.a (P.d - P.a) : ℂ) := by
    rw [← hidx]; rfl
  have hd := GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial D (modT G t) (sfB G t) hm P.a (P.d - P.a) (by omega)
  rw [Nat.add_sub_cancel' P.a_le] at hd
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hprod : ∏ k ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - k) =
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
    obtain ⟨u, hu⟩ := hrk.2.2.1
    have e1 : P.d = 2 * GlobalTheory.SqTop.h0 D i j := by unfold GlobalTheory.SqTop.h0; omega
    rw [← GlobalTheory.BottomRallis.prod_range_sub_eq_prod_Icc (fun s => Λ s) P.a (GlobalTheory.SqTop.h0 D i j) (GlobalTheory.SqTop.e0 D i j)
      (by unfold GlobalTheory.SqTop.h0 GlobalTheory.SqTop.e0; omega)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    rw [Nat.cast_sub P.a_le, e1]
    push_cast
    ring
  refine h5.2.2.2.2.trans ?_
  rw [Finset.sum_congr rfl fun T _ => hT T, ← Finset.mul_sum, ← Finset.sum_mul, hidx', hprod]
  exact collect hd (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)

end Norm

theorem normBig_ratio : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  intro hP hI _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 i j t t' Q Q' P P' P₁ P₁' Λ Λ' hb hb' hΛ hΛ'
  have h1 := norm_bottom hP (hI D) hR hL G hb hΛ
  have h2 := norm_bottom hP (hI D) hR hL G hb' hΛ'
  have h3 := (GlobalTheory.BottomReal.bottom_real_eq G hL hb hb').1
  have h4 : normFactor D δ t0 P.a P.d P.n = normFactor D δ t0 P₁.a P₁.d P₁.n :=
    congr (congr (congrArg (normFactor D δ t0) h3.1) h3.2.1) h3.2.2.1
  rw [h1, h2, h4]
  ring

end GlobalTheory.NormRatio
