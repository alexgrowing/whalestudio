import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRelOfLocalMatching
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSBOfIsNatDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Zact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicVectorThetaTransformHeisenbergDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareIdent

section Real

open GlobalTheory.FockAdjoint GlobalTheory.SquareDict.AlgSmall GlobalTheory.RouteSeesaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S U U' : HSp D}

def sumVar (U U' : HSp D) (n : ℕ) : FVar D U.rank n ⊕ FVar D U'.rank n ≃ FVar D (GlobalTheory.Doubling.hsum U U').rank n where
  toFun := Sum.elim (fun v => (v.1, Fin.castAdd U'.rank v.2.1, v.2.2)) fun v => (v.1, Fin.natAdd U.rank v.2.1, v.2.2)
  invFun w := Sum.map (fun x => (w.1, x, w.2.2)) (fun z => (w.1, z, w.2.2)) (finSumFinEquiv.symm w.2.1)
  left_inv := by rintro (⟨τ, x, y⟩ | ⟨τ, y, z⟩) <;> simp
  right_inv := by
    rintro ⟨τ, k, y⟩
    obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := U.rank) (n := U'.rank)).surjective k
    rcases s with s | s <;> simp

theorem fockVector_product_mul_polynomials (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) (B' : Fr U') {f : WO S U → ℂ}
    {g : WO S U' → ℂ} (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) (P : PolF D U.rank S.rank)
    (Q : PolF D U'.rank S.rank) :
    box2 (ptF ψ θ A B f P) (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g)
      (GlobalTheory.SquareRel.polTens (sumVar U U' S.rank) (P ⊗ₜ Q)) := by
  have hfg := isThetaFunction_externalProductOnHermitianSum hf hg
  rw [GlobalTheory.SquareRel.polTens_tmul]
  have H : box2 f (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g)
      (MvPolynomial.rename (sumVar U U' S.rank ∘ Sum.inr) Q) := by
    induction Q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
      funext x; simp only [box2, Pi.smul_apply, smul_eq_mul]; ring
    | add p q hp hq =>
      rw [map_add, ptF_add, ptF_add, ← hp, ← hq]
      funext x; simp only [box2, Pi.add_apply]; ring
    | mul_X p v hp =>
      obtain ⟨τ, i, j⟩ := v
      rw [map_mul, MvPolynomial.rename_X, mul_comm (MvPolynomial.rename _ p), ptF_X_mul hψ hθ A _ hfg, ← hp, mul_comm p,
        ptF_X_mul hψ hθ A B' hg, show (sumVar U U' S.rank ∘ Sum.inr) (τ, i, j) = (τ, Fin.natAdd _ i, j) from rfl]
      dsimp only
      rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ hf (ptF_theta hψ hθ A B' hg p)]
      erw [((pr_unit B B' τ _ j).2 i).1, ((pr_unit B B' τ _ j).2 i).2]
      rw [aPlus_zero τ hψ hθ hf]
      funext x; simp [box2]
  have hg' := ptF_theta hψ hθ A B' hg Q
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, ptF_C, ← H, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one, externalProductOnHermitianSum_smul_left]
  | add p q hp hq => rw [map_add, add_mul, ptF_add, ptF_add, ← hp, ← hq, externalProductOnHermitianSum_add_left]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, MvPolynomial.rename_X, mul_comm (MvPolynomial.rename _ p), mul_assoc, ptF_X_mul hψ hθ A _ hfg, ← hp,
      mul_comm p, ptF_X_mul hψ hθ A B hf, show (sumVar U U' S.rank ∘ Sum.inl) (τ, i, j) = (τ, Fin.castAdd _ i, j) from rfl]
    dsimp only
    rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ (ptF_theta hψ hθ A B hf p) hg']
    erw [((pr_unit B B' τ _ j).1 i).1, ((pr_unit B B' τ _ j).1 i).2]
    rw [aPlus_zero τ hψ hθ hg']
    funext x; simp [box2]

theorem ptF_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S U → ℂ) (hf : ∀ i ∈ s, IsThetaFunO ψ S U (f i)) (P : PolF D U.rank S.rank) :
    IsThetaFunO ψ S U (∑ i ∈ s, c i • f i) ∧ ptF ψ θ A B (∑ i ∈ s, c i • f i) P = ∑ i ∈ s, c i • ptF ψ θ A B (f i) P := by
  classical
  have lin : ∀ (a : ℂ) (g g' : WO S U → ℂ), IsThetaFunO ψ S U g → IsThetaFunO ψ S U g' →
      ptF ψ θ A B (a • g + g') P = a • ptF ψ θ A B g P + ptF ψ θ A B g' P := by
    intro a g g' hg hg'
    induction P using MvPolynomial.induction_on with
    | C b =>
      rw [← mul_one (MvPolynomial.C b), ptF_C, ptF_C, ptF_C, ptF_one, ptF_one, ptF_one, smul_add, smul_comm]
    | add p q hp hq => rw [ptF_add, ptF_add, ptF_add, hp, hq, smul_add]; abel
    | mul_X p v hp =>
      rw [mul_comm p, ptF_X_mul hψ hθ A B (GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul a hg) hg'),
        ptF_X_mul hψ hθ A B hg, ptF_X_mul hψ hθ A B hg', hp,
        GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul a (ptF_theta hψ hθ A B hg p))
          (ptF_theta hψ hθ A B hg' p), GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a (ptF_theta hψ hθ A B hg p)]
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.sum_empty]; exact GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    have := lin (-1) 0 0 GlobalTheory.OrientedHeis.theta_zero GlobalTheory.OrientedHeis.theta_zero
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using this
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have h3 := hf i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lin _ _ _ h3 h1, h2]
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ h3) h1, rfl⟩

theorem exists_adj_equiv (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) :
    ∃ J : PolF D S.rank U.rank →ₗ[ℂ] PolF D U.rank S.rank, Function.Surjective J ∧ ∀ g, IsVacF ψ θ B A g → ∀ P,
      (fun y => ptF ψ θ B A g P (adjM S U y)) = ptF ψ θ (GlobalTheory.SquareComm.frSgn true A) B (fun y => g (adjM S U y)) (J P) := by
  obtain ⟨j, hjs, hj⟩ := fock_dag D ψ θ hψ hθ U S B A
  have cc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  refine ⟨⟨⟨fun P => MvPolynomial.map (starRingEnd ℂ) (j P), fun P Q => by rw [map_add, map_add]⟩, fun c P => ?_⟩,
    fun Q => ⟨j.symm (MvPolynomial.map (starRingEnd ℂ) Q), ?_⟩, fun g hg P => ?_⟩
  · show MvPolynomial.map _ (j (c • P)) = c • MvPolynomial.map _ (j P)
    rw [hjs, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Complex.conj_conj, MvPolynomial.smul_eq_C_mul]
  · show MvPolynomial.map _ (j (j.symm _)) = _
    rw [AddEquiv.apply_symm_apply, MvPolynomial.map_map, cc, MvPolynomial.map_id]
  obtain ⟨hv, hP⟩ := hj g hg
  have e : ∀ φ : WO U S → ℂ, (fun y => φ (adjM S U y)) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.PairLift.dag U S φ) := fun φ => by
    funext y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, GlobalTheory.PairLift.dag, Complex.conj_conj]
    rfl
  have hc := GlobalTheory.SquareAlg.isVacF_cj hψ hθ A B hv
  have h := GlobalTheory.FockConjNeg.cj_ptF_neg hψ hθ A B hc.1 (MvPolynomial.map (starRingEnd ℂ) (j P))
  rw [GlobalTheory.CjNeg.cj_id_cj_id, MvPolynomial.map_map, cc, MvPolynomial.map_id, hP] at h
  rw [e g, e, ← h, GlobalTheory.CjNeg.cj_id_cj_id]
  rfl

theorem exists_rd_equiv (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) :
    ∃ J : PolF D S.rank U.rank →ₗ[ℂ] PolF D U.rank S.rank, Function.Surjective J ∧ ∀ g, IsThetaFunO ψ (negSp U) S g → ∀ P,
      rd S U (ptF ψ θ (negFr B) A g P) = ptF ψ θ A B (rd S U g) (J P) := by
  let J : PolF D S.rank U.rank →ₐ[ℂ] PolF D U.rank S.rank := MvPolynomial.aeval fun v =>
    MvPolynomial.C (sgv (negFr B) A v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)
  have hX : ∀ τ i j, J (MvPolynomial.X (τ, i, j)) = MvPolynomial.C (sgv (negFr B) A τ i j) * MvPolynomial.X (τ, j, i) :=
    fun τ i j => MvPolynomial.aeval_X _ _
  refine ⟨J.toLinearMap, fun Q => ?_, fun g hg P => ?_⟩
  · show Q ∈ J.range
    induction Q using MvPolynomial.induction_on with
    | C a => exact J.range.algebraMap_mem a
    | add p q hp hq => exact add_mem hp hq
    | mul_X p v hp =>
      refine mul_mem hp ⟨MvPolynomial.C (sgv (negFr B) A v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1), ?_⟩
      show J _ = _
      rw [map_mul, hX, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul, sgv_mul_self, map_one, one_mul]
  show _ = ptF ψ θ A B (rd S U g) (J P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a : PolF D U.rank S.rank), ptF_C, ptF_one]
    erw [← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
    rfl
  | add p q hp hq =>
    rw [map_add, ptF_add, ptF_add, ← hp, ← hq]
    rfl
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, hX, mul_comm (J p), mul_assoc, ptF_C, ptF_X_mul hψ hθ A B (rd_theta hψ hg), ← hp, mul_comm p]
    erw [ptF_X_mul hψ hθ (negFr B) A hg]
    dsimp only
    have e := cdag_unitMap (negFr B) A τ i j
    have e' : (negFr B).onb τ = B.onb τ := rfl
    rw [aPlus_rd hψ hθ, ← e', e, aPlus_real_smul hψ hθ (ptF_theta hψ hθ (negFr B) A hg p)]
    funext x
    have := sgv_mul_self (negFr B) A τ i j
    simp only [rd, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    change _ = (sgv (negFr B) A τ i j * sgv (negFr B) A τ i j) * _
    rw [this, one_mul]

theorem exists_iota (S U U' : HSp D) (J : PolF D S.rank U'.rank →ₗ[ℂ] PolF D U'.rank S.rank) (hJ : Function.Surjective J) :
    ∃ ι : PolF D U.rank S.rank ⊗[ℂ] PolF D S.rank U'.rank →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum U U').rank S.rank,
      Function.Surjective ι ∧ ∀ P Q, ι (P ⊗ₜ Q) = GlobalTheory.SquareRel.polTens (sumVar U U' S.rank) (P ⊗ₜ J Q) :=
  ⟨(GlobalTheory.SquareRel.polTens (sumVar U U' S.rank)).toLinearMap ∘ₗ LinearMap.lTensor _ J, fun x => by
    obtain ⟨y, rfl⟩ := (GlobalTheory.SquareRel.polTens (sumVar U U' S.rank)).surjective x
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective _ hJ y
    exact ⟨z, rfl⟩, fun _ _ => rfl⟩

theorem sum_tens {P Q Z Y Pl : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Pl] [Module ℂ Pl] (zip : Z → (Unit × P) × Q → Z) (F : Z → Y) (ι : P ⊗[ℂ] Q →ₗ[ℂ] Pl) (Ψ : Pl →ₗ[ℂ] Y)
    (τ : Z →₀ ℂ) (h : ∀ d : (Unit × P) × Q, Ψ (ι (d.1.2 ⊗ₜ d.2)) = τ.sum fun z c => c • F (zip z d)) (a : (Unit × P) × Q →₀ ℂ) :
    (a.sum fun d c => τ.sum fun z c' => Finsupp.single (zip z d) (c * c')).sum (fun z c => c • F z) = Ψ (ι (toTens a)) := by
  rw [Finsupp.sum_sum_index (h := fun z (c : ℂ) => c • F z) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _, toTens, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.sum_sum_index (h := fun z (c : ℂ) => c • F z) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _, map_smul, map_smul, h, Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  dsimp only
  rw [Finsupp.sum_single_index (h := fun z (c : ℂ) => c • F z) (zero_smul _ _), mul_smul]

end Real

open GlobalTheory.FockAdjoint GlobalTheory.RouteSeesaw in

theorem realA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∃ ι : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank (G.V (.grid (↑i + 1) (↑j + 1))).rank,
      Function.Surjective ι ∧ ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ (τ : TotT G (routeBig t i j)) τ', HasFlip B t ρ i j n Φ τ τ' →
        ∀ a : PolT G (routeBig t i j) →₀ ℂ, GlobalTheory.SquareDict.datumA W (tensT W a τ) =
          GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) (ι (toTens a)) := by
  intro D T L sc G μ₀ _ W i j A AV AV₁ hA hV hV₁
  obtain ⟨J, hJ, hJ'⟩ := exists_adj_equiv W.ψ_std W.θ_is A AV₁
  obtain ⟨ι, hι, hι'⟩ := exists_iota (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) J hJ
  refine ⟨ι, hι, fun t B ρ n Φ τ τ' hF a => ?_⟩
  obtain ⟨e, he, -, φ₁, φ₂, hφ, -⟩ := hF
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have oA : A.onb = W.onb _ := funext fun τ => (hA τ).1
  have oV : AV.onb = W.onb _ := funext fun τ => (hV τ).1
  have oV₁ : AV₁.onb = W.onb _ := funext fun τ => (hV₁ τ).1
  have t₁ := fun d hd => GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2
  have t₂ := fun d hd => GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2
  have w₂ : ∀ d ∈ τ.support, IsVacF W.ψ W.θ AV₁ A d.2 := fun d hd => ⟨t₂ d hd, fun τ => by
    rw [cA', cV₁]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).2.2 v₂.theta
      (t₂ d hd) (v₂.fock τ)⟩
  have t₃ := fun d hd => (GlobalTheory.SquareAlg.adj_ptF W.ψ_std W.θ_is A AV₁ (w₂ d hd)).1.1
  refine sum_tens (Z := PureT G (routeBig t i j)) (fun d (P : PolT G (routeBig t i j)) =>
      Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)
    (fun d => box2 (S := negSp (G.V (.grid (↑i + 1) (↑j + 1)))) (A := (G.V (.grid ↑i (↑j + 1)))) (B := (G.V (.grid (↑i + 1) ↑j))) d.1.2 fun y => d.2 (adjM (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) y)) ι
    (GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ)) τ (fun P => ?_) a
  rw [hι']
  refine (ptF_sum W.ψ_std W.θ_is (GlobalTheory.SquareComm.frSgn true A) (GlobalTheory.SquareComm.frSum AV AV₁) τ.support τ _
    (fun d hd => GlobalTheory.SquareDict.AlgSmall.isThetaFunction_externalProductOnHermitianSum (t₁ d hd) (t₃ d hd)) _).2.trans (Finset.sum_congr rfl fun d hd => ?_)
  have e₁ : W.fock (.chi i (j + 1)) d.1.2 P.1.2 = ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 P.1.2 := by
    unfold ptF
    rw [cA, cV, oV, show (GlobalTheory.SquareComm.frSgn true A).onb = W.onb _ from oA]
    rfl
  have e₂ : W.fock (.mu t (i + 1) j) d.2 P.2 = ptF W.ψ W.θ AV₁ A d.2 P.2 := by
    unfold ptF
    rw [cA', cV₁, oA, oV₁]
    rfl
  have key := fockVector_product_mul_polynomials W.ψ_std W.θ_is (GlobalTheory.SquareComm.frSgn true A) AV AV₁ (t₁ d hd) (t₃ d hd) P.1.2 (J P.2)
  rw [← hJ' _ (w₂ d hd), ← e₁, ← e₂] at key
  exact congrArg (τ d • ·) key.symm

open GlobalTheory.FockAdjoint GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall in

theorem realB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∃ ι : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank (G.V (.grid ↑i ↑j)).rank,
      Function.Surjective ι ∧ ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ τ (τ' : TotT G (routeSmall t i j)), HasFlip B t ρ i j n Φ τ τ' →
        ∀ b : PolT G (routeSmall t i j) →₀ ℂ, GlobalTheory.SquareDict.datumB W (tensT W b τ') =
          GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') (ι (toTens b)) := by
  intro D T L sc G μ₀ _ W i j A₁ AV AV₁ h₁ hV hV₁
  obtain ⟨J, hJ, hJ'⟩ := exists_rd_equiv W.ψ_std W.θ_is A₁ AV₁
  obtain ⟨ι, hι, hι'⟩ := exists_iota (G.V (.grid ↑i ↑j)) (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) J hJ
  refine ⟨ι, hι, fun t B ρ n Φ τ τ' hF a => ?_⟩
  obtain ⟨e, he, ⟨φ₁, φ₂, hφ, -⟩, -⟩ := hF
  have v₁ := ρ.vT_is t i j i.2.le j.2
  have v₂ := ρ.vX_is i j i.2 j.2.le
  have t₁ := fun d hd => GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2.theta
  have t₂ := fun d hd => GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2.theta
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have o₁ : A₁.onb = W.onb _ := funext fun s => (h₁ s).1
  have oV : AV.onb = W.onb _ := funext fun s => (hV s).1
  have oV₁ : (negFr AV₁).onb = W.onb (.grid (i + 1) j) := funext fun s => (hV₁ s).1
  have ec : (GlobalTheory.SquareComm.frSgn false A₁).cart = A₁.cart := funext (frSgn_false_cart A₁)
  have t₃ := fun d hd => rd_theta W.ψ_std (t₂ d hd)
  refine sum_tens (Z := PureT G (routeSmall t i j)) (fun d (P : PolT G (routeSmall t i j)) =>
      Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)
    (fun d => box2 (S := (G.V (.grid ↑i ↑j))) (A := (G.V (.grid ↑i (↑j + 1)))) (B := (G.V (.grid (↑i + 1) ↑j))) d.1.2 fun y => d.2 (adjM (G.V (.grid ↑i ↑j)) (negSp (G.V (.grid (↑i + 1) ↑j))) y)) ι
    (GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ')) τ' (fun P => ?_) a
  have ef : ∀ f Q, GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) f Q =
      ptF W.ψ W.θ A₁ (GlobalTheory.SquareComm.frSum AV AV₁) f Q := fun f Q => by
    unfold GlobalTheory.SquareComm.fockF
    rw [ec]; rfl
  rw [hι', ef]
  refine (ptF_sum W.ψ_std W.θ_is A₁ (GlobalTheory.SquareComm.frSum AV AV₁) τ'.support τ' _
    (fun d hd => isThetaFunction_externalProductOnHermitianSum (t₁ d hd) (t₃ d hd)) _).2.trans (Finset.sum_congr rfl fun d hd => ?_)
  have key := fockVector_product_mul_polynomials W.ψ_std W.θ_is A₁ AV AV₁ (t₁ d hd) (t₃ d hd) P.1.2 (J P.2)
  rw [← hJ' _ (t₂ d hd)] at key
  refine congrArg (τ' d • ·) (key.symm.trans ?_)
  unfold ptF
  rw [c₁, cV, cV₁, o₁, oV, oV₁]
  rfl

section Fock

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.FockAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (SInf)

variable {D : D7} {S X : HSp D} {d : ℕ} {Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank}
  {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d}

def FockRel (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (A : Fr S)
    (B : Fr X) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X) (f₀ : SInf D.host.F (Fin S.rank × Fin d))
    (P : PolF D X.rank S.rank) (f : SInf D.host.F (Fin S.rank × Fin d)) : Prop :=
  ∀ φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (fockF ψ θ ε A B F P)

theorem fock_datum {θ : InfFam D} (hθ : IsInfFam θ) (ε : Bool) (A : Fr S) (B : Fr X) (e : Fin X.rank ≃ Fin d)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ))
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    {f₀ : SInf D.host.F (Fin S.rank × Fin d)} (hG : M.IsGauss Bs.ψ Bs.emb f₀) :
    (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsFinF Bs.ψ θ ε A B F) ∧
    (∀ P, ∃ f ∈ M.Pol Bs.ψ Bs.emb, FockRel M Bs.ψ θ ε A B cS f₀ P f) ∧
    ((∀ g, M.IsGauss Bs.ψ Bs.emb g → ∃ c : ℂ, g = c • f₀) → ∀ f ∈ M.Pol Bs.ψ Bs.emb, ∃ P, FockRel M Bs.ψ θ ε A B cS f₀ P f) := by
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hstd
  have fin : ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsFinF Bs.ψ θ ε A B F := fun φ h1 h2 F hF => by
    obtain ⟨F', a, b⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS f₀ φ hG h1 h2
    obtain rfl : F = F' := funext fun x => by
      obtain ⟨u, rfl⟩ := cS.surjective x
      exact (hF.2 u).symm.trans (b.2 u)
    exact a
  have L := GlobalTheory.SquareAgree.isDatum_linear M Bs.ψ hstd cS
  have lin : ∀ (c : ℂ) P f P' f', FockRel M Bs.ψ θ ε A B cS f₀ P f → FockRel M Bs.ψ θ ε A B cS f₀ P' f' →
      FockRel M Bs.ψ θ ε A B cS f₀ (P + c • P') (f + c • f') := fun c P f P' f' h h' φ h1 h2 F hF => by
    rw [GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul, map_add, map_smul]
    exact L.2 _ _ _ _ c (h φ h1 h2 F hF) (h' φ h1 h2 F hF)
  have zero : FockRel M Bs.ψ θ ε A B cS f₀ 0 0 := fun φ _ _ F _ => by
    rw [GlobalTheory.BigNZ.DatReal.pure_zero, map_zero]; exact L.1
  have one : FockRel M Bs.ψ θ ε A B cS f₀ 1 f₀ := fun φ _ _ F hF => by
    rw [show fockF Bs.ψ θ ε A B F 1 = F from ptF_one (frSgn ε A) B F]; exact hF
  have h0 : f₀ ∈ M.Pol Bs.ψ Bs.emb := Submodule.mem_sInf.2 fun N hN => hN.1 _ hG
  refine ⟨fin, fun P => ?_, fun hu => ?_⟩
  · induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨0 + a • f₀, add_mem (zero_mem _) (Submodule.smul_mem _ a h0), ?_⟩
      have := lin a _ _ _ _ zero one
      rwa [zero_add, ← MvPolynomial.C_eq_smul_one] at this
    | add p q hp hq =>
      obtain ⟨f, a, b⟩ := hp
      obtain ⟨f', a', b'⟩ := hq
      refine ⟨f + f', add_mem a a', ?_⟩
      simpa only [one_smul] using lin 1 _ _ _ _ b b'
    | mul_X p v hp =>
      obtain ⟨f, a, b⟩ := hp
      have der : ∀ z : Matrix (Fin X.rank) (Fin S.rank) ℂ, ∃ g ∈ M.Pol Bs.ψ Bs.emb, ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
          (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ, IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) F →
          IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) (dRho (heisO Bs.ψ (sgn ε S) X) θ v.1 z F) := fun z => by
        have hat := GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS v.1 z
        obtain ⟨g, hg⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd f _ hat
        exact ⟨g, Submodule.mem_sInf.2 fun N hN => hN.2 _ hat f (Submodule.mem_sInf.1 a N hN) g hg, fun φ h1 h2 F hF =>
          GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS f φ h1 h2 F hF v.1 z g hg⟩
      obtain ⟨g₁, a₁, b₁⟩ := der (unitMap (A.onb v.1) (B.onb v.1) v.2.1 v.2.2)
      obtain ⟨g₂, a₂, b₂⟩ := der (cplxO ((frSgn ε A).cart v.1) (B.cart v.1) (unitMap (A.onb v.1) (B.onb v.1) v.2.1 v.2.2))
      refine ⟨0 + (fockScale D v.1 : ℂ)⁻¹ • (g₁ + (-Complex.I) • g₂), add_mem (zero_mem _) (Submodule.smul_mem _ _
        (add_mem a₁ (Submodule.smul_mem _ _ a₂))), fun φ h1 h2 F hF => ?_⟩
      have k := L.2 _ _ _ _ (fockScale D v.1 : ℂ)⁻¹ L.1
        (L.2 _ _ _ _ (-Complex.I) (b₁ φ h1 h2 _ (b φ h1 h2 F hF)) (b₂ φ h1 h2 _ (b φ h1 h2 F hF)))
      rw [GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul, GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul,
        GlobalTheory.BigNZ.DatReal.pure_zero, mul_comm p, show fockF Bs.ψ θ ε A B F (MvPolynomial.X v * p) = _ from
          ptF_X_mul hψ hθ (frSgn ε A) B (fin φ h1 h2 F hF).1 p v, aPlus, crea, sub_eq_add_neg, ← neg_smul]
      rw [zero_add (M := WO S X → ℂ)] at k
      exact k
  · let N : Submodule ℂ (SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {f | ∃ P, FockRel M Bs.ψ θ ε A B cS f₀ P f}
        zero_mem' := ⟨0, zero⟩
        add_mem' := by
          rintro f f' ⟨P, h⟩ ⟨P', h'⟩
          exact ⟨_, by simpa only [one_smul] using lin 1 _ _ _ _ h h'⟩
        smul_mem' := by
          rintro c f ⟨P, h⟩
          exact ⟨_, by simpa only [zero_add] using lin c _ _ _ _ zero h⟩ }
    have hle : M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => ?_, fun u hu f ⟨P, hP⟩ f₁ h₁ => ?_⟩
    · exact fun f hf => hle hf
    · obtain ⟨c, rfl⟩ := hu g hg
      exact N.smul_mem c ⟨1, one⟩
    choose Lp hLp using fun τ => GlobalTheory.SquareComm.AlgDeriv.exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart
      (frSgn ε A).fr (frSgn ε A).ε B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
      (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ (compAt θ τ (cS u))
    have hsm : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
      intro a v
      rw [hcS, hcS]
      ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
        smul_mul_assoc, id]
    have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS u) := by
      intro a ha
      rw [← hsm, hu a ha, map_zero]
    refine ⟨∑ τ, Lp τ P, fun φ hφ hvac F hF => ⟨?_, fun u' => ?_⟩⟩
    · exact GlobalTheory.TensUniq.pure_mem_schA f₁ φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
    have hF' := fin φ hφ hvac F hF
    have hD := hP φ hφ hvac F hF
    have h2 := GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine M Bs.ψ hstd hM u hu f f₁ φ hφ hvac h₁ u'
    have h3 := GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces D Bs.ψ θ hψ hθ (sgn ε S) X _ (ptF_theta hψ hθ (frSgn ε A) B hF'.1 P) (cS u) hAt (cS u')
    have heq : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.heisLine Bs.ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)))) =
        fun t : ℝ => heisO Bs.ψ (sgn ε S) X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u) (ptF Bs.ψ θ (frSgn ε A) B F P) (cS u') := by
      funext t
      have h4 := (GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) _ hD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)).2 u'
      rw [hsm] at h4
      exact h4
    rw [heq] at h2
    rw [h2.unique h3, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun τ _ => congrFun (hLp τ F hF'.1 (hF'.2 τ) P) _

end Fock

end GlobalTheory.SquareIdent

end
