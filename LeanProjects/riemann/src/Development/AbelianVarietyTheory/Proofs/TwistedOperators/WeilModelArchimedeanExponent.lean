import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineEqRealScalarSmulSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDarbouxComplexStructureTwoInvolutionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.FockMap

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Gauss

open scoped Classical
open GlobalTheory.VacLn

theorem gauss_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    (∀ w, X.θ w * X.θ w = 1) → (∀ w, W.θ w * W.θ w = 1) →
    ∀ f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), M.IsGauss ψ τ g → g ≠ 0 → M.IsGauss ψ τ f → ∃ z : ℂ, f = z • g := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hCM hStd hX hW f g ⟨ε, hg⟩ hg0 ⟨ε', hf⟩
  obtain ⟨D, hDu⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ _ _ M.co hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.exists_darboux_complex_structure_two_involutions F E σ (Fin n) (Fin d) (Fin n × Fin d) τ _ _ M.co X.θ W.θ
    ε ε' hCM hX hW
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have hA : ∀ u, At (evI F) u → ∀ h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) h (D u h) := fun u hu h =>
    (GlobalTheory.RealLift.actsLaws F _ h (D u h) h).1 _ (hz u) (hDu u hu h).1
  have hDx : ∀ u, At (evI F) u → ∀ (h : SInf F (Fin n × Fin d)) x, D u h x = fderiv ℝ h x (coord M.co u).1 -
      2 * Real.pi * Complex.I * (trPair F _ x (coord M.co u).2 : ℝ) * h x := fun u hu h x => (hDu u hu h).2 x
  refine GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F _) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f g hg0 (fun y x => ?_)
    fun y x => ?_
  · obtain ⟨u, -, u₁, hu, -, hu₁, -, hc₁, h0, -, h1⟩ := hy y
    have := congrArg (fun k : SInf F _ => k x) (hg u u₁ hu hu₁ hc₁ _ _ (hA u hu g) (hA u₁ hu₁ g))
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rwa [hDx u hu, hDx u₁ hu₁, h0, h1] at this
  · obtain ⟨u, u', -, hu, hu', -, hc', -, h0, h', -⟩ := hy y
    have := congrArg (fun k : SInf F _ => k x) (hf u u' hu hu' hc' _ _ (hA u hu f) (hA u' hu' f))
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rwa [hDx u hu, hDx u' hu', h0, h'] at this

theorem exists_der {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) :
    ∃ Dr : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)),
      (∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (Dr u f)) ∧
      (∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ = Dr u f) ∧
      ∀ (ι : Type) (s : Finset ι) (u : ι → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), (∀ i, At (evI F) (u i)) →
        ∀ f, Dr (∑ i ∈ s, u i) f = ∑ i ∈ s, Dr (u i) f := by
  obtain ⟨D, hDu⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ _ _ M.co hStd
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have hA : ∀ u, At (evI F) u → ∀ h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) h (D u h) := fun u hu h =>
    (GlobalTheory.RealLift.actsLaws F _ h (D u h) h).1 _ (hz u) (hDu u hu h).1
  have hDx : ∀ u, At (evI F) u → ∀ (h : SInf F (Fin n × Fin d)) x, D u h x = fderiv ℝ h x (coord M.co u).1 -
      2 * Real.pi * Complex.I * (trPair F _ x (coord M.co u).2 : ℝ) * h x := fun u hu h x => (hDu u hu h).2 x
  refine ⟨D, hA, fun u hu f f₁ h => (GlobalTheory.RealLift.actsLaws F _ f f₁ (D u f)).2.2.1 _ h (hA u hu f), fun ι s u hu f => ?_⟩
  have hs : At (evI F) (∑ i ∈ s, u i) := fun a ha => by
    rw [Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ => hu i a ha
  let ev : AF F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)
  have hev : ∀ a, evI F a = ev a := fun _ => rfl
  have hc : coord M.co (∑ i ∈ s, u i) = ∑ i ∈ s, coord M.co (u i) := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp only [coord, hev, map_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  ext x
  rw [hDx _ hs, hc, SchwartzMap.sum_apply, Finset.sum_congr rfl fun i _ => hDx _ (hu i) f x]
  simp only [Prod.fst_sum, Prod.snd_sum, map_sum, Finset.sum_sub_distrib, Complex.ofReal_sum, Finset.mul_sum,
    Finset.sum_mul]

end Gauss

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    schr ψ v (schr ψ w Φ) = ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • schr ψ (v + w) Φ := by
  funext z
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

variable {D : D7}

theorem dRho_ptF {V W : HSp D} (A : Fr V) (B : Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO V W → ℂ} (hf : IsVacF ψ θ A B f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank) :
    ∃ Q, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (ptF ψ θ A B f P) = ptF ψ θ A B f Q := by
  classical
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  obtain ⟨Q₁, h1⟩ := GlobalTheory.FockCreaDir.crea_ptF D V W A B θ ψ hψ hθ f hf.1 τ z P
  have h2 := GlobalTheory.ArchRec.DerFock.pure_deriv (P := IsThetaFunO ψ V W)
    (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb)
    (B := annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z)
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
    (fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h')
    (fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h)
    (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ h h')
    (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ a h)
    (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.1 (hf.2 τ z) P
  obtain ⟨Q₂, h2⟩ : ∃ Q₂, annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (ptF ψ θ A B f P) =
    ptF ψ θ A B f Q₂ := ⟨_, h2⟩
  refine ⟨(1 / 2 : ℂ) • (Q₁ + Q₂), ?_⟩
  have e : ptF ψ θ A B f ((1 / 2 : ℂ) • (Q₁ + Q₂)) = (1 / 2 : ℂ) • (ptF ψ θ A B f Q₁ + ptF ψ θ A B f Q₂) := by
    unfold ptF
    rw [map_smul, map_add]
  rw [e, ← h1, ← h2, crea, annih]
  module

def toO {m k : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (u : Matrix (Fin m) (Fin k) (AE D)) : Mx D k m :=
  HMul.hMul (uᵀ) (G.map (incA D))

theorem map_mul_inv {m : ℕ} {G : Matrix (Fin m) (Fin m) D.host.E} (hG : IsUnit G.det) :
    G.map (incA D) * (G⁻¹).map (incA D) = 1 ∧ (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.mul_nonsing_inv _ hG,
    Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨rfl, rfl⟩

theorem ptO_eq {m k : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (x : Mx D k m) :
    GlobalTheory.TripleRead.ptO G (Equiv.refl (Fin k)) x = (HMul.hMul x ((G⁻¹).map (incA D)))ᵀ := rfl

theorem ptO_toO {m k : ℕ} {G : Matrix (Fin m) (Fin m) D.host.E} (hG : IsUnit G.det) (u : Matrix (Fin m) (Fin k) (AE D)) :
    GlobalTheory.TripleRead.ptO G (Equiv.refl (Fin k)) (toO G u) = u := by
  rw [ptO_eq, toO, Matrix.mul_assoc, (map_mul_inv hG).1, Matrix.mul_one, transpose_transpose]

theorem toO_ptO {m k : ℕ} {G : Matrix (Fin m) (Fin m) D.host.E} (hG : IsUnit G.det) (x : Mx D k m) :
    toO G (GlobalTheory.TripleRead.ptO G (Equiv.refl (Fin k)) x) = x := by
  rw [ptO_eq, toO, transpose_transpose, Matrix.mul_assoc, (map_mul_inv hG).2, Matrix.mul_one]

theorem ptO_smul {m k : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (a : AF D.host.F) (x : Mx D k m) :
    GlobalTheory.TripleRead.ptO G (Equiv.refl (Fin k)) (a • x) = a • GlobalTheory.TripleRead.ptO G (Equiv.refl (Fin k)) x := by
  rw [ptO_eq, ptO_eq, Matrix.smul_mul, transpose_smul]

theorem gram_sgn (ε : Bool) (M : HSp D) : (sgn ε M).gram = -(sgE (D := D) ε • M.gram) := by
  cases ε
  · simp [sgn, sgE]
  · ext i j; simp [HSpace.gram, sgE]

variable {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
  {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)

theorem exists_co (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))) :
    ∃ co : Darboux (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε M).gram⁻¹))) (Fin M.rank × Fin X.rank),
      ∀ x, co.e x = Mo.co.e (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl (Fin X.rank)) x) := by
  have hdet : IsUnit (sgn ε M).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε M)).isUnit
  have hG : ((sgn ε M).gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = ((sgn ε M).gram.map (incA D))ᵀ := by
    ext i j
    show cA D (incA D ((sgn ε M).gram i j)) = incA D ((sgn ε M).gram j i)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let T : Matrix (Fin M.rank) (Fin X.rank) (AE D) ≃+ Mx D X.rank M.rank :=
    { toFun := toO (sgn ε M).gram
      invFun := GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl (Fin X.rank))
      left_inv := ptO_toO hdet
      right_inv := toO_ptO hdet
      map_add' := fun u v => by simp only [toO, transpose_add, Matrix.add_mul] }
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (Equiv.refl _)
    (X.gram.map (incA D)) (incA D D.host.xi0) (map_mul_inv hdet).2 hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Xs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε M).gram⁻¹))
    (by rw [hX, gram_sgn, Matrix.map_neg _ (map_neg (incA D)), neg_neg]; rfl)
    (by rw [hW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) Mo.co T (fun _ => rfl)
  exact ⟨co, fun x => (congrArg co.e (toO_ptO hdet x)).symm.trans (hco _)⟩

theorem thetaSum_rho_rho {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U]
    {B : U → U → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (x y : U) :
    thetaSum F (co.rho ψ x (co.rho ψ y Φ)) = ψ (⅟(2 : AF F) * B x y) * thetaSum F (co.rho ψ (x + y) Φ) := by
  simp only [Darboux.rho, schr_schr, thetaSum, map_add, Pi.smul_apply, smul_eq_mul, tsum_mul_left, co.form]

theorem heisO_thetaTr {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {ξ : AE D} {κ : Type} [Fintype κ]
    (co : Darboux (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JA)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ) (hA : JA = T.gramᵀ)
    (hB : ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Φ : (κ → AF D.host.F) → ℂ) (y x : WO S T) :
    heisO ψ S T y (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) x = thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) := by
  rw [thetaSum_rho_rho, ← GlobalTheory.ThetaTransform.symplO_eq_symp hA hB, GlobalTheory.ThetaTransform.invOf_two_eq]
  rfl

variable (ψ ε) in

abbrev th (Φ : (Fin M.rank × Fin X.rank → AF D.host.F) → ℂ) : WO (sgn ε M) X → ℂ :=
  GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank)) Φ

variable (ε M X) in

abbrev dir (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin M.rank) ℂ) :
    Matrix (Fin M.rank) (Fin X.rank) (AE D) :=
  GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl (Fin X.rank)) (lineAt θ τ z 1)

theorem dir_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin M.rank) ℂ) :
    At (evI D.host.F) (dir ε M X θ τ z) := fun a ha => by
  rw [← ptO_smul, (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z).2 a ha, ptO_eq, Matrix.zero_mul, transpose_zero]

theorem th_laws (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) :
    (∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, th ψ ε Mo (Φ + Φ') = th ψ ε Mo Φ + th ψ ε Mo Φ') ∧
    (∀ (c : ℂ) Φ, th ψ ε Mo (c • Φ) = c • th ψ ε Mo Φ) ∧
    (∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, th ψ ε Mo Φ = th ψ ε Mo Φ' → Φ = Φ') ∧
    (∀ f, IsThetaFunO ψ (sgn ε M) X f ↔ ∃ Φ ∈ schA D.host.F _, th ψ ε Mo Φ = f) ∧
    ∀ τ z, ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _,
      (∀ x, HasDerivAt (fun t => Mo.heisLine ψ (dir ε M X θ τ z) t Φ x) (Φ' x) 0) →
      Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (th ψ ε Mo Φ) = th ψ ε Mo Φ' := by
  obtain ⟨co, hco⟩ := exists_co Mo hX hW
  have hr : ∀ x, co.rho ψ x = Mo.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl (Fin X.rank)) x) := fun x => by
    simp only [Darboux.rho, hco]
  have hth : ∀ Φ, th ψ ε Mo Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := fun Φ => by
    funext x
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, hr]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε M) (T := X) co hψ rfl (one_smul _ _) (fun x => by
    obtain ⟨y, z, h⟩ := hM.rat ((x * (sgn ε M).gram⁻¹)ᵀ)
    refine ⟨y, z, Eq.trans ?_ h⟩
    rw [hco, ptO_eq]
    congr 1
    exact (congrArg transpose (Matrix.map_mul (f := incA D))).symm)
  simp only [hth]
  refine ⟨h1, GlobalTheory.ThetaTransform.thetaTr_smul co, h2, h3, fun τ z Φ hΦ Φ' hΦ' hd => ?_⟩
  have hl := (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ τ z).1
  have hH : ∀ y x, heisO ψ (sgn ε M) X y (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) x =
      thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) := fun y x => heisO_thetaTr (S := sgn ε M) co rfl (one_smul _ _) Φ y x
  funext x
  have := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho co ψ inferInstance hψ.1 (lineAt θ τ z 1) Φ hΦ Φ' hΦ' (fun y => by
    simp only [hr, ptO_smul]
    exact hd y) x
  refine Eq.trans ?_ this.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [hH, hl t]

theorem eq_sum_lineAt {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {x : Mx D m n} (hx : At (evI D.host.F) x) :
    x = ∑ t, lineAt θ t (compAt θ t x) 1 := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hL := fun t => GlobalTheory.OrientedHeis.isLineAt_lineAt hθ t (compAt θ t x)
  let a : AF D.host.F := ⟨0, 1⟩
  have h0 := hx a (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F))
  funext i j
  have h1 : finPart D (x i j) = 0 := by
    have h := GlobalTheory.LineRealAd.finPart_smul a (x i j)
    have h' : a • x i j = 0 := congrFun (congrFun h0 i) j
    rw [h', RingHom.map_zero] at h
    exact (one_mul _).symm.trans h.symm
  rw [Matrix.sum_apply]
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun t' => ?_)
  · have h2 : ∀ t, finPart D (lineAt θ t (compAt θ t x) 1 i j) = 0 := fun t => congrFun (congrFun ((hL t).2.1 1) i) j
    rw [RingHom.map_sub, map_sum, h1, Finset.sum_eq_zero fun t _ => h2 t, sub_zero]
  · have h2 : ∀ t, θ t' (infPart D (lineAt θ t (compAt θ t x) 1 i j)) =
        (if t' = t then ((1 : ℝ) : ℂ) • compAt θ t x else 0) i j := fun t => congrFun (congrFun ((hL t).2.2 1 t') i) j
    rw [RingHom.map_sub, RingHom.map_sub, map_sum, map_sum, Finset.sum_congr rfl fun t _ => h2 t, ← Matrix.sum_apply,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.ofReal_one, one_smul]
    exact sub_self _

theorem eq_sum_dir {θ : InfFam D} (hθ : IsInfFam θ) {u : Matrix (Fin M.rank) (Fin X.rank) (AE D)}
    (hu : At (evI D.host.F) u) : u = ∑ t, dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u)) := by
  have hdet : IsUnit (sgn ε M).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε M)).isUnit
  have h : At (evI D.host.F) (toO (sgn ε M).gram u) := fun a ha => by
    rw [toO, ← Matrix.smul_mul, ← transpose_smul, hu a ha, transpose_zero, Matrix.zero_mul]
  conv_lhs => rw [← ptO_toO hdet u, eq_sum_lineAt hθ h, ptO_eq, Matrix.sum_mul, transpose_sum]
  exact Finset.sum_congr rfl fun _ _ => (ptO_eq _ _).symm

theorem cart_frSgn (A : Fr M) (t : D.what₂.Tau) : (frSgn ε A).cart t = -((if ε then 1 else -1 : ℂ) • A.cart t) := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have e' : Formalism.REAL.Jm (fun a => xor true (A.ε t a)) = -Formalism.REAL.Jm (A.ε t) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : A.ε t a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    show (A.fr t)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε t a)) * A.fr t = _
    rw [e', if_pos rfl, one_smul, Fr.cart, Matrix.mul_neg, Matrix.neg_mul]

theorem compAt_cplx {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w}
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj) {u u' : Matrix (Fin M.rank) (Fin X.rank) (AE D)}
    (h : ∀ w, u'.map (piInf (τ w)) = Complex.I • (Xs.θ w * u.map (piInf (τ w)) * (Ws.θ w)ᵀ)) (t : D.what₂.Tau) :
    compAt θ t (toO (sgn ε M).gram u') =
      cplxO ((frSgn ε A).cart t) (B.cart t) (compAt θ t (toO (sgn ε M).gram u)) := by
  choose τf h1 h2 h3 using hc
  have he : ∀ w, (τ w).1 = (starRingEnd ℂ).comp (tauE D (τf w)) := fun w => RingHom.ext (h1 w)
  have hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding :=
    fun w => he w ▸ (τ w).2
  have hinj : Function.Injective τf := fun w1 w2 h => by
    have e : w1.embedding = w2.embedding := by rw [← hτf w1, ← hτf w2, h]
    rw [← InfinitePlace.mk_embedding w1, ← InfinitePlace.mk_embedding w2, e]
  have hbij : Function.Bijective τf := (Fintype.bijective_iff_injective_and_card τf).2
    ⟨hinj, (Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D)).symm⟩
  obtain ⟨w, rfl⟩ := hbij.2 t
  have hp : ∀ y, piInf (τ w) y = conj (θ (τf w) (infPart D y)) := fun y => by
    rw [show τ w = ⟨_, hτf w⟩ from Subtype.ext (he w)]
    exact GlobalTheory.ConjInfExp.piInf_eq θ hθ (τf w) w (hτf w) y
  have hcomp : ∀ v : Matrix (Fin M.rank) (Fin X.rank) (AE D), compAt θ (τf w) (toO (sgn ε M).gram v) =
      (v.map (piInf (τ w)))ᴴ * gramAt D (sgn ε M) (τf w) := fun v => by
    rw [toO, GlobalTheory.OrientedHeis.compAt_mul]
    congr 1
    · ext i j
      simp only [compAt, map_apply, transpose_apply, conjTranspose_apply, hp, RCLike.star_def, Complex.conj_conj]
    · ext i j
      exact GlobalTheory.FockCompare.comp_incA hθ (τf w) _
  obtain ⟨s1, s2, -⟩ := GlobalTheory.ChainFr.Model.isCartanInv_cart (frSgn ε A) (τf w)
  have hX : Xs.θ w = -(frSgn ε A).cart (τf w) := by rw [cart_frSgn, neg_neg, h2]
  have hW : (Ws.θ w)ᵀ = (B.cart (τf w))ᴴ := by rw [h3]; rfl
  generalize (frSgn ε A).cart (τf w) = s at s1 s2 hX ⊢
  have s3 : sᴴ * gramAt D (sgn ε M) (τf w) = gramAt D (sgn ε M) (τf w) * s := by
    conv_rhs => rw [← s2, Matrix.mul_assoc, s1, Matrix.mul_one]
  rw [hcomp, hcomp, h, hX, hW, cplxO, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_neg, Matrix.smul_mul]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, s3, Complex.star_def, Complex.conj_I, neg_smul, smul_neg,
    neg_neg]

theorem pureA_mem {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ}
    (hg : g ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem rest_fin {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ}
    (hg : g ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI F) f (fun x => g fun i => (x i).2) := by
  refine ⟨fun x z hz => congrArg g (funext fun i => ?_), pureA_mem f hg⟩
  change (x i).2 + (z i).2 = (x i).2
  rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]

section Main

variable (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (hX : Xs.J = sgE (D := D) ε • M.gram)
  (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
  (hM : Mo.IsGood ψ)
include hψ hθ hX hW hM

def thL {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) :
    SInf D.host.F (Fin M.rank × Fin X.rank) →ₗ[ℂ] (WO (sgn ε M) X → ℂ) where
  toFun f := th ψ ε Mo (pureA D.host.F f g)
  map_add' f f' := by
    rw [← (th_laws Mo hψ hθ hX hW hM).1 _ (pureA_mem f hg) _ (pureA_mem f' hg)]
    exact congrArg _ (funext fun x => add_mul _ _ _)
  map_smul' c f := by
    rw [RingHom.id_apply, ← (th_laws Mo hψ hθ hX hW hM).2.1]
    exact congrArg _ (funext fun x => mul_assoc _ _ _)

variable {Dr : Matrix (Fin M.rank) (Fin X.rank) (AE D) →
    (SInf D.host.F (Fin M.rank × Fin X.rank) →L[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank))}
  (hD : ∀ u, At (evI D.host.F) u → ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank),
    ActsD (evI D.host.F) (Mo.heisLine ψ u) f (Dr u f))
include hD

theorem dRho_thL {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (t : D.what₂.Tau)
    (z : Matrix (Fin X.rank) (Fin M.rank) ℂ) (f : SInf D.host.F (Fin M.rank × Fin X.rank)) :
    Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (thL Mo hψ hθ hX hW hM hg f) =
      thL Mo hψ hθ hX hW hM hg (Dr (dir ε M X θ t z) f) :=
  (th_laws Mo hψ hθ hX hW hM).2.2.2.2 t z _ (pureA_mem f hg) _ (pureA_mem _ hg) (hD _ (dir_at hθ t z) f _ (rest_fin f hg))

set_option maxHeartbeats 1000000 in

theorem exists_vacuum (A : Fr (sgn ε M)) (B : Fr X) : ∃ g₀ : SInf D.host.F (Fin M.rank × Fin X.rank), g₀ ≠ 0 ∧
    ∀ t z, Dr (dir ε M X θ t z) g₀ + Complex.I • Dr (dir ε M X θ t (cplxO (A.cart t) (B.cart t) z)) g₀ = 0 := by
  obtain ⟨tadd, tsm, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  have t0 : th ψ ε Mo 0 = 0 := by simpa only [zero_smul] using tsm 0 0
  obtain ⟨An, hAn⟩ : ∃ An : D.what₂.Tau → Matrix (Fin X.rank) (Fin M.rank) ℂ →
      (SInf D.host.F (Fin M.rank × Fin X.rank) →L[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank)),
      ∀ t z f, An t z f = Dr (dir ε M X θ t z) f + Complex.I • Dr (dir ε M X θ t (cplxO (A.cart t) (B.cart t) z)) f :=
    ⟨fun t z => Dr (dir ε M X θ t z) + Complex.I • Dr (dir ε M X θ t (cplxO (A.cart t) (B.cart t) z)), fun _ _ _ => rfl⟩
  have key : ∀ Ψ ∈ schA D.host.F (Fin M.rank × Fin X.rank),
      ∃ s : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → SInf D.host.F (Fin M.rank × Fin X.rank),
        (∀ a y, Ψ (GlobalTheory.RealLift.ptAt a y) = s y a) ∧ ∀ t z, ∃ Ψ' ∈ schA D.host.F (Fin M.rank × Fin X.rank),
          (∀ a y, Ψ' (GlobalTheory.RealLift.ptAt a y) = An t z (s y) a) ∧
          annih (heisO ψ (sgn ε M) X) θ t (cplxO (A.cart t) (B.cart t)) z (th ψ ε Mo Ψ) = th ψ ε Mo Ψ' := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem Ψ h =>
      obtain ⟨f, g, hg, rfl⟩ := h
      refine ⟨fun y => g y • f, fun a y => ?_, fun t z => ⟨_, pureA_mem (An t z f) hg, fun a y => ?_, ?_⟩⟩
      · rw [GlobalTheory.RealLift.pureA_ptAt, mul_comm]; rfl
      · rw [GlobalTheory.RealLift.pureA_ptAt, mul_comm, map_smul]; rfl
      · change annih _ θ t _ z (thL Mo hψ hθ hX hW hM hg f) = thL Mo hψ hθ hX hW hM hg (An t z f)
        rw [annih, dRho_thL Mo hψ hθ hX hW hM hD, dRho_thL Mo hψ hθ hX hW hM hD, hAn, map_add, map_smul]
    | zero =>
      refine ⟨0, fun _ _ => rfl, fun t z => ⟨0, zero_mem _, fun a y => by rw [Pi.zero_apply y, map_zero]; rfl, ?_⟩⟩
      rw [t0]
      simpa only [zero_smul] using GlobalTheory.FockIndep.annih_smul hψ hθ t (cplxO (A.cart t) (B.cart t)) z 0
        (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    | add Ψ₁ Ψ₂ m1 m2 h1 h2 =>
      obtain ⟨s₁, a1, b1⟩ := h1
      obtain ⟨s₂, a2, b2⟩ := h2
      refine ⟨s₁ + s₂, fun a y => by rw [Pi.add_apply, a1, a2]; rfl, fun t z => ?_⟩
      obtain ⟨Ψ₁', n1, c1, d1⟩ := b1 t z
      obtain ⟨Ψ₂', n2, c2, d2⟩ := b2 t z
      refine ⟨Ψ₁' + Ψ₂', add_mem n1 n2, fun a y => by rw [Pi.add_apply, c1, c2, Pi.add_apply, map_add]; rfl, ?_⟩
      rw [tadd _ m1 _ m2, tadd _ n1 _ n2, ← d1, ← d2]
      exact GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ ((tth _).2 ⟨_, m1, rfl⟩) ((tth _).2 ⟨_, m2, rfl⟩)
    | smul c Ψ₁ m1 h1 =>
      obtain ⟨s₁, a1, b1⟩ := h1
      refine ⟨c • s₁, fun a y => by rw [Pi.smul_apply, a1]; rfl, fun t z => ?_⟩
      obtain ⟨Ψ₁', n1, c1, d1⟩ := b1 t z
      refine ⟨c • Ψ₁', Submodule.smul_mem _ c n1, fun a y => by rw [Pi.smul_apply, c1, Pi.smul_apply, map_smul]; rfl, ?_⟩
      rw [tsm, tsm, ← d1]
      exact GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ c ((tth _).2 ⟨_, m1, rfl⟩)
  obtain ⟨f, f0, hf, -⟩ := GlobalTheory.ChainFr.Model.exists_vac A B hψ hθ
  obtain ⟨Ψ, hΨ, rfl⟩ := (tth f).1 hf.1
  obtain ⟨s, hs, hs'⟩ := key Ψ hΨ
  obtain ⟨x, hx⟩ : ∃ x, Ψ x ≠ 0 := by
    by_contra h
    exact f0 ((congrArg _ (funext fun x => not_not.1 fun hx => h ⟨x, hx⟩)).trans t0)
  have ex : x = GlobalTheory.RealLift.ptAt (fun i => evI D.host.F (x i)) fun i => (x i).2 :=
    funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm_apply_apply _).symm rfl
  refine ⟨s fun i => (x i).2, fun h => hx (by rw [ex, hs]; exact DFunLike.congr_fun h _), fun t z => ?_⟩
  obtain ⟨Ψ', n, c, d⟩ := hs' t z
  have h0 : Ψ' = 0 := tinj _ n _ (zero_mem _) (by rw [← d, t0]; exact hf.2 t z)
  rw [← hAn]
  refine DFunLike.ext _ _ fun a => ?_
  rw [← c, h0]
  rfl

end Main

set_option maxHeartbeats 1000000 in

theorem exists_fockMap_of (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ τ ∧ IsFockMap ψ θ ε A B Mo Φ := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨g₀, g0, hg₀⟩ := exists_vacuum Mo hψ hθ hX hW hM hD1 (frSgn ε A) B
  have hg := GlobalTheory.RealLift.indicator_intPts_mem_SB (F := D.host.F) (κ := Fin M.rank × Fin X.rank)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a 0)
    rwa [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts,
      Pi.one_apply, mul_one, mul_one] at e2
  have hv : IsVacF ψ θ (frSgn ε A) B (Θ g₀) := ⟨(tth _).2 ⟨_, pureA_mem g₀ hg, by rw [hΘ]; rfl⟩, fun t z => by
    rw [annih, hd, hd, ← map_smul, ← map_add, hg₀, map_zero]⟩
  have hv0 : Θ g₀ ≠ 0 := fun h => g0 (hi (h.trans (map_zero Θ).symm))
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun hΦ P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t, eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, ?_, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), Θ g₀, _, hv, hv0, fun P => ⟨rest_fin _ hg, ?_⟩⟩
  · have := GlobalTheory.LieScalar.ptF_injective hθ hψ (frSgn ε A) B hv hv0
    rw [← hΦ, LinearMap.coe_comp] at this
    exact this.of_comp
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩
  · rw [← hΦ', hΘ]
    rfl

theorem exists_fockMap : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧ GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT _ _ Xs Ws Mo ψ' χX χW om τ hP hR
  obtain ⟨hCM, hStd, -, -, -, -, -, -, -, -, -, hcX, hcW⟩ := hP
  obtain rfl := hR.psi
  exact exists_fockMap_of Mo hψ hθ A B hCM hStd hR.JX hR.JW hR.good (fun w => (hcX w).1) (fun w => (hcW w).1) hR.cart

end GlobalTheory.RealDict.FockMap

end
