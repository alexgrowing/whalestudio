import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponentsStatement

section
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
namespace GlobalTheory.PairDarboux
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexOrder
theorem exists_darboux_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  intro _ D ψ θ hψ _ ε M X A B χS χT ω eS eT hω _
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hω
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := GlobalTheory.AdelicU.isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  let τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w := fun w => ⟨_, hτf w⟩
  have hτ : ∀ w x, (τ w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  let Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank :=
    ⟨GlobalTheory.RealDict.sgE (D := D) ε • M.gram, ⊥, fun w => (if ε then 1 else -1 : ℂ) • A.cart (τf w), fun _ => 1⟩
  let Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank :=
    ⟨D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)), ⊥,
      fun w => (B.cart (τf w)).map conj, fun _ => 1⟩
  have hXJ : Xs.J = -(sgn ε M).gram := gram_neg_sgn ε M rfl
  have hWJ : Ws.J = D.host.xi0 • X.gramᵀ := rfl
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hXh : ∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j := fun i j => by
    rw [hXJ]
    show star (-(sgn ε M).gram j i) = -(sgn ε M).gram i j
    rw [star_neg, GlobalTheory.TripleSpace.star_gram]
  have hXd : Xs.J.det ≠ 0 := by
    rw [hXJ]
    exact gram_det_ne (neg (sgn ε M))
  have hWs : ∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j := fun i j => by
    show star (D.host.xi0 * X.gram i j) = -(D.host.xi0 * X.gram j i)
    rw [star_mul', Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, GlobalTheory.TripleSpace.star_gram, neg_mul]
  have hWd : Ws.J.det ≠ 0 := by
    rw [hWJ, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hξ) (gram_det_ne X)
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star (R := D.host.E) x
  obtain ⟨co, hrat⟩ := GlobalTheory.RatDarboux.exists_darboux (AF D.host.F) h2 D.sp.cm.sig hσ hXh hWs hXd hWd
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas M
  obtain ⟨hμ', h𝓕'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M (J := Xs.J) _ hc rfl μ 𝓕 hμ h𝓕
  obtain ⟨o, ho⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E D.sp.cm.sig hcm
    (by haveI := GlobalTheory.InertOfConj.unram D; infer_instance)
  let Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws :=
    ⟨co, fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1,
      μ.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl '' 𝓕⟩
  have hgood : Mo.IsGood ψ :=
    { rat := hrat
      vac := fun v => isVac_of_bot Mo rfl ψ o ho v
      std := Filter.Eventually.of_forall fun _ => rfl
      haar := hμ'
      dom := h𝓕' }
  obtain ⟨om, hom, htr⟩ := exists_weil_transp ψ ε M X Xs Ws rfl rfl Mo hrat χS χT ω hω
  refine ⟨Xs, Ws, Mo, ψ, χS, χT, om, τ, ⟨hcm, GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ, hXh, hXd, hWs, hWd,
    GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resS, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resT,
    hω'.hecS, hω'.hecT, hom, fun w => ?_, fun w => ?_⟩,
    ⟨rfl, rfl, rfl, fun w => ⟨τf w, hτ w, rfl, rfl⟩, hgood, htr⟩⟩
  · have h := GlobalTheory.TripleSpace.isCartan_neg_conj
      (isCartanInv_sgn ε M (τf w) (GlobalTheory.CompactFockAction.cart_isCartanInv A (τf w)))
    have e1 : Xs.J.map (τ w).1 = -((gramAt D (sgn ε M) (τf w)).map star) := by
      rw [hXJ]
      ext a b
      simp [gramAt, hτ]
    have e2 : Xs.θ w = -sgnM ε (A.cart (τf w)) := by
      cases ε <;> simp [Xs, sgnM]
    rw [e1, e2]
    exact h
  · have h := isCartan_conj (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (GlobalTheory.CompactFockAction.cart_isCartanInv B (τf w))
    have e0 : Complex.I * conj (tauE D (τf w) D.host.xi0) = ((tauE D (τf w) D.host.xi0).im : ℂ) := by
      apply Complex.ext <;> simp [Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero]
    have e1 : Complex.I • Ws.J.map (τ w).1 = ((tauE D (τf w) D.host.xi0).im : ℂ) • gramAt D X (τf w) := by
      ext a b
      have e3 : conj (tauE D (τf w) (X.gram b a)) = tauE D (τf w) (X.gram a b) := by
        rw [← GlobalTheory.TripleSpace.star_gram X b a]
        exact (hcm.2.2.2 (tauE D (τf w)) (X.gram b a)).symm
      show Complex.I * conj (tauE D (τf w) (D.host.xi0 * X.gram b a)) = _ * tauE D (τf w) (X.gram a b)
      rw [map_mul, map_mul, ← mul_assoc, e0, e3]
    rw [e1]
    exact h
end GlobalTheory.PairDarboux
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_basis_of_symplectic_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  first | exact @_root_.GlobalTheory.PairDarboux.exists_darboux_pair | exact _root_.GlobalTheory.PairDarboux.exists_darboux_pair | (intros; apply _root_.GlobalTheory.PairDarboux.exists_darboux_pair <;> assumption)
end
