import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open GlobalTheory.TriMove GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

private theorem opPow_comm {ι X X' : Type} (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (A' : ι → (X' → ℂ) → (X' → ℂ)) (h : ∀ k g, A' k (tr g) = tr (A k g)) (k : ι →₀ ℕ) (f : X → ℂ) :
    opPow A' k (tr f) = tr (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, h]

private theorem pure_comm {D : D7} {m n m' n' : ℕ} (hm : m = m') (hn : n = n') {X X' : Type}
    (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : FVar D m n → (X → ℂ) → (X → ℂ))
    (A' : FVar D m' n' → (X' → ℂ) → (X' → ℂ))
    (h : ∀ (k : FVar D m n) g, A' (k.1, finCongr hm k.2.1, finCongr hn k.2.2) (tr g) = tr (A k g)) (f : X → ℂ)
    (P : MvPolynomial (FVar D m n) ℂ) :
    pureTensorL A' (tr f) (polMove hm hn P) = tr (pureTensorL A f P) := by
  subst hm hn
  have e : polMove (D := D) (rfl : m = m) (rfl : n = n) P = P := MvPolynomial.rename_id_apply P
  rw [e]
  have e2 : pureTensorL A' (tr f) = tr ∘ₗ pureTensorL A f := by
    refine (MvPolynomial.basisMonomials (FVar D m n) ℂ).ext fun k => ?_
    unfold pureTensorL
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact opPow_comm tr A A' h k f
  rw [e2]
  rfl

private theorem unitMap_move {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (pq : pS * qS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    unitMap (pS * B * (rdx hn : Matrix (Fin n) (Fin n') ℂ)) (pT * B' * (rdx hm : Matrix (Fin m) (Fin m') ℂ)) (finCongr hm i) (finCongr hn j) = pT * unitMap B B' i j * qS := by
  subst hm hn
  have e1 : rdx (K := ℂ) (rfl : m = m) = 1 := rfl
  have e2 : rdx (K := ℂ) (rfl : n = n) = 1 := rfl
  unfold unitMap
  rw [e1, e2, Matrix.mul_one, Matrix.mul_one, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv pq]
  simp only [Matrix.mul_assoc]
  rfl

private theorem cplxO_move {m n m' n' : ℕ} (ε : Bool)
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (qp : qS * pS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (qT : Matrix (Fin m) (Fin m') ℂ) (qp' : qT * pT = 1)
    (s : Matrix (Fin n) (Fin n) ℂ) (s' : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (GlobalTheory.Grid.sgnM ε (pS * s * qS)) (pT * s' * qT) (pT * z * qS) = pT * cplxO (GlobalTheory.Grid.sgnM ε s) s' z * qS := by
  have e : GlobalTheory.Grid.sgnM ε (pS * s * qS) = pS * GlobalTheory.Grid.sgnM ε s * qS := by
    cases ε
    · rfl
    · show -(pS * s * qS) = pS * (-s) * qS
      rw [Matrix.mul_neg, Matrix.neg_mul]
  unfold cplxO
  rw [e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = pT * s' * (qT * pT) * z * (qS * pS) * GlobalTheory.Grid.sgnM ε s * qS := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [qp, qp', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private theorem trace_move {A : Type} [CommRing A] {m n m' n' : ℕ} (s : A →+* A)
    {H : Matrix (Fin n) (Fin n) A} {H' : Matrix (Fin n') (Fin n') A} {Q : Matrix (Fin n) (Fin n') A}
    (hH : Q * H' * cT s Q = H)
    {J : Matrix (Fin m) (Fin m) A} {J' : Matrix (Fin m') (Fin m') A} {P : Matrix (Fin m') (Fin m) A}
    (hJ : cT s P * J' * P = J) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace (H' * (cT s (P * y * Q) * J' * (P * x * Q))) = Matrix.trace (H * (cT s y * J * x)) := by
  rw [← hH, ← hJ, cT_mul, cT_mul]
  calc _ = Matrix.trace ((H' * cT s Q * (cT s y * (cT s P * J' * P) * x)) * Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

variable {D : D7}

private theorem hO_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (cT (cA D) y * T.gram.map (incA D) * x)) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b

variable {S S' T T' : HSp D}

private theorem gram_inv_move (I : IsoMat S S') :
    I.Q * S'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q = S.gram⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← I.gram]
  calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (S'.gram * (I.P * I.Q) * S'.gram⁻¹) *
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S'), Matrix.mul_one, ← cT_mul, I.QP,
        cT_one]

private theorem hO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    hO S' T' (homMap IS IT x) (homMap IS IT y) = hO S T x y := by
  rw [hO_trace, hO_trace]
  refine trace_move (cA D) ?_ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y
  rw [← gram_inv_move IS, Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem heisO_homMap (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (IS : IsoMat S S') (IT : IsoMat T T') (u : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.Grid.sgn ε S') T' (homMap (S := S) (S' := S') IS IT u) (trH (S := S) (S' := S') IS IT f) = trH (S := S) (S' := S') IS IT (heisO ψ (GlobalTheory.Grid.sgn ε S) T u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
  have e : hO (GlobalTheory.Grid.sgn ε S') T' (homMap IS IT w) (homMap IS IT u) = hO (GlobalTheory.Grid.sgn ε S) T w u := by
    cases ε
    · exact hO_homMap IS IT w u
    · exact (GlobalTheory.Grid.hO_neg S' T' _ _).trans ((congrArg Neg.neg (hO_homMap IS IT w u)).trans (GlobalTheory.Grid.hO_neg S T _ _).symm)
  simp only [heisO, trH, ← map_add, AddEquiv.symm_apply_apply, symplOH, symplO, e]

private theorem lineAt_spec {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

private theorem lineAt_homMap {θ : InfFam D} (hθ : IsInfFam θ) (IS : IsoMat S S') (IT : IsoMat T T') (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (IT.pT τ * z * IS.qT τ) t = homMap IS IT (lineAt θ τ z t) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨h1, h2, h3⟩ := lineAt_spec hθ τ z
  have key : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z)) := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · let ρ : AE D →+* ℂ := (θ τ').comp (infPart D)
      have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ' x := fun x => by
        have := (hθ τ').1 x
        rw [← this]
        simp [ρ, incA, inclR, infPart]
      have e1 : IT.aP.map ρ = IT.pT τ' := by ext i j; exact hρ _
      have e2 : IS.aQ.map ρ = IS.qT τ' := by ext i j; exact hρ _
      have e3 : (lineAt θ τ z t).map ρ = _ := h3 t τ'
      show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map ρ = _
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
      split_ifs with c
      · subst c
        rw [Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (lineAt_spec hθ τ _) key]
  rfl

private theorem dRho_homMap (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (ε : Bool) (IS : IsoMat S S')
    (IT : IsoMat T T') (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ (GlobalTheory.Grid.sgn ε S') T') θ τ (IT.pT τ * z * IS.qT τ) (trH (S := S) (S' := S') IS IT f) =
      trH (S := S) (S' := S') IS IT (dRho (heisO ψ (GlobalTheory.Grid.sgn ε S) T) θ τ z f) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_homMap hθ, heisO_homMap]
  rfl

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ → ∀ (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
  pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := S') IS τ (BS τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := T') IT τ (BT τ)) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) (GlobalTheory.TriMove.polMove IT.rank_eq IS.rank_eq P) =
    GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT (pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT BS BT f P) := by
  intro D ψ θ hθ ε S S' T T' IS IT sS BS sT BT f P
  refine pure_comm IT.rank_eq IS.rank_eq (GlobalTheory.TriMove.trLE IS IT).toLinearMap _ _ (fun k g => ?_) f P
  have e : ∀ g, (GlobalTheory.TriMove.trLE IS IT).toLinearMap g = GlobalTheory.TriMove.trH IS IT g := fun _ => rfl
  have e1 : unitMap (GlobalTheory.TriMove.basMove IS k.1 (BS k.1)) (GlobalTheory.TriMove.basMove IT k.1 (BT k.1)) (finCongr IT.rank_eq k.2.1)
      (finCongr IS.rank_eq k.2.2) = _ :=
    unitMap_move IT.rank_eq IS.rank_eq _ _ (IS.pT_qT k.1) (IT.pT k.1) (BS k.1) (BT k.1) k.2.1 k.2.2
  rw [e, e]
  unfold aPlusAll aPlus crea GlobalTheory.TriMove.cartMove
  dsimp only
  rw [e1, cplxO_move ε _ _ (IS.qT_pT k.1) _ _ (IT.qT_pT k.1), dRho_homMap ψ hθ, dRho_homMap ψ hθ]
  rfl
