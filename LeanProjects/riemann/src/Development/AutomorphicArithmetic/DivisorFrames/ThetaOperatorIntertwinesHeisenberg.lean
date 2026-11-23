import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem thetaSum_rho_rho' {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U]
    {B : U → U → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Φ : (κ → AF F) → ℂ) (x y : U) :
    GlobalTheory.WeilM.thetaSum F (co.rho ψ x (co.rho ψ y Φ)) =
      ψ (⅟(2 : AF F) * B x y) * GlobalTheory.WeilM.thetaSum F (co.rho ψ (x + y) Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho, schr_schr', GlobalTheory.WeilM.thetaSum, map_add, Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    co.form]

private theorem exists_co' {D : D7} {ε : Bool} {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank)
    {Vs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E d} (M : Model D.sp.cm.sig Vs Ws)
    (hX : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))) (Fin S.rank × Fin d),
      ∀ x, co.e x = M.co.e (ptO (sgn ε S).gram e x) := by
  have hdet : IsUnit (sgn ε S).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hG : ((sgn ε S).gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = ((sgn ε S).gram.map (incA D))ᵀ := by
    ext i j
    show cA D (incA D ((sgn ε S).gram i j)) = incA D ((sgn ε S).gram j i)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  have hVJ : Vs.J = -(sgn ε S).gram := by
    rw [hX]
    cases ε
    · simp [sgn]
    · ext i j; simp [HSpace.gram]
  obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G = (sgn ε S).gram := ⟨_, rfl⟩
  rw [← hGd] at hdet hG hVJ ⊢
  have h1 : G.map (incA D) * (G⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (G⁻¹).map (incA D) * G.map (incA D) = 1 := mul_eq_one_comm.1 h1
  have hp : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), ptO G e x = ((x * (G⁻¹).map (incA D))ᵀ).submatrix id e :=
    fun _ => rfl
  have hr : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), (ptO G e x)ᵀ.submatrix e.symm id * G.map (incA D) = x := fun x => by
    have e1 : (ptO G e x)ᵀ.submatrix e.symm id = x * (G⁻¹).map (incA D) := by
      rw [hp]
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [e1, Matrix.mul_assoc, h2, Matrix.mul_one]
  let T : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ Matrix (Fin X.rank) (Fin S.rank) (AE D) :=
    { toFun := fun u => uᵀ.submatrix e.symm id * G.map (incA D)
      invFun := ptO G e
      left_inv := fun u => by
        rw [hp, Matrix.mul_assoc, h1, Matrix.mul_one]
        ext i j
        simp only [submatrix_apply, transpose_apply, id, Equiv.symm_apply_apply]
      right_inv := hr
      map_add' := fun u v => by rw [← Matrix.add_mul]; rfl }
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) h2 hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • G⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _)
    (by rw [hW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co T (fun _ => rfl)
  exact ⟨co, fun x => (congrArg co.e (hr x)).symm.trans (hco _)⟩

theorem UpperTheory.thetaOperator_intertwines_heisenberg :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M →
        (∀ x y : WO (sgn ε S) X, GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (ptO (sgn ε S).gram e x) (ptO (sgn ε S).gram e y) =
          symplO (sgn ε S) X x y) ∧
        (∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (y : WO (sgn ε S) X),
          thO M ψ (sgn ε S).gram e (M.co.rho ψ (ptO (sgn ε S).gram e y) Φ) = heisO ψ (sgn ε S) X y (thO M ψ (sgn ε S).gram e Φ)) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e (Φ + Φ') = thO M ψ (sgn ε S).gram e Φ + thO M ψ (sgn ε S).gram e Φ') ∧
        (∀ (c : ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), thO M ψ (sgn ε S).gram e (c • Φ) = c • thO M ψ (sgn ε S).gram e Φ) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e Φ = thO M ψ (sgn ε S).gram e Φ' → Φ = Φ') ∧
        ∀ f : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f ↔
          ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), thO M ψ (sgn ε S).gram e Φ = f := by
  intro D ψ ε S X d e Bs Vs Ws M hP
  have hψ : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hP.psi ▸ hP.base.std)
  obtain ⟨co, hco⟩ := exists_co' e M hP.JV hP.JW
  have hr : ∀ x, co.rho ψ x = M.co.rho ψ (ptO (sgn ε S).gram e x) := fun x => by
    simp only [GlobalTheory.WeilM.Darboux.rho, hco]
  have hth : ∀ Φ, thO M ψ (sgn ε S).gram e Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := fun Φ => by
    funext x
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, hr]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hψ rfl (one_smul _ _) (fun x => by
    obtain ⟨y, z, h⟩ := hP.good.rat (((x * (sgn ε S).gram⁻¹)ᵀ).submatrix id e)
    refine ⟨y, z, Eq.trans ?_ h⟩
    rw [hco]
    congr 1
    exact (congrArg (fun m => (transpose m).submatrix id e) (Matrix.map_mul (f := incA D))).symm)
  have hs := GlobalTheory.ThetaTransform.symplO_eq_symp (S := sgn ε S) (T := X) (ξ := 1) rfl (one_smul _ _)
  simp only [hth]
  refine ⟨fun x y => ?_, fun Φ y => ?_, h1, GlobalTheory.ThetaTransform.thetaTr_smul co, h2, h3⟩
  · rw [hs, co.form, M.co.form, hco, hco]
  · funext x
    rw [← hr]
    show GlobalTheory.WeilM.thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) = _
    rw [thetaSum_rho_rho', ← hs, GlobalTheory.ThetaTransform.invOf_two_eq]
    rfl
