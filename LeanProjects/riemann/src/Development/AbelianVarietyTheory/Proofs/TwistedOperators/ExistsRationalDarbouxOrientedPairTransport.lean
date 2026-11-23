import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring

theorem hTens_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A) {G H : Matrix β β A} (x : A)
    (hGH : H * G = 1) (hG : G.map c = Gᵀ) (u u' : Matrix β γ A) :
    GlobalTheory.WeilM.hTens c Kᵀ (x • H) (uᵀ.submatrix e id * G) (u'ᵀ.submatrix e id * G) =
      -GlobalTheory.WeilM.hTens c (-G) (x • reindex e e Kᵀ) u u' := by
  have hHG : Gᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  have hmap : (u'ᵀ.submatrix e id * G).map c = (u'ᵀ.submatrix e id).map c * Gᵀ := by
    rw [← hG]
    exact Matrix.map_mul (f := (c : A →+* A))
  have hM : ((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id = u'.map c * reindex e e K * uᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
      Matrix.reindex_apply]
    refine Fintype.sum_equiv e _ _ fun a => ?_
    congr 1
    exact Fintype.sum_equiv e _ _ fun b => by simp
  rw [hTens_eq_trace, hTens_eq_trace, hmap, Matrix.transpose_mul, Matrix.transpose_smul]
  calc (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * ((u'ᵀ.submatrix e id).map c * Gᵀ) * (x • Hᵀ)).trace
      = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c * (Gᵀ * Hᵀ)).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c).trace := by
        rw [hHG, Matrix.mul_one]
    _ = x * (((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id * G).trace := by
        congr 1
        rw [← Matrix.trace_transpose]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = x * (u'.map c * reindex e e K * uᵀ * G).trace := by rw [hM]
    _ = x * (uᵀ * G * u'.map c * reindex e e K).trace := by
        rw [Matrix.mul_assoc (u'.map c * reindex e e K), Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = -((uᵀ * -G * u'.map c * (x • reindex e e Kᵀ)ᵀ).trace) := by
        rw [Matrix.transpose_smul, Matrix.transpose_reindex, Matrix.transpose_transpose, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, neg_neg,
          smul_eq_mul]

theorem exists_darboux_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β γ κ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A)
    {G H : Matrix β β A} (x : A) (hGH : H * G = 1) (hG : G.map c = Gᵀ) {JV JB : Matrix β β A} {JW : Matrix γ γ A}
    {JA : Matrix α α A} (hV : JV = -G) (hW : JW = x • reindex e e Kᵀ) (hA : JA = Kᵀ) (hB : JB = x • H)
    (M : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c (-1) JV JW) κ) (T : Matrix β γ A ≃+ Matrix α β A)
    (hT : ∀ u, T u = uᵀ.submatrix e id * G) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c 1 JA JB) κ, ∀ u, co.e (T u) = M.e u := by
  subst hV hW hA hB
  have hsmul : ∀ (r : R) (u : Matrix β γ A), T (r • u) = r • T u := by
    intro r u
    rw [hT, hT, Matrix.transpose_smul]
    exact Matrix.smul_mul r (uᵀ.submatrix e id) G
  have h1 : ∀ v, (T.toLinearEquiv hsmul).symm (T v) = v := fun v => (T.toLinearEquiv hsmul).symm_apply_apply v
  refine ⟨{ e := (T.toLinearEquiv hsmul).symm.trans M.e, form := ?_ }, ?_⟩
  · intro w w'
    obtain ⟨u, rfl⟩ := T.surjective w
    obtain ⟨u', rfl⟩ := T.surjective w'
    simp only [LinearEquiv.trans_apply]
    rw [h1, h1, ← M.form]
    simp only [GlobalTheory.WeilM.symp]
    rw [hT, hT, hTens_transpose_mul c e K x hGH hG, one_mul, neg_one_mul]
  · intro u
    simp only [LinearEquiv.trans_apply]
    rw [h1]

theorem map_transpose_inv_mul {E A : Type} [CommRing E] [CommRing A] (f : E →+* A) {α β γ : Type} [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (x : Matrix α β E) {G : Matrix β β E} (hG : IsUnit G.det) :
    (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id * G.map f = x.map f := by
  have h1 : (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id = (x * G⁻¹).map f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [h1, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

private theorem symp_smul_eq_symp_one_smul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (w w' : Matrix α β A) :
    GlobalTheory.WeilM.symp c ξ JA JB w w' = GlobalTheory.WeilM.symp c 1 JA (ξ • JB) w w' := by
  simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, one_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

set_option maxHeartbeats 800000 in

theorem exists_darboux_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hcS
  have hsgn : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]
  have hdet : IsUnit (sgn ε S).gram.det := isUnit_iff_ne_zero.mpr (Formalism.L2.Theta.gram_det_ne _)
  have hG0 : (sgn ε S).gram = -Vs.J := by
    rw [hsgn, hJ]
    cases ε <;> simp
  have hmapc : ∀ {m n : Type} (J : Matrix m n D.host.E),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (J.map D.sp.cm.sig) := by
    intro m n J
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hGJ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    rw [hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram)ᵀ := by
    rw [hmapc, hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hV.herm]
  have hGH : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
    rw [hJW]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.reindex_apply, map_mul]
  have hT : ∀ u, cS u = uᵀ.submatrix e id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    intro u
    rw [hcS u, hsgn]
  obtain ⟨co0, hco0⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
    hGH hG hGJ hW rfl rfl M.co cS hT
  obtain ⟨co, hco⟩ : ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹))
      (Fin S.rank × Fin d), (∀ u, co.e (cS u) = M.co.e u) ∧ ∀ w, co.e w = co0.e w := by
    refine ⟨⟨co0.e, fun w w' => ?_⟩, hco0, fun _ => rfl⟩
    rw [← co0.form, symp_smul_eq_symp_one_smul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0, ((sgn ε S).gram)⁻¹, co, ?_, ?_, ?_⟩
  · ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  · intro y
    obtain ⟨a, b, hab⟩ := hM.rat ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)
    refine ⟨a, b, ?_⟩
    have hu : cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F y := by
      rw [hT]
      exact map_transpose_inv_mul _ e y hdet
    rw [← hu, hco.1]
    exact hab
  · intro Φ f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun w => ?_⟩
      obtain ⟨u, rfl⟩ := cS.surjective w
      rw [← h2 u]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u => ?_⟩
      rw [← h2]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]

end GlobalTheory.SquareAgree

end
