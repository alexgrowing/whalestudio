import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousTensMap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000

open Classical

variable (D : D7)

def basAF : Module.Basis (Fin 2) (AF D.host.F) (AE D) := Algebra.TensorProduct.basis (AF D.host.F) (basE D)

def basAf : Module.Basis (Fin 2) (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis (Af D.host.F) (basE D)

theorem repr_infPart (x : AE D) (k : Fin 2) :
    (basA D).repr (infPart D x) k = fstA D.host.F ((basAF D).repr x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [infPart, basA, basAF, Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem repr_finPart (x : AE D) (k : Fin 2) :
    (basAf D).repr (finPart D x) k = sndA D.host.F ((basAF D).repr x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, basAf, basAF, Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem ae_ext {x x' : AE D} (h1 : infPart D x = infPart D x') (h2 : finPart D x = finPart D x') : x = x' := by
  apply (basAF D).ext_elem
  intro k
  have e1 := congrArg (fun y => (basA D).repr y k) h1
  have e2 := congrArg (fun y => (basAf D).repr y k) h2
  simp only [repr_infPart, repr_finPart] at e1 e2
  exact Prod.ext e1 e2

def glueA (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  (basAF D).equivFun.symm fun k => pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k)

theorem repr_glueA (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin 2) :
    (basAF D).repr (glueA D y z) k = pairA D.host.F ((basA D).repr y k) ((basAf D).repr z k) := by
  unfold glueA
  rw [← (basAF D).equivFun_apply, LinearEquiv.apply_symm_apply]

theorem infPart_glueA (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (glueA D y z) = y := by
  apply (basA D).ext_elem
  intro k
  rw [repr_infPart, repr_glueA]
  rfl

theorem finPart_glueA (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (glueA D y z) = z := by
  apply (basAf D).ext_elem
  intro k
  rw [repr_finPart, repr_glueA]
  rfl

def psiT (τ : D.what₂.Tau) : AE D →+* ℂ := (thetaC D τ).comp (infPart D)

theorem psiT_glueA (τ : D.what₂.Tau) (f : D.what₂.Tau → ℂ) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    psiT D τ (glueA D (splitInv D f) z) = f τ := by
  show thetaC D τ (infPart D (glueA D (splitInv D f) z)) = f τ
  rw [infPart_glueA, thetaC_splitInv]

theorem ae_ext' {x x' : AE D} (h1 : ∀ τ, psiT D τ x = psiT D τ x') (h2 : finPart D x = finPart D x') : x = x' := by
  refine ae_ext D ?_ h2
  rw [← sub_eq_zero]
  apply thetaC_inj D
  intro τ
  rw [map_sub, sub_eq_zero]
  exact h1 τ

theorem mat_ext {m n : ℕ} {A B : Matrix (Fin m) (Fin n) (AE D)} (h1 : ∀ τ, A.map (psiT D τ) = B.map (psiT D τ))
    (h2 : A.map (finPart D) = B.map (finPart D)) : A = B := by
  ext i j
  apply ae_ext' D
  · intro τ
    exact congrArg (fun M => M i j) (h1 τ)
  · exact congrArg (fun M => M i j) h2

theorem infPart_sigR (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [infPart, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finPart_sigR (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem thetaC_sigR (τ : D.what₂.Tau) (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    thetaC D τ (sigR (Ainf D.host.F) D.sp.cm.sig y) = starRingEnd ℂ (thetaC D τ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have hs : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] (D.sp.cm.sig e) := by
      simp [sigR]
    rw [hs, thetaC_tmul, thetaC_tmul, map_mul, gW_real, Complex.conj_ofReal]
    congr 1
    have he : D.sp.cm.sig e = star e := rfl
    rw [he, tauE_star]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem psiT_sigR (τ : D.what₂.Tau) (x : AE D) :
    psiT D τ (sigR (AF D.host.F) D.sp.cm.sig x) = starRingEnd ℂ (psiT D τ x) := by
  show thetaC D τ (infPart D (sigR (AF D.host.F) D.sp.cm.sig x)) = starRingEnd ℂ (thetaC D τ (infPart D x))
  rw [infPart_sigR, thetaC_sigR]

theorem psiT_inclR (τ : D.what₂.Tau) (e : D.host.E) : psiT D τ (inclR (AF D.host.F) e) = tauE D τ e := by
  simp [psiT, inclR, infPart, thetaC]
  rfl

theorem finPart_inclR (e : D.host.E) : finPart D (inclR (AF D.host.F) e) = inclR (Af D.host.F) e := by
  simp [finPart, inclR]

variable (V : HSp D)

theorem cT_map_psiT (τ : D.what₂.Tau) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (psiT D τ) = (M.map (psiT D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, psiT_sigR]

theorem cT_map_fin (M : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (finPart D) =
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (M.map (finPart D)) := by
  ext i j
  simp [Formalism.UG.cT, finPart_sigR]

theorem JR_map_psiT (τ : D.what₂.Tau) : (JR (AF D.host.F) V.gram).map (psiT D τ) = gramAt D V τ := by
  ext i j
  simp [JR, gramAt, psiT_inclR]

theorem JR_map_fin : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Af D.host.F) V.gram := by
  ext i j
  simp [JR, finPart_inclR]

def atM (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then g i j else (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)
    ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_atM (τ τ' : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (atM D V τ g).map (psiT D τ') = if τ' = τ then g else 1 := by
  ext i j
  simp only [atM, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  split_ifs <;> rfl

theorem fin_atM (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (atM D V τ g).map (finPart D) = 1 := by
  ext i j
  simp only [atM, Matrix.map_apply, Matrix.of_apply, finPart_glueA]

theorem atM_mul (τ : D.what₂.Tau) (g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atM D V τ (g * g') = atM D V τ g * atM D V τ g' := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, psi_atM, psi_atM, psi_atM]
    split_ifs <;> simp
  · rw [Matrix.map_mul, fin_atM, fin_atM, fin_atM, mul_one]

theorem atM_one (τ : D.what₂.Tau) : atM D V τ 1 = 1 := by
  apply mat_ext D
  · intro τ'
    rw [psi_atM]
    simp
  · rw [fin_atM]
    simp

theorem atM_unitary (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (atM D V τ g) * JR (AF D.host.F) V.gram * atM D V τ g =
      JR (AF D.host.F) V.gram := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_atM]
    split_ifs with h
    · subst h
      exact hg
    · simp
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_atM]
    simp [Formalism.UG.cT]

theorem gram_det_ne' : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hi : ∀ i, V.hT (V.frame i) (∑ j, c j • V.frame j) = 0 := by
    intro i
    have h1 := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, Pi.zero_apply] at h1
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : ∀ x, V.hT x (∑ j, c j • V.frame j) = 0 := by
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum V.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi i, smul_zero]
  have hy0 : ∑ j, c j • V.frame j = 0 := V.nondeg.2 _ hker
  funext j
  exact Fintype.linearIndependent_iff.1 V.frame.linearIndependent c hy0 j

theorem gramAt_isUnit (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have hd : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero _).mpr (gram_det_ne' D V)

def ginv (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ

theorem ginv_mul (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    ginv D V τ g * g = 1 := by
  unfold ginv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg,
    Matrix.nonsing_inv_mul _ (gramAt_isUnit D V τ)]

theorem mul_ginv (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    g * ginv D V τ g = 1 := by
  have h1 := ginv_mul D V τ g hg
  rw [← Matrix.inv_eq_left_inv h1]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h1)

def atGL (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    GL (Fin V.rank) (AE D) :=
  ⟨atM D V τ g, atM D V τ (ginv D V τ g), by rw [← atM_mul, mul_ginv D V τ g hg, atM_one],
    by rw [← atM_mul, ginv_mul D V τ g hg, atM_one]⟩

def atH (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) : GA D V :=
  (⟨atGL D V τ g hg, atM_unitary D V τ g hg⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

def matA (h : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  (HA.mat (AF D.host.F) D.sp.cm.sig V.gram h).1

theorem matA_atH (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    matA D V (atH D V τ g hg) = atM D V τ g := rfl

theorem matA_inj {h h' : GA D V} (e : matA D V h = matA D V h') : h = h' := Subtype.ext (Units.ext e)

theorem matA_mul (h h' : GA D V) : matA D V (h * h') = matA D V h * matA D V h' := rfl

theorem matA_one : matA D V 1 = 1 := rfl

theorem matA_unitary (h : GA D V) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matA D V h) * JR (AF D.host.F) V.gram * matA D V h =
      JR (AF D.host.F) V.gram := by
  exact h.2

theorem infMat_thetaC (τ : D.what₂.Tau) (h : GA D V) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) h = (matA D V h).map (psiT D τ) := by
  rfl

theorem mem_GinfC (h : GA D V) : h ∈ GinfC V ↔ (matA D V h).map (finPart D) = 1 := by
  unfold GinfC
  rw [MonoidHom.mem_ker]
  unfold finHom
  rw [Units.ext_iff]
  exact Iff.rfl

theorem isAtTau_atH (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau (thetaC D) V τ g (atH D V τ g hg) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_GinfC, matA_atH, fin_atM]
  · rw [infMat_thetaC, matA_atH, psi_atM, if_pos rfl]
  · intro τ' hτ'
    rw [infMat_thetaC, matA_atH, psi_atM, if_neg hτ']

theorem matA_of_isAtTau {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V}
    (hh : IsAtTau (thetaC D) V τ g h) : matA D V h = atM D V τ g := by
  obtain ⟨h1, h2, h3⟩ := hh
  apply mat_ext D
  · intro τ'
    rw [psi_atM, ← infMat_thetaC]
    split_ifs with e
    · subst e
      exact h2
    · exact h3 τ' e
  · rw [fin_atM]
    exact (mem_GinfC D V h).mp h1

theorem atTauExUnique_holds : AtTauExUnique D := by
  intro θ hθ V τ g hg
  obtain rfl := eq_thetaC D hθ
  refine ⟨atH D V τ g hg, isAtTau_atH D V τ g hg, fun h hh => ?_⟩
  apply matA_inj D V
  rw [matA_of_isAtTau D V hh, matA_atH]

theorem atTauUnitary_holds : AtTauUnitary D := by
  intro θ hθ V τ g h hh
  obtain rfl := eq_thetaC D hθ
  have hm := matA_of_isAtTau D V hh
  have hu := congrArg (fun M => M.map (psiT D τ)) (matA_unitary D V h)
  rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, hm, psi_atM, if_pos rfl] at hu
  exact hu

end Formalism.IndefR.Eqv

end
