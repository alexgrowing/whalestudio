import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CompPiVLocGSame
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Sub NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst)

abbrev tV (v : HeightOneSpectrum (𝓞 I.F)) : Af I.F ⊗[I.F] I.E →+* Fv I.F v ⊗[I.F] I.E :=
  tensMap (E := I.E) (evalV I.F v)

theorem LocIdxLift_tV_theta_same (p : HeightOneSpectrum (𝓞 I.F)) (t : Fv I.F p ⊗[I.F] I.E) :
    tV I p (thetaP I p t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (evalV I.F p) (AlgHom.id I.F I.E))
      (TensorProduct.map (sL I p) LinearMap.id (a ⊗ₜ[I.F] e)) = a ⊗ₜ[I.F] e
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show evalV I.F p (singleV I.F p a) ⊗ₜ[I.F] e = a ⊗ₜ[I.F] e
    rw [Comp_evalV, Comp_single_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem LocIdxLift_tV_theta_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) (t : Fv I.F p ⊗[I.F] I.E) :
    tV I v (thetaP I p t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (evalV I.F v) (AlgHom.id I.F I.E))
      (TensorProduct.map (sL I p) LinearMap.id (a ⊗ₜ[I.F] e)) = 0
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show evalV I.F v (singleV I.F p a) ⊗ₜ[I.F] e = 0
    rw [Comp_evalV, Comp_single_ne I p v h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem LocIdxLift_inj (t : Af I.F ⊗[I.F] I.E) (h : ∀ v, tV I v t = 0) : t = 0 := by
  have h0 := PI.FinKW.local_vector_injective I ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm t) (fun v => by
    have e : PI.FinKW.psiV I v ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm t) = tV I v t := by
      show (Algebra.TensorProduct.map (evalV I.F v) (AlgHom.id I.F I.E))
        ((Algebra.TensorProduct.comm I.F I.E (Af I.F)) ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm t)) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [e]; exact h v)
  simpa using h0

theorem LocIdxLift_ext {m : ℕ} (M N : Matrix (Fin m) (Fin m) (Af I.F ⊗[I.F] I.E))
    (h : ∀ v, M.map (tV I v) = N.map (tV I v)) : M = N := by
  ext i j
  rw [← sub_eq_zero]
  apply LocIdxLift_inj I
  intro v
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun A => A i j) (h v)

def liftM (p : HeightOneSpectrum (𝓞 I.F)) (Y : Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
    Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E) :=
  1 + (Y - 1).map (thetaP I p)

theorem LocIdxLift_liftM_same (p : HeightOneSpectrum (𝓞 I.F))
    (Y : Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : (liftM I p Y).map (tV I p) = Y := by
  ext i j
  simp only [liftM, Matrix.map_apply, Matrix.add_apply, map_add, LocIdxLift_tV_theta_same,
    Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem LocIdxLift_liftM_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p)
    (Y : Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : (liftM I p Y).map (tV I v) = 1 := by
  ext i j
  simp only [liftM, Matrix.map_apply, Matrix.add_apply, map_add, LocIdxLift_tV_theta_ne I p v h, add_zero,
    Matrix.one_apply]
  split_ifs <;> simp

theorem LocIdxLift_map_one (v : HeightOneSpectrum (𝓞 I.F)) :
    (1 : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (tV I v) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def liftGL (p : HeightOneSpectrum (𝓞 I.F)) (y : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
    GL (Fin I.n) (Af I.F ⊗[I.F] I.E) where
  val := liftM I p y
  inv := liftM I p ↑y⁻¹
  val_inv := by
    apply LocIdxLift_ext I
    intro v
    rw [Matrix.map_mul, LocIdxLift_map_one]
    by_cases h : v = p
    · subst h; rw [LocIdxLift_liftM_same, LocIdxLift_liftM_same, Units.mul_inv]
    · rw [LocIdxLift_liftM_ne I p v h, LocIdxLift_liftM_ne I p v h, mul_one]
  inv_val := by
    apply LocIdxLift_ext I
    intro v
    rw [Matrix.map_mul, LocIdxLift_map_one]
    by_cases h : v = p
    · subst h; rw [LocIdxLift_liftM_same, LocIdxLift_liftM_same, Units.inv_mul]
    · rw [LocIdxLift_liftM_ne I p v h, LocIdxLift_liftM_ne I p v h, mul_one]

theorem LocIdxLift_cT_map {A B : Type} [CommRing A] [CommRing B] (s : A →+* A) (s' : B →+* B) (f : A →+* B)
    (hf : f.comp s = s'.comp f) {m : ℕ} (M : Matrix (Fin m) (Fin m) A) :
    (Formalism.UG.cT s M).map f = Formalism.UG.cT s' (M.map f) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
  exact congrArg (fun φ : A →+* B => φ (M j i)) hf

theorem LocIdxLift_mem (p : HeightOneSpectrum (𝓞 I.F)) (y : HA (Fv I.F p) I.cm.sig I.J) :
    liftGL I p (HA.mat (Fv I.F p) I.cm.sig I.J y) ∈ HR (Af I.F) I.cm.sig I.J := by
  show Formalism.UG.cT (sigR (Af I.F) I.cm.sig) (liftM I p _) * JR (Af I.F) I.J * liftM I p _ = JR (Af I.F) I.J
  apply LocIdxLift_ext I
  intro v
  have hJ : (JR (Af I.F) I.J).map (tV I v) = JR (Fv I.F v) I.J := by
    ext i j
    simp [JR, tV, tensMap_inclR]
  rw [Matrix.map_mul, Matrix.map_mul,
    LocIdxLift_cT_map _ (sigR (Fv I.F v) I.cm.sig) _ (tensMap_sigR (evalV I.F v) I.cm.sig), hJ]
  by_cases h : v = p
  · subst h
    rw [LocIdxLift_liftM_same]
    exact y.2
  · rw [LocIdxLift_liftM_ne I p v h, Formalism.UG.cT_one, one_mul, mul_one]

def liftHA (p : HeightOneSpectrum (𝓞 I.F)) (y : HA (Fv I.F p) I.cm.sig I.J) : HA (Af I.F) I.cm.sig I.J :=
  ⟨liftGL I p (HA.mat (Fv I.F p) I.cm.sig I.J y), LocIdxLift_mem I p y⟩

theorem LocIdxLift_piV_same (p : HeightOneSpectrum (𝓞 I.F)) (y : HA (Fv I.F p) I.cm.sig I.J) :
    piV I p (liftHA I p y) = y := by
  apply Bridge_HA_ext
  rw [Comp_piV_mat]
  exact LocIdxLift_liftM_same I p _

theorem LocIdxLift_piV_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) (y : HA (Fv I.F p) I.cm.sig I.J) :
    piV I v (liftHA I p y) = 1 := by
  apply Bridge_HA_ext
  rw [Comp_piV_mat]
  exact LocIdxLift_liftM_ne I p v h _

theorem LocIdxLift_vecV_mulVec (v : HeightOneSpectrum (𝓞 I.F)) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ w) = (M.map (PI.FinKW.psiV I v)) *ᵥ PI.FinKW.vecV I v w := by
  funext i
  simp [PI.FinKW.vecV, Matrix.mulVec, dotProduct, map_sum, map_mul]

variable (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I)

theorem LocIdxLift_psiV_fmat (v : HeightOneSpectrum (𝓞 I.F)) (x : I.Gf) :
    (I.fmat x).map (PI.FinKW.psiV I v) =
      ((HA.mat (Fv I.F v) I.cm.sig I.J (piV I v (tf I hb x)) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) := by
  rw [Comp_piV_mat, Bridge_mat]
  rfl

theorem LocIdxLift_Kg (p : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : g ≠ 0) (y : HA (Fv I.F p) I.cm.sig I.J)
    (hy : y ∈ Formalism.L2.SG.TypedSets.Kgv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) g p) :
    ∃ x ∈ I.Kg g, piV I p (tf I hb x) = y := by
  obtain ⟨x, hx⟩ := Bridge_tf_surjective I hb (liftHA I p y)
  have hcomp : ∀ v, v ≠ p → piV I v (tf I hb x) = 1 := fun v h => by rw [hx, LocIdxLift_piV_ne I p v h]
  have hsame : piV I p (tf I hb x) = y := by rw [hx, LocIdxLift_piV_same]
  refine ⟨x, ⟨?_, ?_⟩, hsame⟩
  · rw [← Bridge_mem_Kf_iff I hb, Kf, Subgroup.mem_iInf]
    intro v
    show HA.mat (Fv I.F v) I.cm.sig I.J (piV I v (tf I hb x)) ∈ Kloc v (I.L : Set (Fin I.n → I.E))
    by_cases h : v = p
    · subst h; rw [hsame]; exact hy.1
    · rw [hcomp v h]; exact (Kloc v _).one_mem
  · intro w hw
    let w' := (I.fmat x - 1) *ᵥ w
    let c : I.E ⊗[I.F] Af I.F := algebraMap I.F _ ((g : I.F)⁻¹)
    have hgF : (g : I.F) ≠ 0 := by exact_mod_cast hg
    refine ⟨c • w', ?_, ?_⟩
    · apply PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I
      intro v
      have e1 : PI.FinKW.vecV I v (c • w') = PI.FinKW.psiV I v c • PI.FinKW.vecV I v w' := by
        funext i; simp [PI.FinKW.vecV, map_mul]
      have e2 : PI.FinKW.vecV I v w' = ((HA.mat (Fv I.F v) I.cm.sig I.J (piV I v (tf I hb x)) :
          GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) - 1 : Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) *ᵥ
            PI.FinKW.vecV I v w := by
        rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat I hb,
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [e1, e2]
      by_cases h : v = p
      · subst h
        have hwv := PI.FinKW.LocTo.mem_local_lattice_iff I w hw v
        obtain ⟨z, hz, he⟩ := hy.2 _ hwv
        rw [hsame, he]
        convert hz using 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, c, AlgHom.commutes, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Pi.mul_apply,
          Pi.natCast_apply]
        rw [← mul_assoc, ← map_natCast (algebraMap I.F (Fv I.F v ⊗[I.F] I.E)) g, ← map_mul,
          inv_mul_cancel₀ hgF, map_one, one_mul]
      · rw [hcomp v h]
        have : ((HA.mat (Fv I.F v) I.cm.sig I.J (1 : HA (Fv I.F v) I.cm.sig I.J) :
            GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) = 1 := rfl
        rw [this, sub_self, Matrix.zero_mulVec, smul_zero]
        exact zero_mem _
    · rw [smul_smul]
      have : (g : I.E ⊗[I.F] Af I.F) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) g, ← map_mul, mul_inv_cancel₀ hgF, map_one]
      rw [this, one_smul]

end PI.MassDataKppVolLemmas
