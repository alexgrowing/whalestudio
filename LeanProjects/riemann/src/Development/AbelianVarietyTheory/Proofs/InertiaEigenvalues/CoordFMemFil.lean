import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.HTBasis

variable {l : ℕ} [Fact l.Prime]

def repOf {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp r)

theorem repOf_apply {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (v : Fin m → ↥LL.1) :
    repOf r g v = (r g : Matrix (Fin m) (Fin m) ↥LL.1).mulVec v := rfl

variable (P : LocPrime l) (LL : FinExt l) (m : ℕ)

def embF : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp LL.1.val

theorem embF_apply (x : ↥LL.1) : embF P LL x = algebraMap (Om l) P.R.BdR (x : Om l) := rfl

def mulF : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (embF P LL) (AlgHom.id ℚ_[l] P.R.BdR) fun _ _ => Commute.all _ _

@[simp] theorem mulF_tmul (c : ↥LL.1) (b : P.R.BdR) : mulF P LL (c ⊗ₜ[ℚ_[l]] b) = embF P LL c * b := by
  simp [mulF]

def coordF : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin m → P.R.BdR) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : Fin m → ↥LL.1) (b : P.R.BdR) j => embF P LL (v j) * b)
    (fun v v' b => by funext j; simp [add_mul])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_assoc])
    (fun v b b' => by funext j; simp [mul_add])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_left_comm]))

@[simp] theorem coordF_tmul (v : Fin m → ↥LL.1) (b : P.R.BdR) :
    coordF P LL m (v ⊗ₜ[ℚ_[l]] b) = fun j => embF P LL (v j) * b := rfl

section Lemmas

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (m : ℕ)

theorem coordF_sm (r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) r x) = mulF P LL r • coordF P LL m x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs, add_smul]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul v b' =>
      funext j
      simp only [GlobalTheory.DRFil.sm_tmul, coordF_tmul, mulF_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring

theorem embF_mem_fil (K : FinExt l) (c : ↥LL.1) : embF P LL c ∈ (P.PD K).Fil 0 :=
  (GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem _)

theorem coordF_mem_fil (K : FinExt l) {n : ℤ} {x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n) (j : Fin m) :
    coordF P LL m x j ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K (v j)) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_mem_fil (K : FinExt l) {n : ℤ} {r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR}
    (hr : r ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) n) : mulF P LL r ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K v) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_idem (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥K.1, ((τ x : ↥LL.1) : Om l) = (x : Om l)) :
    mulF P LL (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  rw [h, map_sum]
  have e : ∀ i, mulF P LL (a i ⊗ₜ[ℚ_[l]] algebraMap ↥K.1 P.R.BdR (c i)) =
      algebraMap (Om l) P.R.BdR (((a i * τ (c i) : ↥LL.1)) : Om l) := by
    intro i
    rw [mulF_tmul, embF_apply, IntermediateField.coe_mul, map_mul, hτ]
    rfl
  simp only [e, ← map_sum]
  have h2 := congrArg (fun x : ↥LL.1 => (x : Om l)) h1
  simp only [IntermediateField.coe_sum, IntermediateField.coe_one] at h2
  simp only [IntermediateField.coe_mul] at h2 ⊢
  rw [h2, map_one]

theorem coordF_act (K : FinExt l) (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (hg : ∀ x ∈ LL.1, (g : GQ l) x = x) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (actVdR (P.PD K) (repOf r) g x) =
      ((r g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
        (fun j => P.actQdR (g : GQ l) (coordF P LL m x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp
  | tmul v b =>
    have hfix : ∀ c : ↥LL.1, P.actQdR (g : GQ l) (embF P LL c) = embF P LL c := fun c => by
      rw [embF_apply, P.actQdR_Om, hg _ c.2]
    funext j
    simp only [actVdR, AlgebraTensorModule.map_tmul, coordF_tmul, repOf_apply, P.PD_actdR,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, hfix, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [mul_assoc]
    exact congrArg _ (congrArg _ (P.PD_actdR K g b))

end Lemmas

section Theta

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def thetaOf (T : LocTied l P AI) : Formalism.MainNotions.LocalSituation.ThetaL P AI :=
  (GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI T).some

def colHT (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℂ_[l] :=
  Matrix.of fun j i => J.θ (((GlobalTheory.DeRhamSymbol.tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j)

end Theta

end GlobalTheory.HTBasis
