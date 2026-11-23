import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      GlobalTheory.BZMir.eLast k n j :=
    fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
  have hblock : ∀ i j : Fin n,
      ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
        (1 : Matrix (Fin n) (Fin n) k) i j :=
    fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hy
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
  apply Units.ext
  ext i j
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
  rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
      GlobalTheory.BZMir.eLast]
  · simp [hrow, GlobalTheory.BZMir.eLast]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

theorem mk_act_unip {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (u : Mir k n) (hu : u ∈ MirUin k n) (v : V) :
    (Submodule.Quotient.mk (τ u v) : TwJacquet τ (MirUin k n) 1) = Submodule.Quotient.mk v := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨⟨u, hu⟩, v, ?_⟩
  simp

theorem mk_act {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (x : Mir k n) (v : V) :
    (Submodule.Quotient.mk (τ x v) : TwJacquet τ (MirUin k n) 1) =
      psiMinus k τ (mirabolicProjection k n x) (Submodule.Quotient.mk v) := by
  have hu : (levi k n (mirabolicProjection k n x))⁻¹ * x ∈ MirUin k n :=
    mem_of_mirProj_eq_one k n _ (by rw [map_mul, map_inv, mirProj_levi, inv_mul_cancel])
  have hx : x = levi k n (mirabolicProjection k n x) * ((levi k n (mirabolicProjection k n x))⁻¹ * x) := by group
  calc (Submodule.Quotient.mk (τ x v) : TwJacquet τ (MirUin k n) 1)
      = Submodule.Quotient.mk (τ (levi k n (mirabolicProjection k n x)) (τ ((levi k n (mirabolicProjection k n x))⁻¹ * x) v)) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hx]
    _ = psiMinus k τ (mirabolicProjection k n x) (Submodule.Quotient.mk (τ ((levi k n (mirabolicProjection k n x))⁻¹ * x) v)) := rfl
    _ = _ := by rw [mk_act_unip τ _ hu v]

theorem twKer_le_ker {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k n) V) (σ : Representation ℂ (GL (Fin n) k) W)
    (h : Representation.IntertwiningMap τ (psiPlus k σ)) :
    twKer τ (MirUin k n) 1 ≤ LinearMap.ker h.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
  rw [show psiPlus k σ (u : Mir k n) = σ (mirabolicProjection k n u) from rfl, mirProj_eq_one_of_mem k n _ u.2, map_one,
    Module.End.one_apply, sub_self]

def adjPsiEquiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k n) V) (σ : Representation ℂ (GL (Fin n) k) W) :
    Representation.IntertwiningMap (psiMinus k τ) σ ≃ Representation.IntertwiningMap τ (psiPlus k σ) where
  toFun f := LinearMap.intertwiningMap_of_isIntertwiningMap τ (psiPlus k σ)
    (f.toLinearMap ∘ₗ (twKer τ (MirUin k n) 1).mkQ) (fun x v => by
      show f (Submodule.Quotient.mk (τ x v)) = σ (mirabolicProjection k n x) (f (Submodule.Quotient.mk v))
      rw [mk_act, Representation.IntertwiningMap.isIntertwining])
  invFun h := LinearMap.intertwiningMap_of_isIntertwiningMap (psiMinus k τ) σ
    ((twKer τ (MirUin k n) 1).liftQ h.toLinearMap (twKer_le_ker τ σ h)) (fun g q => by
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        rw [psiMinus_mk]
        simp only [Submodule.liftQ_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
        rw [show psiPlus k σ (levi k n g) = σ (mirabolicProjection k n (levi k n g)) from rfl, mirProj_levi])
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply Submodule.linearMap_qext
    rfl
  right_inv h := by
    apply Representation.IntertwiningMap.ext
    rfl

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
