import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast

noncomputable section

open Matrix GlobalTheory.PRep

namespace GlobalTheory.BZMir

section Alg

variable (k : Type) [Field k]

theorem mem_Mir_iff {n : ℕ} (g : GL (Fin (n + 1)) k) :
    g ∈ Mir k n ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = eLast k n := by
  show vecMul _ _ = _ ↔ _
  rw [vecMul_eLast]

def blockMat (n : ℕ) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Matrix (Fin n) (Fin n) k :=
  fun i j => g (Fin.castSucc i) (Fin.castSucc j)

theorem blockMat_mul {n : ℕ} (g h : Mir k n) :
    blockMat k n ((g : GL (Fin (n + 1)) k) * (h : GL (Fin (n + 1)) k) : GL (Fin (n + 1)) k) =
      blockMat k n (g : GL (Fin (n + 1)) k) * blockMat k n (h : GL (Fin (n + 1)) k) := by
  have hh := (mem_Mir_iff k (h : GL (Fin (n + 1)) k)).1 h.2
  ext i j
  have e : ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc j) = 0 := by
    rw [hh]; simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  simp [blockMat, Units.val_mul, mul_apply, Fin.sum_univ_castSucc, e]

def mirabolicProjection (n : ℕ) : Mir k n →* GL (Fin n) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => blockMat k n (g : GL (Fin (n + 1)) k)
      map_one' := by
        ext i j
        simp [blockMat, one_apply]
      map_mul' := fun g h => blockMat_mul k g h }

def levi (n : ℕ) : GL (Fin n) k →* Mir k n := (glEmb k n).codRestrict _ (glEmb_mem_Mir k n)

def MirUin (n : ℕ) : Subgroup (Mir k n) := (MirU k n).subgroupOf (Mir k n)

def chrV (ψ : AddChar k Circle) (n : ℕ) : Multiplicative (Fin (n + 1) → k) →* ℂˣ where
  toFun v := Circle.toUnits (ψ (v.toAdd (Fin.last n)))
  map_one' := by simp
  map_mul' a b := by simp [AddChar.map_add_eq_mul]

def mirChar (ψ : AddChar k Circle) (n : ℕ) : MirUin k (n + 1) →* ℂˣ :=
  (chrV k ψ n).comp ((unipEquiv k (n + 1)).symm.toMonoidHom.comp
    (Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k (n + 1))).toMonoidHom)

theorem glEmbMat_mul_colMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    glEmbMat k n A * colMat k n v = colMat k n (A.mulVec v) := by
  ext i j
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases <;> simp [glEmbMat, colMat, mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct]
  · simp [glEmbMat, colMat, mul_apply, hj]

theorem colMat_mul_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (w : Fin n → k) :
    colMat k n w * glEmbMat k n A = colMat k n w := by
  ext i j
  induction j using Fin.lastCases <;> simp [colMat, glEmbMat, mul_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem glEmb_mul_unip' (n : ℕ) (g : GL (Fin n) k) (v : Multiplicative (Fin n → k)) :
    glEmb k n g * unip k n v =
      unip k n (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) * glEmb k n g := by
  ext1
  rw [Units.val_mul, Units.val_mul]
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) * (1 + colMat k n v.toAdd) =
    (1 + colMat k n ((g : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) * glEmbMat k n (g : Matrix (Fin n) (Fin n) k)
  rw [mul_add, add_mul, mul_one, one_mul, glEmbMat_mul_colMat, colMat_mul_glEmbMat]

theorem mulVec_last_of_mem {n : ℕ} (m : GL (Fin (n + 1)) k) (hm : m ∈ Mir k n) (v : Fin (n + 1) → k) :
    ((m : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec v) (Fin.last n) = v (Fin.last n) := by
  have h := (mem_Mir_iff k m).1 hm
  have : ((m : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec v) (Fin.last n) =
      (m : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) ⬝ᵥ v := rfl
  rw [this, h]
  simp [eLast, dotProduct, Pi.single_apply]

theorem mirChar_eq (ψ : AddChar k Circle) (n : ℕ) (x : MirUin k (n + 1)) (w : Multiplicative (Fin (n + 1) → k))
    (hx : ((x : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) w) :
    mirChar k ψ n x = Circle.toUnits (ψ (w.toAdd (Fin.last n))) := by
  have key : (unipEquiv k (n + 1)).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k (n + 1))) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (((unipEquiv k (n + 1)).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k (n + 1))) x)).toAdd (Fin.last n))) = _
  rw [key]

def Q (n : ℕ) : Subgroup (Mir k (n + 1)) := (Mir k n).comap (mirabolicProjection k (n + 1))

def qProj (n : ℕ) : Q k n →* Mir k n :=
  ((mirabolicProjection k (n + 1)).comp (Q k n).subtype).codRestrict (Mir k n) (fun q => q.2)

def qEntry (n : ℕ) (g : GL (Fin (n + 2)) k) : k :=
  (g : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))

theorem qEntry_mul (n : ℕ) (a b : Mir k (n + 1)) (ha : mirabolicProjection k (n + 1) a ∈ Mir k n) :
    qEntry k n ((a : GL (Fin (n + 2)) k) * (b : GL (Fin (n + 2)) k)) =
      qEntry k n (a : GL (Fin (n + 2)) k) + qEntry k n (b : GL (Fin (n + 2)) k) := by
  have ha' : ∀ j : Fin (n + 1), ((a : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = eLast k n j := fun j =>
    congrFun ((mem_Mir_iff k _).1 ha) j
  have hb : ((b : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 b.2) (Fin.last (n + 1))
    simpa [eLast] using this
  simp only [qEntry, Units.val_mul, mul_apply, Fin.sum_univ_castSucc (n := n + 1), ha', hb, mul_one]
  simp [eLast, Pi.single_apply, add_comm]

def qChar (ψ : AddChar k Circle) (n : ℕ) : Q k n →* ℂˣ where
  toFun q := Circle.toUnits (ψ (qEntry k n ((q : Mir k (n + 1)) : GL (Fin (n + 2)) k)))
  map_one' := by
    simp [qEntry, one_apply, Fin.castSucc_ne_last]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, qEntry_mul k n (a : Mir k (n + 1)) (b : Mir k (n + 1)) a.2, AddChar.map_add_eq_mul,
      map_mul]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem levi_normalises (n : ℕ) (m : GL (Fin n) k) (u : MirUin k n) :
    ∃ h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n, (1 : MirUin k n →* ℂˣ) ⟨_, h⟩ = (1 : MirUin k n →* ℂˣ) u := by
  refine ⟨?_, rfl⟩
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
  rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  exact ⟨_, rfl⟩

variable (k) in

def psiMinus {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V) :
    Representation ℂ (GL (Fin n) k) (TwJacquet τ (MirUin k n) 1) :=
  twAct τ (MirUin k n) 1 (levi k n) (levi_normalises n)

variable (k) in

def psiPlus {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin n) k) W) :
    Representation ℂ (Mir k n) W :=
  σ.comp (mirabolicProjection k n)

theorem levi_stab (ψ : AddChar k Circle) (n : ℕ) (m : Mir k n) (u : MirUin k (n + 1)) :
    ∃ h : ((levi k (n + 1)).comp (Mir k n).subtype) m * (u : Mir k (n + 1)) *
        (((levi k (n + 1)).comp (Mir k n).subtype) m)⁻¹ ∈ MirUin k (n + 1),
      mirChar k ψ n ⟨_, h⟩ = mirChar k ψ n u := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
  have hv' : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) = unip k (n + 1) v := hv.symm
  have e : glEmb k (n + 1) (m : GL (Fin (n + 1)) k) * ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) *
      (glEmb k (n + 1) (m : GL (Fin (n + 1)) k))⁻¹ =
      unip k (n + 1) (Multiplicative.ofAdd (((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec
        v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  refine ⟨(show glEmb k (n + 1) (m : GL (Fin (n + 1)) k) * ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) *
      (glEmb k (n + 1) (m : GL (Fin (n + 1)) k))⁻¹ ∈ MirU k (n + 1) from e ▸ ⟨_, rfl⟩), ?_⟩
  rw [mirChar_eq k ψ n _ _ e, mirChar_eq k ψ n u v hv']
  simp only [toAdd_ofAdd]
  rw [mulVec_last_of_mem k _ m.2]

variable (k) in

def phiMinus (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) :
    Representation ℂ (Mir k n) (TwJacquet τ (MirUin k (n + 1)) (mirChar k ψ n)) :=
  twAct τ (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n)

variable (k) in

def qRep (ψ : AddChar k Circle) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Mir k n) W) :
    Representation ℂ (Q k n) W where
  toFun q := ((qChar k ψ n q : ℂˣ) : ℂ) • σ (qProj k n q)
  map_one' := by simp
  map_mul' a b := by
    ext w
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, map_smul, smul_smul, LinearMap.smul_apply]
    rw [mul_comm]

variable (k) in

def phiPlus (ψ : AddChar k Circle) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Mir k n) W) :
    Representation ℂ (Mir k (n + 1)) (cIndSpace (Q k n) (qRep k ψ σ)) :=
  cInd (Q k n) (qRep k ψ σ)

variable (k) in

def phiHat (ψ : AddChar k Circle) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Mir k n) W) :
    Representation ℂ (Mir k (n + 1)) (smoothPart (ind (Q k n) (qRep k ψ σ))) :=
  smInd (Q k n) (qRep k ψ σ)

variable (k) in

structure MRep (n : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  ρ : Representation ℂ (Mir k n) V

attribute [instance] MRep.acg MRep.mod

variable (k) in

def MRep.phiM (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) : MRep k n :=
  ⟨_, phiMinus k ψ τ.ρ⟩

variable (k) in

def iterPhi (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → MRep k (n + j) → MRep k n
  | 0, τ => τ
  | j + 1, τ => iterPhi ψ j (MRep.phiM k ψ τ)

variable (k) in

def derivM (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) (τ : MRep k (n + j)) :
    Representation ℂ (GL (Fin n) k) (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1) :=
  psiMinus k (iterPhi k ψ j τ).ρ

variable (k) in

def resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V) : MRep k n :=
  ⟨V, π.comp (Mir k n).subtype⟩

variable (k) in

def deriv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    Representation ℂ (GL (Fin n) k) (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1) :=
  derivM k ψ j (resM k π)

end Rep

end GlobalTheory.BZMir

end
