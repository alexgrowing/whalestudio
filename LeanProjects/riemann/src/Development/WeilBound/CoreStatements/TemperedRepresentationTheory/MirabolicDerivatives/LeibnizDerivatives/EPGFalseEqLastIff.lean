import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BZMir.Leib

@[reducible] def TwoT (V W : Type) : Bool → Type
  | false => V
  | true => W

instance instACGTwoT {V W : Type} [AddCommGroup V] [AddCommGroup W] : ∀ x, AddCommGroup (TwoT V W x)
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup W)

instance instModTwoT {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W] :
    ∀ x, Module ℂ (TwoT V W x)
  | false => inferInstanceAs (Module ℂ V)
  | true => inferInstanceAs (Module ℂ W)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twoRep {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    ∀ x : Bool, Representation ℂ (GL (Two (Fin r) (Fin t) x) k) (TwoT V W x)
  | false => π₁
  | true => π₂

def prod2 {r t N : ℕ} (hN : r + t = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :=
  multiProd (k := k) (two (stdSum hN)) (twoRep π₁ π₂)

variable (k) in

def eGP (m j : ℕ) : (Σ x, Two (Fin m) (Fin (j + 1)) x) ≃ Fin (m + j + 1) := two (stdSum rfl)

variable (k) in

def MirabolicParabolic (m j : ℕ) : Subgroup (Mir k (m + j)) := (parab k (eGP m j)).comap (Mir k (m + j)).subtype

variable (k) in

def hgpIncl (m j : ℕ) : MirabolicParabolic k m j →* parab k (eGP m j) where
  toFun h := ⟨((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k), h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem blockIndex_true_last (m j : ℕ) : eGP m j ⟨true, Fin.last j⟩ = Fin.last (m + j) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_true_eq_last_iff (m j : ℕ) (b : Fin (j + 1)) : eGP m j ⟨true, b⟩ = Fin.last (m + j) ↔ b = Fin.last j := by
  have hb : ((GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩ : Fin (m + j + 1)) : ℕ) = m + (b : ℕ) := by
    first
      | rfl
      | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
  rw [Fin.ext_iff, hb, Fin.ext_iff, Fin.val_last, Fin.val_last]
  omega

theorem blockIndex_false_ne_last (m j : ℕ) (a : Fin m) : eGP m j ⟨false, a⟩ ≠ Fin.last (m + j) := by
  intro h
  have ha : ((GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩ : Fin (m + j + 1)) : ℕ) = (a : ℕ) := by
    first
      | rfl
      | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
  have h2 := congrArg Fin.val h
  rw [ha, Fin.val_last] at h2
  have := a.isLt
  omega

theorem hgp_block_mem (m j : ℕ) (h : MirabolicParabolic k m j) :
    (leviProj k (eGP m j) (hgpIncl k m j h) true : GL (Fin (j + 1)) k) ∈ Mir k j := by
  refine (GlobalTheory.BZMir.mem_Mir_iff k _).2 ?_
  have hg := (GlobalTheory.BZMir.mem_Mir_iff k _).1 (h : GlobalTheory.BZMir.Mir k (m + j)).2
  funext b
  refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
    (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true (Fin.last j) b).trans ?_
  change ((((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
    (GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.last j⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)) = _
  rw [GlobalTheory.BZMir.Leib.blockIndex_true_last, hg]
  by_cases hb : b = Fin.last j
  · subst hb
    simp [GlobalTheory.BZMir.eLast, GlobalTheory.BZMir.Leib.blockIndex_true_last]
  · have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩ ≠ Fin.last (m + j) :=
      fun h' => hb ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j b).1 h')
    simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hne, hb]

variable (k) in

def gpProj (m j : ℕ) : MirabolicParabolic k m j →* GL (Fin m) k × Mir k j :=
  MonoidHom.prod ((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) false).comp
      ((leviProj k (eGP m j)).comp (hgpIncl k m j)))
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) true).comp
      ((leviProj k (eGP m j)).comp (hgpIncl k m j))).codRestrict (Mir k j) (hgp_block_mem m j))

def prodGP {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin m) k) V) (τ : Representation ℂ (Mir k j) W) :
    Representation ℂ (Mir k (m + j)) (cIndSpace (MirabolicParabolic k m j) ((extTensor ρ τ).comp (gpProj k m j))) :=
  cInd (MirabolicParabolic k m j) ((extTensor ρ τ).comp (gpProj k m j))

variable (k) in

def ePG (i t : ℕ) : (Σ x, Two (Fin (i + 1)) (Fin t) x) ≃ Fin (i + t + 1) :=
  two ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).trans
      ((Equiv.sumAssoc _ _ _).symm.trans ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv)))))

variable (k) in

def HPG (i t : ℕ) : Subgroup (Mir k (i + t)) := (parab k (ePG i t)).comap (Mir k (i + t)).subtype

variable (k) in

def hpgIncl (i t : ℕ) : HPG k i t →* parab k (ePG i t) where
  toFun h := ⟨((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k), h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ePG_false_last (i t : ℕ) : ePG i t ⟨false, Fin.last i⟩ = Fin.last (i + t) := by
  apply Fin.ext
  simp [GlobalTheory.BZMir.Leib.ePG, GlobalTheory.SmGL.two, finSumFinEquiv_symm_last]

theorem ePG_false_eq_last_iff (i t : ℕ) (b : Fin (i + 1)) : ePG i t ⟨false, b⟩ = Fin.last (i + t) ↔ b = Fin.last i := by
  constructor
  · intro h
    by_contra hb
    obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
    have h2 := congrArg Fin.val h
    have ha := a.isLt
    simp [GlobalTheory.BZMir.Leib.ePG, GlobalTheory.SmGL.two,
      finSumFinEquiv_symm_apply_castSucc] at h2 <;> omega
  · rintro rfl
    exact GlobalTheory.BZMir.Leib.ePG_false_last i t

theorem hpg_block_mem (i t : ℕ) (h : HPG k i t) :
    (leviProj k (ePG i t) (hpgIncl k i t h) false : GL (Fin (i + 1)) k) ∈ Mir k i := by
  refine (GlobalTheory.BZMir.mem_Mir_iff k _).2 ?_
  have hg := (GlobalTheory.BZMir.mem_Mir_iff k _).1 (h : GlobalTheory.BZMir.Mir k (i + t)).2
  funext b
  refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.ePG i t)
    (GlobalTheory.BZMir.Leib.hpgIncl k i t h) false (Fin.last i) b).trans ?_
  change ((((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
    (GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.last i⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩)) = _
  rw [GlobalTheory.BZMir.Leib.ePG_false_last, hg]
  by_cases hb : b = Fin.last i
  · subst hb
    simp [GlobalTheory.BZMir.eLast, GlobalTheory.BZMir.Leib.ePG_false_last]
  · have hne : GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩ ≠ Fin.last (i + t) :=
      fun h' => hb ((GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff i t b).1 h')
    simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hne, hb]

variable (k) in

def pgProj (i t : ℕ) : HPG k i t →* Mir k i × GL (Fin t) k :=
  MonoidHom.prod
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin (i + 1)) (Fin t) x) k) false).comp
      ((leviProj k (ePG i t)).comp (hpgIncl k i t))).codRestrict (Mir k i) (hpg_block_mem i t))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin (i + 1)) (Fin t) x) k) true).comp
      ((leviProj k (ePG i t)).comp (hpgIncl k i t)))

def prodPG {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Mir k (i + t)) (cIndSpace (HPG k i t) ((extTensor τ σ).comp (pgProj k i t))) :=
  cInd (HPG k i t) ((extTensor τ σ).comp (pgProj k i t))

end GlobalTheory.BZMir.Leib

end
