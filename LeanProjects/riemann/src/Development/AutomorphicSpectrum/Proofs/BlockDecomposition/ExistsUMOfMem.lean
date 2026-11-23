import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

section Group

variable (k : Type) [Field k]

abbrev Qp (i t : ℕ) : Subgroup (GL (Fin (i + t)) k) := parab k (two (stdSum (rfl : i + t = i + t)))

def qBlocks (i t : ℕ) : Qp k i t →* GL (Fin i) k × GL (Fin t) k :=
  MonoidHom.prod
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) false).comp (leviProj k (two (stdSum rfl))))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) true).comp (leviProj k (two (stdSum rfl))))

def uM (n : ℕ) (y : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd y), MirU_le_Mir k n ⟨_, rfl⟩⟩

def topV (i t : ℕ) (x : Fin i → k) : Fin (i + t) → k := Fin.append x 0

def midV (i t : ℕ) (v : Fin t → k) : Fin (i + t) → k := Fin.append 0 v

theorem uM_add (n : ℕ) (a b : Fin n → k) : uM k n (a + b) = uM k n a * uM k n b := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (a + b)) = unip k n (Multiplicative.ofAdd a) * unip k n (Multiplicative.ofAdd b)
  rw [ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM k n 0 = 1 := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd 0) = 1
  rw [ofAdd_zero, map_one]

theorem uM_mem (n : ℕ) (y : Fin n → k) : uM k n y ∈ MirUin k n := ⟨_, rfl⟩

theorem exists_uM_of_mem (n : ℕ) {u : Mir k n} (hu : u ∈ MirUin k n) : ∃ y, u = uM k n y := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (y : Fin n → k) :
    levi k n g * uM k n y = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec y) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd y)

theorem topV_add_midV (i t : ℕ) (x : Fin i → k) (v : Fin t → k) :
    topV k i t x + midV k i t v = Fin.append x v := by
  funext j
  induction j using Fin.addCases <;> simp [topV, midV]

theorem exists_top_mid (i t : ℕ) (y : Fin (i + t) → k) : ∃ x v, y = topV k i t x + midV k i t v := by
  refine ⟨fun j => y (Fin.castAdd t j), fun j => y (Fin.natAdd i j), ?_⟩
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def qRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Qp k i t) (Jacquet τ (MirUin k i) ⊗[ℂ] W) :=
  twist ((extTensor (psiMinus k τ) σ).comp (qBlocks k i t))
    ((detChar (Fin t) (absPow k (1 : ℂ))).comp ((MonoidHom.snd _ _).comp (qBlocks k i t)))

abbrev hRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (HPG k i t) (V ⊗[ℂ] W) :=
  (extTensor τ σ).comp (pgProj k i t)

def clT (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    V ⊗[ℂ] W →ₗ[ℂ] Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  LinearMap.rTensor W (twKer τ (MirUin k i) 1).mkQ

def evL {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W} (p : Mir k (i + t)) :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] V ⊗[ℂ] W :=
  (LinearMap.proj p) ∘ₗ (indSpace (HPG k i t) (hRep τ σ)).subtype ∘ₗ (smoothPart (ind (HPG k i t) (hRep τ σ))).subtype ∘ₗ
    (cIndSpace (HPG k i t) (hRep τ σ)).subtype

def fibV {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (v : Fin t → k) : V ⊗[ℂ] W :=
  f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g)

def fibInt {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) : Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  clT τ W (smInt μ (fibV f g))

end Rep

end GlobalTheory.CompanionTheory.BZPsiPG

end
