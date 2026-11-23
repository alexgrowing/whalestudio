import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s m a : ℕ}

variable (E) in

def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t

variable (E N r) in

def ctData : @Measure (BlockIx N r → Ad E) (borel _) × Set (BlockIx N r → Ad E) :=
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  Classical.epsilon fun p : Measure (BlockIx N r → Ad E) × Set (BlockIx N r → Ad E) =>
    p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratN E N r) p.2 p.1 ∧ p.1 p.2 = 1

variable (r) in

def ct (f : GA E N → ℂ) (g : GA E N) : ℂ :=
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  ∫ x in (ctData E N r).2, f (unip x * g) ∂(ctData E N r).1

def cl (h : r + s = N) (φ : Sm E N) (p : GA E r × GA E s) : ℂ :=
  ct r φ.1 (blk h p) * ((chiDet r (nu E (-(s : ℝ) / 2)) p.1 : ℂˣ) : ℂ) * ((chiDet s (nu E ((r : ℝ) / 2)) p.2 : ℂˣ) : ℂ)

def evAt (g : GA E N) : Sm E N →ₗ[ℂ] ℂ := (LinearMap.proj g).comp (Sm E N).subtype

def ev2 (T : Sm E r ⊗[ℂ] Sm E s) (p : GA E r × GA E s) : ℂ :=
  TensorProduct.lid ℂ ℂ (TensorProduct.map (evAt p.1) (evAt p.2) T)

variable (E N) in

def Aut : Submodule ℂ (Sm E N) := Submodule.span ℂ {φ | IsAutForm φ}

variable (E N) in

def AutT (M : Type) [AddCommGroup M] [Module ℂ M] : Submodule ℂ (Sm E N ⊗[ℂ] M) :=
  Submodule.map₂ (TensorProduct.mk ℂ (Sm E N) M) (Aut E N) ⊤

def IsCTMap (h : r + s = N) (c : Sm E N →ₗ[ℂ] Sm E r ⊗[ℂ] Sm E s) : Prop :=
  ∀ φ, IsAutForm φ → c φ ∈ Submodule.map₂ (TensorProduct.mk ℂ (Sm E r) (Sm E s)) (Aut E r) (Aut E s) ∧
    ∀ p, ev2 (c φ) p = cl h φ p

def cT (h : r + s = N) : Sm E N →ₗ[ℂ] Sm E r ⊗[ℂ] Sm E s := Classical.epsilon (IsCTMap h)

def AutSp (V : Submodule ℂ (Sm E N)) : Prop := (∀ φ ∈ V, IsAutForm φ) ∧ IsStable V

section Passive

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def con (ℓ : M →ₗ[ℂ] ℂ) : Sm E r ⊗[ℂ] M →ₗ[ℂ] Sm E r :=
  (TensorProduct.rid ℂ (Sm E r)).toLinearMap ∘ₗ LinearMap.lTensor (Sm E r) ℓ

def sl (S : Submodule ℂ (Sm E r ⊗[ℂ] M)) : Submodule ℂ (Sm E r) := ⨆ ℓ : M →ₗ[ℂ] ℂ, S.map (con ℓ)

def Stab1 (S : Submodule ℂ (Sm E r ⊗[ℂ] M)) : Prop := ∀ o : Op E r, ∀ T ∈ S, LinearMap.rTensor M (act o) T ∈ S

def tp (W : Submodule ℂ (Sm E r)) (W' : Submodule ℂ M) : Submodule ℂ (Sm E r ⊗[ℂ] M) :=
  Submodule.map₂ (TensorProduct.mk ℂ (Sm E r) M) W W'

end Passive

def Stab2 (S : Submodule ℂ (Sm E r ⊗[ℂ] Sm E s)) : Prop := ∀ o : Op E s, ∀ T ∈ S, LinearMap.lTensor (Sm E r) (act o) T ∈ S

def slc (h : r + s = N) (g : GA E r) : Sm E N →ₗ[ℂ] Sm E s :=
  (TensorProduct.lid ℂ (Sm E s)).toLinearMap ∘ₗ LinearMap.rTensor (Sm E s) (evAt g) ∘ₗ cT h

variable (E) in

abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u

noncomputable def IsCT : (u : List (Letter E)) → Vec u → (N m : ℕ) → wsize u + m = N → Sm E m → Sm E N → Prop
  | [], _, _, _, _, ψ, φ => HEq ψ φ
  | x :: u, f, _, m, h, ψ, φ => ∀ g : GA E x.1, IsCT u f.2 (wsize u + m) m rfl (f.1.1.1 g • ψ)
      (slc (r := x.1) (s := wsize u + m) (by simpa [wsize, add_assoc] using h) g φ)

theorem IsCT.lin : ∀ (u : List (Letter E)) (f : Vec u) (N m : ℕ) (h : wsize u + m = N) (c : ℂ) (ψ ψ' : Sm E m)
    (φ φ' : Sm E N), IsCT u f N m h ψ φ → IsCT u f N m h ψ' φ' → IsCT u f N m h (c • ψ + ψ') (c • φ + φ')
  | [], _, N, m, h, c, ψ, ψ', φ, φ', h1, h2 => by
    obtain rfl : m = N := by simpa [wsize] using h
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    exact HEq.rfl
  | x :: u, f, N, m, h, c, ψ, ψ', φ, φ', h1, h2 => fun g => by
    have := IsCT.lin u f.2 _ m rfl c _ _ _ _ (h1 g) (h2 g)
    rwa [smul_comm c, ← smul_add, ← map_smul, ← map_add] at this

theorem IsCT.zero : ∀ (u : List (Letter E)) (f : Vec u) (N m : ℕ) (h : wsize u + m = N), IsCT u f N m h 0 0
  | [], _, N, m, h => by
    obtain rfl : m = N := by simpa [wsize] using h
    exact HEq.rfl
  | x :: u, f, N, m, h => fun g => by
    rw [smul_zero, map_zero]
    exact IsCT.zero u f.2 _ m rfl

def DerW (u : List (Letter E)) (h : wsize u + m = N) (V : Submodule ℂ (Sm E N)) : Submodule ℂ (Sm E m) where
  carrier := {ψ | ∀ f : Vec u, ∃ φ ∈ V, IsCT u f N m h ψ φ}
  add_mem' := fun {ψ ψ'} h1 h2 f => by
    obtain ⟨φ, a1, b1⟩ := h1 f
    obtain ⟨φ', a2, b2⟩ := h2 f
    exact ⟨φ + φ', add_mem a1 a2, by simpa using IsCT.lin u f N m h 1 _ _ _ _ b1 b2⟩
  zero_mem' := fun f => ⟨0, zero_mem _, IsCT.zero u f N m h⟩
  smul_mem' := fun c ψ h1 f => by
    obtain ⟨φ, a1, b1⟩ := h1 f
    exact ⟨c • φ, V.smul_mem c a1, by simpa using IsCT.lin u f N m h c _ _ _ _ b1 (IsCT.zero u f N m h)⟩

def Pos (u : List (Letter E)) : Prop := ∀ x ∈ u, 1 ≤ x.1

def HasWord (V : Submodule ℂ (Sm E N)) (u : List (Letter E)) : Prop :=
  Pos u ∧ ∃ h : wsize u + 0 = N, DerW u h V ≠ ⊥

def Wd (V : Submodule ℂ (Sm E N)) (X : List (Letter E)) : Prop := ∀ u, HasWord V u → u.Perm X

variable (E N) in

def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def upart (x : Letter E) : Letter E := tw x (-rexp x)

def IntDiff (u : List (Letter E)) : Prop := ∀ x ∈ u, ∀ y ∈ u, ∀ t : ℝ, y = tw x t → ∃ k : ℤ, t = k

def seg (x : Letter E) (d : ℕ) (c : ℝ) : List (Letter E) := List.ofFn fun i : Fin d => tw x (c - spehExp d i)

def IsExp (h : r + s = N) (V : Submodule ℂ (Sm E N)) (c : ℂ) : Prop :=
  ∃ T ∈ V.map (cT h), T ≠ 0 ∧ LinearMap.rTensor (Sm E s) (zc E r) T = c • T

def Neg (t : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ (r s : ℕ) (h : r + s = N), 0 < r → 0 < s → ∀ c, IsExp h V c → c.re < r * Module.finrank ℚ E * t

def Ess (t : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  AutSp V ∧ (∃ c : ℂ, c.re = N * Module.finrank ℚ E * t ∧ ∀ φ ∈ V, zc E N φ = c • φ) ∧ Neg t V

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B

def SatWord (u : List (Letter E)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∃ C : Fin u.length → Multiset ℂˣ,
    (∀ i, (CG.mk (u.get i).2).HasSat v (C i)) ∧ ∑ i, C i = B v

def IsSquareIntegrableAutomorphicSpace (V : Submodule ℂ (Sm E N)) : Prop := AutSp V ∧ ∀ φ ∈ V, IsSqInt φ.1

variable (E N) in

def SegAt : Prop := ∀ (t : ℝ) (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (u : List (Letter E)),
  Ess t V → SatFam V B → HasWord V u → IntDiff u → ∃ (x : Letter E) (d : ℕ), 1 ≤ d ∧ rexp x = 0 ∧ u.Perm (seg x d t)

def IntInf (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ (τ : E →+* ℂ) (μ : Multiset ℂ), HasInfCharGL V τ μ ∧ ∀ z ∈ μ, ∀ z' ∈ μ, ∃ k : ℤ, z - z' = k

def SpehShape (V : Submodule ℂ (Sm E N)) {a : ℕ} (π : CuspSub E a) (d : ℕ) : Prop :=
  d * a = N ∧ π.IsUnitary ∧ IsNormalised π ∧ HasSpehComp V π d

def DiscSpehInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N),
    IsDiscrete V → IntInf V → ∃ (a d : ℕ) (π : CuspSub E a), SpehShape V π d

end GlobalTheory.ResW

end
