import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def brS (x y : S.V) : E := S.hT y x

def perpS (U : Submodule E S.V) : Submodule E S.V where
  carrier := {y | ∀ x ∈ U, S.hT x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    simp [map_add, ha x hx, hb x hx]
  zero_mem' := by intro x _; simp
  smul_mem' := by
    intro c a ha x hx
    simp [map_smul, ha x hx]

structure FlagG (r : ℕ) (T : E) where
  e : Fin r → S.V
  z : S.V
  e_indep : LinearIndependent E e
  e_iso : ∀ a b, S.hT (e a) (e b) = 0
  z_orth : ∀ a, S.hT (e a) z = 0
  z_norm : S.hT z z = -T

variable {S} {r : ℕ} {T : E}

def FlagG.fvec (F : FlagG S r T) : Fin (r + 1) → S.V := Fin.snoc (α := fun _ => S.V) F.e F.z

def FlagG.Xa (F : FlagG S r T) (a : ℕ) : Submodule E S.V :=
  Submodule.span E (F.e '' {i | i.1 < a})

def FlagG.X (F : FlagG S r T) : Submodule E S.V := Submodule.span E (Set.range F.e)

def FlagG.Xplus (F : FlagG S r T) : Submodule E S.V := F.X ⊔ Submodule.span E {F.z}

def FlagG.XplusPerp (F : FlagG S r T) : Submodule E S.V := perpS S F.Xplus

def FlagG.coefX (F : FlagG S r T) (y : S.V) (a : Fin r) : E := by
  classical
  exact if h : y ∈ Submodule.span E (Set.range F.e) then (F.e_indep.repr ⟨y, h⟩) a else 0

def FlagG.level (F : FlagG S r T) (x : S.V) : ℕ := sInf {a | x ∈ F.Xa a}

def Zhat {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => brS S (F'.fvec b) (F.fvec a)

def leadMinorE {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def Dl {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (l : ℕ) : E := leadMinorE (Zhat F F') l

def Gflag {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : E :=
  Dl F F' (r + 1) * star (Dl F F' (r + 1)) - T * T' * (Dl F F' r * star (Dl F F' r))

def Isp {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V := F.X ⊓ F'.X

def LieU (S : HSpace E) : Set (S.V →ₗ[E] S.V) := {Y | ∀ x y, S.hT (Y x) y + S.hT x (Y y) = 0}

def FlagG.LieN (F : FlagG S r T) : Set (S.V →ₗ[E] S.V) :=
  {Y | Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F.Xa a, Y x ∈ F.Xa (a - 1)) ∧
    ∀ x ∈ perpS S F.X, Y x ∈ F.X}

def FlagG.ell (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : E :=
  ∑ i : Fin r, F.coefX (Y (F.fvec i.succ)) i

def FlagG.dpsi (K : Type) [Field K] [Algebra K E] (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : K :=
  Algebra.trace K E (F.ell Y)

def Relevant (K : Type) [Field K] [Algebra K E] {T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Prop :=
  ∀ Y ∈ F.LieN ∩ F'.LieN, F.dpsi K Y = F'.dpsi K Y

def xv (S : HSpace E) (x v : S.V) : S.V →ₗ[E] S.V where
  toFun y := brS S y v • x - brS S y x • v
  map_add' y y' := by simp only [brS, map_add, add_smul]; abel
  map_smul' c y := by simp [brS, map_smul, smul_sub, mul_smul]

def blockEnds {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 j).filter (fun l => Dl F F' l ≠ 0)

def frameExp (r l : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 l, (r + 1 - a)

def Nloc (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (r l : ℕ) (x : E) : ℚ :=
  FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x *
    dd ^ (-(2 * (frameExp r l : ℤ))))

def absReal (rd : ℝ) (τ : E →+* ℂ) (r l : ℕ) (x : E) : ℝ :=
  ‖τ x‖ * rd ^ (-(2 * (frameExp r l : ℝ)))

end Generic

section D7

variable (D : D7)

@[reducible] def starE : StarRing D.host.E := D.host.cmStar

attribute [local instance] starE

abbrev VS : HSpace D.host.E := D.sp.Y 0

abbrev FlagS (u : D.what₂.Word) : Type :=
  FlagG (VS D) D.R.rS ((((D.mem u).A.T : ℕ) : D.host.E))

def ddS : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

def embS (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

end D7

end Formalism.MainNotions.S
