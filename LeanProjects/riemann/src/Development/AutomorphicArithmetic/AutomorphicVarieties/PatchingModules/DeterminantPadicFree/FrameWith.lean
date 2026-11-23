import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa

section Coc

variable {R G : Type} [CommRing R] [Group G] {n : ℕ} (χ : G → R) (r : G → Matrix (Fin n) (Fin n) R)

def dTw (Y : Matrix (Fin n) (Fin n) R) (g : G) : Matrix (Fin n) (Fin n) R := χ g • (r g * Y * r g⁻¹) - Y

def TwCoc (S : Set G) (z : G → Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, z (g * h) = z g + χ g • (r g * z h * r g⁻¹)

def cV (a : ℕ) (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) < a ∧ ¬ (j : ℕ) < a then Z i j else 0

def cV' (a : ℕ) (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if ¬ (i : ℕ) < a ∧ (j : ℕ) < a then Z i j else 0

end Coc

structure DetFr (F G : Type) [Field F] [Group G] (n : ℕ) where
  two : (2 : F) ≠ 0
  a : ℕ
  a_pos : 1 ≤ a
  a_le : a ≤ n
  G' : Subgroup G
  comm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ G'
  χ : G →* Fˣ
  χ_triv : ∀ g ∈ G', χ g = 1
  g₀ : G
  χ_ne : χ g₀ ≠ 1
  r : G →* Matrix (Fin n) (Fin n) F
  span : Submodule.span F (r '' (G' : Set G)) = Ev F F n a
  ev : ∀ g, r g ∈ Ev F F n a
  σ : G →* G
  σσ : ∀ g, σ (σ g) = g
  χσ : ∀ g, χ (σ g) = χ g
  μ : G → Fˣ
  form : ∀ g, (r g)ᵀ * r (σ g) = (μ g : F) • (1 : Matrix (Fin n) (Fin n) F)

namespace DetFr

variable {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)

abbrev χF (g : G) : F := D.χ g

def KillsRel (z : G → Matrix (Fin n) (Fin n) F) (i j : Fin n) : Prop :=
  ∀ c : G →₀ F, (∀ g ∈ c.support, g ∈ D.G') → c.sum (fun g x => x • D.r g) = 0 →
    (c.sum fun g x => x • (z g * D.r g)) i j = 0

structure IsKap {m : ℕ} (κ : Fin m → G → Matrix (Fin n) (Fin n) F) : Prop where
  coc : ∀ j, TwCoc (fun _ => 1) D.r Set.univ (κ j)
  od : ∀ j g, κ j g ∈ Od F F n D.a
  pol : ∀ j g, κ j (D.σ g) = -(κ j g)ᵀ
  indep : ∀ (c : Fin m → F) (Y), Y ∈ Od F F n D.a → Yᵀ = -Y → (∀ g, ∑ j, c j • κ j g = dTw (fun _ => 1) D.r Y g) → c = 0

structure IsTw {m : ℕ} (κ : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F)
    (la : Fin m → G → Matrix (Fin n) (Fin n) F) : Prop where
  sq : s * s = 1
  coc : ∀ j, TwCoc D.χF D.r Set.univ (la j)
  od : ∀ j g, la j g ∈ Od F F n D.a
  pol : ∀ j g, la j (D.σ g) = s • (la j g)ᵀ
  ev : ∀ g, ph g ∈ Ev F F n D.a
  ph_mul : ∀ g h, ph (g * h) = ph g + D.χF g • (D.r g * ph h * D.r g⁻¹ +
    ∑ j, (κ j g * (D.r g * la j h * D.r g⁻¹) - (D.r g * la j h * D.r g⁻¹) * κ j g))
  ph_pol : ∀ g, ph (D.σ g) = s • (ph g)ᵀ
  ell : ∀ g ∈ D.G', (ph g * D.r g).trace + ∑ j, (la j g * κ j g * D.r g).trace = 0

end DetFr

variable {l : ℕ} [Fact l.Prime]

def NP.Ext2 {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A) : Prop :=
  x.Ext x' j ∧ (∀ v, x'.w v = GeneralLinearGroup.map j (x.w v)) ∧ x'.ty = x.ty

def etaM {X : Type} {g n : ℕ} (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X := Z.map DD.eta

def ep'M {X : Type} {g n : ℕ} (j : Fin g) (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X :=
  Z.map fun d => d.ep' j

class IsEqDVR (l : outParam ℕ) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : Prop where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  finite : Finite (IsLocalRing.ResidueField A)
  char : CharP A l

abbrev frameWith (F : GFrame l) (I : F.St → Subgroup F.η.ker) : GFrame l := { F with Iu := I, D0 := ⊥, I0 := ⊥ }

end UpperTheory.V.Pa
