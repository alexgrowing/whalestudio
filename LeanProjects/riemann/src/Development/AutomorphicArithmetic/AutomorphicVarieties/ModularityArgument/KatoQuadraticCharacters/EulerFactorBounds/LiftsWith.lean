import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.WkTopEq
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH

noncomputable section

open scoped MatrixGroups Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def LiftsWith (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w c : ℕ) : Prop :=
  ∀ (n : ℕ) (H : Subgroup SL(2, ℤ)) (M' : ℕ), 0 < M' → CongruenceSubgroup.Gamma M' ≤ H →
    H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) → ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ →
      ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), a ∈ X.Un (l ^ n) → InvH X H (l ^ n) a → Rep X l n a x →
        ∃ b, LiftB X l N w n c (trH X l w γ lam x) b

def cL (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) : ℕ := Classical.epsilon (LiftsWith X l N w)

def InvM (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (a : X.Fn l) : Prop :=
  (∃ t, PolMod X l w n t ∧ CgF X l n a t) ∧
  (∀ γ ∈ Gam N l, CgF X l n (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) a) a) ∧
  ∃ b, LiftB X l N w n (cL X l N w) a b

def slD (X : Tower Ω ε) (N : ℕ) (f : X.K) : X.K := X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f

def clsG (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M w c d : ℕ) [NeZero M] (g : SL(2, ℤ)) (x' y' : Fin 2 → ℚ)
    (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  trM X l N M w g (clsK X l n (wGen X M l n (slD X N (siegel X c x')) (slD X N (siegel X d y')) σ))

def shB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M : ℕ) (z : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : X.Fn l :=
  X.galB l (repM M y) (z ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))

def cD (N M₀ : ℕ) {M : ℕ} (m : Matrix (Fin 2) (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M₀) :=
  !![((m 0 0).val : ZMod M₀), ((N * (m 0 1).val : ℕ) : ZMod M₀); (((m 1 0).val / N : ℕ) : ZMod M₀), ((m 1 1).val : ZMod M₀)]

def Cnd (l N : ℕ) (g : SL(2, ℤ)) {M : ℕ} (m : Matrix (Fin 2) (Fin 2) (ZMod M)) : Prop :=
  ((m 1 0).val : ZMod N) = 0 ∧ ((m 0 0).val : ZMod N) = (en g 0 0 : ZMod N) ∧
    (en g 1 0 : ZMod l) * ((m 0 0).val : ZMod l) = (en g 0 0 : ZMod l) * ((m 1 0).val : ZMod l)

open Classical in

def Xi (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x y : Row M₀)
    (P : (ZMod M)ˣ → Prop) (a : Fam X M₀) : X.Fn l := fun u =>
  ∑ m ∈ Finset.univ.filter (fun m : GL (Fin 2) (ZMod M) =>
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)),
    (((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) *
        ((((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0).val : ℤ_[l]) * u 0 +
          (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1).val : ℤ_[l]) * u 1) ^ w) •
      clsK X l n (slD X N (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
        (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K))

def CohB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) {A : Type} [Mul A] (κ : (Ω ≃ₐ[ℚ] Ω) → A)
    (z z' : (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l) : Prop :=
  ∃ b : A → X.Fn l, (∀ y, InvM X l N w n (b y)) ∧ ∀ s y, CgF X l n (z s y) (z' s y + (X.galB l s (b (y * κ s)) - b y))

def ixU (l L N : ℕ) (x : ZMod N) : Fin 2 → ℚ :=
  ![(((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L : ℤ) : ℚ) / ((N * l ^ L : ℕ) : ℚ), ((0 : ℤ) : ℚ) / ((N * l ^ L : ℕ) : ℚ)]

def ixV (l L N : ℕ) : Fin 2 → ℚ :=
  ![(((topT l L N : ℤ) * (l : ℤ) ^ L : ℤ) : ℚ) / ((N * l ^ L : ℕ) : ℚ), (((N : ℤ) : ℤ) : ℚ) / ((N * l ^ L : ℕ) : ℚ)]

def bar (l L N p : ℕ) : ℤ := ((((p : ZMod (N * l ^ L))⁻¹).val : ℕ) : ℤ)

def ixUT (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℚ :=
  ![((bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L : ℤ) : ℚ) / ((N * l ^ L * p : ℕ) : ℚ),
    ((0 : ℤ) : ℚ) / ((N * l ^ L * p : ℕ) : ℚ)]

def ixVT (l L N p : ℕ) : Fin 2 → ℚ :=
  ![((bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p : ℤ) : ℚ) / ((N * l ^ L * p : ℕ) : ℚ),
    ((bar l L N p * N * p + N * (l : ℤ) ^ L : ℤ) : ℚ) / ((N * l ^ L * p : ℕ) : ℚ)]

def lvT (l n r N p : ℕ) : ℕ := l ^ (r + n) * (N * N) * p

instance lvT.neZero (l n r N p : ℕ) [Fact l.Prime] [NeZero N] [NeZero p] : NeZero (lvT l n r N p) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N)))
    (NeZero.ne p)⟩

instance sqNeZero (N : ℕ) [NeZero N] : NeZero (N * N) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩

def cls0 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) :
    (Ω ≃ₐ[ℚ] Ω) → X.Fn l :=
  clsG X l n N (topM l n r (N * N)) w c d g (ixU l (r + n) N x) (ixV l (r + n) N)

def clsT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) :
    (Ω ≃ₐ[ℚ] Ω) → X.Fn l :=
  clsG X l n N (lvT l n r N p) w c d g (ixUT l (r + n) N p x) (ixVT l (r + n) N p)

def Y0 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) :
    (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → X.Fn l :=
  GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) (cls0 X l n r N x c d w g))

def rdT (l n r N p : ℕ) (y : (ZMod (lvT l n r N p))ˣ) : (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p)).toMonoidHom y,
   Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
     (ZMod (l ^ r))).toMonoidHom y)

open Classical in

def inv1 (m a : ℕ) : (ZMod m)ˣ := if h : IsUnit (a : ZMod m) then h.unit⁻¹ else 1

def YT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N p : ℕ) [NeZero N] [NeZero p] (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ))
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod p)ˣ × (ZMod (l ^ r))ˣ) : X.Fn l :=
  GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) (clsT X l n r N p x c d w g)) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2)

def kT (l r p : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  ((cycM p s)⁻¹, (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)

structure Hyp (l N c d : ℕ) (g : SL(2, ℤ)) : Prop where
  odd : l ≠ 2
  cop : Nat.Coprime l N
  c1 : 1 < c
  d1 : 1 < d
  cc : Nat.Coprime c (6 * l * N)
  cd : Nat.Coprime d (6 * l * N)
  g0 : (N : ℤ) ∣ en g 1 0

structure TopCoc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n M : ℕ) (z : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) : Prop where
  inv : ∀ σ ∈ fixMu Ω M, InvM X l N w n (z σ)
  coc : ∀ σ ∈ fixMu Ω M, ∀ τ ∈ fixMu Ω M, CgF X l n (z (σ * τ)) (z σ + X.galB l σ (z τ))
  loc : ∃ T : Finset Ω, ∀ σ ∈ fixMu Ω M, ∀ τ ∈ fixMu Ω M, (∀ a ∈ T, σ a = τ a) → CgF X l n (z σ) (z τ)

theorem clsBmu_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ)
    (g : (ZMod l)ˣ → SL(2, ℤ)) (σ : Ω ≃ₐ[ℚ] Ω) :
    clsBmu X l n r N x c d k g σ = ∑ r₀, cls0 X l n r N x c d (k - 2) (g r₀) σ := rfl

end UpperTheory.V.Z.Kato.Nb

end
