import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def thK (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : Qbar l :=
  (eps l s ^ e)⁻¹ * ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def rhoK {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (Qbar l) :=
  (thK l e ψ s)⁻¹ • mat W s

open Classical in

def nuD {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : (Qbar l)ˣ :=
  if h : rhoK W e ψ s 1 1 ≠ 0 then Units.mk0 _ h else 1

def Adm3 {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b) ∧
    (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
      (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
        (t : ZMod l) • ![(r₀ : ZMod l), -1]) ∧
    (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ∧
    ∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
      (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
      ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def LiftB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n c0 : ℕ) (a b : X.Fn l) : Prop :=
  b ∈ X.B N l w ∧ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (b u - ((l : ℤ_[l]) ^ c0) • a u) = 0

def YfB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (n r N : ℕ) [NeZero N] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
  GlobalTheory.KA.push (redM l n r (N * N)) fun s y =>
    rhoK W e ψ (repM (topM l n r (N * N)) y) *ᵥ
      pr (bB ((repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹)))

attribute [local instance] algMdl

def topMu (l n r N : ℕ) : ℕ := l ^ (r + n) * (N * N)

def wkMu (X : Tower Ω ε) (l n r N : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  let M := topMu l n r N
  let tt : ℤ := (topT l (r + n) N : ℤ)
  let u : X.K := GlobalTheory.Glue.sgN X c N (N * l ^ (r + n)) ((N : ℤ) + (x.val : ℤ) * tt * (l : ℤ) ^ (r + n), 0)
  let v : X.K := GlobalTheory.Glue.sgN X d N (N * l ^ (r + n)) (tt * (l : ℤ) ^ (r + n), (N : ℤ))
  ((topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
    (topEta X M (topChar X M l n u) (topChar X M l n v)) (topLift X M σ)⁻¹ : topL X M) : X.K)

open Classical in

def clsBmu (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ))
    (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := topMu l n r N
  haveI : NeZero M := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wkMu X l n r N x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def topMT (l n r N l' : ℕ) : ℕ := l ^ (r + n) * (N * N) * l'

instance topMT.neZero (l n r N l' : ℕ) [Fact l.Prime] [NeZero N] [NeZero l'] : NeZero (topMT l n r N l') :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N)))
    (NeZero.ne l')⟩

def wkTmu (X : Tower Ω ε) (l n r N l' : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  let M := topMT l n r N l'
  let L : ℤ := (l : ℤ) ^ (r + n)
  let lb : ℤ := ((((l' : ZMod (N * l ^ (r + n)))⁻¹).val : ℕ) : ℤ)
  let tt : ℤ := (topT l (r + n) N : ℤ)
  let u : X.K := GlobalTheory.Glue.sgN X c N (N * l ^ (r + n) * l') (lb * ((N : ℤ) + (x.val : ℤ) * tt * L) * l' + N * L, 0)
  let v : X.K := GlobalTheory.Glue.sgN X d N (N * l ^ (r + n) * l') (lb * tt * L * l', lb * N * l' + N * L)
  ((topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
    (topEta X M (topChar X M l n u) (topChar X M l n v)) (topLift X M σ)⁻¹ : topL X M) : X.K)

open Classical in

def clsBTmu (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ)
    (g : (ZMod l)ˣ → SL(2, ℤ)) (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := topMT l n r N l'
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wkTmu X l n r N l' x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def redT (l n r N l' : ℕ) (y : (ZMod (topMT l n r N l'))ˣ) : (ZMod l')ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : l' ∣ topMT l n r N l') (ZMod l')).toMonoidHom y,
   Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right l')
     (ZMod (l ^ r))).toMonoidHom y)

def YfBT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (n r N l' : ℕ) [NeZero N] [NeZero l'] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) : (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
  GlobalTheory.KA.push (redT l n r N l') fun s y =>
    rhoK W e ψ (repM (topMT l n r N l') y) *ᵥ
      pr (bB ((repM (topMT l n r N l') y)⁻¹ * s * repM (topMT l n r N l') (y * (cycM (topMT l n r N l') s)⁻¹)))

def cycT (l r l' : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : (ZMod l')ˣ × (ZMod (l ^ r))ˣ :=
  ((cycM l' s)⁻¹, (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)

open Classical in

def lsqInv (l l' r : ℕ) : (ZMod l')ˣ :=
  if h : IsUnit ((l : ZMod l') ^ (2 * r)) then h.unit⁻¹ else 1

def IsZetaT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ c₀ : ℕ, ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMT l n r N l'), LiftB X l N (k - 2) n c₀ (clsBTmu X l n r N l' x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (YT r s y) (YfBT X l pr W e ψ n r N l' bB s (y.1 * lsqInv l l' r, y.2) + (rhoK W e ψ s *ᵥ b (y * cycT l r l' s) - b y))

def IsZeta3 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ c₀ : ℕ, ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMu l n r N), LiftB X l N (k - 2) n c₀ (clsBmu X l n r N x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (Y r s y) (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def AdmW {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  (∀ x, cw x ≠ 0 → Adm3 ι e gN A W X pr N x c d gm ψ cf) ∧ ∀ x, cw x ∈ cf.O

def IsZetaW (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZeta3 X l pr W e ψ N x c d k g cf (Yx x)) ∧ ∀ r s y, Y r s y = ∑ x, cw x • Yx x r s y

def IsZetaTW (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZetaT X l pr W e ψ N l' x c d k g cf (Yx x)) ∧ ∀ r s y, YT r s y = ∑ x, cw x • Yx x r s y

end GlobalTheory.K4
