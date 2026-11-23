import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

def Rel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l)
    (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) (cf : Coef l) (c n : ℕ) {T : Type} [Mul T] (κ : (Ω ≃ₐ[ℚ] Ω) → T)
    (Y : (Ω ≃ₐ[ℚ] Ω) → T → Fin 2 → Qbar l) (z : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) : Prop :=
  ∃ (β : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) (b : T → Fin 2 → Qbar l), (∀ s y, LiftB X l N (2 * e - 1) n c (z s y) (β s y)) ∧
    (∀ y i, b y i ∈ cf.O) ∧ ∀ s y, Cv n (Y s y) (pr (β s y) + (rhoK W e ψ s *ᵥ b (y * κ s) - b y))

def eul (l : ℕ) [Fact l.Prime] (e p : ℕ) (a δ : Qbar l) : Qbar l := 1 - a * ((p : Qbar l) ^ (e + 1))⁻¹ + δ * ((p : Qbar l) ^ 2)⁻¹

def SRel0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y r) fun s y => ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y

def SRelT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p : ℕ) [NeZero p], Nat.Coprime p l → ∀ (c₀ : ℕ) Y, IsZTc X l pr W e ψ N p x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (kT l r p) (Y r) fun s y => ∑ r₀, YT X l n r N p x c d (2 * e - 1) (gm r₀) s y

def SN2rho : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∃ m : ℕ, ∀ (p : ℕ) [NeZero p], p.Prime → Nat.Coprime p (l * N) → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O →
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l p b) = a • pr b ∧ pr (X.diam N l p b) = δ • pr b) →
    ∀ (c₀ c₁ r n : ℕ) (Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (Y' : (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) z z',
      Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) Y z → Rel X l pr W e ψ N cf (c₀ + c₁) n (kT l r p) Y' z' →
      CohB X l N (2 * e - 1) n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (fun s y => (p : ℤ_[l]) • ∑ t, z' s (t, y))
        (fun s y => (p : ℤ_[l]) • z s y - X.heckeT N l p (z s (y * inv1 (l ^ r) p)) +
          (p : ℤ_[l]) ^ (2 * e - 1) • X.diam N l p (z s (y * inv1 (l ^ r) p ^ 2))) →
      ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
        Cv n ((((l : ℕ) : Qbar l) ^ m * (p : Qbar l)) • ∑ t, Y' s (t, y))
          (((l : ℕ) : Qbar l) ^ (m + c₁) • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
            ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
            (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def SInteg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → (∀ s : G ℚ Ω, ‖thK l e ψ s‖ = 1) ∧ ψ 1 = 1 ∧ (∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v) ∧
    (∀ u : (ZMod l)ˣ, ψ u ∈ cf.O) ∧ (∀ s i k, rhoK W e ψ s i k ∈ cf.O) ∧ (∀ s t, rhoK W e ψ (s * t) = rhoK W e ψ s * rhoK W e ψ t) ∧
    ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r s y i, ‖Y r s y i‖ ≤ 1

def SSpec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∀ (p r : ℕ), p.Prime → l ∣ p - 1 → ∀ (a δ k : Qbar l), ‖a‖ ≤ 1 → ‖δ‖ ≤ 1 → ‖k‖ ≤ 1 →
    ∀ (Y V : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ s y i, ‖Y s y i‖ ≤ 1) → (∀ y i, b y i ∈ cf.O) →
      (∀ s y, Cv r ((p : Qbar l) • V s y) (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))) →
      ∃ b' : Fin 2 → Qbar l, (∀ i, b' i ∈ cf.O) ∧ ∀ s, Cv r (spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) V s)
        (eul l e p a δ • (k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) Y s) + (mat W s *ᵥ b' - b'))

def SDetChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (χ : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → Continuous χ → (∃ s, ∀ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) ≠ t • 1) → ∀ S : Finset ℕ,
    (∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S → IsPlaceOver B v → IsFrob B (normV v) σ → ∃ a : Qbar l,
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) ^ 2 - a • (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) + (χ σ : Qbar l) • 1 = 0) →
    ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s

def SDiamChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → (∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0) → ∃ δ : (ZMod N)ˣ →* (Qbar l)ˣ, ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N →
    (u : ZMod N) = q → ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = (δ u : Qbar l) • pr b

def SEuler : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → ∀ S : Finset Pl, Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → ∃ S' : Finset Pl, S ⊆ S' ∧ ∀ w : Pl, w ∉ S' →
    (normV w).Prime ∧ Nat.Coprime (normV w) (l * N * c * d) ∧ ∃ a δ : Qbar l, a ∈ cf.O ∧ δ ∈ cf.O ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        eps l σ = (normV w : Qbar l) ∧ (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ

def SEulCg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p n : ℕ), p.Prime → 1 ≤ n → l ^ n ∣ p - 1 → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O → eul l e p a δ ∈ cf.O ∧
    ∀ σ : G ℚ Ω, ψ 1 = 1 → eps l σ = (p : Qbar l) → (rhoK W e ψ σ).trace = a → (rhoK W e ψ σ).det = (p : Qbar l) ^ (2 * e) * δ →
      Cg n (eul l e p a δ) (1 * (mat W σ - 1).det)

def SPushPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (cf : Coef l) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (p n : ℕ) [NeZero p] (ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), KillsMu p ψw →
    ∀ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      (∀ r s s' y, Y r (s * s') y = Y r s y + ρ s *ᵥ Y r s' (y * cycT l r p s)) →
      (∀ r, Y r = GlobalTheory.KA.push (Prod.map id (redL l r)) (Y (r + 1))) → (∀ r y i, Continuous fun s => Y r s y i) → (∀ r s u i, Y r s u i ∈ cf.O) →
      ∃ Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        (∀ r, ShCoc ρ (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧ (∀ r s x i, Yw r s x i ∈ cf.O) ∧
        (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
        ∀ r s y, ∑ a, Yw r s (a, y) = ∑ t, Y r s (t, y)

def KatoTameRelationProjected : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y →
  ∃ (k : ℕ) (S' : Finset Pl), (∀ w : Pl, w ∉ S' → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψw → Function.Surjective ψw →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc (rhoK W e ψ) (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ cf.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ cf.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ cf.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • (((l : ℕ) : Qbar l) ^ k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (Y r) s) + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))

end UpperTheory.V.Z.Kato.Nb

end
