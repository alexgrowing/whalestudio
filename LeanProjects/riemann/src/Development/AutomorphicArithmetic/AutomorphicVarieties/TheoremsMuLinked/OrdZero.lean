import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.W UpperTheory.V.Ws.Eb

namespace UpperTheory.V.Th

section Abstract

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {K : Type} [Field K] {n : ℕ}

def TypeI (ρ : F.G₀ →* GL (Fin n) K) : Prop := U3.MatIrr F.G' (mat ρ)

def N3 (ρ : F.G₀ →* GL (Fin n) K) : Prop :=
  ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty → ∃ σ ∈ U ∩ (F.G' : Set F.G₀), (mat ρ σ).charpoly.Separable

def Free (ψ : ∀ v, Fin n → F.Gv v →* Kˣ) : Prop :=
  ∀ v, ∃ g : F.Gv v, F.φ v g ∈ F.G' ∧ Pr.FreeRatios fun i => ψ v i g

def OrdAt {H : Type} [Group H] (I : Subgroup H) (ρ : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (y : H → Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (a : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K), ∀ g,
    (∀ i j, j < i → (a * ρ g * a⁻¹ : GL (Fin n) K) i j = 0) ∧ (∀ i, (a * ρ g * a⁻¹ : GL (Fin n) K) i i = (ψ i g : K)) ∧
    (∀ i j, j < i → ((a : Matrix (Fin n) (Fin n) K) * (y g - (Loc.adGL ρ g X - X)) * (a⁻¹ : GL (Fin n) K)) i j = 0) ∧
    (g ∈ I → ∀ i, ((a : Matrix (Fin n) (Fin n) K) * (y g - (Loc.adGL ρ g X - X)) * (a⁻¹ : GL (Fin n) K)) i i = 0)

variable {F} in

structure OrdCoc {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (ρ : F.G₀ →* GL (Fin n) K)
    (ψ : ∀ v, Fin n → F.Gv v →* Kˣ) (z : F.Γ → Matrix (Fin n) (Fin n) K) : Prop where
  ine : ∀ u, ∀ g ∈ r.Ip u, z g = 0
  ord : ∀ v, OrdAt (F.Iv v) (ρ.comp (F.φ v)) (ψ v) fun g => z (F.φ v g)

end Abstract

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}

structure APt (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous ρ
  rep : x.IsRep (ρ.comp V.pr)
  arith : ∃ h, x.Arith h
  aut : Af.IsAutCsd ι (ρ.comp V.pr)
  unr0 : ∀ g ∈ V.frame.I0, ρ g = 1
  flag : ∀ v : V.frame.Vl, HasFlag (ρ.comp (V.frame.φ v)) (x.psi v)

structure NiceAPt (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop extends APt ι x ρ where
  free : Free V.frame fun v => x.psi v
  irr : TypeI V.frame ρ
  n3 : N3 V.frame ρ

def Par (x : B.Pt) : Prop :=
  ∀ v : Vl l L, ∃ (m : Fin n → ℤ) (k : ℕ), StrictAnti m ∧ 0 < k ∧ ∀ i j (g : Dec (F := L) (s.A v)),
    (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m j - m i)) ^ k = 1

variable (r) in

def OrdZero (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → V.frame.Gv v →* (Qbar l)ˣ) : Prop :=
  ∀ (P : GL (Fin n) (Qbar l)) (R : Representation (Qbar l) V.frame.Γ (Matrix (Fin n) (Fin n) (Qbar l))),
    V.frame.IsForm c.O n ρ P → IsAdExt V.frame ρ P R → ∀ z ∈ Z1 R, OrdCoc r ρ ψ z → ∃ X, ∀ g, z g = R g X - X

variable (V) in

def AdZero (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (P : GL (Fin n) (Qbar l)) (R : Representation (Qbar l) V.frame.Γ (Matrix (Fin n) (Fin n) (Qbar l))),
    V.frame.IsForm ℤ_[l] n ρ P → IsAdExt V.frame ρ P R → ∀ z ∈ Z1 R,
    Af.IsBK l (R.comp (toGS Ω V.S') : Representation (Qbar l) (G (Lp L) Ω) (Matrix (Fin n) (Fin n) (Qbar l)))
      (fun g => z (toGS Ω V.S' g)) → ∃ X, ∀ g, z g = R g X - X

end U

def Core : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), NiceAPt ι x ρ → OrdZero r ρ fun v => x.psi v

def AdL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), NiceAPt ι x ρ → Par x → AdZero V ρ

def FreeAt (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := F) A, cycZ F Ω l g = 1 ∧
    ∃ α : Fin n → (Qbar l)ˣ, Pr.FreeRatios α ∧ (mat r g).charpoly = ∏ i, (X - C ((α i : (Qbar l)ˣ) : Qbar l))

example {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] : FreeAt l (1 : G F Ω →* GL (Fin 1) (Qbar l)) :=
  fun A _ => ⟨1, one_mem _, map_one _, 1, fun i j h => absurd (Subsingleton.elim i j) h, by
    simp [Matrix.charpoly_one]⟩

example {l : ℕ} [Fact l.Prime] {F : GFrame l} {K : Type} [Field K] {n : ℕ} {H : Type} [Group H] (I : Subgroup H) :
    OrdAt I (1 : H →* GL (Fin n) K) 1 0 :=
  ⟨1, 0, fun g => ⟨fun i j h => by simp [Matrix.one_apply_ne h.ne'], fun i => by simp, fun i j _ => by simp, fun _ i => by simp⟩⟩

end UpperTheory.V.Th

end
