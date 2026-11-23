import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def fop {E : Type} [Field E] (k l : ℕ) (χ : ℕ → E) : Letter → Module.End E (ℕ → E)
  | Letter.T q =>
    { toFun := GlobalTheory.EisM.To k (χ q) q
      map_add' := fun a b => by funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c a => by
        funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  | Letter.U => { toFun := GlobalTheory.EisM.Uo l, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | Letter.D d => χ d • 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def th (X : Tower Ω ε) (A : ValuationSubring Ω) (N : ℕ) (j : Ω →+* Qbar l) (n : ℕ) (b : X.Fn l) : ℕ → Qbar l :=
  seqN 1 j (thN X A N l n 1 b)

def Std (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) : Prop :=
  (l : Ω) ∈ A.nonunits ∧ l ≠ 2 ∧ ¬ l ∣ N ∧ 5 ≤ N ∧ Odd w ∧ ∀ x ∈ A, ‖j x‖ ≤ 1

def FormP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ)
    (χE : ℕ → Qbar l) (ev : Letter → Qbar l), 1 ≤ k → GlobalTheory.EisM.EigF k N l χ t α B cc → (∀ d : ℕ, d.Coprime N → ι (χE d) = χ d) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ι (ev (Letter.T q)) = t q) → ι (ev Letter.U) = α →
    (∀ d : ℕ, d.Coprime N → ev (Letter.D d) = χE d) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∀ a : ℕ → Qbar l,
    GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.lam B cc (fun i => ι (FreeAlgebra.lift (Qbar l) (fop k l χE) P a i)) =
        ι (FreeAlgebra.lift (Qbar l) ev P) * GlobalTheory.EisM.lam B cc fun i => ι (a i)

def FinP : Prop := CoefUb →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (B : ℕ) (cc : ℕ → ℂ) (χE : ℕ → Qbar l) (c₀ : Coef l),
    ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∃ (lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (c : Coef l), c₀.O ≤ c.O ∧ FinSupp lam₀ ∧ FinSupp lam ∧
      (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧ (∀ a, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i))) ∧
      ∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop k l χE) P a)

def ThLin : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l), Std A N w j → ∀ n : ℕ,
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)

def ThOp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ (n : ℕ) (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      ∀ i, Cg n (th X A N j n (X.op N l T b) i) (fop (w + 2) l (fun d => ((χ d : ℤ_[l]) : Qbar l)) T (th X A N j n b) i)

def ChiStab : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (N w : ℕ) (χ : ℕ → ℤ_[l]), l ≠ 2 → ¬ l ∣ N → 5 ≤ N → Odd w → ∀ (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b → InChi X N w χ (X.op N l T b)

def ThP : Prop := ThOp → ChiStab →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l),
      (∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)) → ∀ b, InChi X N w χ b → ∀ i,
        Cg (n - c) (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P (th X A N j n b) i)
          (Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)

def LamEig : Prop := ThLin → ThOp → ChiStab → ThP →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (ev : Letter → Qbar l), Std A N w j →
    (∀ T, GlobalTheory.KZ.admitted N l T → ‖ev T‖ ≤ 1) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    (∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ X.B N l w,
      FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b) =
        ev T • FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) →
    ∀ lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam₀ →
    (∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P a)) →
    ∃ c₂ : ℕ, ∀ n, c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      Cg (n - c₂) (lam (th X A N j n (X.op N l T b))) (ev T * lam (th X A N j n b))

def ChiQuad : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    ¬ l ∣ g.M → g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) →
    ∀ d : ℕ, d.Coprime g.M → g.χ d = 1 ∨ g.χ d = -1

def AqInt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (g : Newform k) (q : ℕ), 2 ≤ k → q.Prime → ¬ q ∣ g.M → ‖ι.symm (g.a q)‖ ≤ 1

end UpperTheory.V.Z.Kato.Joint

end
