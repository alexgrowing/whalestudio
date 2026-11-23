import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

structure Bd (Ψ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous Ψ
  left : ∀ γ g, Ψ (ratGL E 2 γ * g) = Ψ g
  bdd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖Ψ (gl h * k)‖ ≤ B

def PosC (Ψ : GL (Fin 2) (A E) → ℂ) : Prop := ∀ s g, Ψ (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = Ψ g

variable [IsTotallyComplex E]

structure InvPair (V V' : Submodule ℂ (Sm E 2)) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) : Prop where
  st : IsStable V
  st' : IsStable V'
  fin : ∀ k (x : V) (y : V'), B ⟨act (.fin k) x.1, st _ _ x.2⟩ ⟨act (.fin k) y.1, st' _ _ y.2⟩ = B x y
  cpt : ∀ k (x : V) (y : V'), B ⟨act (.cpt k) x.1, st _ _ x.2⟩ ⟨act (.cpt k) y.1, st' _ _ y.2⟩ = B x y
  lie : ∀ X (x : V) (y : V'), B ⟨act (.lie X) x.1, st _ _ x.2⟩ y + B x ⟨act (.lie X) y.1, st' _ _ y.2⟩ = 0

end Objects

def MeanLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ y, IntegrableOn (fun h => Ψ (gl h * y)) N.D N.μ) ∧ (Continuous fun y => mean N fun x => Ψ (x * y)) ∧
  (∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y)) ∧
  ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y)

def UILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E) ∧
  (∃ B : ℝ, ∀ t : (A E)ˣ, ab t = 1 → ‖β t‖ ≤ B) ∧ ∀ d : (A E)ˣ, ab d = 1 → (UI fun t => β (t * d)) = UI β

def IILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ Ψ', Bd Ψ' → ∀ c : ℂ, (II N fun x => Ψ x + c * Ψ' x) = II N Ψ + c * II N Ψ') ∧
  (PosC Ψ → ∀ g, (II N fun x => Ψ (x * g)) = II N Ψ)

def IILie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : MeasE E) (Φ φ : Sm E 2) (X),
  (Bd fun x => Φ.1 x * φ.1 x) → (PosC fun x => Φ.1 x * φ.1 x) → (Bd fun x => (act (.lie X) Φ).1 x * φ.1 x) →
  (Bd fun x => Φ.1 x * (act (.lie X) φ).1 x) →
  (II N fun x => (act (.lie X) Φ).1 x * φ.1 x) + (II N fun x => Φ.1 x * (act (.lie X) φ).1 x) = 0

def SpanGrow : Prop := All fun E _ _ _ _ W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π,
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∃ (r : ℕ) (B : ℝ), ∀ b a, ∀ k ∈ C, c ≤ ab a →
    ‖Φ.1 (gl (nU b * mD a) * k)‖ ≤ B * ab a ^ r

def ProdBd : Prop := All fun _ _ _ _ _ W M _ P => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ φ ∈ P.V,
  (Bd fun x => Φ.1 x * φ.1 x) ∧ (PosInv π → GlobalTheory.DiscSpec.IsNormalised P → PosC fun x => Φ.1 x * φ.1 x)

def KillW : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
  (∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → (∀ h, WE D Φ h = 0) → ∀ (h : G1 E) g, Φ (gl h * g) = Φ g

def PairEx : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  ∃ B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ, InvPair _ _ B ∧ (∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g) ∧
    ∀ x : span W M π, (∀ h, WE D x.1.1 h = 0) → B x = 0

def SplitEig : Prop := All fun E _ _ _ D W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ (v : P ℚ) (w : P E), SplitAt v w →
  ∀ B, π.HasSat v B → Fix w Φ.1 → EigAt w B (WE D Φ.1)

def SatPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (w : P E) (T : V →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)),
  (∀ x : V, ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, x.1.1 (g * lc w y) = x.1.1 g) →
  (∀ (x x' : V) y, (∀ g, x'.1.1 g = x.1.1 (g * lc w y)) → ∀ g, T x' g = T x (g * lc w y)) → (∀ x, T x = 0 → B x = 0) →
  ∀ C C' : Multiset ℂˣ, (∀ x : V, Fix w x.1.1 → EigAt w C (T x)) → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹)

def InfPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), m.card = 2 →
  (∀ u, ∀ Φ ∈ V, cap τ u Φ = (m.map (u + ·)).prod • Φ) → Q.HasInfChar τ m' → m' = m.map Neg.neg

def CharSel : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  (UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹)) ≠ 0 →
  ∃ χ : HChar E, (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) ∧
    (∀ z : (A E)ˣ, (∃ s, Matrix.GeneralLinearGroup.scalar (Fin 2) z = GroundTheory.Automorphic.Reduction.centralSection E 2 s) → χ.1 z = 1) ∧
    (UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t) ≠ 0

def CharDown : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (χ : HChar E),
  (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) → ∃ χ₀ : HChar ℚ, ∀ z : (A E)ˣ, χ.1 z = χ₀.1 (ideleNorm ℚ E z)

def FinS : Prop := All fun E _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

def DownN : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Module.finrank ℚ E = 2 → ∀ P : CuspSub E 2,
  GlobalTheory.DiscSpec.IsNormalised P → ConjInv P → ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
