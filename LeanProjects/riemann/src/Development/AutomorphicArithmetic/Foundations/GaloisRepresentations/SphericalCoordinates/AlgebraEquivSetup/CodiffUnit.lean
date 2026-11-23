import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.DatumToG

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def BarEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  ∃ bar : 𝓞 E ≃+* 𝓞 E, ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)

def QuadEx : Prop := ∀ d : ℕ, 0 < d → ∃ (tr nm : ℤ) (f : ℚ), tr ^ 2 - 4 * nm < 0 ∧ ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = f ^ 2 * (-(d : ℚ)) ∧
  ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm

def OmegaEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E),
  (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (tr nm : ℤ) (f : ℚ), ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = f ^ 2 * (-(d : ℚ)) →
  ∃ ω : 𝓞 E, ω + bar ω = (tr : 𝓞 E) ∧ ω * bar ω = (nm : 𝓞 E)

def CEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (τ₀ : E →+* ℂ) (M : ℕ), 0 < M →
  ∃ c : 𝓞 E, IsCMField.complexConj E (c : E) = c ∧ (τ₀ (c : E)).re < 0 ∧
    (∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ (c : E)).re) ∧ ∃ b : 𝓞 E, c = 1 + (M : 𝓞 E) * b

def UnitMod : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ) (c b : 𝓞 E), c ≠ 0 → c = 1 + (M : 𝓞 E) * b →
  ∃ e : ℕ, e.Coprime M ∧ ∃ c' : 𝓞 E, c * c' = (e : 𝓞 E)

def InCodiff {E : Type} [Field E] [NumberField E] (y : E) : Prop := ∀ x : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (y * x) = m

def GenCodiff {E : Type} [Field E] [NumberField E] (M : ℕ) (y : E) : Prop :=
  InCodiff y ∧ ∃ e : ℕ, e.Coprime M ∧ ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (e : E) * z = y * x

def CodiffGen : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ), 0 < M → ∃ y : E, GenCodiff M y

def CodiffUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ), 0 < M → ∀ (y t : E), GenCodiff M y → InCodiff t →
  (∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ∃ s u : 𝓞 E, s ∉ P ∧ u ∉ P ∧ (s : E) * t = (u : E) * y) → GenCodiff M t

def IdemEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E ≃+* 𝓞 E) (ω : 𝓞 E) (tr nm : ℤ), (∀ x, bar (bar x) = x) →
  ω + bar ω = (tr : 𝓞 E) → ω * bar ω = (nm : 𝓞 E) → ∀ M : ℕ, 0 < M →
  (∀ q : ℕ, q.Prime → q ∣ M → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) →
  ∃ ε : 𝓞 E, ∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ε + bar ε - 1 ∈ P ∧ ε * bar ε ∈ P

def RealGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E),
  (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ M : ℕ, 0 < M → ∀ ε : 𝓞 E,
  (∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ε + bar ε - 1 ∈ P ∧ ε * bar ε ∈ P) →
  ∃ t : E, IsCMField.complexConj E t = t ∧ GenCodiff M t

def PosGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 0 < M → ∀ t : E,
  IsCMField.complexConj E t = t → GenCodiff M t →
  ∃ t' : E, IsCMField.complexConj E t' = t' ∧ GenCodiff M t' ∧ ∀ τ : E →+* ℂ, 0 < (τ t').re

def DeltaEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E),
  (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (ω : 𝓞 E) (tr nm : ℤ),
  ω + bar ω = (tr : 𝓞 E) → ω * bar ω = (nm : 𝓞 E) → tr ^ 2 - 4 * nm < 0 → ∀ M : ℕ, IsCoprime (tr ^ 2 - 4 * nm) (M : ℤ) →
  ∀ t : E, IsCMField.complexConj E t = t → GenCodiff M t → (∀ τ : E →+* ℂ, 0 < (τ t).re) → ∀ τ₀ : E →+* ℂ,
  ∃ δ : E, IsCMField.complexConj E δ = -δ ∧ GenCodiff M δ ∧ ∀ τ : E →+* ℂ, τ (ω : E) = τ₀ (ω : E) → (τ δ).im < 0

def PerfOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (M : ℕ), GenCodiff M A.δ →
  (∃ e : ℕ, e.Coprime M ∧ ∃ c' : 𝓞 E, A.c * c' = (e : 𝓞 E)) → ∀ q : ℕ, q ∣ M → A.PerfAt q

def PerfCof : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  ∃ e : ℕ, 0 < e ∧ ∀ q : ℕ, e.Coprime q → A.PerfAt q

def ArithEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), (0 < d ∧ ∃ x : E, x ^ 2 = -(d : E)) →
  ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
  ∃ A : Arith E, A.τ₀ = τ₀ ∧ (∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → A.SplitK q) ∧ ∀ q ∈ Q, A.Good q

def FormOKSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), A.FormOK n

def FormPerfSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n q : ℕ), A.PerfAt q → A.FormPerf n q

def SigSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 1 ≤ n → A.SigOK n

abbrev Phi {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : Type := {τ : E →+* ℂ // τ (A.ω : E) = A.τ₀ (A.ω : E)}

def RealIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ),
  ∃ Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ), ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E)

open Classical in

def TraceType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  (∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ : Phi A, 2 * (τ.1 x).re) ∧
  (∀ f : (E →+* ℂ) → ℂ, ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), f τ =
    ∑ τ : Phi A, f (ComplexEmbedding.conjugate τ.1)) ∧
  (∀ v : InfinitePlace E, ∃! τ : Phi A, InfinitePlace.mk τ.1 = v) ∧ (A.τ₀ (A.ω : E)).im ≠ 0

open Classical in

def FormCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ)), (∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E)) →
  ∀ x y, (A.EF n).baseChange ℝ x y =
    ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k)).re

def HdSign : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (τ : E →+* ℂ) (i : Fin n),
  (τ (A.hd n i : E)).im = 0 ∧ (τ A.δ).re = 0 ∧
  (InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0 → 0 < (τ (A.hd n i : E)).re) ∧
  (¬ (InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0) → (τ (A.hd n i : E)).re < 0)

def DiagTrace : Prop := ∀ (I : Type) [Fintype I] (a : I → ℂ) (M : (I → ℂ) →ₗ[ℝ] (I → ℂ)), (∀ z k, M z k = a k * z k) →
  LinearMap.trace ℝ _ M = 2 * (∑ k, a k).re

def DomSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 1 ≤ n → A.Dom n

def KqEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  ∃ Kq : Subfield E, (A.ω : E) ∈ Kq ∧ (Module.finrank ℚ Kq = 2 ∧ ∀ τ : E →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) ∧
    ∀ x ∈ Kq, ∃ a b : ℚ, x = a + b * (A.ω : E)

def UEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (p : ℕ) [Fact p.Prime], A.SplitK p →
  ∀ Kq : Subfield E, ∀ hω : (A.ω : E) ∈ Kq, (∀ x ∈ Kq, ∃ a b : ℚ, x = a + b * (A.ω : E)) → ∀ τ : E →+* PadicAlgCl p,
  ∃ (u : Kq →+* ℚ_[p]) (ρ : ℤ_[p]), LiesOver Kq u τ ∧ u ⟨A.ω, hω⟩ = (ρ : ℚ_[p])

def OrbEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (Kq : Subfield E) (u : Kq →+* ℚ_[p])
  (τ₁ : E →+* PadicAlgCl p), LiesOver Kq u τ₁ →
  ∃ (m : ℕ) (emb : Fin m → (E →+* PadicAlgCl p)) (w : Fin m), emb w = τ₁ ∧ (∀ i, LiesOver Kq u (emb i)) ∧
    (∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j) ∧
    ∀ τ : E →+* PadicAlgCl p, LiesOver Kq u τ → ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i)

def LiftEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (τ₀ : E →+* ℂ),
  ∃ (s : E →+* AlgebraicClosure ℚ) (iotaC : AlgebraicClosure ℚ →+* ℂ), ∀ x, iotaC (s x) = τ₀ x

def AtPEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (p : ℕ) [Fact p.Prime], A.SplitK p →
  Nonempty (A.AtP p)

def RepEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ),
  ∃ (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)), ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)

def RepOK {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) : Prop :=
  ∃ β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E), (∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) ∧
    ∀ x z, β (rep x z) = x *ᵥ β z

def RepLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  Function.Injective rep ∧
  (∀ M : Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)), (∃ x, rep x = M) ↔ ∀ b : 𝓞 E,
    M * (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ =
      (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ * M) ∧
  (∀ c : 𝓞 E, rep (algebraMap E _ (c : E)) = (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ) ∧
  ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
    rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v)

def RepAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  ∀ x v w, (A.EF n).baseChange ℚ (rep x v) w = (A.EF n).baseChange ℚ v (rep (hermStar (A.H n) (A.det_ne n) x).unop w)

def Orient : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (hn : 1 ≤ n) (hs : A.SigOK n)
  (p : ℕ) [Fact p.Prime] (P : A.AtP p)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  ∃ J : ℝ ⊗[ℚ] (A.grp hn hs P).C, J * J = -1 ∧ (starT (A.grp hn hs P).star ℝ J).unop = -J ∧
    (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn (C := (A.grp hn hs P).C) rep ℝ J x) x) ∧
    ∀ v : InfinitePlace E, (open scoped Classical ComplexOrder in
      ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        ((A.grp hn hs P).gram v * (A.grp hn hs P).psiR v J)).PosDef)

def SetupEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime], 1 ≤ n →
  A.Good p → Nonempty (Setup A n p)

def SetupBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime]
  (S : Setup A n p), S.G.a = 1 ∧ sigPosH (S.G.gram_herm (InfinitePlace.mk A.τ₀)) = 1 ∧
    (2 < Module.finrank ℚ E → S.D.Compact ∧ S.D.CompactB)

end UpperTheory.Gal.W2.Seed
