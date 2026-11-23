import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo

section Hom

variable {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M]

def hd (c : List Γ → M) (x : List Γ) : M := ∑ i ∈ Finset.range x.length, (-1 : ℤ) ^ i • c (x.eraseIdx i)

def HEquiv (ρ : Representation ℂ Γ M) (k : ℕ) (c : List Γ → M) : Prop :=
  ∀ (γ : Γ) (x : List Γ), x.length = k + 1 → c (x.map (γ * ·)) = ρ γ (c x)

def HCoc (ρ : Representation ℂ Γ M) (k : ℕ) (c : List Γ → M) : Prop :=
  HEquiv ρ k c ∧ ∀ x : List Γ, x.length = k + 2 → hd c x = 0

def HCob (ρ : Representation ℂ Γ M) : ℕ → (List Γ → M) → Prop
  | 0, c => ∀ x : List Γ, x.length = 1 → c x = 0
  | k + 1, c => ∃ b, HEquiv ρ k b ∧ ∀ x : List Γ, x.length = k + 2 → c x = hd b x

end Hom

def Zig {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d) :
    (q k : ℕ) → (List Γ → G.Om q) → (List Γ → S → Fin d → ℂ) → Prop
  | 0, k, u, c => ∀ x : List Γ, x.length = k + 1 → u x = G.incl (c x)
  | q + 1, k, u, c => ∃ b : List Γ → G.Om q, HEquiv (G.act q) k b ∧
      (∀ x : List Γ, x.length = k + 1 → G.dOm q (b x) = u x) ∧ Zig G q (k + 1) (hd b) c

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

abbrev Co (Ξ : AlgRep E a) (q : ℕ) : Type := Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))

abbrev IsLev (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) : Prop :=
  IsRelCochain Ξ (IsLevelFn U Ξ) ω

def qht (g : GA E a) : ℝ := ⨅ γ : GL (Fin a) E, height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)

variable {Ξ : AlgRep E a} {q : ℕ}

def Rapid (ω : Co Ξ q) : Prop :=
  ∀ (X : Fin q → Herm E a) (N : ℕ), ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev (ω X) g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C

def RapidD (ω : Co Ξ q) : Prop :=
  ∀ l : List (Lie E a), Rapid (Ξ := Ξ) ((((l.map (smA Ξ)).prod).restrictScalars ℝ).compAlternatingMap ω)

def Moderate (ω : Co Ξ q) : Prop :=
  ∃ N : ℕ, ∀ X : Fin q → Herm E a, ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev (ω X) g.1‖ ≤ C * qht (E := E) (a := a) g.1 ^ N

def CSupp (ω : Co Ξ q) : Prop := ∃ R : ℝ, ∀ (X : Fin q → Herm E a) (g : GA E a), R < qht g → ev (ω X) g = 0

def ptIp (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) (α β : Co Ξ q) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) *
    ∑ I : Fin q → Fin n, star (ev (α fun i => e (I i)) g) ⬝ᵥ G *ᵥ ev (β fun i => e (I i)) g

def PairInt (μ : Measure (GA E a)) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => ptIp χ G e α β x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def pair (μ : Measure (GA E a)) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ptIp χ G e α β x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

structure IsData (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) :
    Prop where
  one : HasOne Ξ r
  tw : IsTw (a := a) r χ
  adm : IsAdm Ξ G
  frame : IsFrame e

structure IsCut (U : Subgroup (GL (Fin a) (Af E))) (u : Sm E a) : Prop where
  left : ∀ γ g, u.1 (ratGL E a γ * g) = u.1 g
  centre : ∀ t g, u.1 (splitCentre E a t * g) = u.1 g
  cpt : ∀ k, act (.cpt k) u = u
  level : ∀ k ∈ U, act (.fin k) u = u
  range : ∀ g, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ u.1 g = t

def IsMulBy (u : Sm E a) (α β : Co Ξ q) : Prop := ∀ X g, ev (β X) g = u.1 g • ev (α X) g

def trans (x : GL (Fin a) (Af E)) (ω : Co Ξ q) : Co Ξ q :=
  (((act (.fin x)).rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap ω

def IsPer (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q)
    (c : List (⊤ : Subgroup (GL (Fin a) E)) → (GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ) : Prop :=
  ∃ (ho : IsOpen (cone E a)) (w : (geo ho U Ξ).Om q), Corr U Ξ α w.1 ∧ Zig (geo ho U Ξ) q 0 (fun _ => w) c

end Defs

def QhtFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ g : GA E a, 1 ≤ qht g) ∧
    (∀ γ t (g : GA E a), qht (ratGL E a γ * splitCentre E a t * g) = qht g) ∧
    (∀ C : Set (GA E a), IsCompact C → ∃ B : ℝ, ∀ (g : GA E a), ∀ h ∈ C, qht (g * h) ≤ B * qht g) ∧
    ∀ R : ℝ, ∃ C : Set (GA E a), IsCompact C ∧ ∀ g : GA E a, qht g ≤ R → ∃ γ t, ratGL E a γ * splitCentre E a t * g ∈ C

def CutEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ ε R : ℝ, 0 < ε → ∃ (u : Sm E a) (R' : ℝ), IsCut U u ∧
      (∀ g, qht g ≤ R → u.1 g = 1) ∧ (∀ g, R' < qht g → u.1 g = 0) ∧ ∀ (X : Lie E a) g, ‖(lie E a X u).1 g‖ ≤ ε * ‖X‖

def MulEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (u : Sm E a) (α : Co Ξ q), IsCut U u → IsLev U Ξ α → ∃ β : Co Ξ q, IsLev U Ξ β ∧ IsMulBy u α β ∧
      ∀ (X : Fin (q + 1) → Herm E a) g, ev (dCo (smLie Ξ) β X) g = u.1 g • ev (dCo (smLie Ξ) α X) g +
        ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * (lie E a (toL (X i).1) u).1 g) • ev (α (i.removeNth X)) g

def PairFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a), IsData Ξ r χ G e → ∀ q : ℕ,
    (∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → Rapid α → Moderate β → PairInt μ χ G e α β) ∧
    (∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CSupp α → PairInt μ χ G e α β ∧ PairInt μ χ G e β α) ∧
    (∀ α : Co Ξ q, IsLev U Ξ α → PairInt μ χ G e α α → pair μ χ G e α α = 0 → α = 0) ∧
    ∀ (β : Co Ξ (q + 1)) (η : Co Ξ q), IsLev U Ξ β → IsLev U Ξ η → CSupp β ∨ CSupp η →
      pair μ χ G e β (dCo (smLie Ξ) η) = ((q : ℂ) + 1) * pair μ χ G e (del (smAdj Ξ r) e β) η

def CuspRapid : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a) (q : ℕ) (ω : Co Ξ q),
    (∀ X, ω X ∈ tens Ξ.d π.V) → RapidD ω

def G1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ (q : ℕ) (β : Co Ξ (q + 1)) (η : Co Ξ q), IsLev U Ξ β → IsLev U Ξ η → Rapid β →
      del (smAdj Ξ r) e β = 0 → Moderate (dCo (smLie Ξ) η) → pair μ χ G e β (dCo (smLie Ξ) η) = 0

def G2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (ω : Co Ξ q),
    IsLev U Ξ ω → dCo (smLie Ξ) ω = 0 → RapidD ω →
      ∃ α : Co Ξ q, IsLev U Ξ α ∧ dCo (smLie Ξ) α = 0 ∧ CSupp α ∧ IsRelExact U Ξ (ω - α)

def PerEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ), (∀ α : Co Ξ q, IsLev U Ξ α → dCo (smLie Ξ) α = 0 → ∃ c, IsPer U Ξ α c) ∧
    (∀ (α : Co Ξ q) c, IsLev U Ξ α → IsPer U Ξ α c → dCo (smLie Ξ) α = 0 ∧ HCoc (levelRep ⊤ U (ratC Ξ)) q c) ∧
    ∀ (α β : Co Ξ q) c c' (s t : ℂ), IsPer U Ξ α c → IsPer U Ξ β c' → IsPer U Ξ (s • α + t • β) (s • c + t • c')

def PerKer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) c, IsLev U Ξ α → IsPer U Ξ α c →
      (HCob (levelRep ⊤ U (ratC Ξ)) q c ↔ IsRelExact U Ξ α)

def PerNat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U U' : Subgroup (GL (Fin a) (Af E)))
    (x : GL (Fin a) (Af E)), (∀ u ∈ U', x⁻¹ * u * x ∈ U) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q), IsLev U Ξ α →
    IsLev U' Ξ (trans x α) ∧ dCo (smLie Ξ) (trans x α) = trans x (dCo (smLie Ξ) α) ∧
      ∀ c c', (∀ z (y : GL (Fin a) (Af E)), c' z (y : GL (Fin a) (Af E) ⧸ U') = c z ((y * x : GL (Fin a) (Af E)) : _ ⧸ U)) →
        IsPer U Ξ α c → IsPer U' Ξ (trans x α) c'

end UpperTheory.V.Lit.Geo
