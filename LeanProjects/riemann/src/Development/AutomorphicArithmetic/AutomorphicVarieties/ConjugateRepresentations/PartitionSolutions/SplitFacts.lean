import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped ContDiff

namespace UpperTheory.V.Cj.A

def IEquiv {Γ I M : Type} [Group Γ] [MulAction Γ I] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Γ M) (k : ℕ)
    (c : List I → M) : Prop :=
  ∀ (γ : Γ) (x : List I), x.length = k + 1 → c (x.map (γ • ·)) = ρ γ (c x)

@[ext] structure Idx (Γ J : Type) where

  g : Γ

  j : J

instance {Γ J : Type} [Group Γ] : MulAction Γ (Idx Γ J) where
  smul γ i := ⟨γ * i.g, i.j⟩
  one_smul i := Idx.ext (one_mul i.g) rfl
  mul_smul γ δ i := Idx.ext (mul_assoc γ δ i.g) rfl

@[simp] theorem Idx.smul_g {Γ J : Type} [Group Γ] (γ : Γ) (i : Idx Γ J) : (γ • i).g = γ * i.g := rfl

@[simp] theorem Idx.smul_j {Γ J : Type} [Group Γ] (γ : Γ) (i : Idx Γ J) : (γ • i).j = i.j := rfl

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

def chg (G : Dr.Geo Γ V S d) {d' : ℕ} (ξ' : Γ →* Matrix (Fin d') (Fin d') ℂ) : Dr.Geo Γ V S d' :=
  ⟨G.ρ, G.σ, ξ', G.Y, G.isOpen, G.maps⟩

variable (G : Dr.Geo Γ V S d)

def ZigI (I : Type) [MulAction Γ I] : (q k : ℕ) → (List I → G.Om q) → (List I → S → Fin d → ℂ) → Prop
  | 0, k, u, c => ∀ x : List I, x.length = k + 1 → u x = G.incl (c x)
  | q + 1, k, u, c => ∃ b : List I → G.Om q, IEquiv (G.act q) k b ∧
      (∀ x : List I, x.length = k + 1 → G.dOm q (b x) = u x) ∧ ZigI I q (k + 1) (hd b) c

def Van {I : Type} (C : I → S → Set V) (F : S → Set V) {q : ℕ} (k : ℕ) (u : List I → G.Om q) : Prop :=
  ∀ x : List I, x.length = k + 1 → ∀ s, ∀ p ∈ F s, (∀ i ∈ x, p ∈ C i s) → (u x).1 s p = 0

def VanC {I : Type} (C : I → S → Set V) (k : ℕ) (c : List I → S → Fin d → ℂ) : Prop :=
  ∀ x : List I, x.length = k + 1 → ∀ s p, (∀ i ∈ x, p ∈ C i s) → c x s = 0

structure IsCvx {I : Type} [MulAction Γ I] (C : I → S → Set V) : Prop where
  isOpen : ∀ i s, IsOpen (C i s)
  convex : ∀ i s, Convex ℝ (C i s)
  sub : ∀ i s, C i s ⊆ G.Y
  equiv : ∀ (γ : Γ) i s p, G.ρ γ p ∈ C (γ • i) (G.σ γ s) ↔ p ∈ C i s

structure IsPart {I : Type} [MulAction Γ I] (φ : I → S → V → ℝ) : Prop where
  smooth : ∀ i s, ContDiffOn ℝ ∞ (φ i s) G.Y
  locFin : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {i | ∃ x ∈ N, φ i s x ≠ 0}.Finite
  sum_one : ∀ s, ∀ p ∈ G.Y, ∑ᶠ i, φ i s p = 1
  equiv : ∀ (γ : Γ) i s p, φ (γ • i) (G.σ γ s) (G.ρ γ p) = φ i s p

def sat (T : Set S) (K : Set V) (s : S) : Set V :=
  {p | ∃ (γ : Γ) (t : ℝ), 0 < t ∧ G.σ γ s ∈ T ∧ t • G.ρ γ p ∈ K}

def CSuppG {q : ℕ} (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : Prop :=
  ∃ (T : Set S) (K : Set V), T.Finite ∧ IsCompact K ∧ K ⊆ G.Y ∧ ∀ s, ∀ p ∈ G.Y, p ∉ sat G T K s → w s p = 0

def InvSet (A : S → Set V) : Prop := ∀ (γ : Γ) s p, G.ρ γ p ∈ A (G.σ γ s) ↔ p ∈ A s

end

def HdFacts : Prop :=
  (∀ (I M : Type) [AddCommGroup M] (c : List I → M) (x : List I), hd (hd c) x = 0) ∧
  (∀ (I M : Type) [AddCommGroup M] (c : List I → M) (i : I) (x : List I), hd c (i :: x) = c x - hd (fun y => c (i :: y)) x) ∧
  (∀ (I J M : Type) [AddCommGroup M] (f : J → I) (c : List I → M) (x : List J),
    hd (fun y => c (y.map f)) x = hd c (x.map f)) ∧
  (∀ (I M N : Type) [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (c : List I → M) (x : List I),
    hd (fun y => f (c y)) x = f (hd c x)) ∧
  (∀ (I M : Type) [AddCommGroup M] (c c' : List I → M) (x : List I),
    (∀ y : List I, y.length + 1 = x.length → (∀ i ∈ y, i ∈ x) → c y = c' y) → hd c x = hd c' x) ∧
  ∀ (Γ I M : Type) [Group Γ] [MulAction Γ I] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Γ M) (k : ℕ)
    (c : List I → M), IEquiv ρ k c → IEquiv ρ (k + 1) (hd c)

def RelPoin : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [CompleteSpace F] (Y C : Set V), IsOpen Y → Convex ℝ Y → Convex ℝ C → C ⊆ Y →
    ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F), ContDiffOn ℝ ∞ w Y → (∀ p ∈ Y, extDeriv w p = 0) → (∀ p ∈ C, w p = 0) →
    ∃ η : V → V [⋀^Fin q]→L[ℝ] F, ContDiffOn ℝ ∞ η Y ∧ (∀ p ∈ Y, extDeriv η p = w p) ∧ ∀ p ∈ C, η p = 0

def RelPrim : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    Convex ℝ G.Y → ∀ (C : S → Set V), (∀ s, Convex ℝ (C s) ∧ C s ⊆ G.Y) → ∀ (q : ℕ) (w : G.Om (q + 1)), G.dOm (q + 1) w = 0 →
    (∀ s, ∀ p ∈ C s, w.1 s p = 0) → ∃ η : G.Om q, G.dOm q η = w ∧ ∀ s, ∀ p ∈ C s, η.1 s p = 0

def FwdStep : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MulAction Γ I] (d : ℕ)
    (G : Dr.Geo Γ V S d), Convex ℝ G.Y → ∀ r : I → Γ, (∀ (γ : Γ) i, r (γ • i) = γ * r i) → ∀ C : I → S → Set V, IsCvx G C →
    ∀ (q k : ℕ) (u : List I → G.Om (q + 1)), IEquiv (G.act (q + 1)) k u →
    (∀ x : List I, x.length = k + 1 → G.dOm (q + 1) (u x) = 0) → Van G C (fun _ => Set.univ) k u →
    ∃ b : List I → G.Om q, IEquiv (G.act q) k b ∧ (∀ x : List I, x.length = k + 1 → G.dOm q (b x) = u x) ∧
      Van G C (fun _ => Set.univ) k b

def ZigFwd : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MulAction Γ I] (d : ℕ)
    (G : Dr.Geo Γ V S d), Convex ℝ G.Y → G.Y.Nonempty → ∀ r : I → Γ, (∀ (γ : Γ) i, r (γ • i) = γ * r i) →
    ∀ C : I → S → Set V, IsCvx G C → ∀ (q k n : ℕ), k + q = n → ∀ u : List I → G.Om q, IEquiv (G.act q) k u →
    (∀ x : List I, x.length = k + 1 → G.dOm q (u x) = 0) → (∀ x : List I, x.length = k + 2 → hd u x = 0) →
    Van G C (fun _ => Set.univ) k u →
    ∃ c : List I → S → Fin d → ℂ, ZigI G I q k u c ∧ IEquiv G.lev n c ∧ (∀ x : List I, x.length = n + 2 → hd c x = 0) ∧
      VanC C n c

def PartMem : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] (d : ℕ) (G : Dr.Geo Γ V S d)
    (φ : I → S → V → ℝ), IsPart G φ → ∀ (q : ℕ) (c : I → G.Om q), (fun s p => ∑ᶠ i, φ i s p • (c i).1 s p) ∈ G.Om q

def PartOp : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] (d : ℕ) (G : Dr.Geo Γ V S d)
    (φ : I → S → V → ℝ), IsPart G φ → ∀ q : ℕ, ∃ P : (I → G.Om q) →ₗ[ℂ] G.Om q, (∀ w, P (fun _ => w) = w) ∧
      (∀ (γ : Γ) c, P (fun i => G.act q γ (c (γ⁻¹ • i))) = G.act q γ (P c)) ∧
      ∀ c s p, (∀ i, φ i s p ≠ 0 → (c i).1 s p = 0) → (P c).1 s p = 0

def BwdStep : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] (d : ℕ) (G : Dr.Geo Γ V S d)
    (φ : I → S → V → ℝ), IsPart G φ → ∀ (C : I → S → Set V) (F : S → Set V), (∀ i s, ∀ p ∈ F s, φ i s p ≠ 0 → p ∈ C i s) →
    ∀ (q k : ℕ) (u : List I → G.Om q), IEquiv (G.act q) (k + 1) u → (∀ x : List I, x.length = k + 3 → hd u x = 0) →
    Van G C F (k + 1) u →
    ∃ b : List I → G.Om q, IEquiv (G.act q) k b ∧ (∀ x : List I, x.length = k + 2 → hd b x = u x) ∧ Van G C F k b

def BwdLast : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] (d : ℕ) (G : Dr.Geo Γ V S d)
    (φ : I → S → V → ℝ), IsPart G φ → ∀ (C : I → S → Set V) (F : S → Set V), (∀ i s, ∀ p ∈ F s, φ i s p ≠ 0 → p ∈ C i s) →
    ∀ (q : ℕ) (u : List I → G.Om q), IEquiv (G.act q) 0 u → (∀ x : List I, x.length = 2 → hd u x = 0) → Van G C F 0 u →
    ∃ w : G.Om q, (∀ γ, G.act q γ w = w) ∧ (∀ x : List I, x.length = 1 → u x = w) ∧ ∀ s, ∀ p ∈ F s, w.1 s p = 0

def ZigFormal : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] (d : ℕ) (G : Dr.Geo Γ V S d),
    (∀ (q k : ℕ) (u u' : List I → G.Om q) c, (∀ x : List I, x.length = k + 1 → u x = u' x) → ZigI G I q k u c →
      ZigI G I q k u' c) ∧
    ∀ ι : Γ → I, (∀ γ δ : Γ, ι (γ * δ) = γ • ι δ) → ∀ (q k : ℕ) (u : List I → G.Om q) c, ZigI G I q k u c →
      Zig G q k (fun x => u (x.map ι)) (fun x => c (x.map ι))

def ZigBwd : Prop :=
  ∀ (Γ V S I : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MulAction Γ I] (d : ℕ)
    (G : Dr.Geo Γ V S d), Convex ℝ G.Y → G.Y.Nonempty → ∀ φ : I → S → V → ℝ, IsPart G φ →
    ∀ (C : I → S → Set V) (F : S → Set V), IsCvx G C → (∀ s, IsOpen (F s)) → (∀ i s, ∀ p ∈ F s, φ i s p ≠ 0 → p ∈ C i s) →
    ∀ (n : ℕ) (c : List I → S → Fin d → ℂ), IEquiv G.lev n c → (∀ x : List I, x.length = n + 2 → hd c x = 0) → VanC C n c →
    ∀ q k : ℕ, k + q = n → ∃ u : List I → G.Om q, ZigI G I q k u c ∧ IEquiv (G.act q) k u ∧
      (∀ x : List I, x.length = k + 1 → G.dOm q (u x) = 0) ∧ (∀ x : List I, x.length = k + 2 → hd u x = 0) ∧ Van G C F k u

def PullOp : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∃ P : ∀ q, G.Om q →ₗ[ℂ] G.Om q,
      (∀ q w s, ∀ p ∈ G.Y, (P q w).1 s p = pull (l s) (w.1 s) p) ∧ (∀ q w, G.dOm q (P q w) = P (q + 1) (G.dOm q w)) ∧
      ∀ f, P 0 (G.incl f) = G.incl f

def PullAct : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ (q : ℕ) (P : G.Om q →ₗ[ℂ] G.Om q),
      (∀ w s, ∀ p ∈ G.Y, (P w).1 s p = pull (l s) (w.1 s) p) → ∀ γ w, G.act q γ (P w) = P (G.act q γ w)

def ZigMap : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (P : ∀ q, G.Om q →ₗ[ℂ] G.Om q), (∀ q w, G.dOm q (P q w) = P (q + 1) (G.dOm q w)) → (∀ f, P 0 (G.incl f) = G.incl f) →
    (∀ q γ w, G.act q γ (P q w) = P q (G.act q γ w)) →
    ∀ (q k : ℕ) (u : List Γ → G.Om q) c, Zig G q k u c → Zig G q k (fun x => P q (u x)) c

def PartBase : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Y : Set V), IsOpen Y →
    ∀ D : V → Set V, (∀ j, IsOpen (D j)) → (∀ p ∈ Y, p ∈ D p) → ∃ ψ : V → V → ℝ, (∀ j, ContDiffOn ℝ ∞ (ψ j) Y) ∧
      (∀ p ∈ Y, ∃ N ∈ nhds p, {j | ∃ x ∈ N, ψ j x ≠ 0}.Finite) ∧ (∀ p ∈ Y, ∑ᶠ j, ψ j p = 1) ∧ ∀ j p, ψ j p ≠ 0 → p ∈ D j

def PartProd : Prop :=
  ∀ (Γ V S J : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d) (u : S → V → ℝ),
    G.IsCutoff u → ∀ ψ : S → J → V → ℝ, (∀ s j, ContDiffOn ℝ ∞ (ψ s j) G.Y) →
    (∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {j | ∃ x ∈ N, ψ s j x ≠ 0}.Finite) → (∀ s, ∀ p ∈ G.Y, ∑ᶠ j, ψ s j p = 1) →
    IsPart G fun (i : Idx Γ J) s p => u (G.σ i.g⁻¹ s) (G.ρ i.g⁻¹ p) * ψ (G.σ i.g⁻¹ s) i.j (G.ρ i.g⁻¹ p)

def CoverEx : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    G.Proper → ∀ A O : S → Set V, (∀ s, IsOpen (A s) ∧ A s ⊆ G.Y ∧ IsOpen (O s) ∧ G.Y ⊆ A s ∪ O s) → InvSet G A → InvSet G O →
    ∃ (C : Idx Γ V → S → Set V) (φ : Idx Γ V → S → V → ℝ), IsCvx G C ∧ IsPart G φ ∧ (∀ i s, C i s ⊆ A s) ∧
      ∀ i s p, p ∉ O s → φ i s p ≠ 0 → p ∈ C i s

def OrbClosed : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    G.Proper → ∀ K ⊆ G.Y, IsCompact K → ∀ s s' : S, IsOpen (G.Y \ {p | ∃ γ : Γ, G.σ γ s = s' ∧ G.ρ γ p ∈ K})

def SatClosed : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    G.Proper → IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ (T : Set S) (K : Set V), T.Finite → IsCompact K → K ⊆ G.Y →
    ∀ s, IsOpen (G.Y \ sat G T K s)

def SatFacts : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d) (T : Set S) (K : Set V),
    InvSet G (sat G T K) ∧ (IsOpen K → ∀ s, IsOpen (sat G T K s)) ∧ (∀ K', K ⊆ K' → ∀ s, sat G T K s ⊆ sat G T K' s) ∧
      ∀ s p (t : ℝ), 0 < t → (t • p ∈ sat G T K s ↔ p ∈ sat G T K s)

def AbsTrans : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d d' : ℕ) (G : Dr.Geo Γ V S d)
    (ξ' : Γ →* Matrix (Fin d') (Fin d') ℂ) (τ : (Fin d → ℂ) →+ (Fin d' → ℂ)), (∀ γ v, τ (G.ξ γ *ᵥ v) = ξ' γ *ᵥ τ v) →
    Convex ℝ G.Y → G.Y.Nonempty → IsCone G.Y → G.Proper → (∃ l, G.IsInvGauge l) →
    ∀ (q : ℕ) (w : G.Om q), (∀ γ, G.act q γ w = w) → G.dOm q w = 0 → CSuppG G w.1 →
    ∃ (c : List Γ → S → Fin d → ℂ) (w' : (chg G ξ').Om q), Zig G q 0 (fun _ => w) c ∧
      Zig (chg G ξ') q 0 (fun _ => w') (fun x s => τ (c x s)) ∧ (∀ γ, (chg G ξ').act q γ w' = w') ∧
      (chg G ξ').dOm q w' = 0 ∧ (∀ s, RadBasic G.Y (w'.1 s)) ∧ CSuppG (chg G ξ') w'.1

def SandCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) ∧
    ∀ K ⊆ cone E a, IsCompact K → IsCompact {g : GL (Fin a) (Cinf E) | sand g (hOne E a) ∈ K}

def SplitFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    (∀ t, GeneralLinearGroup.map (pFin E) (GlobalTheory.UnitaryBC.splitCentre E a t) = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∀ p, sand (GeneralLinearGroup.map (pInf E) (GlobalTheory.UnitaryBC.splitCentre E a t)) p = r • p) ∧
    ∀ r : ℝ, 0 < r → ∃ t, ∀ p, sand (GeneralLinearGroup.map (pInf E) (GlobalTheory.UnitaryBC.splitCentre E a t)) p = r • p

def SuppFwd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) w,
    Corr U Ξ α w → CSupp α → CSuppG (geo ho U Ξ) w

def SuppBwd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) w,
    Corr U Ξ α w → CSuppG (geo ho U Ξ) w → CSupp α

def LevCorr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ),
    (∀ α : Co Ξ q, IsLev U Ξ α → dCo (smLie Ξ) α = 0 → ∃ w : (geo ho U Ξ).Om q, Corr U Ξ α w.1 ∧
      (∀ γ, (geo ho U Ξ).act q γ w = w) ∧ (geo ho U Ξ).dOm q w = 0) ∧
    ∀ w : (geo ho U Ξ).Om q, (∀ γ, (geo ho U Ξ).act q γ w = w) → (geo ho U Ξ).dOm q w = 0 →
      (∀ s, RadBasic (cone E a) (w.1 s)) → ∃ α : Co Ξ q, Corr U Ξ α w.1 ∧ IsLev U Ξ α ∧ dCo (smLie Ξ) α = 0

end UpperTheory.V.Cj.A
