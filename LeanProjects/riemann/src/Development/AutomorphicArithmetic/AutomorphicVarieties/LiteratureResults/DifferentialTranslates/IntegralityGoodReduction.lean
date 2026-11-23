import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DifferentiableAtOm

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

def Acyclic : Prop :=
  ∀ (Γ Ω : Type) [Group Γ] [AddCommGroup Ω] [Module ℂ Ω] (ρ : Representation ℂ Γ Ω), HasAverage ρ →
    ∀ n : ℕ, Subsingleton (groupCohomology (Rep.of ρ) (n + 1))

def ShiftUp : Prop :=
  ∀ (Γ M Ω Z : Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup Ω] [Module ℂ Ω] [AddCommGroup Z] [Module ℂ Z]
    (ρM : Representation ℂ Γ M) (ρΩ : Representation ℂ Γ Ω) (ρZ : Representation ℂ Γ Z) (ι : M →ₗ[ℂ] Ω) (π : Ω →ₗ[ℂ] Z),
    (∀ γ m, ι (ρM γ m) = ρΩ γ (ι m)) → (∀ γ x, π (ρΩ γ x) = ρZ γ (π x)) → Function.Injective ι → Function.Surjective π →
    Function.Exact ι π → (∀ n : ℕ, Subsingleton (groupCohomology (Rep.of ρΩ) (n + 1))) →
    ∀ n : ℕ, Module.rank ℂ (groupCohomology (Rep.of ρZ) (n + 1)) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) (n + 2))

def ShiftOne : Prop :=
  ∀ (Γ M Ω Z : Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup Ω] [Module ℂ Ω] [AddCommGroup Z] [Module ℂ Z]
    (ρM : Representation ℂ Γ M) (ρΩ : Representation ℂ Γ Ω) (ρZ : Representation ℂ Γ Z) (ι : M →ₗ[ℂ] Ω) (π : Ω →ₗ[ℂ] Z),
    (∀ γ m, ι (ρM γ m) = ρΩ γ (ι m)) → (∀ γ x, π (ρΩ γ x) = ρZ γ (π x)) → Function.Injective ι → Function.Surjective π →
    Function.Exact ι π → ∀ (n : ℕ) (w : Fin n → Z), (∀ i γ, ρZ γ (w i) = w i) →
    (∀ c : Fin n → ℂ, (∃ y, (∀ γ, ρΩ γ y = y) ∧ π y = ∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) 1)

def ShiftZero : Prop :=
  ∀ (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Γ M) (n : ℕ) (w : Fin n → M),
    (∀ i γ, ρ γ (w i) = w i) → (∀ c : Fin n → ℂ, ∑ i, c i • w i = 0 → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρ) 0)

def AbsMain : Prop :=
  ∀ (q : ℕ) (Γ M : Type) (Ω : ℕ → Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρM : Representation ℂ Γ M) (ρ : ∀ q, Representation ℂ Γ (Ω q)) (ι : M →ₗ[ℂ] Ω 0) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)),
    (∀ γ m, ι (ρM γ m) = ρ 0 γ (ι m)) → (∀ q γ x, d q (ρ q γ x) = ρ (q + 1) γ (d q x)) → Function.Injective ι →
    Function.Exact ι (d 0) → (∀ q, Function.Exact (d q) (d (q + 1))) → (∀ q, HasAverage (ρ q)) →
    ∀ (n : ℕ) (w : Fin n → Ω q), (∀ i γ, ρ q γ (w i) = w i) → (∀ i, d q (w i) = 0) →
    (∀ c : Fin n → ℂ, InvExact ρ d (∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) q)

def ParamSmooth : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (Y : Set V) (W : Set (V × ℝ)) (Φ : V × ℝ → F),
    IsOpen Y → IsOpen W → Y ×ˢ Set.Icc (0 : ℝ) 1 ⊆ W → ContDiffOn ℝ ∞ Φ W →
    ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, Φ (p, t)) Y

def ParamDeriv : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (p : V) (W : Set (V × ℝ)) (Φ : V × ℝ → F),
    IsOpen W → (∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ W) → ContDiffOn ℝ ∞ Φ W →
    ContinuousOn (fun t => fderiv ℝ (fun x => Φ (x, t)) p) (Set.Icc 0 1) ∧
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x => Φ (x, t)) p) p

def PoinPt : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p₀ p : V) (t : ℝ),
    DifferentiableAt ℝ w (p₀ + t • (p - p₀)) → extDeriv w (p₀ + t • (p - p₀)) = 0 →
    HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
      (extDeriv (fun x => t ^ q • (w (p₀ + t • (x - p₀))).curryLeft (x - p₀)) p) t

def Poincare : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (Y : Set V), IsOpen Y → Convex ℝ Y →
    ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F), ContDiffOn ℝ ∞ w Y → (∀ p ∈ Y, extDeriv w p = 0) →
    ∃ η : V → V [⋀^Fin q]→L[ℝ] F, ContDiffOn ℝ ∞ η Y ∧ ∀ p ∈ Y, extDeriv η p = w p

def AltSmooth : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    (q : ℕ) (f : X → V [⋀^Fin q]→L[ℝ] F) (x : X), (∀ v, ContDiffAt ℝ ∞ (fun y => f y v) x) → ContDiffAt ℝ ∞ f x

def ApplySmooth : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : ℕ) (f : X → V [⋀^Fin q]→L[ℝ] F) (v : Fin q → X → V) (x : X), ContDiffAt ℝ ∞ f x → (∀ i, ContDiffAt ℝ ∞ (v i) x) →
    ContDiffAt ℝ ∞ (fun y => f y fun i => v i y) x

def AltSym : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (L : Fin (q + 1) → V →L[ℝ] V)
    (γ : Fin (q + 1) → ℝ → V) (u : Fin (q + 1) → Fin (q + 1) → ℝ → V) (D : Fin (q + 1) → F),
    DifferentiableAt ℝ w p → (∀ i j, L i (L j p) = L j (L i p)) → (∀ i, γ i 0 = p ∧ HasDerivAt (γ i) (L i p) 0) →
    (∀ i j, u i j 0 = L j p ∧ HasDerivAt (u i j) (L j (L i p)) 0) →
    (∀ i, HasDerivAt (fun t => w (γ i t) fun j => u i (i.succAbove j) t) (D i) 0) →
    extDeriv w p (fun i => L i p) = ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • D i

def Homog : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (Y : Set V), IsOpen Y → IsCone Y → ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F),
    ContDiffOn ℝ ∞ w Y → RadBasic Y w → (∀ p ∈ Y, extDeriv w p = 0) →
    ∀ t : ℝ, 0 < t → ∀ p ∈ Y, ∀ v : Fin q → V, w (t • p) (fun i => t • v i) = w p v

def PullTranslates : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (Y : Set V), IsOpen Y → IsCone Y → ∀ l : V → ℝ, IsGauge Y l → ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F),
    RadBasic Y (pull l w) ∧ (RadBasic Y w →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Y, ∀ v : Fin q → V, w (t • p) (fun i => t • v i) = w p v) → ∀ p ∈ Y, pull l w p = w p)

def PullB : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (Y : Set V), IsOpen Y → IsCone Y → ∀ l : V → ℝ, IsGauge Y l →
    ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffOn ℝ ∞ w Y →
    ContDiffOn ℝ ∞ (pull l w) Y ∧ ∀ p ∈ Y, extDeriv (pull l w) p = pull l (extDeriv w) p

def PullEquiv : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Geo Γ V S d), IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ (q : ℕ) (η : G.Om q), (∀ γ, G.act q γ η = η) →
    ∀ γ s, ∀ p ∈ G.Y, G.tr q γ (pull (l (G.σ γ⁻¹ s)) (η.1 (G.σ γ⁻¹ s)) (G.ρ γ⁻¹ p)) = pull (l s) (η.1 s) p

def Retract : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Geo Γ V S d), IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ (q : ℕ) (η : G.Om q), (∀ γ, G.act q γ η = η) →
    (∀ s, RadBasic G.Y ((G.dOm q η).1 s)) →
    ∃ η' : G.Om q, (∀ γ, G.act q γ η' = η') ∧ (∀ s, RadBasic G.Y (η'.1 s)) ∧ G.dOm q η' = G.dOm q η

def DEquiv : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Geo Γ V S d) (q : ℕ) (γ : Γ) (w : G.Om q), G.dOm q (G.act q γ w) = G.act (q + 1) γ (G.dOm q w)

def InclFacts : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Geo Γ V S d), Convex ℝ G.Y → G.Y.Nonempty →
    (∀ γ f, G.incl (G.lev γ f) = G.act 0 γ (G.incl f)) ∧ Function.Injective G.incl ∧ Function.Exact G.incl (G.dOm 0)

def DExact : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Geo Γ V S d), Convex ℝ G.Y → ∀ q, Function.Exact (G.dOm q) (G.dOm (q + 1))

def AvgMem : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Geo Γ V S d) (u : S → V → ℝ), G.IsCutoff u → ∀ (q : ℕ) (c : Γ → G.Om q),
    (fun s p => ∑ᶠ γ : Γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c γ).1 s p) ∈ G.Om q

def Average : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (G : Geo Γ V S d) (u : S → V → ℝ), G.IsCutoff u → ∀ q : ℕ, HasAverage (G.act q)

def WindowOne : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Geo Γ V S d), Subsingleton S → G.Proper → ∃ W, G.IsWindow W

def Window : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Geo Γ V S d), G.Proper → ∃ W, G.IsWindow W

def Cutoff : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Geo Γ V S d) (W : S → Set V), G.IsWindow W → ∃ u, G.IsCutoff u

end UpperTheory.V.Lit.Dr
