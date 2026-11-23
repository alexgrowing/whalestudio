import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDefs

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

def CompSz : Prop :=
  ∀ (V W F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : W → F) (f : V → W) (x : V) (b : ℝ),
    ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g (f x) → (∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ c) →
    Sz k g (f x) b → Sz k (fun y => g (f y)) x (C * b)

def AppSz : Prop :=
  ∀ (V W F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (x : V),
    (∀ (f : V → W →L[ℝ] F) (g : V → W) (a b : ℝ), ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x → Sz k f x a → Sz k g x b →
      Sz k (fun y => f y (g y)) x (2 ^ k * a * b)) ∧
    (∀ (L : W →L[ℝ] F) (g : V → W) (b : ℝ), ContDiffAt ℝ ∞ g x → Sz k g x b → Sz k (fun y => L (g y)) x (‖L‖ * b)) ∧
    ∀ (ι : Type) (s : Finset ι) (g : ι → V → F) (b : ι → ℝ), (∀ i ∈ s, ContDiffAt ℝ ∞ (g i) x) → (∀ i ∈ s, Sz k (g i) x (b i)) →
      Sz k (fun y => ∑ i ∈ s, g i y) x (∑ i ∈ s, b i)

def AltSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ),
    ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) ∧
    ∃ C : ℝ, ∀ L : V →L[ℝ] V, ‖L‖ ≤ c → Sz k (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) L C

def AltEv : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ),
    ∃ (T : Finset (Fin q → V)) (C : ℝ), 0 ≤ C ∧ ∀ (f : V → V [⋀^Fin q]→L[ℝ] F) (x : V) (b : ℝ), 0 ≤ b →
      (∀ v ∈ T, ContDiffAt ℝ ∞ (fun y => f y v) x) → (∀ v ∈ T, Sz k (fun y => f y v) x b) → Sz k f x (C * b)

def TpSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : V →L[ℝ] V) (B : F →L[ℝ] F) (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (b : ℝ), ‖A‖ ≤ c → ‖B‖ ≤ c →
      ContDiffAt ℝ ∞ w (A p) → Sz k w (A p) b → Sz k (tp A B w) p (C * b)

def FlowSz : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (c : ℝ) (W : V → V) (t : ℝ) (p : V), |t| ≤ 1 →
    ContDiffAt ℝ ∞ W p → Sz (k + 1) W p c → ContDiffAt ℝ ∞ (flow W t) p ∧ ContDiffAt ℝ ∞ (fderiv ℝ (flow W t)) p ∧
      Sz k (fderiv ℝ (flow W t)) p (1 + c) ∧ ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (flow W t) p‖ ≤ 1 + c

def PbSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W : V → V) (t : ℝ) (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (b : ℝ), |t| ≤ 1 → ContDiffAt ℝ ∞ W p → Sz (k + 1) W p c →
      ContDiffAt ℝ ∞ w (flow W t p) → Sz k w (flow W t p) b → Sz k (pb (flow W t) w) p (C * b)

def HkSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W : V → V) (t : ℝ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (b : ℝ), |t| ≤ 1 → ContDiffAt ℝ ∞ W p →
      Sz (k + 1) W p c → ContDiffAt ℝ ∞ w (flow W t p) → Sz k w (flow W t p) b → Sz k (hk W t w) p (C * b)

def IntSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (k : ℕ) (p : V) (O : Set (V × ℝ))
    (Φ : V × ℝ → F) (b : ℝ), IsOpen O → (∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) → ContDiffOn ℝ ∞ Φ O →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (fun x => Φ (x, t)) p b) → Sz k (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p b

def HomSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Y : Set V) (W : V → V) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (b : ℝ), IsOpen Y → IsField Y W → ContDiffOn ℝ ∞ w Y →
      ∀ p ∈ Y, Sz (k + 1) W p c → (∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k w (flow W t p) b) → Sz k (hom W w) p (C * b)

def SumSm : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Y : Set V), IsOpen Y → ∀ y : ℕ → V → F, (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ ∞ (fun x => ∑' j, y j x) Y ∧
      ∀ p ∈ Y, HasSum (fun j => fderiv ℝ (y j) p) (fderiv ℝ (fun x => ∑' j, y j x) p)

def GeoCut : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (Φ : S → V → ℝ), IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
    (∀ s, ContDiffOn ℝ ∞ (η s) {p | p ∈ G.Y ∧ R < Φ s p}) →
    (∀ γ s, ∀ p ∈ G.Y, R < Φ s p → G.tr q γ (η (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = η s p) →
    ∃ z : G.Om q, Inv G z ∧ ∀ s, ∀ p ∈ G.Y, R + 1 ≤ Φ s p → z.1 s p = η s p

def GeoSum : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (Φ : S → V → ℝ), IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (y : ℕ → G.Om q) (w : ℕ → G.Om (q + 1)), (∀ j, Inv G (y j)) →
    (∀ j, G.dOm q (y j) = w (j + 1) - w j) →
    (∀ k s, ∀ p ∈ G.Y, R < Φ s p → ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k ((y j).1 s) x (b j)) →
    (∀ s, ∀ p ∈ G.Y, R < Φ s p → Filter.Tendsto (fun j => (w j).1 s p) Filter.atTop (𝓝 0)) →
    ∃ z : G.Om q, Inv G z ∧ ∀ s, ∀ p ∈ G.Y, R + 1 < Φ s p → (G.dOm q z).1 s p = (w 0).1 s p

def GeoRet : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ Φ : S → V → ℝ, IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (w : G.Om (q + 1))
    (z : G.Om q), G.dOm (q + 1) w = 0 → (∀ s, RadBasic G.Y (w.1 s)) → Inv G z →
    (∀ s, ∀ p ∈ G.Y, R < Φ s p → (G.dOm q z).1 s p = w.1 s p) →
    ∃ z' : G.Om q, Good G z' ∧ ∀ s, ∀ p ∈ G.Y, R < Φ s p → (G.dOm q z').1 s p = w.1 s p

def LamEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ lam : GA E a → ℝ, IsLam lam

def DescEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∃ Φ, Desc U f Φ

def DescFun : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ Φ, Desc U f Φ → IsFun (geo ho U Ξ) Φ

def SecOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ τ : HV E a → GL (Fin a) (Cinf E), τ (hOne E a) = 1 ∧
    ContDiffAt ℝ ∞ (fun p => toL (τ p).val) (hOne E a) ∧ ContDiffAt ℝ ∞ (fun p => toL ((τ p)⁻¹).val) (hOne E a) ∧
    ContDiffAt ℝ ∞ (fun p => sand (τ p)) (hOne E a) ∧ ContDiffAt ℝ ∞ (fun p => sand (τ p)⁻¹) (hOne E a) ∧
    ∀ᶠ p in 𝓝 (hOne E a), sand (τ p) (hOne E a) = p

def LocBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ p₀ ∈ cone E a, ∃ c : ℝ, ∀ᶠ p in 𝓝 p₀,
    ∃ h : GL (Fin a) (Cinf E), Bnd c h ∧ sand h (hOne E a) = p

def ChartSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : ℕ) (ρ : GA E a → ℝ), (∀ g, 0 ≤ ρ g) → ∀ φ : Sm E a,
    (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart φ.1 g) (oneL E a) (C * ρ g)

def ZwSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W → ∀ k : ℕ, ∃ c : ℝ, ∀ g x, Sz k (Zw U W g x) (hOne E a) c

def RapidEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (r : ℝ), HasOne Ξ r → ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)),
    lie E a (oneL E a) ((l.map (lie E a)).prod (Bor.cmp j (α X))) = -(r : ℂ) • (l.map (lie E a)).prod (Bor.cmp j (α X)) ∧
    ∀ g, ev ((l.map (smA Ξ)).prod (α X)) g j = ((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g

def RapidAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f lam : GA E a → ℝ) (C : ℝ), IsLam lam → (∀ g, f g ≤ C * (1 + Real.log (qht g))) →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → RapidD α → ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
        ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * Real.exp (B * |lam g| - A * f g)

def CorrForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (v : Fin q → HV E a),
    ∃ (ι : Type) (_ : Fintype ι) (X : ι → Fin q → Herm E a) (j : ι → Fin Ξ.d) (Θ : ι → HV E a → Fin Ξ.d → ℂ)
      (τ : HV E a → Lie E a), τ (hOne E a) = oneL E a ∧ ContDiffAt ℝ ∞ τ (hOne E a) ∧ (∀ i, ContDiffAt ℝ ∞ (Θ i) (hOne E a)) ∧
      ∀ (U : Subgroup (GL (Fin a) (Af E))) (α : Co Ξ q) (w : Fm U Ξ q), Corr U Ξ α w → ∀ g x,
        (fun p => Tw U Ξ w g x p v) =ᶠ[𝓝 (hOne E a)] fun p => ∑ i, chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p

def CorrSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q), Corr U Ξ α w → ∀ ρ : GA E a → ℝ, (∀ g, 0 ≤ ρ g) →
    (∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) →
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, Sz k (Tw U Ξ w g x) (hOne E a) (M * ρ (pt g x))

def TwOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a), IsFlow (geo ho U Ξ) W → ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    IsField (cone E a) (Zw U W g x) ∧ (∀ t p, flow (Zw U W g x) t p = sand g⁻¹ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g p))) ∧
    ∀ q : ℕ, (∀ w : (geo ho U Ξ).Om q, ContDiffOn ℝ ∞ (Tw U Ξ w.1 g x) (cone E a) ∧ ∀ p ∈ cone E a,
        Tw U Ξ (pbOm (geo ho U Ξ) W w).1 g x p = pb (flow (Zw U W g x) 1) (Tw U Ξ w.1 g x) p) ∧
      ∀ w : (geo ho U Ξ).Om (q + 1), ∀ p ∈ cone E a,
        Tw U Ξ (homOm (geo ho U Ξ) W w).1 g x p = hom (Zw U W g x) (Tw U Ξ w.1 g x) p

def Move : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q k : ℕ) (c : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ (w : (geo ho U Ξ).Om q) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (h : GL (Fin a) (Cinf E)) (b : ℝ), Bnd c h →
      Sz k (Tw U Ξ w.1 (g * h) x) (hOne E a) b → Sz k (Tw U Ξ w.1 g x) (sand h (hOne E a)) (D * b)

def DecP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ W, FCorr U Y W → ∀ lam, IsLam lam →
    ∀ (q k : ℕ) (B : ℝ), 0 ≤ B → ∃ D : ℝ, 0 ≤ D ∧ ∀ A M : ℝ, 0 ≤ A → 0 ≤ M → ∀ w : (geo ho U Ξ).Om q,
      Dec U Ξ f lam f₀ k A B M w.1 → Dec U Ξ f lam f₀ k A B (D * Real.exp (-(A * c)) * M) (pbOm (geo ho U Ξ) W w).1

def DecK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ W, FCorr U Y W → ∀ lam, IsLam lam →
    ∀ (q k : ℕ) (A B : ℝ), 0 ≤ A → 0 ≤ B → ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℝ, 0 ≤ M → ∀ w : (geo ho U Ξ).Om (q + 1),
      Dec U Ξ f lam f₀ k A B M w.1 → Dec U Ξ f lam (f₀ + C) k A B (D * M) (homOm (geo ho U Ξ) W w).1

def Loc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f lam : GA E a → ℝ), (∀ g, 0 ≤ f g) → IsLam lam → ∀ Φ, Desc U f Φ → IsFun (geo ho U Ξ) Φ →
    ∀ (q k : ℕ) (A B R : ℝ), 0 ≤ A → 0 ≤ B → ∀ s, ∀ p ∈ cone E a, R < Φ s p → ∃ N ∈ 𝓝 p, ∃ D : ℝ,
      ∀ M : ℝ, 0 ≤ M → ∀ w : (geo ho U Ξ).Om q, Dec U Ξ f lam R k A B M w.1 → ∀ x ∈ N, Sz k (w.1 s) x (D * M)

def Supp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ Φ, Desc U f Φ → ∀ (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (R : ℝ), Corr U Ξ α w →
    (∀ s, ∀ p ∈ cone E a, R < Φ s p → w s p = 0) → CSupp α

end UpperTheory.V.Lit.Geo.Cs
