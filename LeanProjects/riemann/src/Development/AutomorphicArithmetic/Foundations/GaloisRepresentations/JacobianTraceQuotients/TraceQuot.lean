import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD
open scoped Classical

namespace UpperTheory.Gal.Join

def ForRep (p : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (_ : Representation ℂ (GL (Fin n) k) V), Prop) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), p k n V π

structure IsAvg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G)
    (e : V →ₗ[ℂ] V) : Prop where
  mem : ∀ v, e v ∈ fixed π K
  fix : ∀ v ∈ fixed π K, e v = v
  inv : ∀ g ∈ K, ∀ v, e (π g v) = e v
  lin : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V), (∀ g ∈ K, p (π g v) = p v) → p (e v) = p v

def AvgEx : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ K : Subgroup G, CO K → ∃ e, IsAvg π K e ∧ ∀ (s : G →* G) (A : V →ₗ[ℂ] V), (∀ g v, A (π g v) = π (s g) (A v)) →
      (∀ g ∈ K, s g ∈ K) → (∀ g ∈ K, ∃ h ∈ K, s h = g) → ∀ v, A (e v) = e (A v)

def DcosOp : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ K : Subgroup G, CO K → ∀ e, IsAvg π K e → ∀ x : G,
      IsIntegralOp μ π ({g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b}.indicator fun _ => 1)
        ((μ.real {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} : ℂ) • (e ∘ₗ π x ∘ₗ e))

def HeckeMul : Prop := ForRep fun k _ _ _ _ n _ _ _ π => ∀ K, IwLev K → ∀ e, IsAvg π K e → ∀ t, Dom t → ∀ v ∈ fixed π K,
  (∀ s, Dom s → e (π (diagT k (Fin n) s) (e (π (diagT k (Fin n) t) v))) = e (π (diagT k (Fin n) (s * t)) v)) ∧
    (twKer π (unipB k (Fin n)) 1).mkQ (e (π (diagT k (Fin n) t) v)) = jacBU π t ((twKer π (unipB k (Fin n)) 1).mkQ v)

def KerKill : Prop := ForRep fun k _ _ _ _ n _ _ _ π => ∀ K, IwLev K → ∀ e, IsAvg π K e →
  ∀ v ∈ twKer π (unipB k (Fin n)) 1, ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
    (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) → e (π (diagT k (Fin n) t) v) = 0

def TraceQuot : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (B : V →ₗ[ℂ] V) (p : V →ₗ[ℂ] W) (T : W →ₗ[ℂ] W), (∀ v, B v ∈ S) → (∀ v ∈ S, p (B v) = T (p v)) →
    (∀ v ∈ S, p v = 0 → ∃ m : ℕ, (B ^ m) v = 0) → HasFinTrace B (trIn (S.map p) T)

def ImStab : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsAdmissible π → ∀ K, IwLev K → FiniteDimensional ℂ (imK π K) ∧
  (∀ t, ∀ y ∈ imK π K, jacB π t y ∈ imK π K) ∧ ∀ (σ : k ≃+* k) A (hA : Semi σ π A), (∀ g, Loc.sg (n := n) σ g ∈ K ↔ g ∈ K) →
    ∀ y ∈ imK π K, jacA hA y ∈ imK π K

def DcosVol : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure]
    (K : Subgroup (GL (Fin n) k)), IwLev K → ∀ t, Dom t →
      Test (el K t) ∧ μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹

def JacNorm : Prop := ForRep fun _ _ _ _ _ _ _ _ _ π => ∀ t y, jacBU π t y = ((Real.sqrt (deltaB t) : ℝ) : ℂ) • jacB π t y

def CasTrace : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsAdmissible π →
  ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure],
    ∀ K, IwLev K → ∀ (σ : k ≃+* k) A (hA : Semi σ π A), Isom σ → (∀ g, Loc.sg (n := n) σ g ∈ K ↔ g ∈ K) → ∀ t, Strict t →
      ∃ B, IsIntegralOp μ π (el K t) B ∧ HasFinTrace (B ∘ₗ A) ((μ.real (K : Set (GL (Fin n) k)) : ℂ) *
        ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹ * trIn (imK π K) (jacB π t ∘ₗ jacA hA))

def NormDom : Prop :=
  ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (ι : k →+* k') (σ : k' ≃+* k') (l : ℕ)
    (N : k'ˣ →* kˣ), IsNorm ι σ l N → (∀ x, N (Units.map (σ : k' →* k') x) = N x) ∧ ∀ (n : ℕ) (t : Fin n → k'ˣ),
      (Strict t → Strict (nT n N t)) ∧ deltaB (nT n N t) = deltaB t ∧ ∀ s, Strict t → Dom s → Strict (t * s)

def CharDom : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t₀ : Fin n → kˣ)
    (E E' : Multiset ((Fin n → kˣ) →* ℂˣ)) (c c' : ℂ), c ≠ 0 →
    (∀ t, Dom t → c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) →
    (∀ μ ∈ E, μ ∈ E') ∧ (E ≠ 0 → ∃ t, Dom t ∧ (E.map fun μ => (μ (t₀ * t) : ℂ)).sum ≠ 0)

def TraceExp : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ T X) (P : Submodule ℂ X)
    [FiniteDimensional ℂ P], (∀ t, ∀ y ∈ P, ρ t y ∈ P) → ∃ E : Multiset (T →* ℂˣ),
      (∀ t, trIn P (ρ t) = (E.map fun μ => (μ t : ℂ)).sum) ∧ ∀ μ, μ ∈ E ↔ ∃ y ∈ P, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y

def TwExp : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ T X) (P : Submodule ℂ X)
    [FiniteDimensional ℂ P] (s : T ≃* T) (A : X →ₗ[ℂ] X), (∀ t, ∀ y ∈ P, ρ t y ∈ P) → (∀ y ∈ P, A y ∈ P) →
    (∀ t y, A (ρ t y) = ρ (s t) (A y)) → ∀ t₁, trIn P (ρ t₁ ∘ₗ A) ≠ 0 →
      ∃ μ : T →* ℂˣ, (∀ t, μ (s t) = μ t) ∧ ∃ y ∈ P, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y

def JacFD : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → π.IsIrreducible →
  FiniteDimensional ℂ (Jacquet π (unipB k (Fin n)))

def SubQuot : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (ρ : Representation ℂ T X) (μ : T →* ℂˣ),
    ((∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y) ↔ (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥) ∧
    ((∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y) → ∃ l : X →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ t y, l (ρ t y) = (μ t : ℂ) * l y)

def QuotEmb : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → π.IsIrreducible →
  ∀ (ω : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 →
    (∀ t y, l (jacB π t y) = (torusChar ω t : ℂ) * l y) → IsSubquotient π (prinSeries ω)

def ExpSub : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → π.IsIrreducible → ∀ μ, IsExp π μ →
  ∃ ω : Fin n → kˣ →* ℂˣ, μ = torusChar ω ∧ (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient π (prinSeries ω)

def SubPerm : Prop := ForRep fun k _ _ _ _ n _ _ _ π => π.IsIrreducible → ∀ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
  ∀ w : Equiv.Perm (Fin n), IsSubquotient π (prinSeries ω) → IsSubquotient π (prinSeries (ω ∘ w))

def ExpLev : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → ∀ y : Jacquet π (unipB k (Fin n)),
  ∃ U : Subgroup (GL (Fin n) k), IsOpen (U : Set (GL (Fin n) k)) ∧ ∀ K ≤ U, y ∈ imK π K

end UpperTheory.Gal.Join
