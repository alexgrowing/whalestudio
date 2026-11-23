import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

section Generic

variable {G : Type} [Group G]

def twCent (θ : G →* G) (δ : G) : Subgroup G where
  carrier := {g | g * δ = δ * θ g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at *
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv] at *
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]

def TwCl (θ : G →* G) : Type := Quot fun x y : G => ∃ g, y = g⁻¹ * x * θ g

def TwCl.rep {θ : G →* G} (c : TwCl θ) : G := Quot.out c

def rStab {H : Type} [Group H] (u : H → ℂ) : Subgroup H where
  carrier := {k | ∀ x, u (x * k) = u x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha x
    rw [← ha (x * a⁻¹), inv_mul_cancel_right]

def avg {H : Type} [Group H] (u : H → ℂ) : ℂ := ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out

def levOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (A : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ K', f q.out • (ρ q.out ∘ₗ A)

def twTr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (A : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' then
    LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) else 0

def extT {G' V V' : Type} [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') : Representation ℂ (G × G') (V ⊗[ℂ] V') :=
  Representation.tprod (ρ.comp (MonoidHom.fst G G')) (ρ'.comp (MonoidHom.snd G G'))

variable [TopologicalSpace G]

def cptPart (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}

def twOrb (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G),
    (((twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
      avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def clSum (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ) (f : G → ℂ) : ℂ :=
  ∑ᶠ c : TwCl θ, if c.rep ∈ S then wt c.rep * twOrb θ K c.rep f else 0

def mass (θ : G →* G) (Γ : Subgroup G) (δ : G) : ℂ :=
  (Nat.card (DoubleCoset.Quotient (Γ.subgroupOf (twCent θ δ) : Set (twCent θ δ))
      ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ) : Set (twCent θ δ))) : ℂ) /
    (Nat.card (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) : ℂ)

def IsHecke (K' : Subgroup G) (f : G → ℂ) : Prop :=
  HasCompactSupport f ∧ ∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x

def IsLevel (θ : G →* G) (K K' : Subgroup G) : Prop := IsOpen (K' : Set G) ∧ K' ≤ K ∧ ∀ k ∈ K', θ k ∈ K'

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Pl (E : Type) [Field E] [NumberField E] : Type := HeightOneSpectrum (𝓞 E)

abbrev GLw (n : ℕ) (w : Pl E) : Type := GL (Fin n) (w.adicCompletion E)

def IsSection (S : Set (Pl E)) : Prop :=
  ∀ w : Pl E, ∃! u, u ∈ S ∧ u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))

def cj (w : Pl E) : w.adicCompletion E →+* w.adicCompletion E :=
  if h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) then h.choose else RingHom.id _

def thL (n : ℕ) (w : Pl E) : GLw n w →* GLw n w := if IsSplitAt w then MonoidHom.id _ else thetaGL n (cj w)

def nrmL (n : ℕ) (w : Pl E) (y : GLw n w) : GLw n w := if IsSplitAt w then y else y * thetaGL n (cj w) y

def thE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : GL (Fin n) E →* GL (Fin n) E :=
  thetaGL n (IsCMField.complexConj E).toRingEquiv.toRingHom

def thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : GL (Fin n) (Af E) →* GL (Fin n) (Af E) :=
  thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv)

def ratF (E : Type) [Field E] [NumberField E] (n : ℕ) : GL (Fin n) E →* GL (Fin n) (Af E) :=
  GeneralLinearGroup.map (algebraMap E (Af E))

def locEl (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) : GLw n w :=
  GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (if IsSplitAt w then δ * thE E n δ else δ)

def Ell (E : Type) [Field E] (n : ℕ) : Set E[X] :=
  {P | P.Monic ∧ P.natDegree = n ∧ P.Separable ∧ ∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1}

def kap (P : E[X]) : ℂ :=
  if h : ∃ δ : GL (Fin P.natDegree) E, (δ * thE E _ δ).val.charpoly = P then
    mass (thF E _) (ratF E _).range (ratF E _ h.choose) /
      2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors P) else 0

def chAt {n : ℕ} (lam : DomWeight n) (Q : ℂ[X]) : ℂ :=
  if h : ∃ g : GL (Fin n) ℂ, g.val.charpoly = Q then
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam h.choose) else 0

def chW {n : ℕ} (lam : InfinitePlace E → DomWeight n) (P : E[X]) : ℂ :=
  ∏ v : InfinitePlace E, (starRingEnd ℂ) (chAt (lam v) (P.map v.embedding))

def stTw (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X]) (φ : GLw n w → ℂ) : ℂ :=
  clSum (thL n w) (GlobalTheory.LFun.KGL w n) {y | (nrmL n w y).val.charpoly = Q} 1 φ

def stTw2 (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ) : ℂ :=
  clSum ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂} 1 φ

def UL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := if IsSplitAt w then ⊤ else UJ (cj w) 1

def KL (n : ℕ) (w : Pl E) : Subgroup (UL n w) := (GlobalTheory.LFun.KGL w n).subgroupOf (UL n w)

def kapSign (n : ℕ) (w : Pl E) (Q₁ : (w.adicCompletion E)[X]) (γ : GLw n w) : ℂ :=
  if IsSplitAt w then 1 else
    let V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁))
    (-1) ^ ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E) V₁ i).1 k) * (Module.finBasis (w.adicCompletion E) V₁ j).1 k).det

def kapOrb (n : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (f : UL n w → ℂ) : ℂ :=
  clSum (MonoidHom.id _) (KL n w) {γ | γ.1.val.charpoly = Q₁ * Q₂} (fun γ => kapSign n w Q₁ γ.1) f

structure Term (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type 1 where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  P : ∀ w : Pl E, SmIrr (GLw n w)
  A : ∀ w : Pl E, (P w).V →ₗ[ℂ] (P w).V
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  iso : ∀ w, Nonempty ((P w).ρ.Equiv (locProd h w (σ · w)))
  bij : ∀ w, Function.Bijective (A w)
  split : ∀ w, IsSplitAt w → A w = LinearMap.id
  inter : ∀ w g, A w ∘ₗ (P w).ρ g = (P w).ρ (thL n w g) ∘ₗ A w
  unit : ∀ᶠ w in cofinite, twTr (P w).ρ (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n)
    ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) (A w) = 1

variable {n : ℕ}

abbrev Term.rep (t : Term E n) (w : Pl E) : Representation ℂ (GLw n w) (t.P w).V := (t.P w).ρ

def Term.HasWt (t : Term E n) (lam : InfinitePlace E → DomWeight n) : Prop :=
  ∀ v : InfinitePlace E, ∑ i, t.m i v.embedding = infOfWeight (lam v)

def IsLevelFam {H : Pl E → Type} [∀ w, Group (H w)] [∀ w, TopologicalSpace (H w)] (θ : ∀ w, H w →* H w)
    (K K' : ∀ w : Pl E, Subgroup (H w)) : Prop :=
  (∀ w, IsLevel (θ w) (K w) (K' w)) ∧ ∀ᶠ w in cofinite, K' w = K w

def IsTest {H : Pl E → Type} [∀ w, Group (H w)] [∀ w, TopologicalSpace (H w)] (K K' : ∀ w : Pl E, Subgroup (H w))
    (φ : ∀ w, H w → ℂ) : Prop :=
  (∀ w, IsHecke (K' w) (φ w)) ∧ ∀ᶠ w in cofinite, φ w = (K w : Set (H w)).indicator 1

abbrev atPl (w : Pl E) (P : E[X]) : (w.adicCompletion E)[X] := P.map (algebraMap E (w.adicCompletion E))

def RegAt (n : ℕ) (w : Pl E) (φ : GLw n w → ℂ) : Prop := ∀ y, φ y ≠ 0 → (nrmL n w y).val.charpoly.Separable

def RegAt2 (a b : ℕ) (w : Pl E) (φ : GLw a w × GLw b w → ℂ) : Prop :=
  ∀ y, φ y ≠ 0 → ((nrmL a w y.1).val.charpoly * (nrmL b w y.2).val.charpoly).Separable

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : Pl E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

def spec {ι : Type} [Fintype ι] (S : Set (Pl E)) (t : ι → Term E n) (C : ι → ℂ) (K' : ∀ w : Pl E, Subgroup (GLw n w))
    (φ : ∀ w : Pl E, GLw n w → ℂ) : ℂ :=
  ∑ i, C i * ∏ᶠ w ∈ S, twTr ((t i).rep w) (GlobalTheory.LFun.KGL w n) (K' w) (φ w) ((t i).A w)

def geomRat (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (φ : ∀ w : Pl E, GLw n w → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly ∈ Ell E n then
    mass (thF E n) (ratF E n).range (ratF E n c.rep) * chW lam (c.rep * thE E n c.rep).val.charpoly *
      ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0

def geomSt (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (φ : ∀ w : Pl E, GLw n w → ℂ) : ℂ :=
  ∑ᶠ P ∈ Ell E n, kap P * chW lam P * ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w)

def TraceId (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (geo : Set (Pl E) → (InfinitePlace E → DomWeight n) → (∀ w : Pl E, GLw n w → ℂ) → ℂ) : Prop :=
  ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (GLw n w)),
    IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' →
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → Term E n) (C : ι → ℂ), (∀ i, (t i).HasWt lam) ∧
      ∀ φ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → (∃ w ∈ S, RegAt n w (φ w)) → geo S lam φ = spec S t C K' φ

def STFrat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n, TraceId E n geomRat

def STF : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n, TraceId E n geomSt

def SimpleTwistedTraceFormulaStable : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (K₁ : ∀ w : Pl E, Subgroup (GLw a w))
      (K₂ : ∀ w : Pl E, Subgroup (GLw b w)), IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) K₁ →
    IsLevelFam (thL b) (fun w : Pl E => GlobalTheory.LFun.KGL w b) K₂ →
    ∃ (ι : Type) (_ : Fintype ι) (t₁ : ι → Term E a) (t₂ : ι → Term E b) (C : ι → ℂ),
      (∀ i, (t₁ i).HasWt l₁ ∧ (t₂ i).HasWt l₂) ∧
      ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ,
        IsTest (fun w : Pl E => (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun w : Pl E => (K₁ w).prod (K₂ w)) φ →
        (∃ w ∈ S, RegAt2 a b w (φ w)) →
        (∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
          kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)) =
        ∑ i, C i * ∏ᶠ w ∈ S, twTr (extT ((t₁ i).rep w) ((t₂ i).rep w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
          ((K₁ w).prod (K₂ w)) (φ w) (TensorProduct.map ((t₁ i).A w) ((t₂ i).A w))

def IsCompU (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (σ : SmIrr (UL n w)) : Prop :=
  ∃ p : locU n w →* UL n w, (∀ x, (p x).1 = cLoc w x.1) ∧ IsCompAlong π (locU n w) p σ.ρ

def HasLevel (S : Set (Pl E)) (π : Submodule ℂ (UA E n → ℂ)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Prop :=
  ∃ φ ∈ π, φ ≠ 0 ∧ ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ

def geomU (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  ∑ a ∈ Finset.range (n + 1), ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
    kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)

def USide : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
    ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)) (σ : ι → ∀ w : Pl E, SmIrr (UL n w)),
      (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ HasLevel S (π i) K' ∧
        ∀ w ∈ S, IsCompU (π i) w (σ i w) ∧ fixed (σ i w).ρ (K' w) ≠ ⊥ ∧
          ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed (σ i w).ρ U)) ∧
      (∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → HasLevel S π₀ K' →
        ∃ i, ∀ w ∈ S, IsCompU π₀ w (σ i w)) ∧
      ∀ f, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
        ∑ i, ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = geomU S lam f

def absHalf (w : Pl E) (x : w.adicCompletion E) : ℂ := (Real.sqrt ((qV E w : ℝ) ^ (-ordL x)) : ℝ)

def delta (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (Q₁ Q₂ : (w.adicCompletion E)[X]) : ℂ :=
  let d := ((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree * ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree
  if IsSplitAt w then
    (if h : (-1) ^ (Q₁.natDegree * Q₂.natDegree) * d ≠ 0 then (μ (Units.mk0 _ h) : ℂ) else 0) *
      absHalf w (resultant Q₁ Q₂ ^ 2 / d)
  else (-1) ^ ordL (resultant Q₁ Q₂) * absHalf w (resultant Q₁ Q₂)

def IsCsr (w : Pl E) (Q : (w.adicCompletion E)[X]) : Prop :=
  IsSplitAt w ∨ C (cj w (Q.coeff 0)) * Q = (Q.map (cj w)).reverse

def Match (n a b : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (φ : GLw a w × GLw b w → ℂ) : Prop :=
  ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b →
    (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → stTw2 a b w Q₁ Q₂ φ = delta w μ Q₁ Q₂ * kapOrb n w Q₁ Q₂ f

def HasTransfer (n : ℕ) (w : Pl E) : Prop :=
  ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → ∃ K' ≤ U, IsLevel (MonoidHom.id _) (KL n w) K' ∧
    ∀ a b, a + b = n → ∃ K₁ K₂ φ, IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂ ∧
      IsHecke (K₁.prod K₂) φ ∧ Match n a b w 1 ((K' : Set (UL n w)).indicator 1) φ

def HasBC (π : Submodule ℂ (UA E n → ℂ)) : Prop :=
  ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)) (m : Fin c → (E →+* ℂ) → Multiset ℂ), UnitaryBC.IsBaseChange π h V σ m

def OddInert (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : Pl E, ¬ IsSplitAt w → (2 : 𝓞 E) ∉ w.asIdeal

def BCCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ w, ¬ IsSplitAt w → IsUnramU π w ∨ HasTransfer n w) → HasBC π

def BaseChangeSph : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → OddInert E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ w, ¬ IsSplitAt w → IsUnramU π w) → HasBC π

def TransferInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w → HasTransfer n w

theorem baseChangeSph_of_bcCore : BCCore → BaseChangeSph := fun H E _ _ _ hE _ n hn π hπ hu =>
  H E hE n hn π hπ fun w hw => Or.inl (hu w hw)

theorem oddInert_iff (E : Type) [Field E] [NumberField E] [IsCMField E] :
    OddInert E ↔ ∀ w : Pl E, (2 : 𝓞 E) ∈ w.asIdeal → IsSplitAt w :=
  ⟨fun H w h2 => by_contra fun hs => H w hs h2, fun H w hs h2 => hs (H w h2)⟩

def BCCoreOdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → OddInert E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ w, ¬ IsSplitAt w → IsUnramU π w ∨ HasTransfer n w) → HasBC π

theorem bcCoreOdd_of_bcCore : BCCore → BCCoreOdd := fun H E _ _ _ hE _ => H E hE

example (H : BCCore) (T : TransferInert) (E : Type) [Field E] [NumberField E] [IsCMField E] (hE : Unr E) (n : ℕ)
    (hn : 1 ≤ n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) : HasBC π :=
  H E hE n hn π hπ fun w hw => Or.inr (T E hE n w hw)

end GlobalTheory.BCT
