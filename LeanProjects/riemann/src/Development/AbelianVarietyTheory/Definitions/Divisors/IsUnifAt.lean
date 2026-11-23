import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def toSub {G : Type} [Group G] (H : Subgroup G) (g : G) : H := if h : g ∈ H then ⟨g, h⟩ else 1

def trOn {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ M, L v ∈ M then LinearMap.trace ℂ M (L.restrict h) else 0

def hint {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) : ℂ :=
  (((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out

structure IsoDat (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type 1 where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  P : ∀ w : Pl E, SmIrr (GLw n w)
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  iso : ∀ w, Nonempty ((P w).ρ.Equiv (locProd h w (σ · w)))

def IsoDat.HasWt (D : IsoDat E n) (lam : InfinitePlace E → DomWeight n) : Prop :=
  ∀ v : InfinitePlace E, ∑ i, D.m i v.embedding = infOfWeight (lam v)

def IsoDat.CompAt (D : IsoDat E n) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) : Prop :=
  IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (D.P w).ρ

def IsMu (μ : HChar E) (e : InfinitePlace E → ℤ) : Prop :=
  μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
    (∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
    ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v

def pairRep {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (σ₁ : SmIrr (GLw a w))
    (σ₂ : SmIrr (GLw b w)) :=
  GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) (GlobalTheory.SmGL.extTensor (twRep σ₁.ρ ((μ ^ b).comp GeneralLinearGroup.det))
    (twRep σ₂.ρ ((μ ^ a).comp GeneralLinearGroup.det)))

structure PairTerm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E) : Type 1 where
  a : ℕ
  ha : a ≤ n
  t₁ : Term E a
  t₂ : Term E (n - a)
  D : IsoDat E n
  link : ∀ w, Nonempty ((D.P w).ρ.Equiv (pairRep (Nat.add_sub_cancel' ha) w (μ.loc w) (t₁.P w) (t₂.P w)))

def PairTerm.fac {μ : HChar E} (T : PairTerm E n μ) (w : Pl E) (K' : Subgroup (UL n w)) (f : UL n w → ℂ)
    (K₁ : ∀ a, Subgroup (GLw a w)) (K₂ : ∀ a, Subgroup (GLw (n - a) w))
    (φ : ∀ a, GLw a w × GLw (n - a) w → ℂ) : ℂ :=
  if IsSplitAt w then twTr ((T.D.P w).ρ.comp (UL n w).subtype) (KL n w) K' f LinearMap.id
  else twTr (extT (T.t₁.rep w) (T.t₂.rep w)) ((GlobalTheory.LFun.KGL w T.a).prod (GlobalTheory.LFun.KGL w (n - T.a)))
    ((K₁ T.a).prod (K₂ T.a)) (φ T.a) (TensorProduct.map (T.t₁.A w) (T.t₂.A w))

def MainId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
      (K₁ : ∀ (w : Pl E) a, Subgroup (GLw a w)) (K₂ : ∀ (w : Pl E) a, Subgroup (GLw (n - a) w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ a ≤ n, IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) (K₁ · a) ∧
      IsLevelFam (thL (n - a)) (fun w : Pl E => GlobalTheory.LFun.KGL w (n - a)) (K₂ · a)) →
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → PairTerm E n μ) (C : ι → ℂ), (∀ j, (T j).D.HasWt lam) ∧
      ∀ (f : ∀ w : Pl E, UL n w → ℂ) (φ : ∀ (w : Pl E) a, GLw a w × GLw (n - a) w → ℂ), IsTest (KL n) K' f →
        (∀ a ≤ n, (∀ w, ¬ IsSplitAt w → IsHecke ((K₁ w a).prod (K₂ w a)) (φ w a) ∧ Match n a (n - a) w 1 (f w) (φ w a)) ∧
          ∀ᶠ w in cofinite, ¬ IsSplitAt w →
            φ w a = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) : Subgroup _) : Set _).indicator 1) →
        (∃ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) ∧
          (¬ IsSplitAt w → ∀ a ≤ n, RegAt2 a (n - a) w (φ w a))) →
        geomU S lam f = ∑ j, C j * ∏ᶠ w ∈ S, (T j).fac w (K' w) (f w) (K₁ w) (K₂ w) (φ w)

def blk {a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw n w :=
  let M := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)
  if hM : IsUnit M then hM.unit else 1

def intMat (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
  Subgroup.closure {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}

def ct {a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => avg fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)

def ctMu {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    ct h w (fun y => f (toSub _ y)) m

def iwGL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

def tdiag {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : GLw n w :=
  GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) fun i => ϖ ^ a i

def dcos (n : ℕ) (w : Pl E) (t : GLw n w) : GLw n w → ℂ :=
  fun y => if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

def IsUnifAt {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) : Prop := ordL (ϖ : w.adicCompletion E) = 1 ∧ cj w ϖ = ϖ

def IsWitt (n : ℕ) (w : Pl E) (b : GLw n w) : Prop :=
  b ∈ GlobalTheory.LFun.KGL w n ∧ (b.val.map (cj w))ᵀ * b.val = antiJ (w.adicCompletion E) n

def iwU (n : ℕ) (w : Pl E) (b : GLw n w) : Subgroup (UL n w) :=
  ((iwGL n w).map (MulAut.conj b).toMonoidHom).subgroupOf (UL n w)

def wexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ else if h' : n - 1 - i.val < n / 2 then -l ⟨_, h'⟩ else 0

def sexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ - l ⟨i, h⟩ / 2 else if h' : n - 1 - i.val < n / 2 then -(l ⟨_, h'⟩ / 2) else 0

def Cone {m : ℕ} (l : Fin m → ℤ) : Prop := (∀ i j : Fin m, (j : ℕ) = i + 1 → 2 ≤ l i - l j) ∧ ∀ i, 2 ≤ l i

def fU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) : UL n w → ℂ :=
  fun γ => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 then 1 else 0

def qh (w : Pl E) : ℂ := (Real.sqrt (qV E w : ℝ) : ℝ)

def dlt (n : ℕ) (w : Pl E) (l : Fin (n / 2) → ℤ) : ℂ := qh w ^ (∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)

def vRes (n a : ℕ) (l : Fin (n / 2) → ℤ) (s : Finset (Fin (n / 2))) : ℤ :=
  -2 * (∑ i ∈ s, ∑ j ∈ sᶜ, max (l i) (l j)) -
    (if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, l j else ∑ j ∈ s, l j) else 0)

def phiU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (a : ℕ)
    (y : GLw a w × GLw (n - a) w) : ℂ :=
  ∑ s : Finset (Fin (n / 2)), if h : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 then
    (-qh w) ^ (-vRes n a l s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ *
      ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) * ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) *
      dcos a w (tdiag ϖ (sexp a (l ∘ s.orderEmbOfFin h.1))) y.1 *
      dcos (n - a) w (tdiag ϖ (sexp (n - a) (l ∘ sᶜ.orderEmbOfFin h.2.1))) y.2 else 0

def HasVals {w : Pl E} (Q : (w.adicCompletion E)[X]) (a : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → w.adicCompletion E, Q = ∏ i, (X - C (u i)) ∧ ∀ i, u i ≠ 0 ∧ ordL (u i) = a i

def pw {m : ℕ} (y : Fin m → ℂˣ) (l : Fin m → ℤ) : ℂ := ∏ i, ((y i ^ l i : ℂˣ) : ℂ)

def pm {m : ℕ} (y : Fin m → ℂˣ) : Multiset ℂˣ := Finset.univ.val.map y + Finset.univ.val.map fun i => (y i)⁻¹

def UnrSupp {w : Pl E} (σ : SmIrr (GLw n w)) (B : Multiset ℂˣ) : Prop :=
  ∃ χ : Fin n → ℂˣ, Finset.univ.val.map χ = B ∧
    GlobalTheory.SmGL.IsSubquotient σ.ρ (GlobalTheory.SmGL.prinSeries fun i => GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ i))

def SatUL {w : Pl E} (b : GLw n w) (ϖ : w.adicCompletion E) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (p : UL n w ≃* GU (cj w) n) (σ' : SmIrr (GU (cj w) n)), (∀ x, (p x).1 = b⁻¹ * x.1 * b) ∧
    GlobalTheory.LFun.HasSatU ϖ q σ'.ρ α ∧ Nonempty (σ.ρ.Equiv (σ'.ρ.comp p.toMonoidHom))

def UE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) E) :=
  UJ (IsCMField.complexConj E).toRingEquiv.toRingHom 1

def finPt (γ : UE E n) : finU E n := toSub _ (toSub _ (finGL E n (ratF E n γ.1)))

def ratFinU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (finU E n) :=
  (((UE E n).map ((finGL E n).comp (ratF E n))).comap (UA E n).subtype).comap (finU E n).subtype

def locPt (w : Pl E) (γ : UE E n) : UL n w := toSub _ (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)

def globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (finU E n) :=
  ⨅ w ∈ S, ((K' w).map (UL n w).subtype).comap ((cLoc w).comp (finU E n).subtype)

def globFn (S : Set (Pl E)) (f : ∀ w : Pl E, UL n w → ℂ) (x : finU E n) : ℂ := ∏ᶠ w ∈ S, f w (toSub _ (cLoc w x.1))

def RF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Representation ℂ (finU E n) (UA E n → ℂ) :=
  (RU E n).comp (finU E n).subtype

def forms (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (UA E n → ℂ) :=
  ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)),
    π ⊓ fixed (RF E n) (globLev S K')

def hop (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) :
    (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
  levOp (RF E n) (globLev S (KL n)) (globLev S K') (globFn S f) LinearMap.id

def dimW (lam : InfinitePlace E → DomWeight n) : ℂ :=
  ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (lam v) 1)

def geomURat (lam : InfinitePlace E → DomWeight n) (orb : UE E n → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then
    mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0

def nfac {k : Type} [Field k] (P : k[X]) : ℕ := Multiset.card (UniqueFactorizationMonoid.normalizedFactors P)

end GlobalTheory.BCT
