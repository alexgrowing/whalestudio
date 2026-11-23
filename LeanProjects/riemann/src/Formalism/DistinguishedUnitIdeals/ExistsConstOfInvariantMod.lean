import Mathlib
import Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.ExponentWindows.G

open TensorProduct

structure Level (LL Ks Δ : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] where
  σ : Ks ≃ₐ[LL] Ks
  u : LLˣ
  τ : Δ → Ks ≃ₐ[LL] Ks
  a : Δ → LLˣ

abbrev Amb (LL Ks D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D]
    [Module LL D] : Type :=
  HahnModule ℤ Ks (Ks ⊗[LL] D)

section
variable {LL Ks Δ D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

def cf (f : Amb LL Ks D) (i : ℤ) : Ks ⊗[LL] D := ((HahnModule.of Ks).symm f).coeff i

def tD (D : Type) [AddCommGroup D] [Module LL D] (τ : Ks ≃ₐ[LL] Ks) :
    (Ks ⊗[LL] D) →ₗ[LL] (Ks ⊗[LL] D) :=
  LinearMap.rTensor D τ.toLinearMap

def grd (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : Amb LL Ks D →+ Amb LL Ks D where
  toFun f := HahnModule.of Ks
    { coeff := fun i => ((a ^ i : LLˣ) : LL) • tD D τ (cf f i)
      isPWO_support' := ((HahnModule.of Ks).symm f).isPWO_support.mono (by
        intro i hi h0
        exact hi (by simp only [cf, h0, map_zero, smul_zero])) }
  map_zero' := by
    apply HahnModule.ext
    funext i
    simp [cf]
  map_add' f g := by
    apply HahnModule.ext
    funext i
    simp [cf]

def grdB (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x : HahnSeries ℤ Ks) : HahnSeries ℤ Ks where
  coeff i := algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ (x.coeff i)
  isPWO_support' := x.isPWO_support.mono (by
    intro i hi h0
    exact hi (by simp only [h0, map_zero, mul_zero]))

def Level.γ (Lev : Level LL Ks Δ) : Amb LL Ks D →+ Amb LL Ks D := grd Lev.σ Lev.u

def Level.δ (Lev : Level LL Ks Δ) (j : Δ) : Amb LL Ks D →+ Amb LL Ks D := grd (Lev.τ j) (Lev.a j)

def Level.Inv (Lev : Level LL Ks Δ) (f : Amb LL Ks D) : Prop := ∀ j, Lev.δ j f = f

def cstD (Ks : Type) [CommRing Ks] [Algebra LL Ks] (d : D) : Amb LL Ks D :=
  HahnModule.of Ks (HahnSeries.single 0 ((1 : Ks) ⊗ₜ[LL] d))

def tp (Ks : Type) [CommRing Ks] (g : ℤ) : HahnSeries ℤ Ks := HahnSeries.single g 1

def Xi (Ks : Type) [CommRing Ks] [Algebra LL Ks] (X : ℤ → Submodule LL D) :
    AddSubgroup (Amb LL Ks D) where
  carrier := {f | ∀ i, cf f i ∈ (X i).baseChange Ks}
  zero_mem' := fun i => by simp [cf]
  add_mem' := fun {f g} hf hg i => by
    have : cf (f + g) i = cf f i + cf g i := by simp [cf]
    rw [this]
    exact Submodule.add_mem _ (hf i) (hg i)
  neg_mem' := fun {f} hf i => by
    have : cf (-f) i = -cf f i := rfl
    rw [this]
    exact Submodule.neg_mem _ (hf i)

def IsGr (X : ℤ → Submodule LL D) : Prop :=
  Monotone X ∧ (∃ lo : ℤ, X lo = ⊥) ∧ (∃ hi : ℤ, X hi = ⊤)

def Level.pAct (Lev : Level LL Ks Δ) (P : Polynomial LL) (f : Amb LL Ks D) : Amb LL Ks D :=
  P.sum fun k a => algebraMap LL Ks a • (⇑(Lev.γ (D := D)))^[k] f

end

def PPoly {R : Type} [CommRing R] (u : Rˣ) (ℓ E : ℕ) (JS : Finset ℤ) : Polynomial R :=
  (∏ i ∈ JS.erase 0, (Polynomial.X ^ (ℓ ^ E) -
      Polynomial.C ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Rˣ) : R))) *
    ∑ k ∈ Finset.range (ℓ ^ E), Polynomial.X ^ k

section
variable {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]

def NbK (kind : Kind) (b : ℤ) (U : Submodule LL D) : ℤ → Submodule LL D :=
  match kind with
  | Kind.thin => NbThin
  | Kind.up => NbUp b U
  | Kind.down => NbDown b U

def UOf (kind : Kind) (b η : ℤ) (Fil : ℤ → Submodule LL D) : Submodule LL D :=
  match kind with
  | Kind.thin => ⊤
  | Kind.up => Fil b
  | Kind.down => Fil (-η)

def Jumps (kind : Kind) (G S η b : ℤ) (Fil : ℤ → Submodule LL D) : Prop :=
  match kind with
  | Kind.thin => ∀ u, Fil u ≠ Fil (u + 1) → -G ≤ u ∧ u ≤ G
  | Kind.up => ∀ u, Fil u ≠ Fil (u + 1) → (b ≤ u ∧ u ≤ b + S) ∨ (-η ≤ u ∧ u ≤ η)
  | Kind.down => ∀ u, Fil u ≠ Fil (u + 1) → (-b - S ≤ u ∧ u ≤ -b) ∨ (-η ≤ u ∧ u ≤ η)

end

def Win2 (kind : Kind) (g b i : ℤ) : Prop :=
  match kind with
  | Kind.thin => -g ≤ i ∧ i ≤ -1
  | Kind.up => (-b - g ≤ i ∧ i ≤ -b - 1) ∨ (-g ≤ i ∧ i ≤ -1)
  | Kind.down => (-g ≤ i ∧ i ≤ -1) ∨ (b - g ≤ i ∧ i ≤ b - 1)

section
variable {LL Ks Δ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

def Level.FiniteOrderFixed (Lev : Level LL Ks Δ) (ℓ s : ℕ) : Prop :=
  (∀ x : Ks, (⇑Lev.σ)^[ℓ ^ s] x = x) ∧
  ∀ x : Ks, Lev.σ x = x → (∀ j, Lev.τ j x = x) → ∃ c : LL, algebraMap LL Ks c = x

def Level.PhiGammaCommute (Lev : Level LL Ks Δ) : Prop := ∀ j x, Lev.σ (Lev.τ j x) = Lev.τ j (Lev.σ x)

def Level.FactV (Lev : Level LL Ks Δ) : Prop := ∀ m : ℤ, m ≠ 0 → Lev.u ^ m ≠ 1

end

def XiModule : Prop :=
  ∀ (LL Ks D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (X : ℤ → Submodule LL D), Monotone X → ∀ (a : PowerSeries Ks) (f : Amb LL Ks D),
      f ∈ Xi Ks X → HahnSeries.ofPowerSeries ℤ Ks a • f ∈ Xi Ks X

def XiShift : Prop :=
  ∀ (LL Ks D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (X : ℤ → Submodule LL D) (g : ℤ) (f : Amb LL Ks D),
      tp Ks g • f ∈ Xi Ks X ↔ f ∈ Xi Ks (fun i => X (i + g))

def GrdSemi : Prop :=
  ∀ (LL Ks D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x : HahnSeries ℤ Ks) (f : Amb LL Ks D),
      grd τ a (x • f) = grdB τ a x • grd τ a f

def XiGam : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ),
    (∀ (X : ℤ → Submodule LL D) (f : Amb LL Ks D), f ∈ Xi Ks X → Lev.γ f ∈ Xi Ks X) ∧
    (∀ d : D, Lev.γ (cstD Ks d) = cstD Ks d) ∧ (∀ d : D, Lev.Inv (cstD Ks d))

def KillingPolynomialFinite : Prop :=
  ∀ (LL D : Type) [Field LL] [AddCommGroup D] [Module LL D] (X X' : ℤ → Submodule LL D),
    IsGr X → IsGr X' → {i : ℤ | X i ≠ X' i}.Finite

def CoeffIterateGamma : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (ℓ s E : ℕ), Lev.FiniteOrderFixed ℓ s → s ≤ E → ∀ (f : Amb LL Ks D) (i : ℤ),
      cf ((⇑(Lev.γ (D := D)))^[ℓ ^ E] f) i =
        ((Lev.u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : LLˣ) : LL) • cf f i

def K2ii : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CharZero LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D]
    [Module LL D] (Lev : Level LL Ks Δ) (ℓ s : ℕ), 0 < ℓ → Lev.FiniteOrderFixed ℓ s → Lev.FactV →
    ∀ (I : Finset ℤ) (X X' : ℤ → Submodule LL D), (∀ i, X i ≠ X' i → i ∈ I) →
      (∏ i ∈ I, ((Polynomial.X : Polynomial LL) ^ (ℓ ^ s) -
        Polynomial.C ((Lev.u ^ (i * ((ℓ ^ s : ℕ) : ℤ)) : LLˣ) : LL))).Separable ∧
      ∀ f ∈ Xi Ks X, Lev.pAct (∏ i ∈ I, ((Polynomial.X : Polynomial LL) ^ (ℓ ^ s) -
        Polynomial.C ((Lev.u ^ (i * ((ℓ ^ s : ℕ) : ℤ)) : LLˣ) : LL))) f ∈ Xi Ks X'

def K2iii : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (ℓ s : ℕ), 0 < ℓ → Lev.FiniteOrderFixed ℓ s → Lev.FactV →
    ∀ (X X' : ℤ → Submodule LL D), (∀ i, X' i ≤ X i) → ∀ f ∈ Xi Ks X,
      (∀ j, Lev.δ j f - f ∈ Xi Ks X') → Lev.γ f - f ∈ Xi Ks X' →
      ∃ d ∈ X 0, f - cstD Ks d ∈ Xi Ks X'

def KillingPolyConst : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CharZero LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D]
    [Module LL D] (Lev : Level LL Ks Δ) (ℓ s E : ℕ), 0 < ℓ → Lev.FiniteOrderFixed ℓ s → Lev.PhiGammaCommute → s ≤ E →
    ∀ (JS : Finset ℤ) (X X' : ℤ → Submodule LL D), (∀ i, X i ≠ X' i → i ∈ JS) →
    ∀ f ∈ Xi Ks X,
      (Lev.Inv f → ∃ d ∈ X 0,
        (∑ k ∈ Finset.range (ℓ ^ E), (tD D Lev.σ ^ k) (cf f 0)) =
          ((ℓ ^ E : ℕ) : LL) • ((1 : Ks) ⊗ₜ[LL] d) ∧
        Lev.pAct (PPoly Lev.u ℓ E JS) f - cstD Ks ((PPoly Lev.u ℓ E JS).eval 1 • d) ∈ Xi Ks X') ∧
      (X 0 = X' 0 → Lev.pAct (PPoly Lev.u ℓ E JS) f ∈ Xi Ks X')

def PPeval : Prop :=
  ∀ (R : Type) [CommRing R] (u : Rˣ) (ℓ E : ℕ) (JS : Finset ℤ),
    (PPoly u ℓ E JS).eval 1 =
      ((ℓ ^ E : ℕ) : R) * ∏ i ∈ JS.erase 0, (1 - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Rˣ) : R))

def PActConst : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (P : Polynomial LL) (d : D),
      Lev.pAct P (cstD Ks d) = cstD Ks (P.eval 1 • d)

def ExistsConstOfInvariantMod : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (ℓ s : ℕ), 0 < ℓ → Lev.FiniteOrderFixed ℓ s → Lev.FactV →
    ∀ (Fil : ℤ → Submodule LL D) (f : Amb LL Ks D),
      (∀ j, Lev.δ j f - f ∈ Xi Ks (fun i => Fil (-i))) →
      Lev.γ f - f ∈ Xi Ks (fun i => Fil (-i)) → ∃ d : D, f - cstD Ks d ∈ Xi Ks (fun i => Fil (-i))

def KillingPolyShape : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (ℓ s E : ℕ), Lev.FiniteOrderFixed ℓ s → s ≤ E →
    ∀ (kind : Kind) (g b : ℤ) (U : Submodule LL D) (JS : Finset ℤ), 0 ≤ g →
    (kind ≠ Kind.thin → g < b) →
    (∀ i, Win2 kind g b i → i ∈ JS) →
    ∀ (f : Amb LL Ks D) (d : D), tp Ks g • (f - cstD Ks d) ∈ Xi Ks (NbK kind b U) →
      Lev.pAct (PPoly Lev.u ℓ E JS) f - cstD Ks ((PPoly Lev.u ℓ E JS).eval 1 • d) ∈
        Xi Ks (NbK kind b U)

def KillingPolyFiltration : Prop :=
  ∀ (LL Ks Δ D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Lev : Level LL Ks Δ) (ℓ s E : ℕ), Lev.FiniteOrderFixed ℓ s → Lev.PhiGammaCommute → s ≤ E →
    ∀ (g : ℤ) (Fil : ℤ → Submodule LL D) (JS : Finset ℤ), 0 ≤ g →
    (∀ u z : ℤ, Fil u ≠ Fil (u + 1) → 1 ≤ z → z ≤ g → -u - z ∈ JS) →
    ∀ (f : Amb LL Ks D) (d : D), Lev.Inv f →
      tp Ks g • (f - cstD Ks d) ∈ Xi Ks (fun i => Fil (-i)) →
      ∃ d' : D, Lev.pAct (PPoly Lev.u ℓ E JS) f - cstD Ks d' ∈ Xi Ks (fun i => Fil (-i))

def RDmod : Prop :=
  Rounding →
  ∀ (LL Ks D : Type) [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (Fil : ℤ → Submodule LL D) (kind : Kind) (G S η g b : ℤ), IsFilt Fil → 0 ≤ G → 0 ≤ S →
    0 ≤ η → G ≤ g → S ≤ g → η ≤ g → (kind ≠ Kind.thin → g < b) → Jumps kind G S η b Fil →
    (∀ f ∈ Xi Ks (NbK kind b (UOf kind b η Fil)), tp Ks g • f ∈ Xi Ks (fun i => Fil (-i))) ∧
    (∀ f ∈ Xi Ks (fun i => Fil (-i)), tp Ks g • f ∈ Xi Ks (NbK kind b (UOf kind b η Fil)))

def GradedModel : Prop :=
  XiModule ∧ XiShift ∧ GrdSemi ∧ XiGam ∧ KillingPolynomialFinite ∧ CoeffIterateGamma ∧ K2ii ∧ K2iii ∧ KillingPolyConst ∧ PPeval ∧ PActConst ∧
    ExistsConstOfInvariantMod ∧ KillingPolyShape ∧ KillingPolyFiltration ∧ RDmod

section
variable {O : Type} [CommRing O] {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}

structure LevelModel (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] where
  lev : ∀ s, Level LL (Ks s) Δ
  ρ : ∀ s, PowerSeries O →+* PowerSeries (Ks s)
  ρ_C : ∀ s (a : O), ρ s (PowerSeries.C a) =
    PowerSeries.C (algebraMap LL (Ks s) (algebraMap O LL a))
  pr : ∀ s, S.Lv →+ Amb LL (Ks s) D
  pr_smul : ∀ s (a : PowerSeries O) (e : S.Lv),
    pr s (a • e) = HahnSeries.ofPowerSeries ℤ (Ks s) (ρ s a) • pr s e
  pr_γ : ∀ s < ell, ∀ s' < ell, ∀ e : S.Lv, pr s' (S.gE s e) = (lev s').γ (pr s' e)
  pr_inv : ∀ s < ell, ∀ e : S.Lv, (lev s).Inv (pr s e)
  pr_inj : ∀ e e' : S.Lv, (∀ s < ell, pr s e = pr s e') → e = e'
  Fil : ℕ → ℤ → Submodule LL D
  kind : ℕ → Kind
  b : ℕ → ℕ
  η : ℕ
  mem_Nl : ∀ s < ell, ∀ e : S.Lv, e ∈ S.Nl s ↔ pr s e ∈ Xi (Ks s) (fun i => Fil s (-i))
  mem_Nb : ∀ s < ell, ∀ e : S.Lv, e ∈ S.Nb s ↔
    pr s e ∈ Xi (Ks s) (NbK (kind s) (b s) (UOf (kind s) (b s) η (Fil s)))
  mem_Dc : ∀ s < ell, ∀ e : S.Lv, e ∈ S.Dc s ↔ ∃ d : D, ∀ s' < ell, pr s' e = cstD (Ks s') d
  const : ∀ d : D, ∃ e : S.Lv, ∀ s' < ell, pr s' e = cstD (Ks s') d

variable {S : E.LevelData L c ell Λ r} {LL : Type} [Field LL] [Algebra O LL]
  {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
  [AddCommGroup D] [Module LL D]

def LevelModel.K1b (R : LevelModel S LL Ks Δ D) : Prop :=
  ∀ s < ell, ∃ ε : (PowerSeries (Ks s))ˣ, R.ρ s (B.p s) = (ε : PowerSeries (Ks s)) * PowerSeries.X

def LevelModel.HasU (R : LevelModel S LL Ks Δ D) (u : Oˣ) : Prop :=
  ∀ s < ell, ((R.lev s).u : LL) = algebraMap O LL (u : O)

end

def RDOf : Prop :=
  Rounding →
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (G Sz g : ℕ),
    R.K1b → G ≤ g → Sz ≤ g → R.η ≤ g →
    (∀ s < ell, IsFilt (R.Fil s) ∧ (R.kind s ≠ Kind.thin → g < R.b s) ∧
      Jumps (R.kind s) G Sz R.η (R.b s) (R.Fil s)) →
    S.RD g

def KillingPolynomialDegreeBound : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (ℓ : ℕ), 0 < ℓ →
    (∀ s < ell, (R.lev s).FiniteOrderFixed ℓ s ∧ (R.lev s).FactV) → S.K2iii

def KillingPolynomialValuationBound : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (u : Oˣ) (ℓ E g : ℕ) (JS : Finset ℤ),
    R.K1b → R.HasU u → ell ≤ E + 1 → (∀ s < ell, (R.lev s).FiniteOrderFixed ℓ s) →
    (∀ s < ell, (R.kind s ≠ Kind.thin → g < R.b s) ∧
      ∀ i, Win2 (R.kind s) g (R.b s) i → i ∈ JS) →
    S.K3a2 g (PPoly u ℓ E JS)

def KillingPolynomialLeadingUnit : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (u : Oˣ) (ℓ E g : ℕ) (JS : Finset ℤ),
    R.K1b → R.HasU u → ell ≤ E + 1 → (∀ s < ell, (R.lev s).FiniteOrderFixed ℓ s ∧ (R.lev s).PhiGammaCommute) →
    (∀ s < ell, Antitone (R.Fil s)) →
    (∀ s < ell, ∀ v z : ℤ, R.Fil s v ≠ R.Fil s (v + 1) → 1 ≤ z → z ≤ g → -v - z ∈ JS) →
    S.K3a4 g (PPoly u ℓ E JS)

def DcFixOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (_R : LevelModel S LL Ks Δ D), S.DcFix

def LevelHypsOf : Prop := RDOf ∧ KillingPolynomialDegreeBound ∧ KillingPolynomialValuationBound ∧ KillingPolynomialLeadingUnit ∧ DcFixOf

end Formalism.ExponentWindows.G
