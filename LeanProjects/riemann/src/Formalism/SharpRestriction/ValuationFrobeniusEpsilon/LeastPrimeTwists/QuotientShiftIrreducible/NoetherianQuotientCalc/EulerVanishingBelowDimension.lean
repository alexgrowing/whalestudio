import Mathlib

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

abbrev Deg (k : ℕ) : Type := Fin k → ℤ

def e {k : ℕ} (i : Fin k) : Deg k := Pi.single i 1

structure GMod (B R : Type) [CommRing B] [CommRing R] [Algebra B R] (k : ℕ) where
  M : Type
  [acg : AddCommGroup M]
  [modR : Module R M]
  [modB : Module B M]
  [tow : IsScalarTower B R M]
  gr : Deg k → Submodule B M

attribute [instance] GMod.acg GMod.modR GMod.modB GMod.tow

section Defs

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

namespace GMod

def sub (F : GMod B R k) (N : Submodule R F.M) : GMod B R k where
  M := N
  gr m := (F.gr m).comap (N.subtype.restrictScalars B)

def quo (F : GMod B R k) (N : Submodule R F.M) : GMod B R k where
  M := F.M ⧸ N
  gr m := (F.gr m).map (N.mkQ.restrictScalars B)

def shift (F : GMod B R k) (d : Deg k) : GMod B R k where
  M := F.M
  gr m := F.gr (m - d)

def quot (F : GMod B R k) (s : R) : GMod B R k := F.quo (LinearMap.range (LinearMap.lsmul R F.M s))

def ann (F : GMod B R k) (s : R) (d : Deg k) : GMod B R k :=
  (F.sub (LinearMap.ker (LinearMap.lsmul R F.M s))).shift d

def Ann (F : GMod B R k) : Ideal R := Module.annihilator R F.M

def IsHomSub (F : GMod B R k) (N : Submodule R F.M) : Prop :=
  N = Submodule.span R {x | x ∈ N ∧ ∃ m, x ∈ F.gr m}

end GMod

structure SES (F' F F'' : GMod B R k) where
  f : F'.M →ₗ[R] F.M
  g : F.M →ₗ[R] F''.M
  inj : Function.Injective f
  surj : Function.Surjective g
  exact : Function.Exact f g
  f_gr : ∀ m, F'.gr m = (F.gr m).comap (f.restrictScalars B)
  g_gr : ∀ m, F''.gr m = (F.gr m).map (g.restrictScalars B)

structure GIso (F G : GMod B R k) where
  e : F.M ≃ₗ[R] G.M
  map_gr : ∀ m, (F.gr m).map (e.toLinearMap.restrictScalars B) = G.gr m

def chi : List (Deg k × R) → GMod B R k → Deg k → ℤ
  | [], F, m => ((Module.length B (F.gr m)).toNat : ℤ)
  | (d, s) :: ts, F, m => chi ts (F.quot s) m - chi ts (F.ann s d) m

def secs (ts : List (Deg k × R)) : Ideal R := Ideal.span {s | ∃ d, (d, s) ∈ ts}

variable (𝒜 : Deg k → Submodule B R)

def GMod.self : GMod B R k where
  M := R
  gr := 𝒜

def Irr : Ideal R := ∏ i, Ideal.span (𝒜 (e i) : Set R)

structure Std [IsLocalRing B] : Prop where
  noeth : IsNoetherianRing B
  nonneg : ∀ m, ¬ (0 ≤ m) → 𝒜 m = ⊥
  zero : 𝒜 0 = LinearMap.range (Algebra.linearMap B R)
  fg : ∀ i, (𝒜 (e i)).FG
  gen : ∀ m i, 0 ≤ m → 𝒜 (m + e i) = 𝒜 m * 𝒜 (e i)

structure GMod.IsGr (F : GMod B R k) : Prop where
  smul_mem : ∀ {d m : Deg k} {a : R} {x : F.M}, a ∈ 𝒜 d → x ∈ F.gr m → a • x ∈ F.gr (d + m)
  internal : DirectSum.IsInternal F.gr
  fin : Module.Finite R F.M

def Valid (ts : List (Deg k × R)) : Prop := ∀ p ∈ ts, 0 ≤ p.1 ∧ p.2 ∈ 𝒜 p.1

def admitted [IsLocalRing B] (ts : List (Deg k × R)) (J : Ideal R) : Prop :=
  ∃ N : ℕ, ((maximalIdeal B).map (algebraMap B R) * Irr 𝒜) ^ N ≤ J ⊔ secs ts

variable [GradedAlgebra 𝒜]

structure IsRel (𝔮 : Ideal R) : Prop where
  prime : 𝔮.IsPrime
  hom : 𝔮.IsHomogeneous 𝒜
  rel : ¬ Irr 𝒜 ≤ 𝔮

def DimLT : ℕ → Ideal R → Prop
  | 0, J => ∀ 𝔮, IsRel 𝒜 𝔮 → ¬ J ≤ 𝔮
  | p + 1, J => ∀ 𝔮, IsRel 𝒜 𝔮 → J ≤ 𝔮 → ∀ d σ, σ ∈ 𝒜 d → σ ∉ 𝔮 →
      DimLT p (𝔮 ⊔ Ideal.span {σ})

end Defs

section Rules

structure HidaSetting (k : ℕ) where
  B : Type
  R : Type
  [crB : CommRing B]
  [crR : CommRing R]
  [alg : Algebra B R]
  [loc : IsLocalRing B]
  𝒜 : Deg k → Submodule B R
  [gra : GradedAlgebra 𝒜]
  std : Std 𝒜

attribute [instance] HidaSetting.crB HidaSetting.crR HidaSetting.alg HidaSetting.loc HidaSetting.gra

variable {k : ℕ}

abbrev HidaSetting.Mod (X : HidaSetting k) : Type 1 := GMod X.B X.R k

def RuleGr : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 →
    (∀ N, F.IsHomSub N → (F.sub N).IsGr X.𝒜 ∧ (F.quo N).IsGr X.𝒜) ∧
    (∀ d, (F.shift d).IsGr X.𝒜) ∧
    (∀ d s, s ∈ X.𝒜 d → (F.quot s).IsGr X.𝒜 ∧ (F.ann s d).IsGr X.𝒜)

def RuleFin : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 →
    (∀ m, Module.Finite X.B (F.gr m)) ∧
    (admitted X.𝒜 [] F.Ann → ∀ᶠ m in atTop, Module.length X.B (F.gr m) ≠ ⊤)

def RuleIrr : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → (∃ N : ℕ, Irr X.𝒜 ^ N ≤ F.Ann) →
    ∀ᶠ m in atTop, F.gr m = ⊥

def RuleShift : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d m : Deg k),
    chi ts (F.shift d) m = chi ts F (m - d)

def RuleIso : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F G : X.Mod), GIso F G →
    ∀ m, chi ts F m = chi ts G m

def EulerAdditivityExactSequence : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F' F F'' : X.Mod), Valid X.𝒜 ts →
    F'.IsGr X.𝒜 → F.IsGr X.𝒜 → F''.IsGr X.𝒜 → SES F' F F'' → admitted X.𝒜 ts F.Ann →
    ∀ᶠ m in atTop, chi ts F m = chi ts F' m + chi ts F'' m

def EulerIndependenceOfOrder : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts ts' : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts →
    ts.Perm ts' → F.IsGr X.𝒜 → admitted X.𝒜 ts F.Ann → ∀ᶠ m in atTop, chi ts F m = chi ts' F m

def RuleDev : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 →
    ∃ (t : ℕ) (N : ℕ → Submodule X.R F.M) (𝔮 : ℕ → Ideal X.R) (d : ℕ → Deg k),
      N 0 = ⊥ ∧ N t = ⊤ ∧ (∀ i, F.IsHomSub (N i)) ∧ (∀ i, N i ≤ N (i + 1)) ∧
      ∀ i < t, (𝔮 i).IsPrime ∧ (𝔮 i).IsHomogeneous X.𝒜 ∧ F.Ann ≤ 𝔮 i ∧
        Nonempty (SES (F.sub (N i)) (F.sub (N (i + 1))) (((GMod.self X.𝒜).quo (𝔮 i)).shift (d i)))

def EulerVanishingBelowDimension : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 ts F.Ann → DimLT X.𝒜 ts.length F.Ann → ∀ᶠ m in atTop, chi ts F m = 0

def EulerPositivityInDimension : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 ts F.Ann → DimLT X.𝒜 (ts.length + 1) F.Ann → ∀ᶠ m in atTop, 0 ≤ chi ts F m

def RuleTw : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d : Deg k), Valid X.𝒜 ts →
    F.IsGr X.𝒜 → admitted X.𝒜 ts F.Ann → DimLT X.𝒜 (ts.length + 1) F.Ann →
    ∀ᶠ m in atTop, chi ts (F.shift d) m = chi ts F m

def EulerAdditivityInSection : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d d' : Deg k) (s s' : X.R),
    Valid X.𝒜 ((d, s) :: (d', s') :: ts) → F.IsGr X.𝒜 →
    admitted X.𝒜 ((d + d', s * s') :: ts) F.Ann → DimLT X.𝒜 (ts.length + 2) F.Ann →
    ∀ᶠ m in atTop, chi ((d + d', s * s') :: ts) F m = chi ((d, s) :: ts) F m + chi ((d', s') :: ts) F m

def RuleNzd : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d : Deg k) (s : X.R),
    (∀ x : F.M, s • x = 0 → x = 0) → ∀ m, chi ((d, s) :: ts) F m = chi ts (F.quot s) m

def EulerZeroSectionVanishing : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (s : X.R),
    (∀ x : F.M, s • x = 0) → ∀ m, chi ((0, s) :: ts) F m = 0

def RuleAll0 : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod),
    (∀ p ∈ ts, ∀ x : F.M, p.2 • x = 0) → ∀ m,
      chi ts F m = ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
        (-1 : ℤ) ^ I.card * ((Module.length X.B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

end Rules

end Formalism.MainNotions.V.Pf.V2.Calc
