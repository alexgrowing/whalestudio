import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DZ (y : IrrGL k) : Prop := GlobalTheory.PRep.fixed y.rep (GlobalTheory.SplitWeil.KOne k (Fin y.1)) ≠ ⊥

def TameChar (χ : kˣ →* ℂˣ) : Prop := ∀ u : kˣ, valuation k ((u : k) - 1) < 1 → χ u = 1

end Rep

def Names (g : ℕ) [Fact g.Prime] (n : ℕ) {K : Type} [Field K] [Algebra (ZMod g) K] (θ : Kˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n)) : Prop :=
  ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
    τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure Ext (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (n : ℕ) : Type 1 where
  E' : Type
  [fE : Field E']
  [nE : NumberField E']
  [aE : Algebra E E']
  [aΩ : Algebra E' Ω]
  [tE : IsScalarTower E E' Ω]
  [cE : IsAlgClosure E' Ω]
  w' : HeightOneSpectrum (𝓞 E')
  h' : IsPlaceOver A w'
  unr : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2
  card : normV w' = g ^ n
  a' : Weil h' →* (w'.adicCompletion E')ˣ
  ha' : IsLocalArtin h' a'
  K : Type
  [fK : Field K]
  [aK : Algebra (ZMod g) K]
  red : 𝓞 E' →+* K
  surj : Function.Surjective red
  ker : RingHom.ker red = w'.asIdeal

attribute [instance] Ext.fE Ext.nE Ext.aE Ext.aΩ Ext.tE Ext.cE Ext.fK Ext.aK

def Ext.Res {g n : ℕ} [Fact g.Prime] (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ) : Prop :=
  ∀ (t : Ine (F := E) A) (t' : Ine (F := D.E') A) (x : 𝓞 D.E') (z : D.Kˣ),
    (t : G E Ω) = AlgEquiv.restrictScalars E (t' : G D.E' Ω) → D.red x = z →
    Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 →
    R t = z

variable (h) in

structure TameSys (g : ℕ) [Fact g.Prime] (n : ℕ) {K : Type} [Field K] [Algebra (ZMod g) K] (R : Ine (F := E) A →* Kˣ) : Prop where
  pos : 0 < n
  normV_eq : normV w = g
  rank : Module.finrank (ZMod g) K = n
  surj : Function.Surjective R
  isOpen : IsOpen (R.ker : Set (Ine (F := E) A))
  wild : ∀ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) → R t = 1
  frob : ∀ (σ : Weil h) (t t' : Ine (F := E) A), deg σ = 1 → ineIncl h t' = σ * ineIncl h t * σ⁻¹ → R t' = R t ^ g

def InFor (g n : ℕ) {K : Type} [Field K] (R : Ine (F := E) A →* Kˣ) (θ : Kˣ →* ℂˣ) (V : WD h) : Prop :=
  ∀ t : Ine (F := E) A, V.inePol (t : G E Ω) = ∏ j ∈ Finset.range n, (X - C ((θ (R t ^ g ^ j) : ℂˣ) : ℂ))

def TypeAt (x : IrrGL (w.adicCompletion E)) (V : WD h) : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i → ∀ n : ℕ, 0 < n →
    ∀ (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ), D.Res R → ∀ θ : D.Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character → Names g n θ τ → ∀ σ : IrrRep (GL (Fin n) (w.adicCompletion E)), cls σ = x →
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ → V.mono0 ∧ InFor g n R θ V

structure Par (a : Weil h →* (w.adicCompletion E)ˣ) (y : IrrGL (w.adicCompletion E)) (V : WD h) : Prop where
  irr : IsIrrWD V
  dim : V.lpDim = y.1
  tame : IsTameWD V
  central : ∀ ω, HasCentralChar y.rep ω → ∀ σ, (V.eig σ).prod = (ω (a σ) : ℂ)
  type : TypeAt y V

structure CuspT (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r : IrrGL (w.adicCompletion E) → WD h) : Prop where
  irr : ∀ x, x.IsCusp → IsIrrWD (r x)
  dim : ∀ x, x.IsCusp → (r x).lpDim = x.1
  one : ∀ χ hχ, r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  nu : ∀ x, x.IsCusp → ∀ s : ℝ, r (x.nu s) = (r x).lpTw s
  absCentral : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → ∀ ω, HasCentralChar x.rep ω → ∀ σ, ‖((r x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
  twist : ∀ x, x.IsCusp → GoodCusp x → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)
  central : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → GoodCusp x → ∀ ω, HasCentralChar x.rep ω → ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ)
  dual : ∀ x y, x.IsCusp → y.IsCusp → GoodCusp x → DualCl x y → r y = (r x).lpDual
  inj : ∀ x y, x.IsCusp → y.IsCusp → GoodCusp y → r x = r y → x = y
  depth : ∀ x, x.IsCusp → GoodCusp x → DZ x → IsTameWD (r x)
  type : ∀ x, x.IsCusp → TypeAt x (r x)

def Pin : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = n →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
      (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧ ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
      ∀ θ' : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ' →
        (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
          ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ Finset.range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
        ∃ j < n, θ' = θ ^ g ^ j

def NameLaws : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = n →
    (∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character → ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧ Names g n θ τ) ∧
    (∀ (τ : FDRep ℂ (Gn g n)) (θ θ' : Kˣ →* ℂˣ), GlobalTheory.Published.IsRegularChar g n θ → GlobalTheory.Published.IsRegularChar g n θ' →
      Names g n θ τ → Names g n θ' τ → ∃ j < n, θ' = θ ^ g ^ j) ∧
    (∀ (τ τ' : FDRep ℂ (Gn g n)) (θ : Kˣ →* ℂˣ) (j : ℕ), IsCusp τ.character → IsCusp τ'.character → GlobalTheory.Published.IsRegularChar g n θ →
      Names g n θ τ → Names g n (θ ^ g ^ j) τ' → τ'.character = τ.character) ∧
    ∀ (K' : Type) [Field K'] [Algebra (ZMod g) K'] (e : K ≃+* K') (τ : FDRep ℂ (Gn g n)) (θ' : K'ˣ →* ℂˣ),
      (Names g n θ' τ → Names g n (θ'.comp (Units.map e.toRingHom.toMonoidHom)) τ) ∧
      (GlobalTheory.Published.IsRegularChar g n θ' → GlobalTheory.Published.IsRegularChar g n (θ'.comp (Units.map e.toRingHom.toMonoidHom)))

def NameCentral : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = n →
    ∀ (τ : FDRep ℂ (Gn g n)) (θ : Kˣ →* ℂˣ), IsCusp τ.character → GlobalTheory.Published.IsRegularChar g n θ → Names g n θ τ →
      ∀ (c : (ZMod g)ˣ) (v : τ), τ.ρ (GeneralLinearGroup.scalar (Fin n) c) v =
        ((θ (Units.map (algebraMap (ZMod g) K).toMonoidHom c) : ℂˣ) : ℂ) • v

def IsoUniq : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (g g' : ℕ) [Fact g.Prime] [Fact g'.Prime]
    (i : ℚ_[g] ≃+* k) (i' : ℚ_[g'] ≃+* k), Continuous i → Continuous i' → g = g' ∧ ∀ i'' : ℚ_[g] ≃+* k, Continuous i'' → i'' = i

def TypeEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ σ : IrrRep (GL (Fin n) (w.adicCompletion E)),
      ((cls σ).IsCusp → DZ (cls σ) → ∃ τ : FDRep ℂ (Gn g n), IsCusp τ.character ∧
        GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) ∧
      ∀ (σ' : IrrRep (GL (Fin n) (w.adicCompletion E))) (τ τ' : FDRep ℂ (Gn g n)), cls σ' = cls σ → IsCusp τ.character → IsCusp τ'.character →
        GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ →
        GlobalTheory.SerSys.TameGen.Inflates (σ'.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ' → τ'.character = τ.character

def DetByType : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ (σ σ' : IrrRep (GL (Fin n) (w.adicCompletion E))) (τ τ' : FDRep ℂ (Gn g n)) (ω : (w.adicCompletion E)ˣ →* ℂˣ),
      IsCusp τ.character → τ'.character = τ.character →
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ →
      GlobalTheory.SerSys.TameGen.Inflates (σ'.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ' →
      HasCentralChar σ.ρ ω → HasCentralChar σ'.ρ ω → cls σ' = cls σ

def TwTame : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (y : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    0 < y.1 → DZ y → (DZ (y.tw χ hχ) ↔ TameChar χ)

def ClBasic : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (y : IrrGL k),
    (∃ ω, IsSmoothChar ω ∧ HasCentralChar y.rep ω ∧ ∀ ω', HasCentralChar y.rep ω' → ω' = ω) ∧
    (∀ χ hχ, (y.tw χ hχ).1 = y.1 ∧ ((y.tw χ hχ).IsCusp ↔ y.IsCusp) ∧ (GoodCusp (y.tw χ hχ) ↔ GoodCusp y) ∧
      (∀ χ' hχ' h'', (y.tw χ hχ).tw χ' hχ' = y.tw (χ * χ') h'') ∧
      ∀ ω, HasCentralChar y.rep ω → HasCentralChar (y.tw χ hχ).rep (ω * χ ^ y.1)) ∧
    (∀ h1, y.tw 1 h1 = y) ∧ (y.IsCusp → 0 < y.1) ∧ (y.1 = 1 → y.IsCusp ∧ ∃ χ hχ, y = .ofChar χ hχ) ∧
    (∃ y', DualCl y y') ∧
    ∀ y', DualCl y y' → y'.1 = y.1 ∧ (y'.IsCusp ↔ y.IsCusp) ∧ (DZ y' ↔ DZ y) ∧ (GoodCusp y' ↔ GoodCusp y) ∧
      (∀ y'', DualCl y y'' → y'' = y') ∧ (∀ χ hχ hχ', DualCl (y.tw χ hχ) (y'.tw χ⁻¹ hχ')) ∧
      ∀ ω, HasCentralChar y.rep ω → HasCentralChar y'.rep ω⁻¹

def Expo : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), ∃ e : IrrGL (w.adicCompletion E) → ℝ, ∀ x : IrrGL (w.adicCompletion E), 0 < x.1 →
    (∀ s : ℝ, e (x.nu s) = e x + s) ∧ ∀ ω, HasCentralChar x.rep ω → ∀ (J : WD h), J.lpDim = x.1 → (∀ σ, ‖(J.eig σ).prod‖ = 1) →
      ∀ σ, ‖((J.lpTw (e x)).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖

def GoodSeg : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ (l : List (Segment k)) (x : IrrGL k), IsL (l : Multiset (Segment k)) x.rep → (Good x ↔ ∀ Δ ∈ l, GoodCusp Δ.first)) ∧
    (∀ x : IrrGL k, x.IsCusp → (Good x ↔ GoodCusp x)) ∧
    ∀ (x : IrrGL k) (s s' : Multiset (IrrGL k)), HasSupport x.rep s → HasSupport x.rep s' → s = s'

def ArtEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃! a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a

def ExtEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i → ∀ n : ℕ, 0 < n → Nonempty (Ext h g n)

def ResEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ D : Ext h g n, (∃ R, D.Res R) ∧ ∀ R, D.Res R → TameSys h g n R

def ResBase : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ (D : Ext h g n) (R : Ine (F := E) A →* D.Kˣ), D.Res R → ∀ t : Ine (F := E) A,
      ∃ u : ℤ_[g]ˣ, (a (ineIncl h t) : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) ∧
        algebraMap (ZMod g) D.K (PadicInt.toZMod (u : ℤ_[g])) = ∏ j ∈ Finset.range n, ((R t ^ g ^ j : D.Kˣ) : D.K)

def ResIndep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ (D D' : Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (R' : Ine (F := E) A →* D'.Kˣ), D.Res R → D'.Res R' →
      ∃ e : D.K ≃+* D'.K, ∀ t, ((R' t : D'.Kˣ) : D'.K) = e (R t : D.Kˣ)

def TypeIff : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), TypeLaw h rc ↔ ∀ x, TypeAt x (rc x)

def IndEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (φ : Weil h), deg φ = 1 → ∀ n : ℕ, 0 < n → ∀ η : ℤ → (Ine (F := E) A →* ℂˣ),
    IsOpen ((η 0).ker : Set (Ine (F := E) A)) →
    (∀ (j : ℤ) (t t' : Ine (F := E) A), ineIncl h t' = φ * ineIncl h t * φ⁻¹ → η j t' = η (j + 1) t) →
    (∀ j j' : ℤ, η j = η j' ↔ (n : ℤ) ∣ j - j') → ∀ c : ℂ, c ≠ 0 →
    ∃ V : WD h, IsIrrWD V ∧ V.lpDim = n ∧ (V.eig φ).prod = c ∧
      (∀ t : Ine (F := E) A, V.inePol (t : G E Ω) = ∏ j ∈ Finset.range n, (X - C ((η j t : ℂˣ) : ℂ))) ∧
      ((∀ (j : ℤ) (t : Ine (F := E) A), Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) → η j t = 1) → IsTameWD V)

def WDBasic : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : WD h),
    (∃ δ : Weil h →* ℂˣ, ∀ σ, (V.eig σ).prod = δ σ) ∧
    (∀ (φ : Weil h) (δ δ' : Weil h →* ℂˣ), deg φ = 1 → δ φ = δ' φ → (∀ t, δ (ineIncl h t) = δ' (ineIncl h t)) → δ = δ') ∧
    (∃ φ : Weil h, deg φ = 1) ∧ (IsIrrWD V → V.mono0 ∧ 0 < V.lpDim ∧ IsIrrWD V.lpDual) ∧ (IsTameWD V → IsTameWD V.lpDual) ∧
    V.lpDual.lpDim = V.lpDim ∧ (∀ σ, (V.lpDual.eig σ).prod = ((V.eig σ).prod)⁻¹) ∧
    (∀ (t : Ine (F := E) A) (m : Multiset ℂˣ), V.inePol (t : G E Ω) = (m.map fun z => X - C (z : ℂ)).prod →
      (V.eig (ineIncl h t)).prod = (m.prod : ℂˣ) ∧ V.lpDual.inePol (t : G E Ω) = (m.map fun z => X - C ((z⁻¹ : ℂˣ) : ℂ)).prod ∧
      ∀ ξ hξ, (V.lpTwist ξ hξ).inePol (t : G E Ω) = (m.map fun z => X - C ((z * ξ (ineIncl h t) : ℂˣ) : ℂ)).prod) ∧
    ∀ ξ hξ, (V.lpTwist ξ hξ).lpDim = V.lpDim ∧ (IsIrrWD V → IsIrrWD (V.lpTwist ξ hξ)) ∧
      (∀ σ, ((V.lpTwist ξ hξ).eig σ).prod = (V.eig σ).prod * (ξ σ : ℂ) ^ V.lpDim) ∧
      (∀ ξ' hξ' h'', (V.lpTwist ξ hξ).lpTwist ξ' hξ' = V.lpTwist (ξ * ξ') h'') ∧ (ξ = 1 → V.lpTwist ξ hξ = V) ∧
      (∀ hξ', (V.lpTwist ξ hξ).lpDual = V.lpDual.lpTwist ξ⁻¹ hξ') ∧
      ((∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1) → IsTameWD V → IsTameWD (V.lpTwist ξ hξ)) ∧
      (0 < V.lpDim → IsTameWD V → IsTameWD (V.lpTwist ξ hξ) → ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1)

def TameArt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (χ : (w.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar χ →
    (TameChar χ ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → χ (a σ) = 1)

def TameUniq : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (n : ℕ) (K : Type) [Field K] [Algebra (ZMod g) K] (R : Ine (F := E) A →* Kˣ),
    TameSys h g n R → ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ → ∀ V : WD h, InFor g n R θ V →
      (∀ j : ℕ, InFor g n R (θ ^ g ^ j) V) ∧
      (∀ θ' : Kˣ →* ℂˣ, InFor g n R θ' V → ∃ j < n, θ' = θ ^ g ^ j) ∧
      ∀ V' : WD h, IsIrrWD V → IsIrrWD V' → IsTameWD V → IsTameWD V' → InFor g n R θ V' →
        (∀ σ, (V.eig σ).prod = (V'.eig σ).prod) → V' = V

def JunkEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ), 2 ≤ n → ∃ J : WD h, IsIrrWD J ∧ J.lpDim = n ∧ (∀ σ, ‖(J.eig σ).prod‖ = 1) ∧
    ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) →
      ∀ (V : WD h) ξ hξ, IsTameWD V → J ≠ V.lpTwist ξ hξ)

def ParEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i → ∀ y : IrrGL (w.adicCompletion E), y.IsCusp → DZ y → ∃ V : WD h, Par a y V

def ParUniq : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ y : IrrGL (w.adicCompletion E), y.IsCusp → DZ y → ∀ V : WD h, Par a y V →
      (∀ V', Par a y V' → V' = V) ∧ ∀ y' : IrrGL (w.adicCompletion E), y'.IsCusp → DZ y' → Par a y' V → y' = y

def ParTw : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ y : IrrGL (w.adicCompletion E), y.IsCusp → DZ y → ∀ V : WD h, Par a y V → ∀ χ hχ, TameChar χ →
      Par a (y.tw χ hχ) (V.lpTwist (χ.comp a) (ha.smooth hχ))

def ParDual : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ y y' : IrrGL (w.adicCompletion E), y.IsCusp → DZ y → DualCl y y' → ∀ V : WD h, Par a y V → Par a y' V.lpDual

def ParOne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsIrrWD (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) ∧ (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpDim = 1 ∧
    HasCentralChar (IrrGL.ofChar χ hχ).rep χ ∧ (∀ σ, ((WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).eig σ).prod = (χ (a σ) : ℂ)) ∧
    (DZ (IrrGL.ofChar χ hχ) ↔ TameChar χ) ∧ (TameChar χ → Par a (.ofChar χ hχ) (WD.lpOfChar h (χ.comp a) (ha.smooth hχ))) ∧
    (∀ χ' hχ' h'', (IrrGL.ofChar χ hχ).tw χ' hχ' = .ofChar (χ * χ') h'' ∧
      (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpTwist (χ'.comp a) (ha.smooth hχ') = WD.lpOfChar h ((χ * χ').comp a) (ha.smooth h'')) ∧
    (∀ h'', DualCl (IrrGL.ofChar χ hχ) (.ofChar χ⁻¹ h'') ∧
      (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpDual = WD.lpOfChar h (χ⁻¹.comp a) (ha.smooth h'')) ∧
    ∀ χ' hχ', IrrGL.ofChar χ hχ = .ofChar χ' hχ' → χ = χ'

def GoodMap : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), ∃ r : IrrGL (w.adicCompletion E) → WD h,
    (∀ χ hχ, r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) ∧
    (∀ x, x.IsCusp → GoodCusp x → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)) ∧
    ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) → ∀ y, y.IsCusp → DZ y → Par a y (r y))

def CuspEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), ∃ r : IrrGL (w.adicCompletion E) → WD h, CuspT a ha r

def ExtDim : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r rc : IrrGL (w.adicCompletion E) → WD h), CuspT a ha r → IsLExt r rc →
    ∀ x : IrrGL (w.adicCompletion E), ((rc x).lpDim = x.1 ∧ ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.IsCusp) ∧
      ∀ σ, (rc x).charPol σ = (s.map fun y => (r y).charPol σ).prod) ∧
      ∀ ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖ ∧ (Good x → ((rc x).eig σ).prod = (ω (a σ) : ℂ))

def ExtTw : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r rc : IrrGL (w.adicCompletion E) → WD h), CuspT a ha r → IsLExt r rc →
    (∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s) ∧
      ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (WD.lpOfChar h (χ.comp a) (ha.smooth hχ))

def ExtDual : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r rc : IrrGL (w.adicCompletion E) → WD h), CuspT a ha r → IsLExt r rc →
    ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) →
      rc (cls π') = (rc (cls π)).lpDual

def ExtInj : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r rc : IrrGL (w.adicCompletion E) → WD h), CuspT a ha r → IsLExt r rc → ∀ x y, Good y → rc x = rc y → x = y

def ExtDepth : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (r rc : IrrGL (w.adicCompletion E) → WD h), CuspT a ha r → IsLExt r rc → ∀ x, Good x → DZ x → IsTameWD (rc x)

def RecTTransport : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E')
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i →
    ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), IsRecT h rc → IsRecT h' rc' →
      ∀ x x', RepRel i x x' → Good x → WDRel φ (rc x) (rc' x')

end UpperTheory.Zero.LLC

end
