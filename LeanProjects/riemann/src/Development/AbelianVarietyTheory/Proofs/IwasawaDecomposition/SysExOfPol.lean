import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsPhiDiv (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (BD : EffCartierData Z.X) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t),
      Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
      ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def IsPol (φ : InvFun (𝓞 E)) (m : ℕ) (Z : Model Xo c β) (BD : EffCartierData Z.X) : Prop :=
  IsPhiDiv φ Z BD ∧ GlobalTheory.IsAmpleLB (polOf Z m BD)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

def DomAll {Xo : ∀ l : Level H, Moduli D l} (s : Sys Xo) {l : Level H} {c : Coeff l} (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
    (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Z (s.Y p W hp hW ⟨l, c, hg p hp⟩) b

end Defs

def PolMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPol φ m Z BD → IsPol φ m Z' BD' → r ≫ Z.j ≫ Z.s = Z'.j ≫ Z'.s ≫ spMap b →
    ∃ (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b) (mu : TwMap σ Z'.t Z.t π), IsFinite (pullback.lift π Z'.s hπ) ∧
      Z'.j ≫ π = r ≫ Z.j ∧ Z'.m.φ ≫ mu.cm.F = ν.cm.F ≫ Z.m.φ ∧ BD'.idealSheaf = BD.idealSheaf.comap π

def PolStableSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : TorModel Y) (φ : InvFun (𝓞 E)), IsTwInv H φ →
    IsPol φ T.m0 T.Z T.BD → IsStable T

def PolTransSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l)
    (Xo₂ : Moduli D l₂) (c : Coeff l) (c₂ : Coeff l₂) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Y₂ : Model Xo₂ c₂ (algebraMap (𝓞 c₂.F) c₂.F)) (T : TorModel Y) (T₂ : TorModel Y₂) (φ : InvFun (𝓞 E))
    (b : 𝓞 c.F →+* 𝓞 c₂.F), 1 ≤ D.p + D.q → IsTwInv H φ → T₂.m0 = T.m0 → IsPol φ T.m0 T.Z T.BD →
    IsPol φ T.m0 T₂.Z T₂.BD → l.Dvd l₂ → (∀ x, (((b x : 𝓞 c₂.F) : c₂.F) : ℂ) = ((x : c.F) : ℂ)) → IsTorTrans T T₂ b

def PolSuppSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (BD : EffCartierData Z.X)
    (φ : InvFun (𝓞 E)), IsDedFrac β → IsPosFn H φ → IsPhiDiv φ Z BD →
    ∀ x, x ∈ BD.idealSheaf.support ↔ x ∉ abLocus Z.t.G

def PolArcSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (s : Sys Xo) (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : EffCartierData Z.X) (φ : InvFun (𝓞 E)) (m : ℕ),
    (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
    DomAll s hg Z → IsPol φ m Z BD → Z.N4

def HorizSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)), Z.N4 →
    ∀ x, x ∉ abLocus Z.t.G → x ∈ closure (genι Z '' (genBd Z : Set (gen Z)))

def PolDescSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (s : Sys Xo) (l : Level H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (Z : ∀ c : Coeff l, Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : ∀ c, EffCartierData (Z c).X)
    (φ : InvFun (𝓞 E)) (m : ℕ), l.A = 1 → IsTwInv H φ → (∀ c, DomAll s hg (Z c) ∧ IsPol φ m (Z c) (BD c)) →
    ∀ c, (Z c).Descends

def PolExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (φ : InvFun (𝓞 E)) (m : ℕ), 0 < m ∧ IsTwInv H φ ∧ IsPosFn H φ ∧
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (BD : EffCartierData Z.X), DomAll s hg Z ∧ IsPol φ m Z BD ∧
          SmoothOfRelativeDimension D.dim (genStr Z) ∧ FinalTheorems.Snc (genBdIdeal Z) ∧ ∀ x ∈ genBd Z, HasToricChart Z x

theorem sysEx_of_pol (hD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l),
      IsDedFrac (algebraMap (𝓞 c.F) c.F))
    (hSt : PolStableSt) (hTr : PolTransSt) (hSu : PolSuppSt) (hArc : PolArcSt) (hHo : HorizSt) (hDe : PolDescSt)
    (hEx : PolExSt) : SysExSt := by
  intro E _ _ _ H D h1 Xo
  obtain ⟨s, φ, m, hm, htw, hpos, hhom, h⟩ := hEx E H D h1 Xo
  choose Z BD hdom hpol hsm hsnc htor using h
  have hsupp := fun l c hg => hSu E H D l (Xo l) c _ _ (Z l c hg) (BD l c hg) φ (hD E H l c) hpos (hpol l c hg).1
  have hN4 := fun l c hg => hArc E H D Xo s l c hg (Z l c hg) (BD l c hg) φ m hhom (hdom l c hg) (hpol l c hg)
  let T : ∀ l c hg, TorModel (Z l c hg) := fun l c hg =>
    selfTor (Z l c hg) (hsm l c hg) (hsnc l c hg) (htor l c hg) (BD l c hg) (fun x hx => (hsupp l c hg x).1 hx)
      (fun x hx => (hsupp l c hg _).2 (mem_genBd_iff.1 hx)) m hm
  refine ⟨s, ⟨⟨Z, fun l c hg => ⟨fun hA => ?_, hdom l c hg, hN4 l c hg⟩, T, fun l c hg => ⟨(hpol l c hg).2, ?_, ?_⟩,
    fun l c hg l₂ c₂ hg₂ b hl hb => ?_⟩⟩⟩
  · exact hDe E H D Xo s l hg (fun c => Z l c hg) (fun c => BD l c hg) φ m hA htw
      (fun c => ⟨hdom l c hg, hpol l c hg⟩) c
  · exact fun x hx => hHo E H D l (Xo l) c (Z l c hg) (hN4 l c hg) x ((hsupp l c hg x).1 hx)
  · exact hSt E H D l (Xo l) c _ (T l c hg) φ htw (hpol l c hg)
  · exact hTr E H D l l₂ _ _ c c₂ _ _ (T l c hg) (T l₂ c₂ hg₂) φ b h1 htw rfl (hpol l c hg) (hpol l₂ c₂ hg₂) hl hb

end GlobalTheory.TorRef
