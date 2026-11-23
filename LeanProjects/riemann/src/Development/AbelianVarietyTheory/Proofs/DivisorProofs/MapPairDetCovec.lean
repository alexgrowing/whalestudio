import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def IsTest (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (yb : Sp 𝓞_ℂ_[p] ⟶ X) : Prop :=
  (∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb) ∧
    Set.range (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ⊆ Xw

def ChartAt (p n : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (J : Type) (_ : Finite J) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ), IsOpenImmersion ξ ∧ x ∈ Set.range ξ ∧
    ∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖

def GeomIrr {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V) (Xw : X.Opens) : Prop :=
  ∀ (k : Type) [Field k] (f : V →+* k), Function.Injective f → IrreducibleSpace ↑(pullback (Xw.ι ≫ s) (spMap f))

def ConnSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (X : Scheme.{0})
    (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → GeomIrr s Xw →
      ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s)

def GlueSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s →
      Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → ∀ (n : ℕ) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x ∈ closure (Xw : Set X), ChartAt p n Xw K x) →
      ∃ ρ : ℝ, ∀ yb, IsTest p Xw yb → ∀ κ ∈ K yb, ‖κ‖ = ρ

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

def PackSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ℂ_[p]), x ≠ 0 →
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
      (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
      IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
      (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
      ∃ sig : (D.pull (genericι f)).Gen, sig.IsGen ∧ ∃ φ : O →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of 𝓞_ℂ_[p]) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ), ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord f D sig ybar y e cc ∧ ‖(cc : ℂ_[p])‖ = ‖x‖

section Minors

variable {R V J : Type} [CommRing R] [CommRing V] {N g m : ℕ}

def pairDet (h U : Fin m → Fin g → R) : R := (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b).det

def covec (β : V →+* R) (T : J → Fin N → V) (h : Fin N → Fin g → R) (I : Fin m → J) : Fin m → Fin g → R :=
  fun k b => ∑ a, β (T (I k) a) * h a b

theorem map_pairDet_covec {S : Type} [CommRing S] (φ : R →+* S) (β : V →+* R) (T : J → Fin N → V)
    (h : Fin N → Fin g → R) (I : Fin m → J) (U : Fin m → Fin g → R) :
    φ (pairDet (covec β T h I) U) =
      pairDet (covec (φ.comp β) T (fun a b => φ (h a b)) I) fun k b => φ (U k b) := by
  rw [pairDet, pairDet, RingHom.map_det]
  congr 1
  ext k k'
  simp [covec, map_sum]

end Minors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W).toSubring fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff (R := c.V W) (K := c.F).1
      ((map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a)).tower_top)
    exact hy ▸ y.2

section Lie

variable {X : Scheme.{0}} (t : SAB H X) {g m : ℕ}

def IsEigG {S : Type} [CommRing S] (σ : 𝓞 E →+* S) (u : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∀ a, u ≫ (t.act.act a).left = spMap (epsMul (σ a)) ≫ u

def EigRowsAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin m → Fin g → S) : Prop :=
  ∀ k u, IsCombAtG t x e (U k) u → IsEigG t σ u

def EigAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin g → Fin g → S) : Prop :=
  EigRowsAt t x σ e U ∧
    ∀ w v, IsCombAtG t x e w v → IsEigG t σ v → ((discr E : ℤ) : S) • w ∈ Submodule.span S (Set.range U)

def bcV {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    Fin g → (Sp (DualNumber S) ⟶ t.G.left) := fun i => spMap (dualMap φ) ≫ e i

def EigFam {R : Type} [CommRing R] (x : Sp R ⟶ X) (σ : 𝓞 E →+* R) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (U : Fin g → Fin g → R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S), EigAt t (spMap φ ≫ x) (φ.comp σ) (bcV t φ e) fun k b => φ (U k b)

end Lie

abbrev Ind (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult τ) ⊕ Fin (Dw.mult (conjEmb τ))

variable (Dw) in

def LatData {V J : Type} [CommRing V] [DecidableEq J] (σ : 𝓞 E →+* V) {N : ℕ} (a : Fin N → Dw.La)
    (T S : J → Fin N → V) : Prop :=
  (∀ i o, ∑ m, T i m ⊗ₜ[ℤ] (o • a m) = ∑ m, (σ o * T i m) ⊗ₜ[ℤ] a m) ∧
  (∀ i j, ∑ m, ∑ m', S i m * T j m' * ((Dw.EF (a m) (a m') : ℤ) : V) = if i = j then 1 else 0) ∧
  ∀ x : V ⊗[ℤ] Dw.La, (∀ o, ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange V x = σ o • x) →
    x ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m)

section Model

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))

def OverIncl (hle : c.F ≤ c'.F) : Prop :=
  r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom

def IsCover (hle : c.F ≤ c'.F) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) (Xw : Y.X.Opens) : Prop :=
  OverIncl r hle ∧ (∀ x : c.F, (x : ℂ) ∈ W ↔ la.valuation c.F x ≤ 1) ∧ (p : ℂ) ∈ W.nonunits ∧
  (p : c'.F) ∈ (c'.V W).nonunits ∧ (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
  (∀ z, Y.j z ∈ Xw → r z ∈ (Z : Set (Xo.XF c))) ∧ GeomIrr Y.s Xw ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
    x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
    Set.range x ⊆ (Z : Set (Xo.XF c)) →
    ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range (yy ≫ Y.j) ⊆ Xw

def GVal (τ : E →+* ℂ) (f : Rul Xo c) {k : Type} [Field k] [Algebra c.F k] (yy : Sp k ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber k) ⟶ Y.t.G.left)) (U₁ : Fin (Dw.mult τ) → Fin g → k)
    (U₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → k) (fv : k) : Prop :=
  ∀ y : FrPt Xo c k, Tested y → GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) k),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₁ i) (w₁ i ≫ Y.m.φ)) → (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₂ i) (w₂ i ≫ Y.m.φ)) →
      (∀ i, IsCombAt y.x (y.u τ) (g₁ i) (w₁ i ≫ ν.φ)) → (∀ i, IsCombAt y.x (y.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ)) →
      fv * g₁.det = g₂.det * evR Xo c f y

variable {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)]

variable (p E) in

abbrev PtP : Type 1 := Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)

def PtOn (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Y.j ∧ IsGrpPullback P.G Y.t.G yb π ∧
    (∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left) ∧ IsGrpPullback P.A.A Y.oF.t.G yy ψ ∧
    ψ ≫ Y.m.φ = P.gen ≫ π ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ)

def ITie (P : PtP E p) {G : Scheme.{0}} (π : P.G.left ⟶ G) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ G) : Prop :=
  ∃ xG : LieG P.G, Corr P x.1 xG.1 ∧ xG.1.left ≫ π = u

def HTApprox (n : ℕ) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) {N g : ℕ} (a : Fin N → Dw.La)
    (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (h : Fin N → Fin g → 𝓞_ℂ_[p]) : Prop :=
  ∀ (m : Fin N) (t : P.T), (t.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left → ∀ (k : Fin g) (x : LieG P.Gt),
    ITie P π x (e k) → h m k - (P.al₀ t).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}

variable [Algebra c.F ℂ_[p]]

def HTAt (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]) : Prop :=
  PtOn Y yb yy P π ψ ∧ Tested y ∧ GlobalTheory.AllWt.ptF y = yy ≫ r ∧ ∃ z, IsHTChange P (ψ ≫ ν.φ) z y

def KapSpec (τ : E →+* ℂ) (f : Rul Xo c) (n : ℕ) {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ → Fin N → c'.V W)
    (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (κ : ℂ_[p]) : Prop :=
  ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
  ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
    (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ)) e U₁ →
    EigAt Y.t yb (β.comp (embV c' W (conjEmb τ))) e U₂ → HTApprox Y n yy P π ψ a e h →
    (∃ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) ∧
    ∀ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖ →
      ∀ fv : ℂ_[p], GVal Y r ν τ f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
        (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
        ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
          (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖

end Model

def DualFam {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (σ : 𝓞 E →+* 𝓞_ℂ_[p]) {J : Type} [DecidableEq J]
    (t s : J → P.V) (u : ℂ_[p]) : Prop :=
  (∀ i, t i ∈ P.latTSub σ) ∧ (∀ i, s i ∈ P.latT) ∧ ‖u‖ = 1 ∧ (∀ i j, P.pairV (s i) (t j) = if i = j then u else 0) ∧
    P.eigV σ ≤ Submodule.span ℂ_[p] (Set.range t)

def CoverSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
    1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ q : ℕ, q.Prime → l.GoodAt q) → FnAlgClosed Xo c →
    ∀ (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p n : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal →
    ∃ (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
      (r : Xo'.XF c' ⟶ Xo.XF c) (_ : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
      (Xw : Y.X.Opens), l'.A = p ^ n ∧ IsCover Y r hle Z la p Xw

def ChartSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ x : Y.X,
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsIntegrallyClosed R) (ξ : Sp R ⟶ Y.X) (g : ℕ)
      (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsOpenImmersion ξ ∧ x ∈ Set.range ξ ∧ IsTanBasis Y.t ξ e

def ProjSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l)
    (W : ValuationSubring ℂ) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (β : c.V W →+* R)
    (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), IsTanBasis t ξ e → ∀ σ : E →+* ℂ,
    ∃ U : Fin g → Fin g → R, EigFam t ξ (β.comp (embV c W σ)) e U

def LatSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ τ : Psi H,
    ∃ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c.V W), LatData Dw (embV c W (conjEmb τ.1)) a T S

def HTLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ)
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)),
    IsTanBasis Y.t ξ e → ∀ (N : ℕ) (a : Fin N → Dw.La) (𝔭 : Ideal R), 𝔭.IsPrime →
    ∃ (f : R) (h : Fin N → Fin g → Localization.Away f), f ∉ 𝔭 ∧
      ∀ (φ : Localization.Away f →+* 𝓞_ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
        (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y (spMap (φ.comp (algebraMap R _)) ≫ ξ) yy P π ψ →
        HTApprox Y n yy P π ψ a (bcV Y.t (φ.comp (algebraMap R _)) e) fun m k => φ (h m k)

def GenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
      ∃ f : Aˣ, ∀ (k : Type) [Field k] [Algebra c.F k] (φ : A →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap φ ≫ ξ →
        GVal Y r ν τ.1 s.sig yy (bcV Y.t φ e) (fun k b => φ (U₁ k b)) (fun k b => φ (U₂ k b)) (φ f)

def CmpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr),
      (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) →
    ∀ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]),
      IsHTFrameCp p y₀ k y → ∀ (k' : T'.Fr →+* ℂ_[p]) (kO : T'.V →+* 𝓞_ℂ_[p]),
      (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k' (algebraMap T'.V T'.Fr a)) → (∀ a, k' (iF a) = k a) →
    ∀ (yT : Sp T'.V ⟶ Y.X) (yyT : Sp T'.Fr ⟶ Xo'.XF c'), spMap (algebraMap T'.V T'.Fr) ≫ yT = yyT ≫ Y.j →
      yyT ≫ r = spMap iF ≫ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1) →
      letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        HTAt Y r ν (spMap kO ≫ yT) (spMap k' ≫ yyT) P π ψ y

def ExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ q : ℕ, q.Prime → l.GoodAt q) →
    ∀ (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] (Xw : Y.X.Opens), IsCover Y r hle Z la p Xw →
    ∀ yb : Sp 𝓞_ℂ_[p] ⟶ Y.X, IsTest p Xw yb →
      ∃ (_ : Algebra c.F ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]),
      letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        HTAt Y r ν yb yy P π ψ y

def LiftSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] (Xw : Y.X.Opens), IsCover Y r hle Z la p Xw →
    ∀ [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y₀ : IntFr Xo c T io), OverLa la T.V io e →
      algOn Z T io y₀ → ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y →
      ∃ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), IsTest p Xw yb ∧
      letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        HTAt Y r ν yb yy P π ψ y

def TateSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ)
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ → ∀ (β : c'.V W →+* 𝓞_ℂ_[p]) (σ : E →+* ℂ) (J : Type)
      [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La) (T S : J → Fin N → c'.V W), LatData Dw (embV c' W σ) a T S →
      ∃ (ta : Fin N → P.T) (u : ℂ_[p]), (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        DualFam P (β.comp (embV c' W σ)) (fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)
          (fun i => ∑ m, (β (S i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) u

def ValueSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (P : PtP E p) (τ : Psi H) (t s : Ind Dw τ.1 → P.V) (u : ℂ_[p]),
      DualFam P (embInt c P.integers (conjEmb τ.1)) t s u →
    ∀ (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V),
      (∀ k, w₁ k ∈ P.eigV (embInt c P.integers τ.1)) → (∀ k, w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) →
      (∀ k k', P.pairV (w₁ k) (w₂ k') = 0) → IsLatBasis ℂ_[p] (htLat c P τ.1) w₁ →
      IsLatBasis ℂ_[p] (htLat c P (conjEmb τ.1)) w₂ →
      ∃ lam : ℂ_[p], ‖lam‖ = 1 ∧
        (∀ σ : Equiv.Perm (Ind Dw τ.1), ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) *
          (Matrix.of fun k k' => P.pairV (w₁ k) (t (σ (Sum.inl k')))).det =
            lam * (Matrix.of fun k k' => P.pairV (w₂ k) (s (σ (Sum.inr k')))).det) ∧
        ∃ σ : Equiv.Perm (Ind Dw τ.1), ‖(Matrix.of fun k k' => P.pairV (w₁ k) (t (σ (Sum.inl k')))).det‖ = 1

def BoundSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)] (P : PtP E p), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.CokernelBound P →
    ∀ (σ : E →+* ℂ) (w : P.V), w ∈ htLat c P σ → w ∈ Submodule.span ℂ_[p] (Set.range P.bLie) →
      w ∈ P.eigV (embInt c P.integers σ) → ∃ x : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x ∧
        P.bLie x = (((discr E : ℤ) : ℂ_[p]) * (p : ℂ_[p]) ^ 2) • w

def PtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∃ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧ KapSpec Y r ν τ.1 f n a T S yb yy P π ψ κ

section BaseChange

variable {X : Scheme.{0}} {t : SAB H X} {g : ℕ} {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']

theorem bcV_bcV (φ : R →+* S) (ψ : S →+* S') (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    bcV t ψ (bcV t φ e) = bcV t (ψ.comp φ) e := by
  funext i
  rw [bcV, bcV, bcV, ← Category.assoc, spMap_spMap]
  congr 2
  ext s <;> simp [dualMap]

theorem sp_sp (φ : R →+* S) (ψ : S →+* S') (x : Sp R ⟶ X) : spMap ψ ≫ spMap φ ≫ x = spMap (ψ.comp φ) ≫ x := by
  rw [← Category.assoc, spMap_spMap]

theorem isTanBasis_bc {x : Sp R ⟶ X} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x e)
    (φ : R →+* S) : IsTanBasis t (spMap φ ≫ x) (bcV t φ e) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun S' _ ψ w hw => ?_⟩
  · rw [bcV, Category.assoc, (h.1 i).1, sp_sp, sp_sp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · have e1 : (1 : Over.mk (spMap φ ≫ x) ⟶ t.G) = (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [e1, Over.comp_left, ← (h.1 i).2, bcV, ← Category.assoc, spMap_spMap]
    change _ = spMap φ ≫ _ ≫ _
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sp_sp] at hw ⊢
    have := h.2 S' (ψ.comp φ) w hw
    change ∃! a, IsCombAtG t _ (bcV t ψ (bcV t φ e)) a w
    rw [bcV_bcV]
    exact this

theorem bot_map [IsDomain R] [IsDomain S] {φ : R →+* S} (hφ : Function.Injective φ) (x : Sp R ⟶ X) :
    (spMap φ ≫ x) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) = x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg x ?_)
  exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot φ).1 hφ)

theorem bot_mem [IsDomain R] (x : Sp R ⟶ X) {O : X.Opens} {z : Sp R} (h : x z ∈ O) :
    x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ O := by
  have h1 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ z := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact (h1.map x.continuous).mem_open O.isOpen h

end BaseChange

theorem coe_valued (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]

end GlobalTheory.FlatModel

end
