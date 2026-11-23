import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamModelDR
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest

namespace GlobalTheory.TwoLat

section General

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E E' : X.Modules} {r : ℕ}

def IsoHom (h : VMetric p E r) (h' : VMetric p E' r) (u : E ⟶ E') : Prop :=
  ∀ σ (V : X.Opens) (s t : Γ(E, V)), ∀ y ∈ CxPts.ptsIn p σ V,
    (h'.met σ).form (u.app V s) (u.app V t) y = (h.met σ).form s t y

def Compat (u : E ⟶ E') (fl : Vert.Flag E r) (fl' : Vert.Flag E' r) : Prop :=
  ∀ i, ∃ t : fl.F i ⟶ fl'.F i, t ≫ fl'.ι i = fl.ι i ≫ u

theorem Compat.pull {u : E ⟶ E'} {fl : Vert.Flag E r} {fl' : Vert.Flag E' r} (h : Compat u fl fl') {Y : Scheme.{0}}
    (π : Y ⟶ X) : Compat ((Scheme.Modules.pullback π).map u) (fl.pull π) (fl'.pull π) := fun i => by
  obtain ⟨t, ht⟩ := h i
  exact ⟨(Scheme.Modules.pullback π).map t, ((Functor.map_comp _ _ _).symm.trans (congrArg _ ht)).trans
    (Functor.map_comp _ _ _)⟩

def Vanish [IsIntegral X] {ι : Type} [Fintype ι] {r : ι → ℕ} (n e : ℕ) (x x' : (Σ a, Fin (r a)) → HermLB p) : Prop :=
  ∀ Φ : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim x x') (n + 1 + e) Φ →
    ∀ Q : MvPolynomial (Σ a, Fin (r a)) ℝ, Q.IsHomogeneous e → GlobalTheory.GoodMetric.antisymm Q = 0 →
      Φ ((∑ z, MvPolynomial.X (Sum.inr z) ^ 2 - ∑ z, MvPolynomial.X (Sum.inl z) ^ 2) *
        rename Sum.inl ((∑ z, MvPolynomial.X z) ^ n * Q)) = 0

end General

def VanishOn (P : ∀ (B : Scheme.{0}) (ι : Type) (E E' : ι → B.Modules), (ι → ℕ) → (∀ a, E a ⟶ E' a) → Prop) : Prop :=
  ∀ (k : Type) [CommRing k] (B Y X : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral X] (q : B ⟶ Sp k) (π : Y ⟶ B)
    (ρ : X ⟶ Y) (p : X ⟶ Sp k) (w : ρ ≫ π ≫ q = p) (n e : ℕ), IsArithVar q (n + 1) → IsArithVar (π ≫ q) (n + 1 + e) →
    FlagChain.IsCov (π ≫ q) (n + 1 + e) ρ → ∀ (ι : Type) [Fintype ι] (E E' : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (h' : ∀ a, VMetric q (E' a) (r a)) (H : ∀ a, (h a).IsCInf) (H' : ∀ a, (h' a).IsCInf)
    (u : ∀ a, E a ⟶ E' a), (∀ a, IsoHom (h a) (h' a) (u a)) → P B ι E E' r u →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj (E' a))) (r a)),
      (∀ a, Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map (u a))) ((fl a).pull ρ) (fl' a)) →
      Vanish n e (fun z : Σ a, Fin (r a) => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ w)
        fun z : Σ a, Fin (r a) => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ w)

def RegFlagged (B : Scheme.{0}) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (u : ∀ a, E a ⟶ E' a) : Prop :=
  (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) ∧
    ∀ a, ∃ (m : Vert.Flag (E a) (r a)) (m' : Vert.Flag (E' a) (r a)), Compat (u a) m m'

open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def InGr {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (Λ : Set (Sp (DualNumber K) ⟶ Z.t.G.left))
    (τ : E →+* ℂ) (w : Sp (DualNumber K) ⟶ Z.t.G.left) : Prop :=
  ∃ (m : ℕ) (ρ : Fin m → (E →+* ℂ)) (v : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)),
    (∀ i, Fintype.equivFin (E →+* ℂ) (ρ i) < Fintype.equivFin (E →+* ℂ) τ ∧ IsEigTan Z φ x (ρ i) (v i)) ∧
      ∃ w' ∈ Λ, IsCombAtG Z.t x (Fin.cons w v : Fin (m + 1) → _) (fun _ => 1) w'

def IsGrLat {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (u : FrAssign Z M r jB) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
    xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
    spMap ε.O.subtype ≫ xt = xg ≫ jB →
    ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f), ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
        ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
            IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
              (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u U f hf _ xg hx i) a w) ↔
          InGr Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (latDR Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)) τ w)

def Matches {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {M M' : X.Modules} {r : ℕ} (g : M ⟶ M')
    (u : FrAssign Z M r jB) (u' : FrAssign Z M' r jB) : Prop :=
  ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (f' : Fin r → Γ(M', U)) (hf : VB.IsFrame f) (hf' : VB.IsFrame f')
    (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (i : Fin r),
    IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u' U f' hf' K x hx)
      (fun b => TangentOrigin.evalPt (x ≫ jB) U hx ((hf'.basis le_rfl).repr (Twist.resM M' le_rfl (g.app U (f i))) b))
      (u U f hf K x hx i)

end Free

variable {D : D7} (O : Setup D)

def PairBase (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → Bs.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ) : Prop :=
  ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (_ : IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB) (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB)
    (G : ∀ σ', EigMet O.s.T.Z σ'),
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (t σ)) ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E' σ) _ σ false (t' σ)) ∧
    (∀ σ, Matches O.s.T.Z jB πB (u σ) (t σ) (t' σ)) ∧
    (∀ σ, IsLieLat O.s.T.Z O.κ.e jB πB (E σ) _ σ (ArIn.ind ∅) (fun _ => True) (t σ)) ∧
    (∀ σ, IsGrLat O.s.T.Z O.κ.e jB πB (E' σ) _ σ (t' σ)) ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    (∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E σ) _ σ false rfl G (h σ) (t σ)) ∧
    ∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E' σ) _ σ false rfl G (h' σ) (t' σ)

abbrev lineAdl (R : ℝ) (c : O.s.Comp) (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (s : ℤ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (ArIn.ind ∅, some R, st) s)

def PairCover (R : ℝ) (c : O.s.Comp) {B : Scheme.{0}} (q : B ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → B.Modules) {h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)}
    {h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)} (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf)
    (u : ∀ σ, E σ ⟶ E' σ) : Prop :=
  ∃ (V : Cover (O.var c)) (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ B) (ρ : V.X ⟶ Y) (w : ρ ≫ π ≫ q = V.p)
    (fl : ∀ σ, Vert.Flag ((Scheme.Modules.pullback π).obj (E σ)) (O.S.Dw.mult σ))
    (fl' : ∀ σ, Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj (E' σ))) (O.S.Dw.mult σ)),
    IsArithVar (π ≫ q) (O.var c).dim ∧ FlagChain.IsCov (π ≫ q) (O.var c).dim ρ ∧ IsFlagBundle π E O.S.Dw.mult fl ∧
    (∀ σ, Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map (u σ))) ((fl σ).pull ρ) (fl' σ)) ∧
    (∀ z : Letter O.S.Dw, V.Induces (lineAdl O R c (.inl (z.1, z.2)) 1)
      ((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ w) 1) ∧
    ∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z → V.Induces (lineAdl O R c (.inr k) 1)
      (VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ w)) 1

end GlobalTheory.TwoLat

end
