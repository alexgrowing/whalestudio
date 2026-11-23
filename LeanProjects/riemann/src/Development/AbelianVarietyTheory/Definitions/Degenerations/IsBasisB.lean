import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.Ser
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UT
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

def ThetaSys.Real.Crd (ρ : S.Real) {K : Type} [CommRing K] (a : Sp K ⟶ ρ.P.A.left) (v : S.J → K) : Prop :=
  ∃ a' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left, a' ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = a ∧
    GlobalTheory.ZH.Crd (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s a' v

def FamOf {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ}
    (f : ∀ α, D.SecB k α) (s : Fam D F k) : Prop :=
  ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (f α)
    (DegPre.prB D F).left 1

def IsBasisB {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {k : ℕ} {α : D.X} {I : Type} [Fintype I]
    (β : I → D.SecB k α) : Prop :=
  ∀ gm₀ : D.SecB k α, ∃! a : I → V, ∀ j, gm₀.f j = ∑ i, constFn D.P.A.hom _ (a i) * (β i).f j
namespace ThetaSys.Real.UTest
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def j : u.V →+* OO p :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).codRestrict (OO p)
    (fun x => (mem_OO_iff _).2 ((u.norm_le _).2 ⟨x, rfl⟩))

abbrev H (k : ℕ) : LB u.G.left := LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => 𝟙 u.G.left) (fun _ => (k : ℤ))

abbrev PtC : Type := TFK (R := u.V) (PadicAlgCl p) ⟶ (Over.pullback (jK u.V)).obj u.G

def toG (a : u.PtC) : Sp (PadicAlgCl p) ⟶ u.G.left := a.left ≫ pullback.fst u.G.hom (jK u.V)

def toA (a : u.PtC) : Sp (PadicAlgCl p) ⟶ ρ.P.A.left := a.left ≫ u.U.gen.hom.left ≫ u.φ

def Int (a : u.PtC) : Prop := ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a
open Classical in

def Basis (l : u.Lab) (k : ℕ) {J : Type} [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X)
    (f : J → ∀ α, u.D.toPre.SecB k α) : Prop :=
  (∀ i, Short l.q k (cls i)) ∧ (∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') ∧
  (∀ α, ∃ i m, α = cls i + k • m) ∧ (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) ∧
  (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) ∧
  (∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, (f i α).f j = 0) ∧
  ∀ i₀, IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))

def IntGood (J : ((TF (R := u.V) (PadicAlgCl p)).left ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι) : Prop :=
  ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j →
    ⊤ ≤ ψ ⁻¹ᵁ u.D.toPre.P.L.U (J (gPt p ≫ ψ))

def GtN (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) : Prop :=
  ∀ J, u.IntGood J → ∀ χ, ‖valF (𝟙 (Sp (PadicAlgCl p))) _
    ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ = Real.exp (-ν χ)

def ParAt (k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)) : Prop :=
  ∀ w : Frm u.D.toPre (PadicAlgCl p) k g.b, w.IsGen → ∀ l : u.U.LG.L.ι, ⊤ ≤ u.toG a ⁻¹ᵁ u.U.LG.L.U l →
    ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (s : Fam u.D.toPre (PadicAlgCl p) k),
      u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → HasSum (fun χ => coef s g w χ)
        (κ * valF (show Sp (PadicAlgCl p) ⟶ _ from (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left) _ (σ.f (fun _ => l)))

abbrev lev (e : ℕ) : Ideal (OO p) := (IsLocalRing.maximalIdeal u.V ^ (e + 1)).map u.j

def Lev (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) : Prop :=
  ∃ b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left, gPt p ≫ b₀ = g.b.left ∧
    ∀ (e : ℕ) (ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left),
      ce ≫ (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c →
      ce ≫ (u.U.gt e).pG.left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀ ∧
      ∀ (χ : u.D.toPre.X) (jj : Fin 4 → u.D.toPre.P.L.ι),
        ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt e).pG χ) jj →
        ∃ x : OO p, (x : PadicAlgCl p) = valF (𝟙 (Sp (PadicAlgCl p))) _ ((g.s χ).s jj).val ∧
          Ideal.Quotient.mk (u.lev e) x = valR ce _ (((u.U.gt e).t χ).s jj).val
attribute [local instance] SplitExt.free SplitExt.finite

structure FibOf (N : ℕ) where
  Φ : FibPre (kb p)
  r : Φ.G.left ⟶ u.G.left
  cart : IsGrpPullback Φ.G u.G (rPt p ≫ spMap u.j) r
  xe : Φ.E.X ≃+ u.D.toPre.X
  pol : Φ.Pol N
  dim : pol.PB.g = u.D.toPre.P.g
  red : ∀ α, u.D.toPre.SecB N α → (Φ.H 1).Sec
  pure : ∀ α β, Φ.Pure (xe.symm α) (red α β)
  lin : ∀ α (I : Type) [Fintype I] (β : I → u.D.toPre.SecB N α) (a : I → u.V) (gm₀ : u.D.toPre.SecB N α),
    (∀ j, gm₀.f j = ∑ i, constFn u.D.toPre.P.A.hom _ (a i) * (β i).f j) →
    IsLin Φ.G.hom (fun i => red α (β i)) (fun i => IsLocalRing.residue (OO p) (u.j (a i))) (red α gm₀)
  basis : ∀ α (I : Type) [Fintype I] (β : I → u.D.toPre.SecB N α), IsBasisB u.D.toPre β →
    ∀ φ : (Φ.H 1).Sec, Φ.Pure (xe.symm α) φ → ∃! a : I → kb p, IsLin Φ.G.hom (fun i => red α (β i)) a φ
  exp : ∀ (J : Type) (σ : J → (u.H N).Sec) (f : J → ∀ α, u.D.toPre.SecB N α),
    (∀ i, u.U.toUnifPre.ExpandsAt 0 N (σ i) (f i)) → ∃ F : J → (Φ.H 1).Sec,
      (∀ i α, Φ.IsPart (xe.symm α) (F i) (red α (f i α))) ∧
      ∀ (x : Φ.Pt) (v : J → kb p), GlobalTheory.ZH.Crd (Φ.H 1) F x.left v → GlobalTheory.ZH.Crd (u.H N) σ (x.left ≫ r) v

def Link (σ : S.J → (u.H S.N).Sec) (b : Matrix S.J S.J (FractionRing u.V)) : Prop :=
  ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), ρ.Crd (u.toA a) v →
    GlobalTheory.ZH.Crd (u.H S.N) σ (u.toG a) ((b.map (algebraMap _ (PadicAlgCl p))).mulVec v)
end ThetaSys.Real.UTest

structure ThetaSys.Real.GeoTest (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) where
  u : ρ.UTest p y₀
  l : u.Lab
  τ : S.Test p y₀
  mt : l.Match τ
  σ : S.J → (u.H S.N).Sec
  cls : S.J → u.D.toPre.X
  mod : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls
  b : Matrix S.J S.J (FractionRing u.V)
  link : u.Link σ b
  span : τ.E = Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p))))
  wt : ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec
    (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i

def ThetaSys.Real.HasU (ρ : S.Real) : Prop := ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ Fs : Finset (PadicAlgCl p),
    ∃ (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀), l.Match τ ∧
      ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))

def ThetaSys.Real.HasGeo (ρ : S.Real) : Prop := ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p),
  (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ Fs : Finset (PadicAlgCl p),
    ∃ gm₀ : ρ.GeoTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing gm₀.u.V) (PadicAlgCl p))
end GlobalTheory.ZH
end
