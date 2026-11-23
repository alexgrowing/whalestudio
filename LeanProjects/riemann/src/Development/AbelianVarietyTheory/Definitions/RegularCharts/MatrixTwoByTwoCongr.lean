import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable {O : Type} [CommRing O] {β : O →+* c.F}

structure MChart (Y : Model Xo c β) where
  U : Y.X.Opens
  hU : IsAffineOpen U
  dom : IsDomain Γ(Y.X, U)
  θ : ∀ i, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U i)
  θ_mem : θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U)
  θ_ne : ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i)
  n : ℕ
  v₀ : Fin n → (Sp (DualNumber Γ(Y.X, U)) ⟶ Y.t.G.left)
  ρ : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U)
  lie : ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, U) →+* R') (t' : SAB H (Sp R'))
    (m : SABMap t' Y.t (spMap f ≫ hU.fromSpec)), ∃ v' : Fin n → (epsR R' ⟶ t'.G),
      (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧
        ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a)

variable {Y : Model Xo c β}

structure MChart.Lift (M : MChart Y) {R : Type} [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R)
    (x : Sp R ⟶ Xo.X) where
  xF : Sp R ⟶ Xo.XF c
  xF_fst : xF ≫ pullback.fst _ _ = x
  xF_snd : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)
  xF_j : xF ≫ Y.j = spMap f ≫ M.hU.fromSpec
  t' : SAB H (Sp R)
  m' : SABMap t' Y.oF.t xF
  m1 : SABMap t' Xo.univ.t x
  m2 : SABMap t' Y.t (spMap f ≫ M.hU.fromSpec)
  liftedChartMap_eq : m1.φ = m'.φ ≫ Y.m0.toSABMap.φ
  matrix_two_by_two_congr : m2.φ = m'.φ ≫ Y.m.φ

variable {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

def MChart.Lift.Vec (Λ : M.Lift f x) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ (v' : Fin M.n → (epsR R ⟶ Λ.t'.G)) (u' : epsR R ⟶ Λ.t'.G),
    (∀ j, (v' j).left ≫ Λ.m2.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ M.v₀ j) ∧ IsLieComb cv v' u' ∧
      u'.left ≫ Λ.m1.φ = w

def MChart.Lift.LieTie (Λ : M.Lift f x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R)
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) : Prop :=
  ∀ τ i, Λ.Vec (fun j => u τ j i) (w τ i)

def MChart.Lift.ThTie (Λ : M.Lift f x) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (Y.t.PP.L.pull Λ.m2.φ))
    (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)),
    RigIso Λ.m1 w1 ∧ RigIso Λ.m2 w2 ∧ IsoMaps w1 σ s1 ∧
    (∀ (j : Y.t.PP.L.ι) (k : Λ.t'.PP.L.ι) (W : Λ.t'.G.left.Opens)
      (h₁ : W ≤ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j))
      (h₂ : W ≤ (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k),
      (Λ.m2.φ.appLE _ _ h₁).hom (M.θ j) =
        resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k)) ∧
    ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ →
      g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

def MChart.Comparison₂ (M : MChart Y) {R : Type} [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R)
    (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R) (y : FrPt Xo c R) : Prop :=
  ∃ Λ : M.Lift f y.x, Λ.LieTie u y.u ∧ Λ.ThTie y.s

def MChart.Eig (M : MChart Y) {R : Type} [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (τ : E →+* ℂ)
    (cv : Fin M.n → R) : Prop :=
  ∀ a : 𝓞 E, ((M.ρ a).map f).mulVec cv = algebraMap c.F R (embK c τ a) • cv

def InCell {R : Type} [CommRing R] {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) R) : Prop :=
  (∀ i j : Fin r, i < j → u (ix i) j = 0) ∧ ∀ i, u (ix i) i = 1

end GlobalTheory.Reg
