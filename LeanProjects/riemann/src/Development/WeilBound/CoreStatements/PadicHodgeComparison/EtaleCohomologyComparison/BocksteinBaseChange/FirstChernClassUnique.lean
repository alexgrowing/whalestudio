import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop} {C : PerC R}

structure XEnd (I : Iso l K C.K₀) : Type 2 where
  Ln : Model l K → Type 1
  oneT : ∀ M : Model l K, M.T 0 → Prop
  c1T : ∀ {M : Model l K}, Ln M → M.T 2 → Prop
  oneD : ∀ M : Model l K, I.D M 0 → Prop
  c1D : ∀ {M : Model l K}, Ln M → I.D M 2 → Prop
  cupD : ∀ (M : Model l K) (i j : ℕ), I.D M i →ₗ[C.K₀] I.D M j →ₗ[C.K₀] I.D M (i + j)

variable {I : Iso l K C.K₀}

structure CrysCmp.Plus (c : CrysCmp G C I) (X : XEnd I) (N : ℕ) : Prop where
  cup : ∀ (M : Model l K), G M → ∀ {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)), M.CupT x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i)) (b' : Module.Basis (Fin m') C.K₀ (I.D M j))
      (f : Module.Dual C.K₀ (I.D M (i + j))), c.c M (i + j) (M.toV _ z) f =
        ∑ s, ∑ s', c.c M i (M.toV _ x) (b.coord s) * c.c M j (M.toV _ y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
  one : ∀ (M : Model l K), G M → ∀ v y, X.oneT M v → X.oneD M y → ∀ f, c.c M 0 (M.toV 0 v) f = C.k (f y)
  c1 : ∀ (M : Model l K), G M → ∀ (L : X.Ln M) v y, X.c1T L v → X.c1D L y → ∀ f,
    (l : C.C) ^ N * C.c R.t * c.c M 2 (M.toV 2 v) f = C.k (f y)

structure XMid (D : Dat R) (X : XEnd I) : Type 2 where
  one' : ∀ {M : Model l K} (a : D.Ch M), (D.H' a).N 0 → Prop
  cup' : ∀ {M : Model l K} (a : D.Ch M) {i j : ℕ}, (D.H' a).N i → (D.H' a).N j → (D.H' a).N (i + j) → Prop
  c1' : ∀ {M : Model l K} (a : D.Ch M), X.Ln M → (D.H' a).N 2 → Prop
  c1A : ∀ {M : Model l K} (a : D.Ch M), X.Ln M → (D.A a).N 2 → Prop

structure XLaws {D : Dat R} {X : XEnd I} (Y : XMid D X) (e : EMap G D) (β : BMap G D) (β₁ : BPhi β) (F : FMap G C I D β₁.pull) : Prop where
  e_one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ v, X.oneT M v → (D.A a).one (e.e a 0 v)
  etale_firstChern : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (L : X.Ln M) v, X.c1T L v → Y.c1A a L (R.t • e.e a 2 v)
  first_chern_class_unique : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (L : X.Ln M) x y, Y.c1A a L x → Y.c1A a L y → x = y
  one_ex : ∀ {M : Model l K} (a : D.Ch M), G M → ∃ x, Y.one' a x
  cup_ex : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H' a).N i) (y : (D.H' a).N j), ∃ z, Y.cup' a x y z
  first_chern_class_exists : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ L : X.Ln M, ∃ x, Y.c1' a L x
  β_one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x, Y.one' a x → (D.A a).one (β.β' a 0 x)
  β_cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H' a).N i) (y : (D.H' a).N j) (z : (D.H' a).N (i + j)),
    Y.cup' a x y z → (D.A a).cup (β.β' a i x) (β.β' a j y) (β.β' a (i + j) z)
  beta_firstChern : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (L : X.Ln M) x, Y.c1' a L x → Y.c1A a L (β.β' a 2 x)
  ψ_one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x y, Y.one' a x → X.oneD M y → ∀ f, F.ψ a 0 x f = C.k (f y)
  ψ_cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H' a).N i) (y : (D.H' a).N j) (z : (D.H' a).N (i + j)),
    Y.cup' a x y z → ∀ {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i)) (b' : Module.Basis (Fin m') C.K₀ (I.D M j))
      (f : Module.Dual C.K₀ (I.D M (i + j))),
      F.ψ a (i + j) z f = ∑ s, ∑ s', F.ψ a i x (b.coord s) * F.ψ a j y (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
  psi_firstChern : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (L : X.Ln M) x y, Y.c1' a L x → X.c1D L y →
    ∀ f, F.ψ a 2 x f = C.k (f y)

def ProductClassComparison : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (C : PerC R) (I : Iso l K C.K₀) (D : Dat R) (X : XEnd I) (Y : XMid D X), R.Facts → C.Facts → EtSide G → D.Laws G →
    ∀ (e : EMap G D) (β : BMap G D) (β₁ : BPhi β), PMap G D → ∀ F : FMap G C I D β₁.pull, XLaws Y e β β₁ F →
      ∃ c : CrysCmp G C I, c.Plus X F.k

end CrystallineSemistableComparison
