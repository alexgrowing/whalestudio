import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev gl (g : Br.G D.nbr i w hw) : GE D.nd := ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)

def vecL {a : ℕ} (v : Fin a → Fin D.R.nV → KK D.nd i) : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw :=
  fun b j => Br.toLLK (D.nbr i w hw) (v b j)

def spanL {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (vecL i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (v j)) =
      fun j => Br.toLLK (D.nbr i w hw) ((mapM (toK D.nd i) M (gl i w hw g)).mulVec v j) := by
  funext j
  rw [RingHom.map_mulVec]
  congr 1
  ext p q
  simp [Br.loc, Br.locM, Br.locO, mapM, Br.iota, Br.toLLK_alg]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem contTw (hr : GoodR D.nd i r) (x : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw) :
    Continuous fun g => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec v :=
  (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.T.twisted_dual_families_continuous D i r hr x).1).matrix_mulVec continuous_const

def sumG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GRep.sum (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) (contTw i w hw r Xs hr) x

def actK {a : ℕ} (x : Fin a → ↥Xs) (γ : GE D.nd) (v : Fin a → Fin D.R.nV → KK D.nd i) :
    Fin a → Fin D.R.nV → KK D.nd i :=
  fun b => (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ).mulVec (v b)

theorem sumG_vecL (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs) (g : Br.G D.nbr i w hw)
    (v : Fin a → Fin D.R.nV → KK D.nd i) :
    (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) = vecL i w hw (actK i r Xs x (gl i w hw g) v) := by
  funext b
  exact loc_mulVec i w hw _ g (v b)

theorem spanL_stable (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ spanL i w hw Y, (sumG i w hw r Xs hr x).ρ g u ∈ spanL i w hw Y := by
  intro g u hu
  have h : spanL i w hw Y ≤ (spanL i w hw Y).comap ((sumG i w hw r Xs hr x).ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show (sumG i w hw r Xs hr x).ρ g (vecL i w hw y) ∈ spanL i w hw Y
    rw [sumG_vecL]
    exact Submodule.subset_span ⟨_, hst _ y hy, rfl⟩
  exact h hu

def XG (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  (sumG i w hw r Xs hr x).sub (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst)

def latY {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y) :=
  Submodule.span _ {u | (u : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) ∈ vecL i w hw '' (Y : Set _)}

def yfun {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) : ↥(spanL i w hw Y) :=
  ⟨vecL i w hw (actK i r Xs x (gl i w hw g) E - E), Submodule.subset_span ⟨_, hE _, rfl⟩⟩

end GlobalTheory.Pass.LocDual.OneX

end
