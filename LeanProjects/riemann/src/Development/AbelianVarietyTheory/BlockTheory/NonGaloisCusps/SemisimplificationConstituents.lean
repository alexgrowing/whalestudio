import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Rep

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

def IsSemisimplificationOf {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) : Prop :=
  IsSS s ∧ ∃ (m : ℕ) (Ws : Fin m → Submodule k W) (e : W ≃ₗ[k] V),
    (∀ j, Stable s (Ws j)) ∧ DirectSum.IsInternal Ws ∧
    ∀ j g, ∀ v ∈ Ws j, ρ g (e v) - e (s g v) ∈ (⨆ j' ∈ Set.Iio j, Ws j').map (e : W →ₗ[k] V)

def IsIrred {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k Γ V) : Prop :=
  (⊤ : Submodule k V) ≠ ⊥ ∧ ∀ U : Submodule k V, Stable ρ U → U = ⊥ ∨ U = ⊤

def blockSum {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) :
    Representation k Γ ((Fin r → k) × (Fin t → k)) where
  toFun g := LinearMap.prodMap (matRep ρ g)
    (LinearMap.pi fun c => ((χ c g : kˣ) : k) • (LinearMap.proj c : (Fin t → k) →ₗ[k] k))
  map_one' := by
    refine LinearMap.ext fun u => Prod.ext ?_ (funext fun c => ?_) <;> simp
  map_mul' g h := by
    refine LinearMap.ext fun u => Prod.ext ?_ (funext fun c => ?_) <;> simp [mul_assoc]

theorem blockSum_apply {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) (g : Γ)
    (u : (Fin r → k) × (Fin t → k)) :
    blockSum ρ χ g u = ((ρ g).mulVec u.1, fun c => ((χ c g : kˣ) : k) * u.2 c) := by
  refine Prod.ext ?_ (funext fun c => ?_)
  · rfl
  · rfl

theorem isSemisimplificationOf_self {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k Γ V)
    (h : IsSS ρ) : IsSemisimplificationOf ρ ρ := by
  refine ⟨h, 1, fun _ => ⊤, LinearEquiv.refl k V, fun _ _ _ _ => trivial, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨iSupIndep_subsingleton _, by simp⟩
  · intro j g v _
    simp

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

abbrev RepFam : Type := D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))

def matAlong {a : ℕ} {L : Type} [Field L] (f : D.nd.O i →+* L) (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) :
    GE D.nd →* Matrix (Fin a) (Fin a) L :=
  mapM f ((Units.coeHom _).comp ρ)

def chiAlong {L : Type} [Field L] (f : D.nd.O i →+* L) (c : Fin D.R.t) : GE D.nd →* Lˣ :=
  (Units.map f.toMonoidHom).comp (D.nd.chi i ((c : ℕ) + 1))

def redK {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) :
    Representation (kk D.nd i) (GE D.nd) (Fin a → kk D.nd i) :=
  matRep (matAlong D i (IsLocalRing.residue (D.nd.O i)) ρ)

theorem repK_eq (r : RepFam D i) (x : D.nd.X i) :
    repK D.nd i r x = matRep (matAlong D i (toK D.nd i) (r x)) := rfl

def Realised : Prop := ∃ r : RepFam D i, GoodR D.nd i r

def ConstituentsAbsIrrDistinct : Prop :=
  ∀ r : RepFam D i, GoodR D.nd i r → ∀ x, AbsIrrDistinct (repK D.nd i r x)

def ResidualCommon : Prop :=
  ∃ s : Representation (kk D.nd i) (GE D.nd) (Fin D.R.nV → kk D.nd i),
    ∀ r : RepFam D i, GoodR D.nd i r → ∀ x, IsSemisimplificationOf s (redK D i (r x))

def ConstituentsAt : Prop := Realised D i ∧ ConstituentsAbsIrrDistinct D i ∧ ResidualCommon D i

def GoodRowPoint (x₀ : D.nd.X i) : Prop :=
  ∃ (σ : D.what₂.FT) (P : D.naut.AV i),
    D.nd.goodRow σ ∧ thetaOf D.nd D.naut i σ P ∧ D.naut.ptV i P = some x₀

def OffBlock (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e (matRep (matAlong D i (toK D.nd i) r₀) g u) =
      blockSum (matAlong D i (toK D.nd i) ρ) (chiAlong D i (toK D.nd i)) g (e u)

def residualBlockSum (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    Representation (kk D.nd i) (GE D.nd) ((Fin D.R.r → kk D.nd i) × (Fin D.R.t → kk D.nd i)) :=
  blockSum (matAlong D i (IsLocalRing.residue (D.nd.O i)) ρ)
    (chiAlong D i (IsLocalRing.residue (D.nd.O i)))

def ResidualShape (r : RepFam D i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  (∀ x, IsSemisimplificationOf (residualBlockSum D i ρ) (redK D i (r x))) ∧
    IsIrred (redK D i ρ) ∧ 1 < D.R.r

def ResidualShapeAt : Prop :=
  ∀ r : RepFam D i, GoodR D.nd i r → ∀ x₀, GoodRowPoint D i x₀ →
    (∃ ρ, OffBlock D i (r x₀) ρ) ∧ ∀ ρ, OffBlock D i (r x₀) ρ → ResidualShape D i r ρ

end Loc

def TypeHypothesis (D : D7) : Prop := 100 ≤ D.R.r ∧ ∀ k, 2 * D.R.r ≤ D.host.g k

def Constituents_at (D : D7) : Prop := ∀ i, ConstituentsAt D i

def ResidualShape_at (D : D7) : Prop := TypeHypothesis D → ∀ i, ResidualShapeAt D i

def ConstituentsAndShape_at (D : D7) : Prop := Constituents_at D ∧ ResidualShape_at D

def ConstituentsAndShapeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstituentsAndShape_at (Fm.D x i)

def ConstituentsAndShape (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstituentsAndShapeF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

end
