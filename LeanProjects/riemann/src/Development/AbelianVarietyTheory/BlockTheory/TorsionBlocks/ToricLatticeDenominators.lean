import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

def IsLatIn (V : Submodule (FractionRing R) W) (L : Submodule R W) : Prop :=
  L.FG ∧ Submodule.span (FractionRing R) (L : Set W) = V

def IsIdx (l : ℕ) (V : Submodule (FractionRing R) W) (L₁ L₂ : Submodule R W) (x : ℝ) : Prop :=
  IsLatIn V L₁ ∧ IsLatIn V L₂ ∧
    ∃ g : ↥V ≃ₗ[FractionRing R] ↥V, (∀ v : ↥V, (v : W) ∈ L₁ ↔ ((g v : ↥V) : W) ∈ L₂) ∧
      x = vK R l (LinearMap.det (g : ↥V →ₗ[FractionRing R] ↥V))

theorem vK_one (l : ℕ) : vK R l 1 = 0 := by
  have h := (IsLocalization.surj (nonZeroDivisors R) (1 : FractionRing R)).choose_spec
  rw [one_mul] at h
  have h' := IsFractionRing.injective R (FractionRing R) h
  simp only [vK]
  rw [h', sub_self]

omit [IsScalarTower R (FractionRing R) W] in

theorem isIdx_self (l : ℕ) (V : Submodule (FractionRing R) W) (L : Submodule R W) (h : IsLatIn V L) :
    IsIdx l V L L 0 := by
  refine ⟨h, h, LinearEquiv.refl _ _, fun v => Iff.rfl, ?_⟩
  simp [vK_one]

end Index

section Lattices

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

def eOp : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)) (Y.eAlg i b)

def AOp : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  ((Nat.card (G0g N) : ℕ) : FractionRing (X.O i)) • eOp Y i j b

def typePart : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  ⨅ u : Y.U, Module.End.eigenspace
    ((Y.actG i j b u : Y.Fm i j b ≃ₗ[FractionRing (X.O i)] Y.Fm i j b) :
      Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i))

def V0 : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  LinearMap.range (eOp Y i j b) ⊓ typePart Y i j b

def Theta : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) (Set.range (Y.th i j b))

def ATheta : Submodule (X.O i) (Y.Fm i j b) :=
  (Theta Y i j b).map ((AOp Y i j b).restrictScalars (X.O i))

def IsBasisSeries {n : ℕ} (d : Fin n → Y.Dat i j b) : Prop :=
  IsLatIn (V0 Y i j b) (ATheta Y i j b) ∧
    LinearIndependent (X.O i) (fun a => AOp Y i j b (Y.th i j b (d a))) ∧
    Submodule.span (X.O i) (Set.range fun a => AOp Y i j b (Y.th i j b (d a))) = ATheta Y i j b

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

abbrev FmExt : Type := FractionRing O' ⊗[X.O i] Y.Fm i j b

def eExt : FmExt Y i j b O' →ₗ[O'] FmExt Y i j b O' :=
  (((eOp Y i j b).restrictScalars (X.O i)).baseChange (FractionRing O')).restrictScalars O'

def invariantSpanBaseChange : Submodule (FractionRing O') (FmExt Y i j b O') :=
  Submodule.span (FractionRing O')
    ((fun x => (1 : FractionRing O') ⊗ₜ[X.O i] x) '' (V0 Y i j b : Set (Y.Fm i j b)))

def ThetaExt : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' ((fun x => (1 : FractionRing O') ⊗ₜ[X.O i] x) '' (Theta Y i j b : Set (Y.Fm i j b)))

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def incl : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.O i] FmExt Y i j b O' :=
  LinearMap.rTensor (Y.Fm i j b)
    ((IsScalarTower.toAlgHom (X.O i) O' (FractionRing O')).comp
      (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O')).toLinearMap

def ThetaPsi (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' (⋃ d ∈ {d : Y.Dat i j b | Disjoint (Y.lev i j b d) Q},
    incl Y i j b O' k '' Y.thPsi i j b k Q ψ d)

def ThetaMt (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) : Submodule O' (FmExt Y i j b O') :=
  Submodule.span O' ((fun f => incl Y i j b O' k (Y.thP i j b k Q ψ f)) ''
    (Y.MtLat i j b k Q ψ : Set (Y.MtV i j b k Q ψ)))

theorem thetaPsi_one : ThetaPsi Y i j b O' k ∅ 1 = ThetaExt Y i j b O' := by
  have hi : ∀ x : Y.Fm i j b, incl Y i j b O' k ((1 : X.Ok i k) ⊗ₜ[X.O i] x) =
      (1 : FractionRing O') ⊗ₜ[X.O i] x := by
    intro x; simp [incl]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro y hy
    simp only [Set.mem_iUnion, Y.thPsi_one, Set.image_singleton, Set.mem_singleton_iff, hi] at hy
    obtain ⟨d, -, rfl⟩ := hy
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨d, rfl⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      refine Submodule.subset_span ?_
      simp only [Set.mem_iUnion, Y.thPsi_one, Set.image_singleton, Set.mem_singleton_iff, hi]
      exact ⟨d, by simp, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul O' a]
      exact Submodule.smul_mem _ _ hx

end Lattices

section Statement

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def partBAt (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) (ε : ℝ) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']
    [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O'] [Module.Finite (X.Ok i k) O'],
    Function.Injective (algebraMap (X.Ok i k) O') →
    IsLatIn (invariantSpanBaseChange Y i j b O') ((ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O')) ∧
    (ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O') ≤
      (ThetaMt Y i j b O' k Q ψ).map (eExt Y i j b O') ∧
    ∀ M : Submodule O' (FmExt Y i j b O'), IsLatIn (invariantSpanBaseChange Y i j b O') M →
      ∃ x y : ℝ,
        IsIdx (X.l i) (invariantSpanBaseChange Y i j b O') M ((ThetaPsi Y i j b O' k Q ψ).map (eExt Y i j b O')) x ∧
        IsIdx (X.l i) (invariantSpanBaseChange Y i j b O') M ((ThetaExt Y i j b O').map (eExt Y i j b O')) y ∧
        x ≤ y + ε

def ThroughDel (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : GE N →* (X.Ok i k)ˣ) : Prop :=
  ∃ (M : ℕ) (ψ₀ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    1 ≤ M ∧ ψ = ψ₀.comp (Y.delU i Q M)

variable (bkP : BKPh X)

def exportAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i →
  ∃ (n : ℕ → Bool → ℕ) (d : ∀ j b, Fin (n j b) → bkP.ex.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IsBasisSeries bkP.ex i j b (d j b)) ∧
    ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (epsB : ℕ → Bool → ℝ),
      PsiOk i A Q k' ψ' ∧
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (a : Fin (n j b)), Disjoint (bkP.ex.lev i j b (d j b a)) Q) ∧
      ThroughDel bkP.ex i k' Q (ψ'.comp (X.art i Q)) ∧
      (∀ j b, 0 ≤ epsB j b) ∧ ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
        partA bkP i Q k' (ψ' ^ a) eps' ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
          partBAt bkP.ex i j b k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (epsB j b)) ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps'

theorem projectionDerivative_of_exportAt (N0 : X.Tw → ℕ) (i : X.Tw) (h : exportAt bkP N0 i) : ProjectionDerivativeEstimate bkP N0 i := by
  intro hs eps' he A
  obtain ⟨n, d, -, H⟩ := h hs
  obtain ⟨Q, k', ψ', epsB, h1, -, -, -, -, h2⟩ := H eps' he A
  obtain ⟨ha, hat, -, hc, hd⟩ := h2 1 isCoprime_one_left
  rw [zpow_one] at ha hat hc hd
  exact ⟨Q, k', ψ', h1, ha, hat, hc, hd⟩

end Statement

def aux₃ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → exportAt (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 i

def BoundedDenominatorsCase (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, Formalism.MainNotions.BlochKatoReduction.adm9 D N0 → aux₃ D (Formalism.MainNotions.BlochKatoReduction.bk0 D) N0

end GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators

end
