import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie

attribute [local instance] Over.cartesianMonoidalCategory

section Lattice

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := R) (Chart.JetR R (Fin n) m) ⟶ G}

def lieAct (hx : Chart.IsUnivChart G n x) {O : Type} [CommRing O] (act : OAct O G) (a : O) :
    (Fin n → R) →ₗ[R] (Fin n → R) :=
  haveI := act.hom a
  Chart.tmap hx (act.act a)

def eigenLattice (hx : Chart.IsUnivChart G n x) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* R) :
    Submodule R (Fin n → R) where
  carrier := {c | ∀ a, lieAct hx act a c = τ a • c}
  zero_mem' a := by simp
  add_mem' {c c'} hc hc' a := by rw [map_add, hc a, hc' a, smul_add]
  smul_mem' r c hc a := by rw [map_smul, hc a, smul_comm]

theorem mem_eigenLattice_iff (hx : Chart.IsUnivChart G n x) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* R)
    (c : Fin n → R) :
    c ∈ eigenLattice hx act τ ↔ ∀ a, Chart.tvec (x := x) c ≫ act.act a =
      Chart.spMap (Chart.scaleD (τ a)) ≫ Chart.tvec (x := x) c := by
  refine forall_congr' fun a => ?_
  have := act.hom a
  rw [← Chart.tvec_tmap hx, ← Chart.tvec_smul hx]
  constructor
  · intro h
    exact congrArg _ h
  · intro h
    exact (Chart.tcoord_tvec hx _).symm.trans
      ((Chart.tcoord_congr hx h _ (Chart.isTan_tvec hx _)).trans (Chart.tcoord_tvec hx _))

example [IsDomain R] (hx : Chart.IsUnivChart G n x) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* R)
    (r : R) (hr : r ≠ 0) (c : Fin n → R) (h : r • c ∈ eigenLattice hx act τ) : c ∈ eigenLattice hx act τ := by
  intro a
  have := h a
  rw [map_smul, smul_comm] at this
  exact smul_right_injective _ hr this

end Lattice

section Extend

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

abbrev fstOver (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : DualNumber S →ₐ[R] S :=
  (Chart.fstD S).restrictScalars R

variable {S}

abbrev scaleOver (R : Type) [CommRing R] [Algebra R S] (s : S) : DualNumber S →ₐ[R] DualNumber S :=
  (Chart.scaleD s).restrictScalars R

def dualLiftOver {n : ℕ} (c : Fin n → S) : Chart.JetR R (Fin n) 1 →ₐ[R] DualNumber S :=
  Chart.jetLift R (RingHom.ker (Chart.fstD S)) Chart.kerD_sq (fun j => TrivSqZeroExt.inr (c j))
    (fun _ => Chart.inr_mem_kerD _)

def tvecOver {G : Over (Spec (CommRingCat.of R))} {n : ℕ}
    (x : ∀ m : ℕ, Chart.sp (R₀ := R) (Chart.JetR R (Fin n) m) ⟶ G) (c : Fin n → S) :
    Chart.sp (R₀ := R) (DualNumber S) ⟶ G :=
  Chart.spMap (dualLiftOver c) ≫ x 1

def extendLin (S : Type) [CommRing S] [Algebra R S] {n : ℕ} (T : (Fin n → R) →ₗ[R] (Fin n → R)) :
    (Fin n → S) →ₗ[S] (Fin n → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' T).map (algebraMap R S))

example {G : Over (Spec (CommRingCat.of R))} {n : ℕ}
    (x : ∀ m : ℕ, Chart.sp (R₀ := R) (Chart.JetR R (Fin n) m) ⟶ G) (c : Fin n → R) :
    tvecOver x c = Chart.tvec (x := x) c := rfl

example {n : ℕ} (T : (Fin n → R) →ₗ[R] (Fin n → R)) : extendLin R T = T := by
  simp [extendLin]

end Extend

def TangentBaseChange : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (x : ∀ m : ℕ, Chart.sp (R₀ := R) (Chart.JetR R (Fin n) m) ⟶ G) (hx : Chart.IsUnivChart G n x)
    (S : Type) [CommRing S] [Algebra R S],
    (∀ c : Fin n → S, Chart.spMap (fstOver R S) ≫ tvecOver x c = 1) ∧
    (∀ w : Chart.sp (R₀ := R) (DualNumber S) ⟶ G, Chart.spMap (fstOver R S) ≫ w = 1 →
      ∃! c : Fin n → S, w = tvecOver x c) ∧
    (∀ c c' : Fin n → S, tvecOver x (c + c') = tvecOver x c * tvecOver x c') ∧
    (∀ (s : S) (c : Fin n → S), tvecOver x (s • c) = Chart.spMap (scaleOver R s) ≫ tvecOver x c) ∧
    ∀ (f : G ⟶ G) [IsMonHom f] (c : Fin n → S),
      tvecOver x c ≫ f = tvecOver x (extendLin S (Chart.tmap hx f) c)

def EigenLatticeRank : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (t : SAB H (Sp V)) (k : Type) [Field k] [IsAlgClosed k] (j : V →+* k), Function.Injective j →
    ∀ ρ : k, ρ ^ 2 = -(H.d : k) → DetCond D t.act (Geo.Tor.spMap j) ρ →
    ∀ (n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := V) (Chart.JetR V (Fin n) m) ⟶ t.G) (hx : Chart.IsUnivChart t.G n x)
      (τ : 𝓞 E →+* V),
      (j (τ H.rt) = ρ → Module.finrank V (eigenLattice hx t.act τ) = D.p) ∧
      (j (τ H.rt) ≠ ρ → Module.finrank V (eigenLattice hx t.act τ) = D.q)

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie
