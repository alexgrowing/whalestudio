import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.SelFun

def Tors (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (B : Type) [AddCommGroup B] [Module Λ B] : Prop :=
  ∀ b : B, ∃ n : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, x • b = 0

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']

theorem repOn_map (f : B →ₗ[Λ] B') (g : Γ) (m : Fin r → B) :
    f.compLeft (Fin r) (repOn ρ κ B g m) = repOn ρ κ B' g (f.compLeft (Fin r) m) := by
  funext a
  simp [repOn, matAct, map_sum, Finset.smul_sum]

variable [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']

def h1Map (f : B →ₗ[Λ] B') : H1 (repOn ρ κ B) →ₗ[Λ] H1 (repOn ρ κ B') :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (repOn_map ρ κ f)

def h1MapSubgroup (U : Subgroup Γ) (f : B →ₗ[Λ] B') :
    H1 ((repOn ρ κ B).comp U.subtype) →ₗ[Λ] H1 ((repOn ρ κ B').comp U.subtype) :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (fun g m => repOn_map ρ κ f g.1 m)

end Maps

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  (Q : Finset (PlE D.host))

def Setup : Prop :=
  GalHyp bkP i s ∧ IsLocalHom (algebraMap (X.O0 i) Λ) ∧ Module.Finite (X.O0 i) Λ ∧
    IsOpen (κ.ker : Set (GE N)) ∧ (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) ∧ TrivAbove κ (X.l i) ∧
    (∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i)) ∧
    ∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, κ σ = 1

def SelMaps : Prop :=
  ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B'),
    (selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ f) ≤ selOn bkP i (Tgl i s) κ B' Q

def NoInv : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    H0 (repOn (Tgl i s) κ B) = ⊥

def LocSat : Prop :=
  ∀ v ∈ placesOver D.host.E (X.l i),
  ∀ (B' B : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ f : B' →ₗ[Λ] B, Function.Injective f → ∀ y : H1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype),
      h1MapSubgroup (Tgl i s) κ (DecV N v) f y ∈ bkOn bkP i (Tgl i s) κ B v → y ∈ bkOn bkP i (Tgl i s) κ B' v

def SelLeft : Prop :=
  ∀ (B' B B'' : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], Tors Λ B → Tors Λ B'' →
    ∀ (f : B' →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g →
      Function.Injective (h1Map (Tgl i s) κ f) ∧
      ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, h1Map (Tgl i s) κ g y = 0 →
        ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ f x = y

def SelColim : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, ∃ B' : Submodule Λ B, B'.FG ∧
      ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ B'.subtype x = y

def LocCount : Prop :=
  ∀ (K : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K], IsSimpleModule Λ K →
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ K v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        Nat.card K ^ (D.R.f * D.R.r)

def SelObs : Prop :=
  ∀ (K B B'' : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K]
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], IsSimpleModule Λ K → Tors Λ B →
    ∀ (f : K →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g → Function.Surjective g →
      Finite (selOn bkP i (Tgl i s) κ K Q) ∧
      Finite (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ∧
      Nat.card (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ≤ Nat.card (selOn bkP i (Tgl i s) κ K Q)

open CategoryTheory in

def KernelRep : Prop :=
  ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
    (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ y : F.obj B, ∃ B' : Submodule Λ B, B'.FG ∧
      y ∈ LinearMap.range (F.map (ModuleCat.ofHom B'.subtype)).hom) →
    (∀ (K B B'' : ModuleCat.{0} Λ), IsSimpleModule Λ K → Tors Λ B → ∀ (f : K ⟶ B) (g : B ⟶ B''),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
      Finite (F.obj K) ∧ Finite (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ∧
        Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ≤ Nat.card (F.obj K)) →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
      ∃ e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] F.obj B),
        ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B')
          (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ))),
          (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x)

end GlobalTheory.SelFun
