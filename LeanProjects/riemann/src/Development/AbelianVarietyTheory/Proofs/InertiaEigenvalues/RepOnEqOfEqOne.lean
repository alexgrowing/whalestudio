import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Colim

section General

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ] {B : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]

theorem exists_fg_cocycle [CompactSpace Γ] (z : Z1 (repOn ρ κ B)) :
    ∃ B' : Submodule Λ B, B'.FG ∧ ∃ z' : Z1 (repOn ρ κ B'), ∀ g a, ((z'.1 g a : B') : B) = z.1 g a := by
  have hfin : (Set.range fun p : Γ × Fin r => z.1 p.1 p.2).Finite := by
    have hc : Continuous fun p : Γ × Fin r => z.1 p.1 p.2 :=
      continuous_prod_of_discrete_right.2 fun a => (continuous_apply a).comp z.2.1
    exact (isCompact_range hc).finite_of_discrete
  refine ⟨Submodule.span Λ _, Submodule.fg_span hfin, ⟨fun g a => ⟨z.1 g a, Submodule.subset_span ⟨(g, a), rfl⟩⟩,
    continuous_pi fun a => ((continuous_apply a).comp z.2.1).subtype_mk _, fun g h => ?_⟩, fun g a => rfl⟩
  funext a
  apply Subtype.ext
  have e := congrFun (repOn_map ρ κ (Submodule.span Λ (Set.range fun p : Γ × Fin r => z.1 p.1 p.2)).subtype g
    (fun a => ⟨z.1 h a, Submodule.subset_span ⟨(h, a), rfl⟩⟩)) a
  have e2 := congrFun (z.2.2 g h) a
  exact e2.trans (congrArg (z.1 g a + ·) e.symm)

omit [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] in
theorem repOn_eq_of_eq_one {g : Γ} (h1 : ρ g = 1) (h2 : κ g = 1) (m : Fin r → B) : repOn ρ κ B g m = m := by
  have : repOn ρ κ B g = repOn ρ κ B 1 := by simp [repOn, h1, h2]
  rw [this, map_one, Module.End.one_apply]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tgl_eq_one (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) (v : PlE D.host)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (A : ValuationSubring N.Om) (hA : IsPlaceOver A v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) A) : Tgl i s σ = 1 := by
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  have h1 : X.rhoS i s σ = 1 := h.1 v hl hg A hA σ hσ
  have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg hp A hA σ hσ
  simp [Tgl, twGL, h1, h2]

theorem selColim : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelColim bkP i s κ Q := by
  intro D N X bkP i s Λ _ _ _ κ Q hSet _ hSat B _ _ _ _ hB y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨B', hfg, z', hz⟩ := exists_fg_cocycle (Tgl i s) κ z
  have hmap : h1Map (Tgl i s) κ B'.subtype (Submodule.Quotient.mk z') = Submodule.Quotient.mk z :=
    congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => hz g a))
  refine ⟨B', hfg, Submodule.Quotient.mk z', ?_, hmap⟩
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hy v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with hl hS
  · refine hSat v hl B' B hB B'.subtype B'.injective_subtype _ ?_
    rw [← hmap] at hv
    exact hv
  · trivial
  · have hS1 : v ∉ Spl i := fun h => hS (Or.inl h)
    have hQ : v ∉ Q := fun h => hS (Or.inr h)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hv)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
    have hg : (g.1.1 : GE N) ∈ Ine (F := D.host.E) (N.plOm.1 v) := g.2
    have e : z.1 g.1.1 = repOn (Tgl i s) κ B g.1.1 m - m := hm g
    rw [repOn_eq_of_eq_one _ _ (tgl_eq_one bkP i s hSet.1.1 v hl hS1 _ (N.plOm.2 v) _ hg)
      (hSet.2.2.2.2.2.2.2 v hQ _ (N.plOm.2 v) _ hg), sub_self] at e
    show z'.1 g.1.1 = repOn (Tgl i s) κ B' g.1.1 0 - 0
    rw [LinearMap.map_zero, sub_zero]
    funext a
    apply Subtype.ext
    exact (hz g.1.1 a).trans (congrFun e a)

end GlobalTheory.SelFun.Colim
