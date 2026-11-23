import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsMain

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)

include hH in

theorem class_eq_iff_translate_level_one (i i' : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (Lt Lt' : Fin nV → Submodule W (Fin (m + 1) → Qq))
    (h : ∀ v, IsLattice W (Lt v)) (h' : ∀ v, IsLattice W (Lt' v)) :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y,
        Lt' = (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt := by
  simp only [level_action_lattice_eq]
  subst hy
  exact class_eq_iff_translate_level_zero hk I hdet hH i i' Lt Lt' h h'

set_option maxHeartbeats 2000000 in
include hH in

theorem clsC_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  class_eq_iff_translate_level_one hS r lam0 dom hk I ψ hdet hH i i' _ rfl Lt Lt' h h'

include hH in

theorem clsC_surj (c : ClassSet (HA sp) (KA L)) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsC I hdet hk i Lt = c := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨i, g, hg⟩ := (fibP I hdet hk hH).cls_surj (HA sp) (repP L p) (repP_mk L p) x
  exact ⟨i, tupOf W g, tupOf_lat W g, (clsC_tupOf I hdet hk hH i g).trans hg⟩

include hH hdet in

theorem finClasses : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).FinClasses := by
  intro i
  have := finite_classSet_U L
  let f : {Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup //
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt} → ClassSet (HA sp) (KA L) :=
    fun Lt => clsC I hdet hk i Lt.1
  let s : Set.range f → (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup := fun c => (Classical.choose c.2).1
  have hs : ∀ c : Set.range f, f (Classical.choose c.2) = c.1 := fun c => Classical.choose_spec c.2
  refine ⟨(Set.finite_range s).toFinset, ?_, ?_⟩
  · intro L0 hL0
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hL0
    exact (Classical.choose c.2).2
  · intro Lt hLt
    let c : Set.range f := ⟨f ⟨Lt, hLt⟩, Set.mem_range_self _⟩
    refine ⟨s c, (Set.Finite.mem_toFinset _).2 ⟨c, rfl⟩, ?_⟩
    exact ((clsC_iff hS r lam0 dom hk I ψ e hdet hH i i (s c) Lt (Classical.choose c.2).2 hLt).1 (hs c)).2

end Formalism.L2.G.Cmp
