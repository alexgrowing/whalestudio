import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsOrb

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

open Classical in

def gOf (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : Fin nV → GL (Fin (m + 1)) Qq :=
  if h : ∀ v, IsLattice W (Lt v) then Classical.choose (exists_tupOf W Lt h) else 1

theorem gOf_spec (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v)) : Lt = tupOf W (gOf Lt) := by
  unfold gOf
  rw [dif_pos h]
  exact Classical.choose_spec (exists_tupOf W Lt h)

def clsC (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (i : compL L p)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : ClassSet (HA sp) (KA L) :=
  clsG I hdet i (fun v => toF I hk v (gOf Lt v))

theorem clsC_eq (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (i : compL L p)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    clsC I hdet hk i Lt = Fib.mkC (HA sp) (KA L) (repP L p i * jQ I hdet hk (gOf Lt)) := rfl

theorem prP_repP (I : LocId L p nV W Qq) (hk : m + 1 = R.k) (i : compL L p) : prP I hk (repP L p i) = 1 := by
  funext v
  rw [prP_apply, repP_over L p i (I.plc v) (I.pl v).2, map_one, map_one]
  rfl

theorem act_eq_prP (I : LocId L p nV W Qq) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : Fin nV)
    (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y) :
    (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).act v γ =
      prP I hk (ratA sp γ.1) v := by
  rw [prP_ratA, MulEquiv.eq_symm_apply]
  exact levC_act sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y v γ

theorem orb_iff (I : LocId L p nV W Qq) (hk : m + 1 = R.k) (y : GA sp) (g g' : Fin nV → GL (Fin (m + 1)) Qq) :
    (∃ γ ∈ HA sp, y⁻¹ * γ * y ∈ KA' L p ∧ g'⁻¹ * (prP I hk γ * g) ∈ stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) ↔
      ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _),
        tupOf W g' = fun v => gMap W (prP I hk (ratA sp γ.1) v) (tupOf W g v) := by
  have key : ∀ γ : GA sp, g'⁻¹ * (prP I hk γ * g) ∈ stabTup (nV := nV) (k := m + 1) (Qq := Qq) W ↔
      tupOf W g' = fun v => gMap W (prP I hk γ v) (tupOf W g v) := by
    intro γ
    rw [← tupOf_eq_iff, eq_comm]
    have : tupOf W (prP I hk γ * g) = fun v => gMap W (prP I hk γ v) (tupOf W g v) := by
      funext v
      exact gMap_mul W _ _ _
    rw [this]
  constructor
  · rintro ⟨γ, hγ, h1, h2⟩
    obtain ⟨γ0, rfl⟩ := exists_ratA γ hγ
    exact ⟨⟨γ0, (mem_gamC_iff y γ0).2 h1⟩, (key _).1 h2⟩
  · rintro ⟨γ, h⟩
    exact ⟨ratA sp γ.1, ratA_mem _, (mem_gamC_iff y γ.1).1 γ.2, (key _).2 h⟩

theorem clsC_tupOf (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (hH : HypAtP I) (i : compL L p)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    clsC I hdet hk i (tupOf W g) = Fib.mkC (HA sp) (KA L) (repP L p i * jQ I hdet hk g) := by
  rw [clsC_eq]
  refine ((fibP I hdet hk hH).cls_iff (HA sp) (repP L p) (repP_mk L p) (prP_repP I hk) i i _ _).2
    ⟨rfl, 1, Subgroup.one_mem _, ?_, ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · show g⁻¹ * (prP I hk 1 * gOf (tupOf W g)) ∈ _
    rw [map_one, one_mul, ← tupOf_eq_iff]
    exact (gOf_spec (tupOf W g) (tupOf_lat W g)).symm

section Main

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)

include hH in

theorem class_eq_iff_translate_level_zero (i i' : compL L p) (Lt Lt' : Fin nV → Submodule W (Fin (m + 1) → Qq))
    (h : ∀ v, IsLattice W (Lt v)) (h' : ∀ v, IsLattice W (Lt' v)) :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i : GL (Fin R.k) _),
        Lt' = fun v => gMap W (prP I hk (ratA sp γ.1) v) (Lt v) := by
  rw [clsC_eq, clsC_eq]
  refine ((fibP I hdet hk hH).cls_iff (HA sp) (repP L p) (repP_mk L p) (prP_repP I hk) i i' (gOf Lt) (gOf Lt')).trans
    (and_congr_right fun _ => ?_)
  refine (orb_iff I hk (repP L p i) (gOf Lt) (gOf Lt')).trans (exists_congr fun γ => ?_)
  rw [← gOf_spec Lt' h', ← gOf_spec Lt h]

theorem level_action_lattice_eq (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt =
      fun v => gMap W (prP I hk (ratA sp γ.1) v) (Lt v) := by
  funext v
  rw [← act_eq_prP I hS r lam0 dom hk ψ y v γ]
  rfl

end Main

end Formalism.L2.G.Cmp
