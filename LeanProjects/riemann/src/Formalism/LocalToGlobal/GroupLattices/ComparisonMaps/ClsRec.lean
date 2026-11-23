import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsStab

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

def clsR (i : compL L p) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : C.cls 0 :=
  clsOf L (clsC I hdet hk i Lt)

include hH in
theorem stab_card1 (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v)) :
    Nat.card {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt} =
      Nat.card (C.stab 0 (clsR hk I hdet i Lt)) := by
  have h1 := (Nat.card_congr (fixEquiv hS r lam0 dom hk I ψ hdet hH i y hy (gOf Lt))).trans (card_stabU _)
  rw [← gOf_spec Lt h] at h1
  exact h1

include hH hdet in
theorem trivStab1 (hT : TrivStabU L) (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v))
    (hfix : (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt = Lt) :
    γ = 1 := by
  rw [level_action_lattice_eq] at hfix
  have h1 := (fix_iff hk I hdet hH i (gOf Lt) γ.1).2 ⟨hy ▸ γ.2, by rw [← gOf_spec Lt h]; exact hfix⟩
  exact Subtype.ext (hT _ _ h1)

set_option maxHeartbeats 2000000 in
include hH in

theorem clsR_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsR hk I hdet i Lt = clsR hk I hdet i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  clsOf_inj.eq_iff.trans (clsC_iff hS r lam0 dom hk I ψ e hdet hH i i' Lt Lt' h h')

include hH in

theorem clsR_surj (c : C.cls 0) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsR hk I hdet i Lt = c := by
  obtain ⟨c', rfl⟩ := clsOf_surj (L := L) c
  obtain ⟨i, Lt, h1, h2⟩ := clsC_surj hS r lam0 dom hk I ψ e hdet hH c'
  exact ⟨i, Lt, h1, congrArg (clsOf L) h2⟩

set_option maxHeartbeats 2000000 in
include hH in

theorem stab_card (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt) :
    Nat.card {γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ //
      ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt = Lt} = Nat.card (C.stab 0 (clsR hk I hdet i Lt)) :=
  stab_card1 hS r lam0 dom hk I ψ hdet hH i _ rfl Lt h

set_option maxHeartbeats 2000000 in
include hH hdet in

theorem trivStab (hT : TrivStabU L) : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).TrivStab :=
  fun i γ Lt h hfix => trivStab1 hS r lam0 dom hk I ψ hdet hH hT i _ rfl γ Lt h hfix

end Formalism.L2.G.Cmp
