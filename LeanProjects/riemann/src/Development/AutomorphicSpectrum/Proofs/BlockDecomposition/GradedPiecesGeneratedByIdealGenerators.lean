import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

def liftSub {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e)
    (e : ℕ) (V : X.Opens) (W : Submodule Γ(X, V) Γ(gr hS e, V)) : Submodule Γ(X, V) Γ(P, V) where
  carrier := {t | ∃ x : Γ((lvl S e : X.Modules), V),
    (lvl S e).arrow.app V x = t ∧ (grπ hS e).app V x ∈ W}
  add_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, map_add _ _ _, by rw [map_add]; exact W.add_mem hx hy⟩
  zero_mem' := ⟨0, map_zero _, by rw [map_zero]; exact W.zero_mem⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl, hx⟩
    exact ⟨c • x, Scheme.Modules.Hom.app_smul _ _ _,
      by rw [Scheme.Modules.Hom.app_smul]; exact W.smul_mem c hx⟩

lemma incl_arrow_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (lvl S e).arrow.app V ((incl hS e).app V y) = (lvl S (e + 1)).arrow.app V y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_arrow]

lemma incl_grπ_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (grπ hS e).app V ((incl hS e).app V y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_grπ]
  rfl

lemma pow_smul_le_secs_lvl {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) (e : ℕ) (U : X.affineOpens) {n : Γ(P, U)}
    (hn : n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U))) : n ∈ secs (lvl S e) (U : X.Opens) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      change IsIso (⊤ : Subobject P).arrow
      infer_instance
    refine ⟨(inv (lvl S 0).arrow).app (U : X.Opens) n, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id]
    simp
  | succ e =>
    have h1 : n ∈ secs (powSub I P (e + 1)) (U : X.Opens) := by
      rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2]
      exact hn
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le e) U h1

theorem span_grT_eq_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) (S : ℕ → Subobject P)
    (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A) (hg : Ideal.span (Set.range g) = I)
    (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  set W := Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) with hW
  have hgen : ∀ i, ∀ n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)),
      toFunctions (A := A) (U : X.Opens) (g i) • n ∈ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    intro i n hn
    obtain ⟨v, rfl⟩ := pow_smul_le_secs_lvl I hP hS e U hn
    refine ⟨(mulLvl (hr i) e).app (U : X.Opens) v, ?_, ?_⟩
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, mulLvl_arrow,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
      congr 1
      exact restrictTop_restrict (homOfLE le_top) _
    · refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (grπ (anti hS) e).app (U : X.Opens) v, ?_⟩)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, grπ_grT,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hle : (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (e + 1)) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)) ≤ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    rw [pow_succ', Ideal.map_mul, Submodule.mul_smul, Submodule.smul_le]
    intro r hr' n hn
    rw [← hg, Ideal.map_span] at hr'
    induction hr' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := h
      exact hgen i n hn
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb
  haveI : ((lvl S (e + 1 + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh (e + 1)
  haveI : ((lvl S (e + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh e
  have hsur : Function.Surjective ((grπ (anti hS) (e + 1)).app (U : X.Opens)) :=
    surjective_cokernel_π_app (incl (anti hS) (e + 1)) U.2
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hsur s
  have hq : ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    haveI := hP
    (closedSys_pow I P).qcoh e
  have hx : (lvl S (e + 1)).arrow.app (U : X.Opens) x ∈
      secs (S (e + 1) ⊔ powSub I P (e + 1)) (U : X.Opens) := by
    rw [← hS.succ e]
    exact ⟨x, rfl⟩
  rw [(GlobalTheory.T.quasicoherent_sup_sections hP _ _ (hS.qcoh (e + 1)) hq).2 U U.2] at hx
  obtain ⟨_, ⟨y, rfl⟩, t, ht, hxy⟩ := hx
  rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2] at ht
  obtain ⟨x', hx't, hx'W⟩ := hle ht
  have hdec : x = (incl (anti hS) (e + 1)).app (U : X.Opens) y + x' := by
    apply injective_app_of_mono (lvl S (e + 1)).arrow (U : X.Opens)
    rw [map_add, hx't, hxy]
    exact congrArg (· + t) (incl_arrow_app (anti hS) (e + 1) (U : X.Opens) y).symm
  have hz : ∀ z : Γ((lvl S (e + 1 + 1) : X.Modules), (U : X.Opens)),
      (grπ (anti hS) (e + 1)).app (U : X.Opens)
        ((incl (anti hS) (e + 1)).app (U : X.Opens) z + x') =
      (grπ (anti hS) (e + 1)).app (U : X.Opens) x' := fun z => by
    rw [map_add, incl_grπ_app, zero_add]
  rw [hdec]
  exact Eq.mpr (congrArg (· ∈ W) (hz y)) hx'W

end GlobalTheory.CompanionTheory.GE.Step
