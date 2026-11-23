import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.NUTransport

section Lin
variable {E V W : Type} [CommRing E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

abbrev As {r : ℕ} (f : Fin (r + 1) → V) (j : ℕ) : Submodule E V := Submodule.span E (f '' {i | (i : ℕ) < j})

theorem As_mono {r : ℕ} (f : Fin (r + 1) → V) {i j : ℕ} (h : i ≤ j) : (As (E := E) f i) ≤ As (E := E) f j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem As_zero {r : ℕ} (f : Fin (r + 1) → V) : (As (E := E) f 0) = ⊥ := by
  simp [As]

theorem unip_iff (e : V ≃ₗ[E] W) (g : V ≃ₗ[E] V) (A B : Submodule E V) :
    ((∀ x, ((e.symm.trans g).trans e) x ∈ A.map (e : V →ₗ[E] W) ↔ x ∈ A.map (e : V →ₗ[E] W)) ∧
      ∀ x ∈ A.map (e : V →ₗ[E] W), ((e.symm.trans g).trans e) x - x ∈ B.map (e : V →ₗ[E] W)) ↔
    ((∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B) := by
  simp only [Submodule.mem_map_equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_sub]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => by simpa using h1 (e v), fun v hv => by simpa using h2 (e v) (by simpa using hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 _, fun x hx => h2 _ hx⟩

variable {r : ℕ} (g : V ≃ₗ[E] V) (f : Fin (r + 1) → V)

theorem step (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m + 1 ≤ r) : ∀ v ∈ As (E := E) f (m + 1), g v - v ∈ As (E := E) f m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := lt_of_lt_of_le hi hm
    have hc : i = (⟨i, hi'⟩ : Fin r).castSucc := Fin.ext rfl
    have := hN ⟨i, hi'⟩
    rw [← hc] at this
    exact As_mono f (Nat.lt_succ_iff.mp hi) this
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ a hx

theorem fwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) : ∀ v ∈ As (E := E) f m, g v ∈ As (E := E) f m := by
  intro v hv
  cases m with
  | zero => rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m =>
    have h := step g f hN m hm v hv
    have : g v = v + (g v - v) := by abel
    rw [this]; exact Submodule.add_mem _ hv (As_mono f (Nat.le_succ m) h)

theorem bwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a) :
    ∀ m : ℕ, m ≤ r → ∀ v ∈ As (E := E) f m, g.symm v ∈ As (E := E) f m := by
  intro m
  induction m with
  | zero => intro _ v hv; rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m ih =>
    intro hm v hv
    have h := step g f hN m hm v hv
    have h2 := ih (Nat.le_of_succ_le hm) _ h
    have : g.symm v = v - g.symm (g v - v) := by simp
    rw [this]; exact Submodule.sub_mem _ hv (As_mono f (Nat.le_succ m) h2)

theorem iff_of (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) (v : V) : g v ∈ As (E := E) f m ↔ v ∈ As (E := E) f m :=
  ⟨fun h => by simpa using bwd g f hN m hm _ h, fun h => fwd g f hN m hm v h⟩

end Lin

section Loc
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem X_eq (f : Fin (r + 1) → V) : H.X f = As (E := E) f r := by
  unfold HermSp.X As
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.castSucc, a.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, congrArg f (Fin.ext rfl)⟩

theorem flag_eq (f : Fin (r + 1) → V) (a : Fin r) :
    Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a}) = As (E := E) f a := by
  unfold As
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b.castSucc, (Fin.lt_def.mp hb : (b : ℕ) < a), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < r := lt_trans hi a.isLt
    exact ⟨⟨i, hi'⟩, Fin.lt_def.mpr hi, congrArg f (Fin.ext rfl)⟩

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)

theorem spanTo_eq (f : Fin (r + 1) → V) (j : ℕ) :
    S.spanTo (fun a => c.e (f a)) j = (As (E := E) f j).map (c.e : V →ₗ[E] S.V) := by
  unfold Frames.spanTo As
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem perp_eq (A : Submodule E V) :
    perp M.L S.Hm (A.map (c.e : V →ₗ[E] S.V)) = (H.perp A).map (c.e : V →ₗ[E] S.V) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  ext x
  rw [Submodule.mem_map_equiv]
  show (∀ y ∈ A.map (c.e : V →ₗ[E] S.V), hf M.L S.Hm x y = 0) ↔ ∀ y ∈ A, H.h (c.e.symm x) y = 0
  constructor
  · intro hx y hy
    rw [← hh, LinearEquiv.apply_symm_apply]
    exact hx _ (Submodule.mem_map_of_mem hy)
  · intro hx y hy
    rw [Submodule.mem_map_equiv] at hy
    have := hx _ hy
    rwa [← hh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this

end Loc

end GlobalTheory.HL.NUTransport

namespace GlobalTheory.HL.NUTransport

section Main
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem mem_unipOn_iff {n : ℕ} (A B : Submodule E (Fin n → E)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := Iff.rfl

theorem mem_hperp_iff (A : Submodule E V) (v : V) : v ∈ H.perp A ↔ ∀ x ∈ A, H.h v x = 0 := Iff.rfl

theorem mem_NU_iff_mem_Nof {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)
    (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) :
    g ∈ NU H f ↔ (c.e.symm.trans g).trans c.e ∈ S.Nof (fun a => c.e (f a)) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  have hU : (c.e.symm.trans g).trans c.e ∈ isomG M.L S.Hm ↔ LocNG.IsUnitary H g := by
    show (∀ x y, hf M.L S.Hm _ _ = hf M.L S.Hm x y) ↔ ∀ x y, H.h (g x) (g y) = H.h x y
    constructor
    · intro h x y
      have := h (c.e x) (c.e y)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hh] at this
      exact this
    · intro h x y
      have h1 := hh (g (c.e.symm x)) (g (c.e.symm y))
      have h2 := hh (c.e.symm x) (c.e.symm y)
      simp only [LinearEquiv.apply_symm_apply] at h2
      simp only [LinearEquiv.trans_apply]
      rw [h1, h2, h]
  have hN : ∀ n, n ∈ S.Nof (fun a => c.e (f a)) ↔ n ∈ isomG M.L S.Hm ∧
      (∀ j : Fin r, n ∈ unipOn (S.spanTo (fun a => c.e (f a)) ((j : ℕ) + 1)) (S.spanTo (fun a => c.e (f a)) j)) ∧
      n ∈ unipOn (perp M.L S.Hm (S.spanTo (fun a => c.e (f a)) r)) (S.spanTo (fun a => c.e (f a)) r) := by
    intro n
    simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, and_assoc]
  rw [hN, hU]
  simp only [spanTo_eq c f, perp_eq c, mem_unipOn_iff, unip_iff]
  show (LocNG.IsUnitary H g ∧ (∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
      ∀ v ∈ H.perp (H.X f), g v - v ∈ H.X f) ↔ _
  simp only [flag_eq, X_eq]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨hu, fun j => ⟨iff_of g f hfl _ j.isLt, step g f hfl j j.isLt⟩, ⟨fun v => ?_, hp⟩⟩
    rw [mem_hperp_iff, mem_hperp_iff]
    constructor
    · intro h x hx
      have := h (g x) ((iff_of g f hfl r le_rfl x).2 hx)
      rwa [hu] at this
    · intro h x hx
      have h1 := h (g.symm x) (bwd g f hfl r le_rfl x hx)
      rw [← hu v (g.symm x), LinearEquiv.apply_symm_apply] at h1
      exact h1
  · rintro ⟨hu, hj, -, hp⟩
    refine ⟨hu, fun a => (hj a).2 _ (Submodule.subset_span ⟨a.castSucc, ?_, rfl⟩), hp⟩
    show (a : ℕ) < (a : ℕ) + 1
    omega

end Main

end GlobalTheory.HL.NUTransport
