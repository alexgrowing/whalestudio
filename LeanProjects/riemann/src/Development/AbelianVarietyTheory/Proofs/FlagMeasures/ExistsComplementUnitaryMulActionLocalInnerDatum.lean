import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.InnerDatumAct

open Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def FixesFrame (H : HermSp M V) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop :=
  IsUnitary H g ∧ ∀ b, g (f b) = f b

lemma FixesFrame.symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    FixesFrame H f g.symm := by
  refine ⟨fun x y => ?_, fun b => ?_⟩
  · have := hg.1 (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rw [LinearEquiv.symm_apply_eq, hg.2 b]

lemma FixesFrame.mem_X {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.X f) : g v ∈ H.X f := by
  have hle : H.X f ≤ (H.X f).comap (g : V →ₗ[E] V) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hg.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact hle hv

lemma FixesFrame.mem_perp {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' := hg.symm.mem_X hx
  have h1 := hg.1 v (g.symm x)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact (hv : ∀ x ∈ H.X f, H.h v x = 0) _ hx'

def perpMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    ↥(H.perp (H.X f)) →ₗ[E] ↥(H.perp (H.X f)) :=
  (g : V →ₗ[E] V).restrict (fun _ hv => hg.mem_perp hv)

def wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) : H.Wb f →ₗ[E] H.Wb f :=
  Submodule.mapQ _ _ (perpMap hg) (fun x hx => by
    show ((perpMap hg x : ↥(H.perp (H.X f))) : V) ∈ H.X f
    exact hg.mem_X hx)

lemma wMap_mk {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (x : ↥(H.perp (H.X f))) : wMap hg (H.mkW f x) = H.mkW f ⟨g x, hg.mem_perp x.2⟩ := rfl

lemma mkW_congr {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) = y) :
    H.mkW f x = H.mkW f y := by
  rw [Subtype.ext h]

lemma wMap_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg (H.mkW f x) = H.mkW f y := by
  rw [wMap_mk]; exact mkW_congr h.symm

lemma wMap_symm_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg.symm (H.mkW f y) = H.mkW f x := by
  rw [wMap_mk]; apply mkW_congr; simp [h]

lemma wMap_symm_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg.symm (wMap hg w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  exact (congrArg (wMap hg.symm) (wMap_of_eq hg (y := ⟨g x, hg.mem_perp x.2⟩) rfl)).trans
    (wMap_symm_of_eq hg rfl)

lemma wMap_wMap_symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg (wMap hg.symm w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  have e : (x : V) = g (g.symm x) := by simp
  exact (congrArg (wMap hg) (wMap_symm_of_eq hg (x := ⟨g.symm x, hg.symm.mem_perp x.2⟩) e)).trans
    (wMap_of_eq hg e)

lemma mem_map_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (L : Submodule M.L.O (H.Wb f)) (w : H.Wb f) :
    w ∈ L.map ((wMap hg).restrictScalars M.L.O) ↔ wMap hg.symm w ∈ L := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show wMap hg.symm (wMap hg u) ∈ L
    rw [wMap_symm_wMap]; exact hu
  · intro h
    exact ⟨_, h, wMap_wMap_symm hg w⟩

def InU (P : FPair H r) (g : V ≃ₗ[E] V) : Prop := FixesFrame H P.A.f g ∧ FixesFrame H P.B.f g

lemma inU_of_mem {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) : InU P g := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨⟨hx.1, fun b => (hx.2 b).1⟩, ⟨hx.1, fun b => (hx.2 b).2⟩⟩
  | one => exact ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨⟨fun a b => ?_, fun b => ?_⟩, ⟨fun a b => ?_, fun b => ?_⟩⟩ <;>
      simp only [LinearEquiv.mul_apply]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.1.2, hx.1.2]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.2.2, hx.2.2]
  | inv x _ hx => exact ⟨hx.1.symm, hx.2.symm⟩

lemma isInner_map (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : FixesFrame H Fr.f g)
    {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) :
    Fr.IsInner (L.map ((wMap hg).restrictScalars M.L.O)) := by
  obtain ⟨hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : g.symm xz = xz := by
    rw [hxz]; exact hg.symm.2 (Fin.last r)
  refine ⟨hfg.map _, fun x => ?_, xz, hxz, ?_, fun c y hy heq => ?_⟩
  · rw [mem_map_wMap, wMap_mk, hdual]
    constructor
    · intro h y hy
      rw [mem_map_wMap, wMap_mk] at hy
      have h1 := h _ hy
      have h2 := hg.symm.1 x y
      simp only at h1
      rw [h2] at h1
      exact h1
    · intro h y hy
      have hy' : H.mkW Fr.f ⟨g y, hg.mem_perp y.2⟩ ∈ L.map ((wMap hg).restrictScalars M.L.O) := by
        rw [mem_map_wMap, wMap_symm_of_eq hg rfl]; exact hy
      have h1 := h _ hy'
      have h2 := hg.symm.1 x (g y)
      simp only [LinearEquiv.symm_apply_apply] at h2
      show H.h (g.symm x) y ∈ M.L.O
      rw [h2]; exact h1
  · rw [mem_map_wMap, wMap_mk]
    rw [mkW_congr (y := xz) hz]; exact hxzL
  · rw [mem_map_wMap] at hy
    refine hprim c ⟨g.symm y, hg.symm.mem_perp y.2⟩ ?_ ?_
    · rw [← wMap_mk]; exact hy
    · have h3 := congrArg (wMap hg.symm) heq
      rw [LinearMap.map_smul, wMap_mk, wMap_mk, mkW_congr (y := xz) hz] at h3
      exact h3

def act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) : Datum P where
  L := d.L.map ((wMap hg.1).restrictScalars M.L.O)
  L' := d.L'.map ((wMap hg.2).restrictScalars M.L.O)
  hL := isInner_map P.A hg.1 d.hL
  hL' := isInner_map P.B hg.2 d.hL'
  io := {p | (wMap hg.2.symm p.1, wMap hg.1.symm p.2) ∈ d.io}
  io_L := fun h => by
    ext p
    simp [d.io_L h]

lemma datum_ext {P : FPair H r} {d₁ d₂ : Datum P} (hL : d₁.L = d₂.L) (hL' : d₁.L' = d₂.L')
    (hio : d₁.io = d₂.io) : d₁ = d₂ := by
  cases d₁; cases d₂
  simp only at hL hL' hio
  subst hL hL' hio
  rfl

lemma moves_act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) :
    Datum.Moves g d (act hg d) := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · show _ ↔ _ ∈ d.L.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.1 hxy]
  · show _ ↔ _ ∈ d.L'.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.2 hxy]
  · show _ ↔ (wMap hg.2.symm _, wMap hg.1.symm _) ∈ d.io
    rw [wMap_symm_of_eq hg.2 hx', wMap_symm_of_eq hg.1 hx]

lemma moves_unique {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) {d d₁ d₂ : Datum P}
    (h₁ : Datum.Moves g d d₁) (h₂ : Datum.Moves g d d₂) : d₁ = d₂ := by
  refine datum_ext ?_ ?_ ?_
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e)
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e)
  · ext ⟨w', w⟩
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ w'
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e' : (y' : V) = g (g.symm y') := by simp
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y' ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y
      e' e).symm.trans (h₂.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y'
        ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e' e)

lemma moves_one {P : FPair H r} (d : Datum P) : Datum.Moves (1 : V ≃ₗ[E] V) d d := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hx, Subtype.ext hx']

lemma moves_comp {P : FPair H r} {g g' : V ≃ₗ[E] V} (hg : InU P g) {d₁ d₂ d₃ : Datum P}
    (h₁₂ : Datum.Moves g d₁ d₂) (h₂₃ : Datum.Moves g' d₂ d₃) : Datum.Moves (g' * g) d₁ d₃ := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · exact (h₁₂.1 x ⟨g x, hg.1.mem_perp x.2⟩ rfl).trans
      (h₂₃.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.1 x ⟨g x, hg.2.mem_perp x.2⟩ rfl).trans
      (h₂₃.2.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.2 x' ⟨g x', hg.2.mem_perp x'.2⟩ x ⟨g x, hg.1.mem_perp x.2⟩ rfl rfl).trans
      (h₂₃.2.2 _ y' _ y (by rw [hx', LinearEquiv.mul_apply]) (by rw [hx, LinearEquiv.mul_apply]))

theorem exists_mulAction : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _
  let sm : P.UW0 → Datum P → Datum P := fun g d => act (inU_of_mem g.2) d
  have key : ∀ (g : P.UW0) d d', Datum.Moves g.1 d d' ↔ sm g d = d' := fun g d d' =>
    ⟨fun h => moves_unique (inU_of_mem g.2) (moves_act _ d) h, fun h => h ▸ moves_act _ d⟩
  letI act' : MulAction P.UW0 (Datum P) :=
    { smul := sm
      one_smul := fun d => (key 1 d d).1 (moves_one d)
      mul_smul := fun g g' d => (key (g * g') d _).1
        (moves_comp (inU_of_mem g'.2) ((key g' d _).2 rfl) ((key g _ _).2 rfl)) }
  refine ⟨act', key, fun d g => ?_⟩
  have hS : Datum.Stab d = (MulAction.stabilizer P.UW0 d).map P.UW0.subtype := by
    unfold Datum.Stab
    have hset : {g | g ∈ P.UW0 ∧ Datum.Moves g d d} =
        ((MulAction.stabilizer P.UW0 d).map P.UW0.subtype : Set (V ≃ₗ[E] V)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map, MulAction.mem_stabilizer_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, hg⟩, (key ⟨g, hg⟩ d d).1 hm, rfl⟩
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, (key g' d d).2 hg'⟩
    rw [hset, Subgroup.closure_eq]
  rw [hS, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := Subtype.ext he
    subst this
    exact MulAction.mem_stabilizer_iff.1 hg'
  · intro h
    exact ⟨g, MulAction.mem_stabilizer_iff.2 h, rfl⟩

end GlobalTheory.InnerDatumAct
