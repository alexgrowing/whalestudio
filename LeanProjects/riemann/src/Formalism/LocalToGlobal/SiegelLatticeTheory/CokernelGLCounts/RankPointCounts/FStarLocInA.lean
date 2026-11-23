import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfD

noncomputable section

open scoped Classical
open Formalism.MainNotions.S Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LocInA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

section Map

variable (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)

theorem locInA_osmul (o : M.L.O) (x : V) : e (o • x) = o • e x := by
  first
    | exact map_smul_of_tower e o x
    | exact e.map_smul (o : E) x

def eO : V →ₗ[M.L.O] V where
  toFun := e
  map_add' := e.map_add
  map_smul' o x := locInA_osmul e o x

theorem locInA_span_mem {ι : Type} (v w : ι → V) (h : ∀ i, e (v i) = w i) {x : V}
    (hx : x ∈ Submodule.span E (Set.range v)) : e x ∈ Submodule.span E (Set.range w) := by
  have key : Submodule.span E (Set.range v) ≤
      (Submodule.span E (Set.range w)).comap (e : V →ₗ[E] V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (v i) ∈ Submodule.span E (Set.range w)
    rw [h i]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact key hx

theorem locInA_spanO_mem {ι : Type} (v : ι → V) {x : V}
    (hx : x ∈ Submodule.span M.L.O (Set.range v)) : e x ∈ Submodule.span M.L.O (Set.range fun i => e (v i)) := by
  have key : Submodule.span M.L.O (Set.range v) ≤
      (Submodule.span M.L.O (Set.range fun i => e (v i))).comap (eO e) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (v i) ∈ Submodule.span M.L.O (Set.range fun i => e (v i))
    exact Submodule.subset_span ⟨i, rfl⟩
  exact key hx

variable {abelian₂ Lam' : Submodule M.L.O V} (hL : ∀ x, x ∈ Lam' ↔ e.symm x ∈ abelian₂)
include hL

theorem locInA_mem (x : V) (hx : x ∈ abelian₂) : e x ∈ Lam' := (hL _).2 (by rwa [LinearEquiv.symm_apply_apply])

theorem locInA_map_eq : Lam' = abelian₂.map (eO e) := by
  ext x
  rw [hL, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨e.symm x, hx, (by first | exact e.apply_symm_apply x | simp [eO])⟩
  · rintro ⟨y, hy, rfl⟩
    show e.symm (e y) ∈ abelian₂
    rwa [LinearEquiv.symm_apply_apply]

theorem locInA_prim {ι : Type} (v : ι → V) (h : H.Prim abelian₂ v) : H.Prim Lam' (fun i => e (v i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => locInA_mem e hL (v a) (h1 a), ?_, ?_⟩
  · first
      | exact h2.map' (e : V →ₗ[E] V) (LinearEquiv.ker e)
      | exact h2.map' (e : V →ₗ[E] V) (LinearMap.ker_eq_bot.2 e.injective)
  · intro x hx hxs
    have hs : e.symm x ∈ Submodule.span E (Set.range v) :=
      locInA_span_mem e.symm (fun i => e (v i)) v (fun i => e.symm_apply_apply (v i)) hxs
    have h5 := locInA_spanO_mem e v (h3 _ ((hL x).1 hx) hs)
    rwa [LinearEquiv.apply_symm_apply] at h5

theorem locInA_smulLat (c : E) {x : V} (hx : x ∈ H.smulLat c abelian₂) : e x ∈ H.smulLat c Lam' := by
  have key : H.smulLat c abelian₂ ≤ (H.smulLat c Lam').comap (eO e) := by
    show Submodule.span M.L.O ((fun v => c • v) '' (abelian₂ : Set V)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show e (c • y) ∈ H.smulLat c Lam'
    rw [map_smul]
    exact Submodule.subset_span ⟨e y, locInA_mem e hL y hy, rfl⟩
  exact key hx

include hiso

theorem locInA_selfDual (h : H.IsSelfDual abelian₂) : H.IsSelfDual Lam' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [locInA_map_eq e hL]
    exact h1.map _
  · rw [eq_top_iff]
    intro x _
    have hx : e.symm x ∈ Submodule.span E (abelian₂ : Set V) := by
      rw [h2]
      exact Submodule.mem_top
    have key : Submodule.span E (abelian₂ : Set V) ≤
        (Submodule.span E (Lam' : Set V)).comap (e : V →ₗ[E] V) := by
      rw [Submodule.span_le]
      intro y hy
      show e y ∈ Submodule.span E (Lam' : Set V)
      exact Submodule.subset_span (locInA_mem e hL y hy)
    have h5 : e (e.symm x) ∈ Submodule.span E (Lam' : Set V) := key hx
    rwa [LinearEquiv.apply_symm_apply] at h5
  · intro x
    rw [hL x, h3]
    constructor
    · intro hH y hy
      have h6 := hH (e.symm y) ((hL y).1 hy)
      rwa [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h6
    · intro hH y hy
      rw [← hiso, LinearEquiv.apply_symm_apply]
      exact hH (e y) (locInA_mem e hL y hy)

omit hL in
theorem locInA_zhat {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Zhat (fun a => e (f a)) (fun b => e (f' b)) = H.Zhat f f' := by
  first
    | (ext a b; simp only [Loc.HermSp.Zhat, Matrix.of_apply, hiso])
    | (unfold Loc.HermSp.Zhat; simp only [hiso])

omit hL in
theorem locInA_dl {r : ℕ} (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl (fun a => e (f a)) (fun b => e (f' b)) l = H.Dl f f' l := by
  first
    | simp only [Loc.HermSp.Dl, locInA_zhat H e hiso f f']
    | (unfold Loc.HermSp.Dl; rw [locInA_zhat H e hiso f f'])

theorem locInA_frame {r : ℕ} (f : Fin (r + 1) → V) (T : F) (h : H.IsFrame abelian₂ r f T) :
    H.IsFrame Lam' r (fun a => e (f a)) T := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨locInA_prim H e hL f h1, fun a b hab => ?_, ?_, h4, h5⟩
  · show H.h (e (f a)) (e (f b)) = 0
    rw [hiso]
    exact h2 a b hab
  · show H.h (e (f (Fin.last r))) (e (f (Fin.last r))) = -algebraMap F E T
    rw [hiso]
    exact h3

omit hL hiso in
theorem locInA_mmfam {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) :
    H.MMfam (⟨Lam', fun a => e (f a), fun b => e (f' b), T, T'⟩ : Loc.Term V M r) =
      fun i => e (H.MMfam (⟨abelian₂, f, f', T, T'⟩ : Loc.Term V M r) i) := by
  funext i
  rcases hsp : M.split with _ | g
  · simp only [Loc.HermSp.MMfam, hsp]
    cases i <;> rfl
  · simp only [Loc.HermSp.MMfam, hsp]
    cases i <;> simp [map_smul, map_sub]

theorem isGeneric_map {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (h : H.IsGeneric (⟨abelian₂, f, f', T, T'⟩ : Loc.Term V M r)) :
    H.IsGeneric (⟨Lam', fun a => e (f a), fun b => e (f' b), T, T'⟩ : Loc.Term V M r) := by
  obtain ⟨⟨hsd, hfr, hfr', hu, hg, hsp⟩, hpr⟩ := h
  have hdl : ∀ l, H.Dl (fun a => e (f a)) (fun b => e (f' b)) l = H.Dl f f' l :=
    fun l => locInA_dl H e hiso f f' l
  refine ⟨⟨locInA_selfDual H e hiso hL hsd, locInA_frame H e hiso hL f T hfr,
    locInA_frame H e hiso hL f' T' hfr', ?_, ?_, ?_⟩, ?_⟩
  · show IsUnit (H.Dl (fun a => e (f a)) (fun b => e (f' b)) (r + 1))
    rw [hdl]
    exact hu
  · show H.Gdet (fun a => e (f a)) (fun b => e (f' b)) T T' ≠ 0
    simp only [Loc.HermSp.Gdet, hdl]
    exact hg
  · intro g hgs
    obtain ⟨h1, h2, h3⟩ := hsp g hgs
    refine ⟨h1, h2, ?_⟩
    intro b
    have h3' : ∀ b, f' b - f b ∈ H.smulLat (algebraMap F E (g.q : F)) abelian₂ := h3
    show e (f' b) - e (f b) ∈ H.smulLat (algebraMap F E (g.q : F)) Lam'
    rw [← map_sub]
    exact locInA_smulLat H e hL _ (h3' b)
  · rw [locInA_mmfam H e (abelian₂ := abelian₂) (Lam' := Lam') f f' T T']
    exact locInA_prim H e hL _ hpr

end Map

section Move

variable (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
variable {r : ℕ} (t₁ : Loc.Term V M r) {f₂' f₃' : Fin (r + 1) → V} (hf : ∀ a, e (t₁.f a) = t₁.f a)
  (hf' : ∀ b, e (f₂' b) = f₃' b) (hX : ∀ v ∈ H.perp (H.X t₁.f), e v - v ∈ H.X t₁.f)

include hiso

include hf in
theorem locInA_fs (a : Fin (r + 1)) : e.symm (t₁.f a) = t₁.f a := by
  first
    | exact e.symm_apply_eq.2 (hf a).symm
    | (conv_lhs => rw [← hf a]
       exact e.symm_apply_apply _)

include hf' in
theorem locInA_fs' (b : Fin (r + 1)) : e.symm (f₃' b) = f₂' b := by
  rw [← hf' b]
  exact e.symm_apply_apply _

include hf in
theorem locInA_X (x : V) (hx : x ∈ H.X t₁.f) : e x ∈ H.X t₁.f := by
  exact locInA_span_mem e (fun a : Fin r => t₁.f a.castSucc) (fun a : Fin r => t₁.f a.castSucc)
    (fun a => hf _) hx

include hf in
theorem locInA_Xs (x : V) (hx : x ∈ H.X t₁.f) : e.symm x ∈ H.X t₁.f := by
  exact locInA_span_mem e.symm (fun a : Fin r => t₁.f a.castSucc) (fun a : Fin r => t₁.f a.castSucc)
    (fun a => locInA_fs H e hiso t₁ hf _) hx

include hf' in
theorem locInA_X' (x : V) (hx : x ∈ H.X f₂') : e x ∈ H.X f₃' := by
  exact locInA_span_mem e (fun a : Fin r => f₂' a.castSucc) (fun a : Fin r => f₃' a.castSucc)
    (fun a => hf' _) hx

include hf' in
theorem locInA_Xs' (x : V) (hx : x ∈ H.X f₃') : e.symm x ∈ H.X f₂' := by
  exact locInA_span_mem e.symm (fun a : Fin r => f₃' a.castSucc) (fun a : Fin r => f₂' a.castSucc)
    (fun a => locInA_fs' H e hiso hf' _) hx

abbrev qE : H.Wb f₂' ≃ₗ[E] H.Wb f₃' :=
  qEquiv H e hiso (H.X f₂') (H.X f₃') (locInA_X' H e hiso hf') (locInA_Xs' H e hiso hf')

include hX in
theorem locInA_mk_e (x : ↥(H.perp (H.X t₁.f))) (y : ↥(H.perp (H.X t₁.f))) (hy : (y : V) = e x) :
    H.mkW t₁.f y = H.mkW t₁.f x := by
  have h1 : (y : V) - x ∈ H.X t₁.f := by
    rw [hy]
    exact hX (x : V) x.2
  have h2 : y - x ∈ (H.X t₁.f).comap (H.perp (H.X t₁.f)).subtype := h1
  first
    | exact (Submodule.Quotient.eq _).2 h2
    | (simp only [Loc.HermSp.mkW, Submodule.mkQ_apply]
       exact (Submodule.Quotient.eq _).2 h2)

include hf hX in

theorem lset_eq {Lam₂ Lam₃ : Submodule M.L.O V} (hL : ∀ x, x ∈ Lam₃ ↔ e.symm x ∈ Lam₂) :
    H.Lset Lam₂ t₁.f = H.Lset Lam₃ t₁.f := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hp : e x ∈ H.perp (H.X t₁.f) := perp_map H e hiso _ _ (locInA_Xs H e hiso t₁ hf) x.2
    refine ⟨⟨e x, hp⟩, (hL _).2 ?_, locInA_mk_e H e hiso t₁ hX x ⟨e x, hp⟩ rfl⟩
    show e.symm (e (x : V)) ∈ Lam₂
    rw [LinearEquiv.symm_apply_apply]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    have hp : e.symm y ∈ H.perp (H.X t₁.f) := perp_map_symm H e hiso _ _ (locInA_X H e hiso t₁ hf) y.2
    refine ⟨⟨e.symm y, hp⟩, (hL _).1 hy, ?_⟩
    exact (locInA_mk_e H e hiso t₁ hX ⟨e.symm y, hp⟩ y (e.apply_symm_apply _).symm).symm

theorem locInA_q_mk (x : ↥(H.perp (H.X f₂'))) (y : ↥(H.perp (H.X f₃'))) (hy : (y : V) = e x) :
    qE H e hiso hf' (H.mkW f₂' x) = H.mkW f₃' y := by
  have hxy : perpEquiv H e hiso (H.X f₂') (H.X f₃') (locInA_X' H e hiso hf')
      (locInA_Xs' H e hiso hf') x = y := by
    first
      | exact Subtype.ext hy.symm
      | exact Subtype.ext (by simp [perpEquiv, hy])
  rw [← hxy]
  first
    | rfl
    | (simp only [qEquiv, Loc.HermSp.mkW, Submodule.mkQ_apply]
       rfl)

theorem lset_q {Lam₂ Lam₃ : Submodule M.L.O V} (hL : ∀ x, x ∈ Lam₃ ↔ e.symm x ∈ Lam₂) :
    qE H e hiso hf' '' H.Lset Lam₂ f₂' = H.Lset Lam₃ f₃' := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hp : e x ∈ H.perp (H.X f₃') := perp_map H e hiso _ _ (locInA_Xs' H e hiso hf') x.2
    refine ⟨⟨e x, hp⟩, (hL _).2 ?_, (locInA_q_mk H e hiso hf' x ⟨e x, hp⟩ rfl).symm⟩
    show e.symm (e (x : V)) ∈ Lam₂
    rw [LinearEquiv.symm_apply_apply]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    have hp : e.symm y ∈ H.perp (H.X f₂') := perp_map_symm H e hiso _ _ (locInA_X' H e hiso hf') y.2
    exact ⟨H.mkW f₂' ⟨e.symm y, hp⟩, ⟨⟨e.symm y, hp⟩, (hL _).1 hy, rfl⟩,
      locInA_q_mk H e hiso hf' ⟨e.symm y, hp⟩ y (e.apply_symm_apply _).symm⟩

include hf hX in

theorem iota_q {Lam₂ Lam₃ : Submodule M.L.O V} (hL : ∀ x, x ∈ Lam₃ ↔ e.symm x ∈ Lam₂) (g : Loc.SplitG M.L)
    (T T' : F) :
    H.iotaGraph g (⟨Lam₃, t₁.f, f₃', T, T'⟩ : Loc.Term V M r) =
      Prod.map (qE H e hiso hf') id '' H.iotaGraph g (⟨Lam₂, t₁.f, f₂', T, T'⟩ : Loc.Term V M r) := by
  have hL' : ∀ y, y ∈ Lam₂ ↔ e.symm.symm y ∈ Lam₃ := fun y => by
    rw [LinearEquiv.symm_symm, hL, LinearEquiv.symm_apply_apply]
  ext ⟨p1, p2⟩
  constructor
  · rintro ⟨x', x, hx'L, hxL, hsub, hp⟩
    have hp1 : e.symm x' ∈ H.perp (H.X f₂') :=
      perp_map_symm H e hiso _ _ (locInA_X' H e hiso hf') x'.2
    have hp2 : e.symm x ∈ H.perp (H.X t₁.f) :=
      perp_map_symm H e hiso _ _ (locInA_X H e hiso t₁ hf) x.2
    refine ⟨(H.mkW f₂' ⟨e.symm x', hp1⟩, H.mkW t₁.f ⟨e.symm x, hp2⟩),
      ⟨⟨e.symm x', hp1⟩, ⟨e.symm x, hp2⟩, (hL _).1 hx'L, (hL _).1 hxL, ?_, rfl⟩, ?_⟩
    · show e.symm (x : V) - e.symm x' ∈ H.smulLat (algebraMap F E (g.q : F)) Lam₂
      rw [← map_sub]
      exact locInA_smulLat H e.symm hL' _ hsub
    · rw [hp]
      exact Prod.ext (locInA_q_mk H e hiso hf' ⟨e.symm x', hp1⟩ x' (e.apply_symm_apply _).symm)
        (locInA_mk_e H e hiso t₁ hX ⟨e.symm x, hp2⟩ x (e.apply_symm_apply _).symm).symm
  · rintro ⟨⟨q1, q2⟩, ⟨x', x, hx'L, hxL, hsub, hq⟩, hp⟩
    have hp1 : e x' ∈ H.perp (H.X f₃') :=
      perp_map H e hiso _ _ (locInA_Xs' H e hiso hf') x'.2
    have hp2 : e x ∈ H.perp (H.X t₁.f) :=
      perp_map H e hiso _ _ (locInA_Xs H e hiso t₁ hf) x.2
    refine ⟨⟨e x', hp1⟩, ⟨e x, hp2⟩, (hL _).2 ?_, (hL _).2 ?_, ?_, ?_⟩
    · show e.symm (e (x' : V)) ∈ Lam₂
      rw [LinearEquiv.symm_apply_apply]
      exact hx'L
    · show e.symm (e (x : V)) ∈ Lam₂
      rw [LinearEquiv.symm_apply_apply]
      exact hxL
    · show e (x : V) - e x' ∈ H.smulLat (algebraMap F E (g.q : F)) Lam₃
      rw [← map_sub]
      exact locInA_smulLat H e hL _ hsub
    · rw [← hp, hq]
      exact Prod.ext (locInA_q_mk H e hiso hf' x' ⟨e x', hp1⟩ rfl)
        (locInA_mk_e H e hiso t₁ hX x ⟨e x, hp2⟩ rfl).symm

theorem sendsTo_trans (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') (c₁ c₂ : E) (v₁ v₂ : V)
    (h : H.SendsTo φ'.toLinearMap c₁ c₂ v₁ v₂) :
    H.SendsTo (φ'.trans (qE H e hiso hf')).toLinearMap c₁ c₂ v₁ (e v₂) := by
  intro x x₂ hx hx₂
  have hp : e.symm (x₂ : V) ∈ H.perp (H.X f₂') :=
    perp_map_symm H e hiso _ _ (locInA_X' H e hiso hf') x₂.2
  have h1 : c₁ • φ' (H.mkW t₁.f' x) = c₂ • H.mkW f₂' ⟨e.symm x₂, hp⟩ :=
    h x ⟨e.symm x₂, hp⟩ hx (by show e.symm (x₂ : V) = v₂; rw [hx₂, LinearEquiv.symm_apply_apply])
  show c₁ • qE H e hiso hf' (φ' (H.mkW t₁.f' x)) = c₂ • H.mkW f₃' x₂
  rw [← map_smul (qE H e hiso hf') c₁, h1, map_smul (qE H e hiso hf') c₂,
    locInA_q_mk H e hiso hf' ⟨e.symm x₂, hp⟩ x₂ (e.apply_symm_apply _).symm]

include hf hX in
theorem sendsTo_refl_trans (c₁ c₂ : E) (v₁ v₂ : V)
    (h : H.SendsTo (LinearEquiv.refl E (H.Wb t₁.f)).toLinearMap c₁ c₂ v₁ v₂) :
    H.SendsTo (LinearEquiv.refl E (H.Wb t₁.f)).toLinearMap c₁ c₂ v₁ (e v₂) := by
  intro x x₂ hx hx₂
  have hp : e.symm (x₂ : V) ∈ H.perp (H.X t₁.f) :=
    perp_map_symm H e hiso _ _ (locInA_X H e hiso t₁ hf) x₂.2
  have h1 := h x ⟨e.symm x₂, hp⟩ hx (by show e.symm (x₂ : V) = v₂; rw [hx₂, LinearEquiv.symm_apply_apply])
  rw [h1, ← locInA_mk_e H e hiso t₁ hX ⟨e.symm x₂, hp⟩ x₂ (e.apply_symm_apply _).symm]

include hf hf' in
theorem locInA_zhat' : H.Zhat t₁.f f₃' = H.Zhat t₁.f f₂' := by
  have h1 : (fun a => e (t₁.f a)) = t₁.f := funext hf
  have h2 : (fun b => e (f₂' b)) = f₃' := funext hf'
  calc H.Zhat t₁.f f₃' = H.Zhat (fun a => e (t₁.f a)) (fun b => e (f₂' b)) := by rw [h1, h2]
    _ = H.Zhat t₁.f f₂' := locInA_zhat H e hiso t₁.f f₂'

include hf hf' in
theorem locInA_dl' (l : ℕ) : H.Dl t₁.f f₃' l = H.Dl t₁.f f₂' l := by
  have h1 : (fun a => e (t₁.f a)) = t₁.f := funext hf
  have h2 : (fun b => e (f₂' b)) = f₃' := funext hf'
  calc H.Dl t₁.f f₃' l = H.Dl (fun a => e (t₁.f a)) (fun b => e (f₂' b)) l := by rw [h1, h2]
    _ = H.Dl t₁.f f₂' l := locInA_dl H e hiso t₁.f f₂' l

include hf hf' hX in

theorem ident_trans (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hI : H.Ident t₁ ⟨⊥, t₁.f, f₂', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) φ') :
    H.Ident t₁ ⟨⊥, t₁.f, f₃', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) (φ'.trans (qE H e hiso hf')) := by
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
  have hz := locInA_zhat' H e hiso t₁ hf hf'
  have hd : ∀ l, H.Dl t₁.f f₃' l = H.Dl t₁.f f₂' l := fun l => locInA_dl' H e hiso t₁ hf hf' l
  have hom' : H.om' t₁.f f₃' = e (H.om' t₁.f f₂') := by
    simp only [Loc.HermSp.om', hz, map_sum, map_smul, hf']
  have hom : H.om t₁.f f₃' = e (H.om t₁.f f₂') := by
    simp only [Loc.HermSp.om, hz, map_sum, map_smul, hf]
  have h21 : ∀ y ∈ H.Xp t₁.f ⊔ H.Xp f₃', e.symm y ∈ H.Xp t₁.f ⊔ H.Xp f₂' := by
    intro y hy
    have key : H.Xp t₁.f ⊔ H.Xp f₃' ≤ (H.Xp t₁.f ⊔ H.Xp f₂').comap (e.symm : V →ₗ[E] V) := by
      refine sup_le ?_ ?_
      · show Submodule.span E (Set.range t₁.f) ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        show e.symm (t₁.f a) ∈ H.Xp t₁.f ⊔ H.Xp f₂'
        rw [locInA_fs H e hiso t₁ hf a]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
      · show Submodule.span E (Set.range f₃') ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        show e.symm (f₃' b) ∈ H.Xp t₁.f ⊔ H.Xp f₂'
        rw [locInA_fs' H e hiso hf' b]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
    exact key hy
  refine ⟨i1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y x₂ y₂ hx hy
    have hp1 : e.symm (x₂ : V) ∈ H.perp (H.X f₂') :=
      perp_map_symm H e hiso _ _ (locInA_X' H e hiso hf') x₂.2
    have hp2 : e.symm (y₂ : V) ∈ H.perp (H.X f₂') :=
      perp_map_symm H e hiso _ _ (locInA_X' H e hiso hf') y₂.2
    have hx' : φ' (H.mkW t₁.f' x) = H.mkW f₂' ⟨e.symm x₂, hp1⟩ := by
      apply (qE H e hiso hf').injective
      rw [locInA_q_mk H e hiso hf' ⟨e.symm x₂, hp1⟩ x₂ (e.apply_symm_apply _).symm]
      exact hx
    have hy' : φ' (H.mkW t₁.f' y) = H.mkW f₂' ⟨e.symm y₂, hp2⟩ := by
      apply (qE H e hiso hf').injective
      rw [locInA_q_mk H e hiso hf' ⟨e.symm y₂, hp2⟩ y₂ (e.apply_symm_apply _).symm]
      exact hy
    rw [← i2 x y _ _ hx' hy']
    show H.h (x₂ : V) y₂ = H.h (e.symm (x₂ : V)) (e.symm (y₂ : V))
    rw [← hiso (e.symm (x₂ : V)) (e.symm (y₂ : V)), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  · intro w hw
    obtain ⟨w₂, hw₂, s1, s2⟩ := i3 w hw
    exact ⟨e w₂, perp_map H e hiso _ _ h21 hw₂, sendsTo_refl_trans H e hiso t₁ hf hX 1 1 w w₂ s1,
      sendsTo_trans H e hiso t₁ hf' φ' 1 1 w w₂ s2⟩
  · show H.SendsTo (LinearEquiv.refl E (H.Wb t₁.f)).toLinearMap (H.Dl t₁.f f₃' (r + 1))
      (H.Dl t₁.f t₁.f' (r + 1)) (H.om' t₁.f t₁.f') (H.om' t₁.f f₃')
    rw [hd, hom']
    exact sendsTo_refl_trans H e hiso t₁ hf hX _ _ _ _ i4
  · show H.SendsTo (φ'.trans (qE H e hiso hf')).toLinearMap (M.L.cj (H.Dl t₁.f f₃' (r + 1)))
      (M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) (H.om t₁.f t₁.f') (H.om t₁.f f₃')
    rw [hd, hom]
    exact sendsTo_trans H e hiso t₁ hf' φ' _ _ _ _ i5
  · show H.Dl t₁.f t₁.f' r * H.Dl t₁.f f₃' (r + 1) = H.Dl t₁.f f₃' r * H.Dl t₁.f t₁.f' (r + 1)
    rw [hd, hd]
    exact i6

include hf hf' hX in

theorem locSet_back {Lam₂ Lam₃ : Submodule M.L.O V} (hL : ∀ x, x ∈ Lam₃ ↔ e.symm x ∈ Lam₂)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hI : H.Ident t₁ ⟨⊥, t₁.f, f₂', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) φ')
    (hz : H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)))
    (hP : ∀ ψ : H.Wb t₁.f' ≃ₗ[E] H.Wb f₃', H.Ident t₁ ⟨⊥, t₁.f, f₃', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) ψ →
      H.SendsTo ψ.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₃' (Fin.last r)) →
      H.IsGeneric ⟨Lam₃, t₁.f, f₃', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Lam₃, t₁.f, f₃', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) ψ) :
    H.IsGeneric ⟨Lam₂, t₁.f, f₂', t₁.T, t₁.T'⟩ ∧
      H.Respects t₁ ⟨Lam₂, t₁.f, f₂', t₁.T, t₁.T'⟩ (LinearEquiv.refl E _) φ' := by
  obtain ⟨hgen, hres⟩ := hP (φ'.trans (qE H e hiso hf')) (ident_trans H e hiso t₁ hf hf' hX φ' hI)
    (by
      have h0 := sendsTo_trans H e hiso t₁ hf' φ' 1 1 _ _ hz
      rwa [hf' (Fin.last r)] at h0)
  refine ⟨?_, ?_⟩
  · have hL' : ∀ x, x ∈ Lam₂ ↔ e.symm.symm x ∈ Lam₃ := fun x => by
      rw [LinearEquiv.symm_symm, hL, LinearEquiv.symm_apply_apply]
    have hiso' : ∀ v w, H.h (e.symm v) (e.symm w) = H.h v w := fun v w => by
      have h0 := hiso (e.symm v) (e.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h0
      exact h0.symm
    have h1 := isGeneric_map H e.symm hiso' hL' t₁.f f₃' t₁.T t₁.T' hgen
    have h2 : (fun a => e.symm (t₁.f a)) = t₁.f := funext (locInA_fs H e hiso t₁ hf)
    have h3 : (fun b => e.symm (f₃' b)) = f₂' := funext (locInA_fs' H e hiso hf')
    rw [h2, h3] at h1
    exact h1
  · obtain ⟨r1, r2, r3, r4, r5⟩ := hres
    refine ⟨r1.trans ?_, r2, ?_, hz, ?_⟩
    · exact (lset_eq H e hiso t₁ hf hX hL).symm
    · have hc : (qE H e hiso hf') '' (φ' '' H.Lset t₁.abelian₂ t₁.f') =
          (qE H e hiso hf') '' H.Lset Lam₂ f₂' := by
        rw [lset_q H e hiso hf' hL, Set.image_image]
        exact r3
      exact Set.image_injective.2 (qE H e hiso hf').injective hc
    · intro g hg
      have he : Prod.map (qE H e hiso hf') id '' (Prod.map φ' (LinearEquiv.refl E (H.Wb t₁.f)) ''
          H.iotaGraph g t₁) =
          Prod.map (qE H e hiso hf') id '' H.iotaGraph g ⟨Lam₂, t₁.f, f₂', t₁.T, t₁.T'⟩ := by
        rw [← iota_q H e hiso t₁ hf hf' hX hL g t₁.T t₁.T', Set.image_image]
        exact r5 g hg
      have hinj : Function.Injective (Prod.map (qE H e hiso hf') (id : H.Wb t₁.f → H.Wb t₁.f)) := by
        first
          | exact (qE H e hiso hf').injective.prodMap Function.injective_id
          | exact (qE H e hiso hf').injective.Prod_map Function.injective_id
          | exact Prod.map_injective.2 ⟨(qE H e hiso hf').injective, Function.injective_id⟩
      exact Set.image_injective.2 hinj he

end Move

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LocInA
