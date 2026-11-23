import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueFwdOf
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Back

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GramMM (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → IsUnit (H.gram (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))).det

def ThFG (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t → (ThL H t).FG

def ThSpan (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    Submodule.span E (ThL H t : Set V) = H.W0 t.f t.f'

set_option maxHeartbeats 800000 in
theorem glueBack_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : GlueBack M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT hDl hMM θ hθ
  let t₀ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' }
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  have hsd : ∀ x : V, x ∈ t₁.abelian₂ ↔ ∀ y ∈ t₁.abelian₂, H.h x y ∈ M.L.O := by
    obtain ⟨⟨⟨-, -, h⟩, -⟩, -⟩ := id hG₁
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  let g : ThL H t₁ →ₗ[M.L.O] V :=
    { toFun := fun x => (ψ ⟨x, ((memL _ _).1 x.2).2⟩ : V)
      map_add' := fun a b => by
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memL _ _).1 a.2).2⟩ ⟨(b : V), ((memL _ _).1 b.2).2⟩)
        exact h
      map_smul' := fun c a => by
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memL _ _).1 a.2).2⟩)
        exact h }
  have hg : ∀ y : ThL H t₁, g y = (ψ ⟨y, ((memL _ _).1 y.2).2⟩ : V) := fun _ => rfl
  obtain ⟨N₂, hN₂⟩ : ∃ N : Submodule M.L.O V, N = Submodule.map g ⊤ := ⟨_, rfl⟩
  have memN : ∀ v : V, v ∈ N₂ ↔ ∃ y, g y = v := by
    intro v
    rw [hN₂]
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  have keyN : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ N₂ := by
    intro x hx
    constructor
    · intro h
      exact (memN _).2 ⟨⟨x, (memL _ _).2 ⟨h, hx⟩⟩, rfl⟩
    · intro h
      obtain ⟨y, hy⟩ := (memN _).1 h
      rw [hg] at hy
      have h2 : (y : V) = x := congrArg Subtype.val (ψ.injective (Subtype.ext hy))
      rw [← h2]
      exact ((memL _ _).1 y.2).1
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₀ N₂ := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨y, rfl⟩ := (memN _).1 hn'
    rw [hg, hψh]
    exact ((memS _ _ _).1 hw).2 _ y.2
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₀ N₂),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memN _).2 ⟨⟨n, hn'⟩, rfl⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₀ N₂ :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₀ N₂)
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₀ N₂).subtype N₂ := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (memN _).2 ⟨⟨y, hy⟩, rfl⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨y, hy⟩ := (memN _).1 hx
      rw [hg] at hy
      have h4 : ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩ = ⟨(y : V), ((memL _ _).1 y.2).2⟩ :=
        (LinearEquiv.symm_apply_eq ψ).2 (Subtype.ext hy).symm
      have h3 : (e.symm x : V) = y := congrArg Subtype.val h4
      rw [h3]
      exact y.2
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₀ N₂ := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₀ N₂ (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₀ N₂, H.h (e.symm a : V) (e.symm b : V) = H.h a b := by
    intro a b
    have h := hψh (ψ.symm ⟨(a : V), ((memS _ _ _).1 a.2).1⟩) (ψ.symm ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let η : DDt H t₀ ≃ₗ[M.L.O] DDW H t₀ N₂ := (θ.symm.trans η₁).trans κ
  have hle : N₂ ≤ Submodule.restrictScalars M.L.O (H.W0 t₀.f t₀.f') := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memN v).1 hv
    exact (ψ _).2
  have hfg : N₂.FG := by
    rw [hN₂]
    haveI : Module.Finite M.L.O (ThL H t₁) := Module.Finite.iff_fg.2 (hFG V H t₁ hG₁)
    exact (Module.Finite.fg_top).map g
  have hS1 := hS V H t₁ hG₁
  have hspan : Submodule.span E (N₂ : Set V) = H.W0 t₀.f t₀.f' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      exact hle hv
    · intro v hv
      have hu : ((ψ.symm ⟨v, hv⟩ : H.W0 t₁.f t₁.f') : V) ∈ Submodule.span E (ThL H t₁ : Set V) := by
        rw [hS1]
        exact (ψ.symm _).2
      have main : ∀ (x : V) (hx : x ∈ Submodule.span E (ThL H t₁ : Set V)),
          ∀ h : x ∈ H.W0 t₁.f t₁.f', (ψ ⟨x, h⟩ : V) ∈ Submodule.span E (N₂ : Set V) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          intro h
          exact Submodule.subset_span ((keyN x h).1 ((memL _ _).1 hx).1)
        | zero =>
          intro h
          have h0 : (⟨0, h⟩ : H.W0 t₁.f t₁.f') = 0 := rfl
          rw [h0, map_zero]
          exact Submodule.zero_mem _
        | add x y hx hy ihx ihy =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have hy' : y ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hy
          have h0 : (⟨x + y, h⟩ : H.W0 t₁.f t₁.f') = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
          rw [h0, map_add, Submodule.coe_add]
          exact Submodule.add_mem _ (ihx hx') (ihy hy')
        | smul a x hx ihx =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have h0 : (⟨a • x, h⟩ : H.W0 t₁.f t₁.f') = a • ⟨x, hx'⟩ := rfl
          rw [h0, map_smul, Submodule.coe_smul]
          exact Submodule.smul_mem _ a (ihx hx')
      have h4 := main _ hu (ψ.symm ⟨v, hv⟩).2
      simpa using h4
  have hint : ∀ x ∈ N₂, ∀ y ∈ N₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (memN x).1 hx
    obtain ⟨b, rfl⟩ := (memN y).1 hy
    rw [hg, hg, hψh]
    exact (hsd _).1 ((memL _ _).1 a.2).1 _ ((memL _ _).1 b.2).1
  have hpair : ∀ (m m' : MMsharp H t₀) (w w' : ThSharp H t₀ N₂),
      η (ddMk H t₀ m) = dwMk H t₀ N₂ w → η (ddMk H t₀ m') = dwMk H t₀ N₂ w' →
      H.h m m' + H.h w w' ∈ M.L.O := by
    intro m m' w w' hw hw'
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m))
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m'))
    have hθx : θ (ddMk H t₁ x) = ddMk H t₀ m := by
      rw [show ddMk H t₁ x = θ.symm (ddMk H t₀ m) from hx, LinearEquiv.apply_symm_apply]
    have hθx' : θ (ddMk H t₁ x') = ddMk H t₀ m' := by
      rw [show ddMk H t₁ x' = θ.symm (ddMk H t₀ m') from hx', LinearEquiv.apply_symm_apply]
    have h1 : η₁ (ddMk H t₁ x) = dwMk H t₁ (ThL H t₁) (e.symm w) := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw]
      show κ (η₁ (ddMk H t₁ x)) = κ (η₁ (θ.symm (ddMk H t₀ m)))
      rw [← hx]
      rfl
    have h1' : η₁ (ddMk H t₁ x') = dwMk H t₁ (ThL H t₁) (e.symm w') := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw']
      show κ (η₁ (ddMk H t₁ x')) = κ (η₁ (θ.symm (ddMk H t₀ m')))
      rw [← hx']
      rfl
    have a1 := hη₁b x x' (e.symm w) (e.symm w') h1 h1'
    rw [hh] at a1
    have a2 := hθ x x' m m' hθx hθx'
    have a3 := add_mem a2 a1
    convert a3 using 1
    ring
  have hGr := hG V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨Λ, ⟨hsd2, hprim, hcap, hη⟩, -⟩ :=
    hV hM V H t₀ hGr hMM N₂ hle hfg hspan hint η hpair
  have hgen := hP hM V H hn t₁ f₂ f₂' φ φ' hT hDl Λ hsd2 hprim
  have hthc : ThCond H t₁ t₀ Λ φ φ' := by
    intro n₁ n₂ hc
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    rw [keyN n₁ hn₁, ← hcap]
    constructor
    · intro h
      exact (Submodule.mem_inf.1 h).1
    · intro h
      exact Submodule.mem_inf.2 ⟨h, (ψ _).2⟩
  refine ⟨Λ, hgen, hthc, ?_⟩
  intro m₁ m₂
  obtain ⟨w, hw⟩ := surj m₁
  have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
  have step : θ (ddMk H t₁ m₁) = ddMk H t₀ m₂ ↔ η (ddMk H t₀ m₂) = dwMk H t₀ N₂ (e w) := by
    constructor
    · intro h
      show κ (η₁ (θ.symm (ddMk H t₀ m₂))) = _
      rw [← h, LinearEquiv.symm_apply_apply, hw, hκ]
    · intro h
      have h2 : κ (η₁ (θ.symm (ddMk H t₀ m₂))) = κ (η₁ (ddMk H t₁ m₁)) := by
        rw [hw, hκ]
        exact h
      have h3 := η₁.injective (κ.injective h2)
      rw [← h3, LinearEquiv.apply_symm_apply]
  refine step.trans ((hη m₂ (e w)).trans ?_)
  constructor
  · intro h
    exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, h⟩
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
    have hdL : n₁ - w ∈ t₁.abelian₂ := by
      have h4 := t₁.abelian₂.sub_mem h1 hmw
      simpa using h4
    have h3 : (ψ ⟨n₁ - w, hd⟩ : V) ∈ Λ := by
      have h5 := (keyN _ hd).1 hdL
      rw [← hcap] at h5
      exact (Submodule.mem_inf.1 h5).1
    have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = (ψ ⟨n₁, hn₁⟩ : V) - (e w : V) := by
      have h6 := congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      exact h6
    rw [hψd] at h3
    have h5 := Λ.sub_mem h2 h3
    convert h5 using 1
    abel

end Back

end Formalism.L2.SG.LsDatumA
