import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodFamilyMassFormula

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.GoodFamilyMass

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem mkW_eq_iff (f : Fin (r + 1) → V) (x y : ↥(H.perp (H.X f))) :
    H.mkW f x = H.mkW f y ↔ (x : V) - y ∈ H.X f := by
  unfold Formalism.MainNotions.S.Loc.HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  rfl

theorem isUnitary_and_fixes_frames_of_mem_complementUnitary {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx.1, hy.1]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hy.2 b).1, (hy.2 b).2, (hx.2 b).1, (hx.2 b).2]
      exact ⟨rfl, rfl⟩
  | inv x _ hx =>
    refine ⟨fun u v => ?_, fun b => ?_⟩
    · rw [LinearEquiv.coe_inv, ← hx.1 (x.symm u) (x.symm v), LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    · rw [LinearEquiv.coe_inv]
      exact ⟨(LinearEquiv.symm_apply_eq x).2 (hx.2 b).1.symm, (LinearEquiv.symm_apply_eq x).2 (hx.2 b).2.symm⟩

theorem fix_X (f : Fin (r + 1) → V) {g : V ≃ₗ[E] V} (hg : ∀ b, g (f b) = f b) {x : V} (hx : x ∈ H.X f) : g x = x := by
  unfold Formalism.MainNotions.S.Loc.HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact hg _
  | zero => exact map_zero g
  | add u v _ _ hu hv => rw [map_add, hu, hv]
  | smul c u _ hu => rw [map_smul, hu]

theorem N_perp (Fr : FrameD H r) {s : V ≃ₗ[E] V} (hs : s ∈ Fr.N) {v : V} (hv : v ∈ H.perp (H.X Fr.f)) :
    s v ∈ H.perp (H.X Fr.f) ∧ s v - v ∈ H.X Fr.f := by
  have hiso : ∀ x ∈ H.X Fr.f, ∀ y ∈ H.X Fr.f, H.h x y = 0 := by
    have hgen : ∀ a b : Fin r, H.h (Fr.f a.castSucc) (Fr.f b.castSucc) = 0 := fun a b =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
    have hleft : ∀ y ∈ H.X Fr.f, ∀ b : Fin r, H.h y (Fr.f b.castSucc) = 0 := by
      intro y hy b
      unfold Formalism.MainNotions.S.Loc.HermSp.X at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        exact hgen a b
      | zero => simpa using H.h_smul_left 0 0 (Fr.f b.castSucc)
      | add u w _ _ hu hw => rw [H.h_add_left, hu, hw, add_zero]
      | smul c u _ hu => rw [H.h_smul_left, hu, mul_zero]
    intro x hx y hy
    have hx2 : ∀ b : Fin r, H.h (Fr.f b.castSucc) y = 0 := fun b => by
      rw [H.h_herm, hleft y hy b, map_zero]
    unfold Formalism.MainNotions.S.Loc.HermSp.X at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact hx2 a
    | zero => simpa using H.h_smul_left 0 0 y
    | add u w _ _ hu hw => rw [H.h_add_left, hu, hw, add_zero]
    | smul c u _ hu => rw [H.h_smul_left, hu, mul_zero]
  have hXp : ∀ x ∈ H.X Fr.f, x ∈ H.perp (H.X Fr.f) := fun x hx y hy => hiso x hx y hy
  have hFr : Fr.Fj r = H.X Fr.f := by
    unfold FrameD.Fj Formalism.MainNotions.S.Loc.HermSp.X
    congr 1
    ext w
    simp [FrameD.e]
  have hF0 : Fr.Fj 0 = ⊥ := by simp [FrameD.Fj]
  have hFmono : ∀ j, Fr.Fj (j - 1) ≤ Fr.Fj j := fun j =>
    Submodule.span_mono (Set.image_mono fun a (ha : a.val < j - 1) => (show a.val < j by omega))
  have hFsucc : ∀ j, Fr.Fj j ≤ Fr.Fj (j + 1) := fun j => by simpa using hFmono (j + 1)
  have gen : ∀ g ∈ Fr.NSet, (∀ y ∈ H.X Fr.f, g y ∈ H.X Fr.f) ∧ (∀ y ∈ H.X Fr.f, g⁻¹ y ∈ H.X Fr.f) := by
    intro g hg
    obtain ⟨_, hgF, _⟩ := hg
    have pres : ∀ j, j ≤ r → ∀ w ∈ Fr.Fj j, g w ∈ Fr.Fj j := fun j hj w hw => by
      have h1 := (Fr.Fj j).add_mem hw (hFmono j (hgF j hj w hw))
      simpa using h1
    have presinv : ∀ j, j ≤ r → ∀ w ∈ Fr.Fj j, g⁻¹ w ∈ Fr.Fj j := by
      intro j
      induction j with
      | zero =>
        intro _ w hw
        rw [hF0, Submodule.mem_bot] at hw
        rw [hw, map_zero]
        exact zero_mem _
      | succ j ih =>
        intro hj w hw
        have h1 : g w - w ∈ Fr.Fj j := by simpa using hgF (j + 1) hj w hw
        have h2 : g⁻¹ (g w - w) ∈ Fr.Fj j := ih (by omega) _ h1
        have h3 : g⁻¹ w = w - g⁻¹ (g w - w) := by
          rw [map_sub, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
          abel
        rw [h3]
        exact sub_mem hw (hFsucc j h2)
    rw [← hFr]
    exact ⟨pres r le_rfl, presinv r le_rfl⟩
  have inPerp : ∀ t : V ≃ₗ[E] V, (∀ w ∈ H.perp (H.X Fr.f), t w - w ∈ H.X Fr.f) → ∀ w ∈ H.perp (H.X Fr.f), t w ∈ H.perp (H.X Fr.f) := by
    intro t ht w hw
    have h1 := (H.perp (H.X Fr.f)).add_mem hw (hXp _ (ht w hw))
    simpa using h1
  have hQ : ∀ t ∈ Fr.N, IsUnitary H t ∧ (∀ y ∈ H.X Fr.f, t y ∈ H.X Fr.f) ∧ (∀ y ∈ H.X Fr.f, t⁻¹ y ∈ H.X Fr.f) ∧
      (∀ w ∈ H.perp (H.X Fr.f), t w - w ∈ H.X Fr.f) ∧ (∀ w ∈ H.perp (H.X Fr.f), t⁻¹ w - w ∈ H.X Fr.f) := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨hgX, hgXi⟩ := gen g hg
      obtain ⟨hgu, _, hgP⟩ := hg
      refine ⟨hgu, hgX, hgXi, hgP, fun w hw => ?_⟩
      have hu : g⁻¹ w ∈ H.perp (H.X Fr.f) := by
        intro y hy
        rw [← hgu (g⁻¹ w) y, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
        exact hw _ (hgX y hy)
      have h1 := hgP _ hu
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h1
      rw [LinearEquiv.coe_inv]
      have h2 := (H.X Fr.f).neg_mem h1
      simpa using h2
    | one => exact ⟨fun x y => rfl, fun y hy => hy, fun y hy => by simpa using hy, fun w _ => by simp,
        fun w _ => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun u v => ?_, fun z hz => ?_, fun z hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx.1, hy.1]
      · rw [LinearEquiv.mul_apply]
        exact hx.2.1 _ (hy.2.1 z hz)
      · rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact hy.2.2.1 _ (hx.2.2.1 z hz)
      · rw [LinearEquiv.mul_apply]
        have h1 := hx.2.2.2.1 (y w) (inPerp y hy.2.2.2.1 w hw)
        have h2 := hy.2.2.2.1 w hw
        have h3 := (H.X Fr.f).add_mem h1 h2
        simpa using h3
      · rw [mul_inv_rev, LinearEquiv.mul_apply]
        have hxw : x⁻¹ w ∈ H.perp (H.X Fr.f) := inPerp x⁻¹ hx.2.2.2.2 w hw
        have h1 := hy.2.2.2.2 (x⁻¹ w) hxw
        have h2 := hx.2.2.2.2 w hw
        have h3 := (H.X Fr.f).add_mem h1 h2
        simpa using h3
    | inv x _ hx =>
      refine ⟨fun u v => ?_, hx.2.2.1, by simpa using hx.2.1, hx.2.2.2.2, by simpa using hx.2.2.2.1⟩
      rw [LinearEquiv.coe_inv, ← hx.1 (x.symm u) (x.symm v), LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
  obtain ⟨_, _, _, hsP, _⟩ := hQ s hs
  exact ⟨inPerp s hsP v hv, hsP v hv⟩

theorem fixX_perp (f : Fin (r + 1) → V) {g : V ≃ₗ[E] V} (hgu : IsUnitary H g) (hgX : ∀ x ∈ H.X f, g x = x)
    {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  intro x hx
  rw [← hgX x hx, hgu v x]
  exact hv x hx

theorem lset_move (Fr : FrameD H r) {g s : V ≃ₗ[E] V} (hgu : IsUnitary H g) (hgX : ∀ x ∈ H.X Fr.f, g x = x)
    (hs : s ∈ Fr.N) {Λ Λ' : Submodule M.L.O V} (he : Λ' = img g (img s Λ)) (x y : ↥(H.perp (H.X Fr.f)))
    (hxy : (y : V) = g x) :
    H.mkW Fr.f x ∈ H.Lset Λ Fr.f ↔ H.mkW Fr.f y ∈ H.Lset Λ' Fr.f := by
  have hsN : ∀ w, w ∈ H.Lset Λ Fr.f ↔ w ∈ H.Lset (img s Λ) Fr.f := by
    intro w
    constructor
    · rintro ⟨x, hxΛ, rfl⟩
      obtain ⟨h1, h2⟩ := N_perp Fr hs x.2
      refine ⟨⟨s x, h1⟩, ⟨x, hxΛ, rfl⟩, ?_⟩
      rw [mkW_eq_iff]
      exact h2
    · rintro ⟨y, ⟨x, hxΛ, hxy⟩, rfl⟩
      have hsi : s⁻¹ ∈ Fr.N := Fr.N.inv_mem hs
      obtain ⟨h1, h2⟩ := N_perp Fr hsi y.2
      have hx : (s⁻¹ : V ≃ₗ[E] V) y = x := by
        rw [LinearEquiv.coe_inv, ← hxy]
        exact s.symm_apply_apply x
      refine ⟨⟨x, hx ▸ h1⟩, hxΛ, ?_⟩
      rw [mkW_eq_iff]
      show x - (y : V) ∈ H.X Fr.f
      rw [← hx]
      exact h2
  rw [he, hsN]
  have hgi_u : IsUnitary H g⁻¹ := fun u v => by
    rw [LinearEquiv.coe_inv, ← hgu (g.symm u) (g.symm v), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hgi_X : ∀ z ∈ H.X Fr.f, g⁻¹ z = z := fun z hz => by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq]
    exact (hgX z hz).symm
  constructor
  · rintro ⟨x', hx'Θ, hx'eq⟩
    rw [mkW_eq_iff] at hx'eq
    refine ⟨⟨g x', fixX_perp Fr.f hgu hgX x'.2⟩, ⟨x', hx'Θ, rfl⟩, ?_⟩
    rw [mkW_eq_iff]
    show g x' - (y : V) ∈ H.X Fr.f
    rw [hxy, ← map_sub, hgX _ hx'eq]
    exact hx'eq
  · rintro ⟨y', ⟨x'', hx''Θ, hx''y⟩, hy'eq⟩
    rw [mkW_eq_iff] at hy'eq
    have hgx : g x'' = y' := hx''y
    have hx''perp : x'' ∈ H.perp (H.X Fr.f) := by
      have h1 := fixX_perp Fr.f hgi_u hgi_X y'.2
      have h4 : (g⁻¹ : V ≃ₗ[E] V) y' = x'' := by
        rw [LinearEquiv.coe_inv, ← hgx]
        exact g.symm_apply_apply x''
      rwa [h4] at h1
    refine ⟨⟨x'', hx''perp⟩, hx''Θ, ?_⟩
    rw [mkW_eq_iff]
    show x'' - (x : V) ∈ H.X Fr.f
    have h2 : g (x'' - x) ∈ H.X Fr.f := by
      rw [map_sub, hgx, ← hxy]
      exact hy'eq
    have h3 : g⁻¹ (g (x'' - x)) = x'' - x := by
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    rw [← h3, hgi_X _ h2]
    exact h2

section Lset

variable (Fr : FrameD H r)

theorem prF_add' (v w : V) : Fr.prF (v + w) = Fr.prF v + Fr.prF w := by
  simp only [FrameD.prF, H.h_add_left, add_smul, Finset.sum_add_distrib]
  abel

theorem prF_smul' (c : E) (v : V) : Fr.prF (c • v) = c • Fr.prF v := by
  simp only [FrameD.prF, H.h_smul_left, mul_smul, smul_sub, Finset.smul_sum]

theorem e_mem_X' (a : Fin r) : Fr.e a ∈ H.X Fr.f := Submodule.subset_span ⟨a, rfl⟩

theorem sub_prF_mem_X {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h v (Fr.e a) = 0 := fun a => hv _ (e_mem_X' Fr a)
  have h1 : v - Fr.prF v = ∑ a, H.h v (Fr.es a) • Fr.e a := by
    simp [FrameD.prF, h0]
  rw [h1]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_X' Fr a)

theorem prF_mem_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := by
  have hz : ∀ y, H.h 0 y = 0 := fun y => by simpa using H.h_smul_left 0 0 y
  have hsub : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y := fun x x' y => by
    rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
    ring
  have hsum : ∀ (s : Finset (Fin r)) (g : Fin r → V) y, H.h (∑ a ∈ s, g a) y = ∑ a ∈ s, H.h (g a) y := by
    intro s g y
    induction s using Finset.induction_on with
    | empty => simpa using hz y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  have hee : ∀ a b : Fin r, H.h (Fr.e a) (Fr.e b) = 0 := fun a b =>
    Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  have hees : ∀ a b : Fin r, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a b => Fr.h_es a b
  have hese : ∀ a b : Fin r, H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := fun a b => by
    rw [H.h_herm, hees b a]
    split_ifs <;> simp
  have hss : ∀ a b : Fin r, H.h (Fr.es a) (Fr.es b) = 0 := fun a b => Fr.h_ss a b
  have hkey : ∀ (v : V) b, H.h (Fr.prF v) (Fr.e b) = 0 ∧ H.h (Fr.prF v) (Fr.es b) = 0 := by
    intro v b
    constructor
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hee, hese, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hees, hss, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have hR : ∀ u y, H.h u y = M.L.cj (H.h y u) := fun u y => H.h_herm y u
  intro y hy
  unfold Formalism.MainNotions.S.Loc.HermSp.X at hy
  induction hy using Submodule.span_induction with
  | mem z hz' =>
    obtain ⟨a, rfl⟩ := hz'
    exact (hkey v a).1
  | zero => rw [hR, hz, map_zero]
  | add a b _ _ ha hb => rw [hR, H.h_add_left, map_add, ← hR, ← hR, ha, hb, add_zero]
  | smul c a _ ha => rw [hR, H.h_smul_left, map_mul, ← hR, ha, mul_zero]

theorem prF_prF' (v : V) : Fr.prF (Fr.prF v) = Fr.prF v := by
  have hz : ∀ y, H.h 0 y = 0 := fun y => by simpa using H.h_smul_left 0 0 y
  have hsub : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y := fun x x' y => by
    rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
    ring
  have hsum : ∀ (s : Finset (Fin r)) (g : Fin r → V) y, H.h (∑ a ∈ s, g a) y = ∑ a ∈ s, H.h (g a) y := by
    intro s g y
    induction s using Finset.induction_on with
    | empty => simpa using hz y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  have hee : ∀ a b : Fin r, H.h (Fr.e a) (Fr.e b) = 0 := fun a b =>
    Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  have hees : ∀ a b : Fin r, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a b => Fr.h_es a b
  have hese : ∀ a b : Fin r, H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := fun a b => by
    rw [H.h_herm, hees b a]
    split_ifs <;> simp
  have hss : ∀ a b : Fin r, H.h (Fr.es a) (Fr.es b) = 0 := fun a b => Fr.h_ss a b
  have hkey : ∀ (v : V) b, H.h (Fr.prF v) (Fr.e b) = 0 ∧ H.h (Fr.prF v) (Fr.es b) = 0 := by
    intro v b
    constructor
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hee, hese, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hees, hss, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have h1 : ∀ a, H.h (Fr.prF v) (Fr.e a) = 0 := fun a => (hkey v a).1
  have h2 : ∀ a, H.h (Fr.prF v) (Fr.es a) = 0 := fun a => (hkey v a).2
  show Fr.prF v - ∑ a, H.h (Fr.prF v) (Fr.es a) • Fr.e a - ∑ a, H.h (Fr.prF v) (Fr.e a) • Fr.es a = Fr.prF v
  simp only [h1, h2, zero_smul, Finset.sum_const_zero, sub_zero]

theorem lset_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) (w : H.Wb Fr.f) :
    w ∈ L ↔ w ∈ H.Lset (Fr.LamStd L) Fr.f := by
  have hz : ∀ y, H.h 0 y = 0 := fun y => by simpa using H.h_smul_left 0 0 y
  have hsub : ∀ x x' y, H.h (x - x') y = H.h x y - H.h x' y := fun x x' y => by
    rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
    ring
  have hsum : ∀ (s : Finset (Fin r)) (g : Fin r → V) y, H.h (∑ a ∈ s, g a) y = ∑ a ∈ s, H.h (g a) y := by
    intro s g y
    induction s using Finset.induction_on with
    | empty => simpa using hz y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  have hee : ∀ a b : Fin r, H.h (Fr.e a) (Fr.e b) = 0 := fun a b =>
    Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  have hees : ∀ a b : Fin r, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a b => Fr.h_es a b
  have hese : ∀ a b : Fin r, H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := fun a b => by
    rw [H.h_herm, hees b a]
    split_ifs <;> simp
  have hss : ∀ a b : Fin r, H.h (Fr.es a) (Fr.es b) = 0 := fun a b => Fr.h_ss a b
  have hkey : ∀ (v : V) b, H.h (Fr.prF v) (Fr.e b) = 0 ∧ H.h (Fr.prF v) (Fr.es b) = 0 := by
    intro v b
    constructor
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hee, hese, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    · simp only [FrameD.prF, hsub, hsum, H.h_smul_left, hees, hss, mul_zero, Finset.sum_const_zero, sub_zero,
        mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  constructor
  · intro hw
    obtain ⟨x, hxw⟩ := Submodule.mkQ_surjective _ w
    have hxw' : H.mkW Fr.f x = w := hxw
    have hpx := prF_mem_perp Fr (x : V)
    have hmk : H.mkW Fr.f ⟨Fr.prF x, hpx⟩ = H.mkW Fr.f x := by
      rw [mkW_eq_iff]
      have h3 := (H.X Fr.f).neg_mem (sub_prF_mem_X Fr x.2)
      simpa using h3
    have hS : Fr.prF (x : V) ∈ Fr.LamStd L := by
      apply Submodule.subset_span
      refine ⟨fun a => (hkey x a).2 ▸ zero_mem _, fun a => (hkey x a).1 ▸ zero_mem _, ⟨Fr.prF x, hpx⟩,
        (prF_prF' Fr (x : V)).symm, ?_⟩
      rw [hmk, hxw']
      exact hw
    exact ⟨⟨Fr.prF x, hpx⟩, hS, by rw [hmk, hxw']⟩
  · rintro ⟨x, hxS, rfl⟩
    have hφ : ∀ u ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF u, prF_mem_perp Fr u⟩ ∈ L := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨_, _, w', hw'1, hw'2⟩ := hu
        have h6 : (⟨Fr.prF u, prF_mem_perp Fr u⟩ : ↥(H.perp (H.X Fr.f))) = w' := Subtype.ext hw'1.symm
        rw [h6]
        exact hw'2
      | zero =>
        have h6 : (⟨Fr.prF 0, prF_mem_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0 :=
          Subtype.ext (by simpa using prF_smul' Fr 0 0)
        rw [h6, map_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        have h6 : (⟨Fr.prF (a + b), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            ⟨Fr.prF a, prF_mem_perp Fr a⟩ + ⟨Fr.prF b, prF_mem_perp Fr b⟩ := Subtype.ext (prF_add' Fr a b)
        rw [h6, map_add]
        exact add_mem ha hb
      | smul c a _ ha =>
        have h6 : (⟨Fr.prF (c • a), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) = (c : E) • ⟨Fr.prF a, prF_mem_perp Fr a⟩ :=
          Subtype.ext (prF_smul' Fr (c : E) a)
        rw [h6, map_smul]
        exact L.smul_mem c ha
    have h1 := hφ x hxS
    have h2 : H.mkW Fr.f ⟨Fr.prF x, prF_mem_perp Fr x⟩ = H.mkW Fr.f x := by
      rw [mkW_eq_iff]
      have h3 := (H.X Fr.f).neg_mem (sub_prF_mem_X Fr x.2)
      simpa using h3
    rwa [h2] at h1

theorem img_one' (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  unfold img
  have h1 : ((1 : V ≃ₗ[E] V) : V →ₗ[E] V).restrictScalars M.L.O = LinearMap.id := LinearMap.ext fun x => rfl
  rw [h1, Submodule.map_id]

theorem lset_N {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N) (Λ : Submodule M.L.O V) (w : H.Wb Fr.f) :
    w ∈ H.Lset Λ Fr.f ↔ w ∈ H.Lset (img n Λ) Fr.f := by
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨h1, h2⟩ := N_perp Fr hn x.2
    refine ⟨⟨n x, h1⟩, ⟨x, hxΛ, rfl⟩, ?_⟩
    rw [mkW_eq_iff]
    exact h2
  · rintro ⟨y, ⟨x, hxΛ, hxy⟩, rfl⟩
    have hni : n⁻¹ ∈ Fr.N := Fr.N.inv_mem hn
    obtain ⟨h1, h2⟩ := N_perp Fr hni y.2
    have hx : (n⁻¹ : V ≃ₗ[E] V) y = x := by
      rw [LinearEquiv.coe_inv, ← hxy]
      exact n.symm_apply_apply x
    refine ⟨⟨x, hx ▸ h1⟩, hxΛ, ?_⟩
    rw [mkW_eq_iff]
    show x - (y : V) ∈ H.X Fr.f
    rw [← hx]
    exact h2

end Lset

theorem lset_term {P : FPair H r} {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) :
    (∀ w, w ∈ d.L ↔ w ∈ H.Lset t.abelian₂ P.A.f) ∧ (∀ w, w ∈ d.L' ↔ w ∈ H.Lset t.abelian₂ P.B.f) := by
  obtain ⟨_, _, ⟨n, hn, _, hL⟩, ⟨n', hn', _, hL'⟩, _⟩ := ht
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [hL, lset_LamStd P.A d.L w, lset_N P.A hn]
  · rw [hL', lset_LamStd P.B d.L' w, lset_N P.B hn']

def StepOrbitLat (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' →
          ∃ g ∈ P.UW0, ∃ s ∈ P.St, t'.abelian₂ = img g (img s t.abelian₂)

theorem moves_of (hsp : M.split = none) {P : FPair H r} {d d' : Datum P} {t t' : Term V M r}
    (ht : IsTermOver P d t) (ht' : IsTermOver P d' t') {g s : V ≃ₗ[E] V} (hg : g ∈ P.UW0) (hs : s ∈ P.St)
    (he : t'.abelian₂ = img g (img s t.abelian₂)) : Datum.Moves g d d' := by
  obtain ⟨hA, hB⟩ := lset_term ht
  obtain ⟨hA', hB'⟩ := lset_term ht'
  obtain ⟨hgu, hgf⟩ := isUnitary_and_fixes_frames_of_mem_complementUnitary hg
  have hsA : s ∈ P.A.N := (Subgroup.mem_inf.1 hs).1
  have hsB : s ∈ P.B.N := (Subgroup.mem_inf.1 hs).2
  have hgXA : ∀ x ∈ H.X P.A.f, g x = x := fun x hx => fix_X P.A.f (fun b => (hgf b).1) hx
  have hgXB : ∀ x ∈ H.X P.B.f, g x = x := fun x hx => fix_X P.B.f (fun b => (hgf b).2) hx
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y _ _ => ?_⟩
  · rw [hA, hA']
    exact lset_move P.A hgu hgXA hsA he x y hxy
  · rw [hB, hB']
    exact lset_move P.B hgu hgXB hsB he x y hxy
  · rw [d.io_L hsp, d'.io_L hsp]
    simp

theorem stepDataOne_of (k r : ℕ) (h : StepOrbitLat k r) : StepDataOne k r := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hrk hk P hR hP d d' t t' ht ht'
  obtain ⟨g, hg, s, hs, he⟩ := h F E M hOK V H hrk hk P hR hP d d' t t' ht ht'
  exact ⟨g, hg, moves_of hP.1 ht ht' hg hs he⟩

end Formalism.L2.SG.GoodFamilyMass
