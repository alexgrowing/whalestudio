import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

lemma hl_apply (y x : V) : hl H y x = H.h x y := rfl

lemma h_swap_zero {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h, map_zero]

lemma h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]

lemma h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

lemma mem_perp_span (s : Set V) (v : V) :
    v ∈ H.perp (Submodule.span E s) ↔ ∀ x ∈ s, H.h v x = 0 := by
  constructor
  · intro hv x hx; exact hv x (Submodule.subset_span hx)
  · intro hv x hx
    have : Submodule.span E s ≤ LinearMap.ker (hl H v) :=
      Submodule.span_le.2 fun y hy => h_swap_zero (hv y hy)
    exact h_swap_zero (this hx)

variable (Fr : LocNG.FrameD H r)

lemma mem_perpX (v : V) : v ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h v (Fr.e a) = 0 := by
  unfold HermSp.X
  rw [mem_perp_span]
  simp [LocNG.FrameD.e]

lemma h_ee (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)

lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

lemma h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if a = b then 1 else 0 := by
  rw [H.h_herm, h_e_es]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

lemma e_mem_X (a : Fin r) : Fr.e a ∈ H.X Fr.f := Submodule.subset_span ⟨a, rfl⟩

lemma z_perp : Fr.z ∈ H.perp (H.X Fr.f) :=
  (mem_perpX Fr _).2 fun a => Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)

lemma X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  exact (mem_perpX Fr _).2 fun b => h_ee Fr a b

noncomputable def prL : V →ₗ[E] V :=
  LinearMap.id - ∑ a, (hl H (Fr.es a)).smulRight (Fr.e a) - ∑ a, (hl H (Fr.e a)).smulRight (Fr.es a)

lemma prL_apply (v : V) : prL Fr v = Fr.prF v := by
  simp [prL, LocNG.FrameD.prF, hl_apply]

lemma h_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  rw [← hl_apply]
  simp only [LocNG.FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_ee, h_es_e]
  simp

lemma h_prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  rw [← hl_apply]
  simp only [LocNG.FrameD.prF, map_sub, map_sum, map_smul, hl_apply, Fr.h_ss, h_e_es]
  simp

lemma prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perpX Fr _).2 (h_prF_e Fr v)

lemma prF_of (v : V) (h1 : ∀ a, H.h v (Fr.e a) = 0) (h2 : ∀ a, H.h v (Fr.es a) = 0) :
    Fr.prF v = v := by
  simp [LocNG.FrameD.prF, h1, h2]

lemma prF_e (a : Fin r) : Fr.prF (Fr.e a) = 0 := by
  simp [LocNG.FrameD.prF, h_ee, h_e_es]

lemma prF_es (a : Fin r) : Fr.prF (Fr.es a) = 0 := by
  simp [LocNG.FrameD.prF, Fr.h_ss, h_es_e]

lemma prF_X {v : V} (hv : v ∈ H.X Fr.f) : Fr.prF v = 0 := by
  have : H.X Fr.f ≤ LinearMap.ker (prL Fr) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (prL_apply Fr _).trans (prF_e Fr a)
  exact (prL_apply Fr v).symm.trans (this hv)

lemma sub_prF {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by
  rw [mem_perpX] at hv
  simp only [LocNG.FrameD.prF, hv, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a)

lemma mkW_eq (x y : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f x = H.mkW Fr.f y ↔ (x : V) - y ∈ H.X Fr.f := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  rfl

lemma mkW_surj : Function.Surjective (H.mkW Fr.f) := Submodule.mkQ_surjective _

lemma mkW_prF (x : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f ⟨Fr.prF x, prF_perp Fr x⟩ = H.mkW Fr.f x :=
  ((mkW_eq Fr _ _).2 (sub_prF Fr x.2)).symm

noncomputable def sec : H.Wb Fr.f →ₗ[E] V :=
  Submodule.liftQ _ ((prL Fr).comp (H.perp (H.X Fr.f)).subtype) fun x hx =>
    (prL_apply Fr _).trans (prF_X Fr hx)

lemma sec_mkW (x : ↥(H.perp (H.X Fr.f))) : sec Fr (H.mkW Fr.f x) = Fr.prF x :=
  prL_apply Fr _

lemma sec_inj : Function.Injective (sec Fr) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := mkW_surj Fr a
  obtain ⟨b, rfl⟩ := mkW_surj Fr b
  rw [sec_mkW, sec_mkW] at hab
  rw [← mkW_prF Fr a, ← mkW_prF Fr b]
  congr 1
  exact Subtype.ext hab

noncomputable def pre (L : Submodule M.L.O (H.Wb Fr.f)) : Submodule M.L.O V :=
  (L.comap ((H.mkW Fr.f).restrictScalars M.L.O)).map ((H.perp (H.X Fr.f)).subtype.restrictScalars M.L.O)

lemma mem_pre (L : Submodule M.L.O (H.Wb Fr.f)) (v : V) :
    v ∈ pre Fr L ↔ ∃ hv : v ∈ H.perp (H.X Fr.f), H.mkW Fr.f ⟨v, hv⟩ ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩

lemma coe_mem_pre (L : Submodule M.L.O (H.Wb Fr.f)) (x : ↥(H.perp (H.X Fr.f))) :
    (x : V) ∈ pre Fr L ↔ H.mkW Fr.f x ∈ L := by
  rw [mem_pre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

lemma mem_map_sec (L : Submodule M.L.O (H.Wb Fr.f)) (v : V) :
    v ∈ L.map ((sec Fr).restrictScalars M.L.O) ↔ v ∈ pre Fr L ∧ ∀ a, H.h v (Fr.es a) = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := mkW_surj Fr w
    have h : ((sec Fr).restrictScalars M.L.O) (H.mkW Fr.f x) = Fr.prF x := sec_mkW Fr x
    rw [h]
    refine ⟨(mem_pre Fr L _).2 ⟨prF_perp Fr x, ?_⟩, h_prF_es Fr x⟩
    rw [mkW_prF]; exact hw
  · rintro ⟨hv, h2⟩
    obtain ⟨hv, hL⟩ := (mem_pre Fr L v).1 hv
    refine ⟨_, hL, ?_⟩
    exact (sec_mkW Fr ⟨v, hv⟩).trans (prF_of Fr v ((mem_perpX Fr v).1 hv) h2)

lemma lamStd_eq (L : Submodule M.L.O (H.Wb Fr.f)) :
    Fr.LamStd L = Submodule.span M.L.O (Set.range Fr.e) ⊔ L.map ((sec Fr).restrictScalars M.L.O) ⊔
      Submodule.span M.L.O (Set.range Fr.es) := by
  have hite : ∀ a b : Fin r, (if a = b then (1 : E) else 0) ∈ M.L.O := fun a b => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨h1, h2, w, hw, hL⟩
    have hv : v = ∑ a, H.h v (Fr.es a) • Fr.e a + Fr.prF v + ∑ a, H.h v (Fr.e a) • Fr.es a := by
      simp only [LocNG.FrameD.prF]; abel
    rw [SetLike.mem_coe, hv]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ (⟨_, h1 a⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
    · refine ⟨_, hL, (sec_mkW Fr w).trans ?_⟩
      rw [hw]
      exact prF_of Fr _ (h_prF_e Fr v) (h_prF_es Fr v)
    · exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ (⟨_, h2 a⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
  · refine sup_le (sup_le (Submodule.span_mono ?_) ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨a, rfl⟩
      refine ⟨fun b => ?_, fun b => ?_, 0, (prF_e Fr a).symm, by simp⟩
      · rw [h_e_es]; exact hite a b
      · rw [h_ee]; exact zero_mem _
    · intro v hv
      obtain ⟨hv, h2⟩ := (mem_map_sec Fr L v).1 hv
      obtain ⟨hv, hL⟩ := (mem_pre Fr L v).1 hv
      have h1 := (mem_perpX Fr v).1 hv
      refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨v, hv⟩, (prF_of Fr v h1 h2).symm, hL⟩
      · rw [h2]; exact zero_mem _
      · rw [h1]; exact zero_mem _
    · rintro _ ⟨a, rfl⟩
      refine ⟨fun b => ?_, fun b => ?_, 0, (prF_es Fr a).symm, by simp⟩
      · rw [Fr.h_ss]; exact zero_mem _
      · rw [h_es_e]; exact hite a b

lemma prim_iff (hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O) (hpir : IsPrincipalIdealRing M.L.O)
    (hT : Fr.T ≠ 0) (L : Submodule M.L.O (H.Wb Fr.f))
    (hsd : ∀ x : ↥(H.perp (H.X Fr.f)),
      H.mkW Fr.f x ∈ L ↔ ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h x y ∈ M.L.O)
    (hz : H.mkW Fr.f ⟨Fr.z, z_perp Fr⟩ ∈ L) :
    (∀ (c : M.L.O) (y : ↥(H.perp (H.X Fr.f))), H.mkW Fr.f y ∈ L →
      H.mkW Fr.f ⟨Fr.z, z_perp Fr⟩ = (c : E) • H.mkW Fr.f y → IsUnit c) ↔
    ∃ y ∈ pre Fr L, H.h Fr.z y = 1 := by
  constructor
  · intro hp
    let I : Ideal M.L.O :=
      { carrier := {c | ∃ y ∈ pre Fr L, H.h Fr.z y = (c : E)}
        zero_mem' := ⟨0, zero_mem _, h_swap_zero (H.h_zero_left _)⟩
        add_mem' := by
          rintro a b ⟨y, hy, ha⟩ ⟨y', hy', hb⟩
          exact ⟨y + y', add_mem hy hy', by rw [h_add_right, ha, hb]; rfl⟩
        smul_mem' := by
          rintro a b ⟨y, hy, hb⟩
          refine ⟨(⟨M.L.cj a, hcj _ a.2⟩ : M.L.O) • y, Submodule.smul_mem _ _ hy, ?_⟩
          change H.h Fr.z (M.L.cj a • y) = (a : E) * b
          rw [h_smul_right, M.L.cj_cj, hb] }
    obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
    have hmul : ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → ∃ b : M.L.O, (b : E) * c = H.h Fr.z y := by
      intro y hy
      have hI : (⟨_, (hsd _).1 hz y hy⟩ : M.L.O) ∈ I := ⟨y, (coe_mem_pre Fr L y).2 hy, rfl⟩
      rw [hc] at hI
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hI
      exact ⟨b, congrArg Subtype.val hb⟩
    obtain ⟨a, ha⟩ := hmul _ hz
    have hzz : H.h Fr.z Fr.z = -(algebraMap F E Fr.T) := Fr.h_zz
    have hu : (-(algebraMap F E Fr.T⁻¹) * a) * (c : E) = 1 := by
      rw [mul_assoc, ha]
      change _ * H.h Fr.z Fr.z = 1
      rw [hzz, neg_mul_neg, ← map_mul, inv_mul_cancel₀ hT, map_one]
    set u : E := -(algebraMap F E Fr.T⁻¹) * a
    have huz : H.mkW Fr.f (u • ⟨Fr.z, z_perp Fr⟩) ∈ L := by
      refine (hsd _).2 fun y hy => ?_
      obtain ⟨b, hb⟩ := hmul y hy
      change H.h (u • Fr.z) y ∈ _
      rw [H.h_smul_left, ← hb, mul_left_comm, hu, mul_one]
      exact b.2
    have hunit := hp c _ huz (by rw [map_smul, smul_smul, mul_comm, hu, one_smul])
    have h1 : (1 : M.L.O) ∈ I := by
      rw [hc]
      exact (Ideal.eq_top_iff_one _).1 (Ideal.span_singleton_eq_top.2 hunit)
    exact h1
  · rintro ⟨y0, hy0, h1⟩ c y hy hzy
    obtain ⟨hy0, hL⟩ := (mem_pre Fr L y0).1 hy0
    rw [← map_smul, mkW_eq] at hzy
    have h2 : hl H y0 (Fr.z - (c : E) • (y : V)) = 0 := h_swap_zero (hy0 _ hzy)
    rw [map_sub, map_smul, hl_apply, hl_apply, h1, sub_eq_zero] at h2
    exact IsUnit.of_mul_eq_one (⟨_, (hsd y).1 hy ⟨y0, hy0⟩ hL⟩ : M.L.O) (Subtype.ext h2.symm)

section Transport

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

lemma mem_lat (Λ : Submodule M.L.O V) (v : V) : c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← c.e.injective h]
  · intro h; exact ⟨v, h, rfl⟩

lemma mem_inn (L : Submodule M.L.O (H.Wb Fr.f)) (v : V) : c.e v ∈ c.inn Fr.f L ↔ v ∈ pre Fr L :=
  mem_lat c _ v

lemma inn_inj : Function.Injective (c.inn Fr.f) := by
  intro L L' h
  ext w
  obtain ⟨x, rfl⟩ := mkW_surj Fr w
  rw [← coe_mem_pre, ← coe_mem_pre, ← mem_inn Fr c, ← mem_inn Fr c, h]

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)

lemma mem_perp_es (hgs : ∀ a, gs a = c.e (Fr.es a)) (v : V) :
    c.e v ∈ perp M.L S.Hm (Submodule.span E (Set.range gs)) ↔ ∀ a, H.h v (Fr.es a) = 0 := by
  constructor
  · intro h a
    rw [← c.h_eq, ← hgs]
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h y hy
    obtain ⟨y, rfl⟩ := c.e.surjective y
    have : Submodule.span E (Set.range gs) ≤ (LinearMap.ker (hl H v)).map (c.e : V →ₗ[E] S.V) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact ⟨_, h_swap_zero (h a), (hgs a).symm⟩
    obtain ⟨y', hy', he⟩ := this hy
    rw [← c.e.injective he]
    exact (c.h_eq v y').trans (h_swap_zero hy')

lemma inn_inf (hgs : ∀ a, gs a = c.e (Fr.es a)) (L : Submodule M.L.O (H.Wb Fr.f)) :
    c.inn Fr.f L ⊓ (perp M.L S.Hm (Submodule.span E (Set.range gs))).restrictScalars M.L.O =
      c.lat (L.map ((sec Fr).restrictScalars M.L.O)) := by
  ext v
  obtain ⟨v, rfl⟩ := c.e.surjective v
  rw [mem_lat, mem_map_sec, Submodule.mem_inf, mem_inn, Submodule.restrictScalars_mem,
    mem_perp_es Fr c gs hgs]

lemma lat_lamStd (hg : ∀ a, g a = c.e (Fr.f a)) (hgs : ∀ a, gs a = c.e (Fr.es a))
    (L : Submodule M.L.O (H.Wb Fr.f)) :
    c.lat (Fr.LamStd L) = S.stdLat g gs (c.inn Fr.f L) := by
  unfold Frames.stdLat
  rw [inn_inf Fr c gs hgs, lamStd_eq]
  unfold Coord.lat
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Submodule.map_span,
    ← Set.range_comp, ← Set.range_comp]
  have h1 : (fun j : Fin r => g j.castSucc) =
      ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) ∘ Fr.e := funext fun a => hg _
  have h2 : gs = ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) ∘ Fr.es := funext fun a => hgs _
  rw [h1, h2]

lemma inn_surj (hg : ∀ a, g a = c.e (Fr.f a)) (A : Submodule M.L.O S.V) (hA : S.IsInner g gs A) :
    ∃ L, A = c.inn Fr.f L := by
  refine ⟨((A.comap ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)).comap
    ((H.perp (H.X Fr.f)).subtype.restrictScalars M.L.O)).map ((H.mkW Fr.f).restrictScalars M.L.O), ?_⟩
  ext v
  obtain ⟨v, rfl⟩ := c.e.surjective v
  rw [mem_inn, mem_pre]
  constructor
  · intro hv
    exact ⟨(CoordUnip.mem_perp S c.e Fr g c.h_eq hg v).2 (hA.2.1 _ hv), _, hv, rfl⟩
  · rintro ⟨hv, y, hy, hyv⟩
    have h1 : (y : V) - v ∈ H.X Fr.f := (mkW_eq Fr y ⟨v, hv⟩).1 hyv
    have h2 := hA.1 _ ((CoordUnip.mem_X S c.e Fr g hg _).1 h1)
    have h3 : c.e y ∈ A := hy
    have h4 := A.sub_mem h3 h2
    rwa [map_sub, sub_sub_cancel] at h4

lemma isInner_iff (hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O) (hpir : IsPrincipalIdealRing M.L.O)
    (hT : Fr.T ≠ 0) (hg : ∀ a, g a = c.e (Fr.f a)) (hgs : ∀ a, gs a = c.e (Fr.es a))
    (L : Submodule M.L.O (H.Wb Fr.f)) : Fr.IsInner L ↔ S.IsInner g gs (c.inn Fr.f L) := by
  have hsw : ∀ x y, H.h x y ∈ M.L.O → H.h y x ∈ M.L.O := fun x y h => by
    rw [H.h_herm]; exact hcj _ h
  have hfg : L.FG ↔ (c.inn Fr.f L ⊓
      (perp M.L S.Hm (Submodule.span E (Set.range gs))).restrictScalars M.L.O).FG := by
    rw [inn_inf Fr c gs hgs]
    constructor
    · intro h; exact (h.map _).map _
    · intro h
      exact Submodule.fg_of_fg_map_injective ((sec Fr).restrictScalars M.L.O) (sec_inj Fr)
        (Submodule.fg_of_fg_map_injective ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) c.e.injective h)
  have hsd : (∀ x : ↥(H.perp (H.X Fr.f)),
      H.mkW Fr.f x ∈ L ↔ ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h x y ∈ M.L.O) ↔
      ∀ y ∈ perp M.L S.Hm (S.spanTo g r), (∀ x ∈ c.inn Fr.f L, S.h x y ∈ M.L.O) ↔ y ∈ c.inn Fr.f L := by
    have key : ∀ x : ↥(H.perp (H.X Fr.f)),
        (∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h x y ∈ M.L.O) ↔
          ∀ y ∈ c.inn Fr.f L, S.h y (c.e x) ∈ M.L.O := by
      intro x
      constructor
      · intro h y hy
        obtain ⟨y, rfl⟩ := c.e.surjective y
        obtain ⟨hy, hL⟩ := (mem_pre Fr L y).1 ((mem_inn Fr c L y).1 hy)
        rw [c.h_eq]
        exact hsw _ _ (h ⟨y, hy⟩ hL)
      · intro h y hy
        have := h _ ((mem_inn Fr c L y).2 ((coe_mem_pre Fr L y).2 hy))
        rw [c.h_eq] at this
        exact hsw _ _ this
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := c.e.surjective y
      have hy' := (CoordUnip.mem_perp S c.e Fr g c.h_eq hg y).2 hy
      exact ((key ⟨y, hy'⟩).symm.trans (h ⟨y, hy'⟩).symm).trans
        ((coe_mem_pre Fr L ⟨y, hy'⟩).symm.trans (mem_inn Fr c L y).symm)
    · intro h x
      rw [key, h _ ((CoordUnip.mem_perp S c.e Fr g c.h_eq hg x).1 x.2), mem_inn, coe_mem_pre]
  have hz : g (Fin.last r) ∈ c.inn Fr.f L ↔ H.mkW Fr.f ⟨Fr.z, z_perp Fr⟩ ∈ L := by
    rw [hg, mem_inn]
    exact coe_mem_pre Fr L ⟨Fr.z, z_perp Fr⟩
  have hy : (∃ y ∈ pre Fr L, H.h Fr.z y = 1) ↔ ∃ y ∈ c.inn Fr.f L, S.h (g (Fin.last r)) y = 1 := by
    rw [hg]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨c.e y, (mem_inn Fr c L y).2 hy, (c.h_eq _ _).trans h⟩
    · rintro ⟨y, hy, h⟩
      obtain ⟨y, rfl⟩ := c.e.surjective y
      exact ⟨y, (mem_inn Fr c L y).1 hy, (c.h_eq _ _).symm.trans h⟩
  constructor
  · rintro ⟨h1, h2, ⟨_, _⟩, rfl, h3, h4⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_, hfg.1 h1, hsd.1 h2, hz.2 h3,
      hy.1 ((prim_iff Fr hcj hpir hT L h2 h3).1 h4)⟩
    · obtain ⟨x, rfl⟩ := c.e.surjective x
      have hx' := (CoordUnip.mem_X S c.e Fr g hg x).2 hx
      rw [mem_inn, mem_pre]
      refine ⟨X_le_perp Fr hx', ?_⟩
      rw [(mkW_eq Fr _ 0).2 (by simpa using hx'), map_zero]
      exact zero_mem _
    · obtain ⟨x, rfl⟩ := c.e.surjective x
      obtain ⟨hx', -⟩ := (mem_pre Fr L x).1 ((mem_inn Fr c L x).1 hx)
      exact (CoordUnip.mem_perp S c.e Fr g c.h_eq hg x).1 hx'
  · rintro ⟨-, -, h1, h2, h3, h4⟩
    exact ⟨hfg.2 h1, hsd.2 h2, ⟨Fr.z, z_perp Fr⟩, rfl, hz.1 h3,
      (prim_iff Fr hcj hpir hT L (hsd.2 h2) (hz.1 h3)).2 (hy.2 h4)⟩

end Transport

theorem transport : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.B.f) ∧ (∀ L, P.B.IsInner L ↔ S.IsInner S.f' S.es' (c.inn P.B.f L)) ∧ (∀ A, S.IsInner S.f' S.es' A → ∃ L, A = c.inn P.B.f L) ∧ ∀ L, c.lat (P.B.LamStd L) = S.stdLat S.f' S.es' (c.inn P.B.f L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  letI := hM.loc
  letI := hM.char0
  have hO := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hT : P.B.T ≠ 0 := by rw [← c.T'_eq]; exact S.T'.ne_zero
  exact ⟨inn_inj P.B c,
    isInner_iff P.B c S.f' S.es' (fun x hx => (hO.2.1 x hx).1) hO.2.2.2.1 hT c.f'_eq c.es'_eq,
    inn_surj P.B c S.f' S.es' c.f'_eq, lat_lamStd P.B c S.f' S.es' c.f'_eq c.es'_eq⟩

end GlobalTheory.HL.CoordInnerSnd
