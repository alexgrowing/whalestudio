import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField

namespace LocF

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem incf_res_q : Lc.res (q : Lc.O) = 0 := (Lc.res_ker _).2 ⟨1, by simp⟩

theorem incf_inv_q : ((q : Lc.K))⁻¹ ∉ Lc.O := fun h => by
  have : Lc.res 1 = 0 := (Lc.res_ker _).2 ⟨⟨_, h⟩, by simp [Lc.q_ne]⟩
  simp at this

theorem incf_inv_mem (a : Lc.O) (ha : Lc.res a ≠ 0) : (a : Lc.K) ≠ 0 ∧ (a : Lc.K)⁻¹ ∈ Lc.O := by
  have h0 : (a : Lc.K) ≠ 0 := fun h => ha (by
    have : a = 0 := Subtype.ext h
    simp [this])
  refine ⟨h0, ?_⟩
  obtain ⟨m, y, hy, hy', hay⟩ := Lc.sep a h0
  have hq : (q : Lc.K) ∈ Lc.O := natCast_mem _ _
  have hy0 : y ≠ 0 := by rintro rfl; exact h0 (by simpa using hay)
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -((k : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    apply incf_inv_q (Lc := Lc)
    have : ((q : Lc.K))⁻¹ = a * y⁻¹ * (q : Lc.K) ^ k := by
      have := Lc.q_ne
      rw [hay, hk, zpow_neg, zpow_add_one₀ this, zpow_natCast]
      field_simp
    rw [this]
    exact mul_mem (mul_mem a.2 hy') (pow_mem hq _)
  · rw [hay]; simpa using hy'
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = ((k : ℤ) + 1) := ⟨(m - 1).toNat, by omega⟩
    apply ha
    refine (Lc.res_ker _).2 ⟨⟨(q : Lc.K) ^ k * y, mul_mem (pow_mem hq _) hy⟩, ?_⟩
    rw [hay, hk, zpow_add_one₀ Lc.q_ne, zpow_natCast]
    simp only
    ring

theorem incf_mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ k, x k ∈ Lc.O := by
  simp only [std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem incf_smul (a : Lc.O) (x : Fin n → Lc.K) : a • x = (a : Lc.K) • x := rfl

theorem incf_q_smul (x : Fin n → Lc.K) : (q : Lc.K) • x = (q : Lc.O) • x := by
  rw [incf_smul]; simp

theorem incf_mem_of_ne (p : PP Lc n) {x : Fin n → Lc.K} (h : p.1.f x ≠ 0) : x ∈ p.1.L := by
  by_contra h'; exact h (p.2.off x h')

theorem incf_f_q (p : PP Lc n) {x : Fin n → Lc.K} (h : x ∈ p.1.L) : p.1.f ((q : Lc.K) • x) = 0 := by
  rw [incf_q_smul, p.2.smul _ _ h, incf_res_q, zero_mul]

theorem incf_q_mem (L : Submodule Lc.O (Fin n → Lc.K)) {x : Fin n → Lc.K} (h : x ∈ L) : (q : Lc.K) • x ∈ L := by
  rw [incf_q_smul]; exact L.smul_mem _ h

theorem incf_ext (p p' : PP Lc n) (hL : ∀ x, x ∈ p.1.L ↔ x ∈ p'.1.L) (hf : ∀ x ∈ p.1.L, p.1.f x = p'.1.f x) :
    p = p' := by
  apply Subtype.ext
  apply Raw.ext
  · exact Submodule.ext hL
  · funext x
    by_cases hx : x ∈ p.1.L
    · exact hf x hx
    · rw [p.2.off x hx, p'.2.off x (fun h => hx ((hL x).2 h))]

theorem latticeFunctionalPair_mem_eq_of_ker_eq (p p' : PP Lc n) (hk : p.ker = p'.ker) {e : Fin n → Lc.K} (he : p.1.f e = 1)
    (he' : p'.1.f e = 1) (y : Fin n → Lc.K) (hy : y ∈ p.1.L) : y ∈ p'.1.L ∧ p.1.f y = p'.1.f y := by
  obtain ⟨a, ha⟩ := Lc.res_surj (p.1.f y)
  have h1 : e ∈ p.1.L := incf_mem_of_ne p (by simp [he])
  have h1' : e ∈ p'.1.L := incf_mem_of_ne p' (by simp [he'])
  have h2 : y + (-a) • e ∈ p.ker := by
    refine ⟨add_mem hy (p.1.L.smul_mem _ h1), ?_⟩
    rw [p.2.add _ hy _ (p.1.L.smul_mem _ h1), p.2.smul _ _ h1, he, map_neg, ha]; ring
  rw [hk] at h2
  have h3 : y = (y + (-a) • e) + a • e := by simp
  refine ⟨h3 ▸ add_mem h2.1 (p'.1.L.smul_mem _ h1'), ?_⟩
  conv_rhs => rw [h3]
  rw [p'.2.add _ h2.1 _ (p'.1.L.smul_mem _ h1'), h2.2, p'.2.smul _ _ h1', he', ha]; ring

theorem incf_ker_ext (p p' : PP Lc n) (hk : p.ker = p'.ker) {e : Fin n → Lc.K} (he : p.1.f e = 1)
    (he' : p'.1.f e = 1) : p = p' :=
  incf_ext p p' (fun x => ⟨fun h => (latticeFunctionalPair_mem_eq_of_ker_eq p p' hk he he' x h).1,
    fun h => (latticeFunctionalPair_mem_eq_of_ker_eq p' p hk.symm he' he x h).1⟩) fun x h => (latticeFunctionalPair_mem_eq_of_ker_eq p p' hk he he' x h).2

theorem incf_surj (h : GL (Fin n) Lc.K) (x : Fin n → Lc.K) :
    ∃ u, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) u = x :=
  ⟨Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

theorem incf_reps [Finite F] (L : Submodule Lc.O (Fin n → Lc.K)) (hL : ∃ h, Lc.IsFrame n h L) :
    ∃ S : Set (Fin n → Lc.K), S.Finite ∧ (∀ s ∈ S, s ∈ L) ∧
      ∀ x ∈ L, ∃ s ∈ S, ∃ l ∈ L, x = s + (q : Lc.K) • l := by
  obtain ⟨h, hh⟩ := hL
  choose σ hσ using Lc.res_surj
  refine ⟨Set.range fun c : Fin n → F =>
    Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun k => (σ (c k) : Lc.K)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (hh _).2 ((incf_mem_std _).2 fun k => (σ (c k)).2)
  · intro x hx
    obtain ⟨u, rfl⟩ := incf_surj h x
    have hu := (incf_mem_std _).1 ((hh u).1 hx)
    have : ∀ k, ∃ y : Lc.O, u k = σ (Lc.res ⟨u k, hu k⟩) + (q : Lc.K) * y := fun k => by
      obtain ⟨y, hy⟩ := (Lc.res_ker (⟨u k, hu k⟩ - σ (Lc.res ⟨u k, hu k⟩))).1 (by simp [hσ])
      refine ⟨y, ?_⟩
      rw [← hy]; simp
    choose y hy using this
    refine ⟨_, ⟨fun k => Lc.res ⟨u k, hu k⟩, rfl⟩,
      Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun k => (y k : Lc.K)),
      (hh _).2 ((incf_mem_std _).2 fun k => (y k).2), ?_⟩
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
    congr 1
    funext k
    simpa using hy k

theorem incf_fin_up [Finite F] (p : PP Lc n) : {p₁ | p.Inc p₁}.Finite := by
  obtain ⟨S, hS, hSL, hrep⟩ := incf_reps p.1.L p.2.lat
  refine Set.Finite.subset (hS.biUnion (t := fun s =>
    {p₁ : PP Lc n | p₁.ker = (p.1.L : Set _) ∧ p₁.1.f (((q : Lc.K))⁻¹ • s) = 1}) fun s _ =>
      Set.Subsingleton.finite fun a ha b hb => incf_ker_ext a b (ha.1.trans hb.1.symm) ha.2 hb.2) ?_
  rintro p₁ ⟨x, -, hx, hk, hf⟩
  obtain ⟨s, hs, l, hl, rfl⟩ := hrep x hx
  simp only [Set.mem_iUnion]
  refine ⟨s, hs, hk, ?_⟩
  have hl' : -l ∈ p₁.ker := by rw [hk]; exact neg_mem hl
  have : ((q : Lc.K))⁻¹ • s = ((q : Lc.K))⁻¹ • (s + (q : Lc.K) • l) + -l := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ Lc.q_ne]; simp
  rw [this, p₁.2.add _ (incf_mem_of_ne p₁ (by rw [hf]; exact one_ne_zero)) _ hl'.1, hf, hl'.2, add_zero]

theorem incf_fin_dn [Finite F] (p : PP Lc n) : {p₀ : PP Lc n | p₀.Inc p}.Finite := by
  rcases Set.eq_empty_or_nonempty {p₀ : PP Lc n | p₀.Inc p} with h | ⟨r, -, -, -, hr, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨S, hS, hSL, hrep⟩ := incf_reps r.1.L r.2.lat
  haveI := hS.to_subtype
  refine Set.Finite.of_finite_image (f := fun (a : PP Lc n) (s : S) => a.1.f s) (Set.toFinite _) ?_
  rintro a ⟨-, -, -, ha, -⟩ b ⟨-, -, -, hb, -⟩ hab
  have ha' : a.1.L = r.1.L := SetLike.coe_injective (ha.symm.trans hr)
  have hb' : b.1.L = r.1.L := SetLike.coe_injective (hb.symm.trans hr)
  refine incf_ext a b (fun x => by rw [ha', hb']) fun x hx => ?_
  obtain ⟨s, hs, l, hl, rfl⟩ := hrep x (ha' ▸ hx)
  have h1 := hSL s hs
  rw [a.2.add _ (ha' ▸ h1) _ (incf_q_mem _ (ha' ▸ hl)), b.2.add _ (hb' ▸ h1) _ (incf_q_mem _ (hb' ▸ hl)),
    incf_f_q a (ha' ▸ hl), incf_f_q b (hb' ▸ hl)]
  exact congrArg (· + 0) (congrFun hab ⟨s, hs⟩)

theorem incf_act_unique {g : GL (Fin n) Lc.K} {p a b : PP Lc n} (ha : p.IsAct g a) (hb : p.IsAct g b) : a = b := by
  refine incf_ext a b (fun x => ?_) fun x _ => ?_
  · obtain ⟨u, rfl⟩ := incf_surj g x
    rw [(ha u).1, (hb u).1]
  · obtain ⟨u, rfl⟩ := incf_surj g x
    rw [(ha u).2, (hb u).2]

theorem incf_act_inc {g : GL (Fin n) Lc.K} {p p₁ a a₁ : PP Lc n} (ha : p.IsAct g a) (ha₁ : p₁.IsAct g a₁)
    (h : p.Inc p₁) : a.Inc a₁ := by
  obtain ⟨x, hx, hxL, hk, hf⟩ := h
  refine ⟨Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x, by rw [(ha x).2, hx], (ha x).1.2 hxL, ?_, ?_⟩
  · ext y
    obtain ⟨u, rfl⟩ := incf_surj g y
    have : u ∈ p₁.ker ↔ u ∈ p.1.L := by rw [hk]; rfl
    simp only [PP.ker, Set.mem_setOf_eq, SetLike.mem_coe] at this ⊢
    rw [(ha₁ u).1, (ha₁ u).2, (ha u).1, this]
  · rw [← Matrix.mulVec_smul, (ha₁ _).2, hf]

theorem incf_frame (p : PP Lc n) {x : Fin n → Lc.K} (hx : p.1.f x = 1) :
    ∃ h, Lc.IsFrame n h (p.1.L ⊔ Submodule.span Lc.O {((q : Lc.K))⁻¹ • x}) := by
  obtain ⟨h, hh⟩ := p.2.lat
  have hxL : x ∈ p.1.L := incf_mem_of_ne p (by simp [hx])
  obtain ⟨u, rfl⟩ := incf_surj h x
  have hu := (incf_mem_std _).1 ((hh u).1 hxL)
  have hq := Lc.q_ne
  have hqO : (q : Lc.K) ∈ Lc.O := natCast_mem _ _
  obtain ⟨j, hj⟩ : ∃ j, Lc.res ⟨u j, hu j⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    choose y hy using fun k => (Lc.res_ker _).1 (hcon k)
    have : u = (q : Lc.K) • fun k => (y k : Lc.K) := funext fun k => by simpa using hy k
    rw [this, Matrix.mulVec_smul, incf_f_q p ((hh _).2 ((incf_mem_std _).2 fun k => (y k).2))] at hx
    exact zero_ne_one hx
  obtain ⟨hj0, hji⟩ := incf_inv_mem _ hj
  simp only at hj0 hji
  set A : Matrix (Fin n) (Fin n) Lc.K := (1 : Matrix (Fin n) (Fin n) Lc.K).updateCol j (((q : Lc.K))⁻¹ • u) with hA
  have hdet : A.det ≠ 0 := by
    rw [hA, ← Matrix.cramer_apply, Matrix.cramer_one]
    simp [hq, hj0]
  have hAy : ∀ (y : Fin n → Lc.K), A.mulVec y = Function.update y j 0 + y j • (((q : Lc.K))⁻¹ • u) := by
    intro y
    funext k
    simp only [hA, Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl, add_comm,
      Finset.sum_congr rfl (g := fun i => if k = i then y i else 0)
        (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi), Matrix.one_apply]; split_ifs <;> simp),
      Finset.sum_ite_eq]
    by_cases hk : k = j
    · subst hk; simp; ring
    · simp [hk, Function.update_of_ne hk]; ring
  refine ⟨h * Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, fun y => ?_⟩
  have hv : ((h * Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)
      = (h : Matrix (Fin n) (Fin n) Lc.K) * A := rfl
  rw [hv, ← Matrix.mulVec_mulVec, hAy, Submodule.mem_sup, incf_mem_std]
  constructor
  · rintro ⟨l, hl, z, hz, hlz⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h1 : Function.update y j 0 + y j • (((q : Lc.K))⁻¹ • u) - (a : Lc.K) • (((q : Lc.K))⁻¹ • u) ∈ Lc.std n := by
      rw [← hh, Matrix.mulVec_sub, ← hlz, Matrix.mulVec_smul, Matrix.mulVec_smul, incf_smul]
      simpa using hl
    rw [incf_mem_std] at h1
    have h2 := h1 j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.update_self] at h2
    intro k
    by_cases hk : k = j
    · subst hk
      convert add_mem (mul_mem (mul_mem h2 hqO) hji) a.2 using 1
      field_simp
      ring
    · have h3 := h1 k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.update_of_ne hk] at h3
      convert sub_mem h3 (mul_mem (mul_mem h2 hji) (hu k)) using 1
      field_simp
      ring
  · intro hy
    refine ⟨Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Function.update y j 0), ?_,
      (⟨y j, hy j⟩ : Lc.O) • _, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    · refine (hh _).2 ((incf_mem_std _).2 fun k => ?_)
      by_cases hk : k = j
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hy k
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, incf_smul]

theorem incf_up_existsUnique (p : PP Lc n) (x : Fin n → Lc.K) (hx : p.1.f x = 1) : ∃! r, p.IsUp x r := by
  have hxL : x ∈ p.1.L := incf_mem_of_ne p (by simp [hx])
  have hq := Lc.q_ne
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb =>
    incf_ker_ext a b (ha.2.1.trans hb.2.1.symm) ha.2.2 hb.2.2
  set L := p.1.L ⊔ Submodule.span Lc.O {((q : Lc.K))⁻¹ • x} with hL
  have hmem : ∀ y, y ∈ L ↔ ∃ l ∈ p.1.L, ∃ a : Lc.O, y = l + a • ((q : Lc.K))⁻¹ • x := fun y => by
    rw [hL, Submodule.mem_sup]
    constructor
    · rintro ⟨l, hl, z, hz, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact ⟨l, hl, a, rfl⟩
    · rintro ⟨l, hl, a, rfl⟩
      exact ⟨l, hl, _, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩
  have hqe : ∀ (l : Fin n → Lc.K) (a : Lc.O),
      (q : Lc.K) • (l + a • ((q : Lc.K))⁻¹ • x) = (q : Lc.K) • l + a • x := fun l a => by
    rw [smul_add, smul_comm (q : Lc.K) a, smul_smul (q : Lc.K), mul_inv_cancel₀ hq, one_smul]
  have hqL : ∀ y ∈ L, (q : Lc.K) • y ∈ p.1.L := fun y hy => by
    obtain ⟨l, hl, a, rfl⟩ := (hmem y).1 hy
    rw [hqe]
    exact add_mem (incf_q_mem _ hl) (p.1.L.smul_mem _ hxL)
  have he : ((q : Lc.K))⁻¹ • x ∈ L := (hmem _).2 ⟨0, zero_mem _, 1, by simp⟩
  have hfe : p.1.f ((q : Lc.K) • ((q : Lc.K))⁻¹ • x) = 1 := by
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul, hx]
  refine ⟨⟨⟨L, fun y => if y ∈ L then p.1.f ((q : Lc.K) • y) else 0⟩, incf_frame p hx, ?_, ?_, ?_, ?_⟩,
    hxL, ?_, ?_⟩
  · intro y hy z hz
    simp only at hy hz ⊢
    rw [if_pos hy, if_pos hz, if_pos (add_mem hy hz), smul_add, p.2.add _ (hqL y hy) _ (hqL z hz)]
  · intro a y hy
    simp only at hy ⊢
    rw [if_pos hy, if_pos (L.smul_mem a hy), smul_comm, p.2.smul _ _ (hqL y hy)]
  · intro y hy
    simp only at hy ⊢
    rw [if_neg hy]
  · exact ⟨_, by simp only; rw [if_pos he, hfe]; exact one_ne_zero⟩
  · ext y
    simp only [PP.ker, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨hy, hf⟩
      rw [if_pos hy] at hf
      obtain ⟨l, hl, a, rfl⟩ := (hmem y).1 hy
      rw [hqe, p.2.add _ (incf_q_mem _ hl) _ (p.1.L.smul_mem _ hxL), incf_f_q p hl, p.2.smul _ _ hxL, hx,
        zero_add, mul_one] at hf
      obtain ⟨b, hb⟩ := (Lc.res_ker a).1 hf
      have : a • ((q : Lc.K))⁻¹ • x = b • x := by
        rw [incf_smul, incf_smul, smul_smul, hb]
        congr 1
        field_simp
      rw [this]
      exact add_mem hl (p.1.L.smul_mem _ hxL)
    · intro hy
      have hy' : y ∈ L := (hmem _).2 ⟨y, hy, 0, by simp⟩
      exact ⟨hy', by rw [if_pos hy', incf_f_q p hy]⟩
  · simp only
    rw [if_pos he, hfe]

end LocF

theorem PtModel.inc_smul {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} (M : PtModel X i) (v : X.A.vT)
    (g : M.G) (p p₁ : M.Pt) (h : M.Inc v p p₁) : M.Inc v (g • p) (g • p₁) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨M.smul_fst g _ _ h1, fun v' hv' => ?_,
    LocF.incf_act_inc (M.smul_snd g p v) (M.smul_snd g p₁ v) h3⟩
  have := M.smul_snd g p₁ v'
  rw [h2 v' hv'] at this
  exact LocF.incf_act_unique this (M.smul_snd g p v')

theorem inc_finite_stable (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) :
    (∀ p, {p₁ | M.Inc v p p₁}.Finite ∧ {p₀ | M.Inc v p₀ p}.Finite) ∧
    (∀ (g : M.G) p p₁, M.Inc v p p₁ ↔ M.Inc v (g • p) (g • p₁)) ∧
    ∀ (p : M.Pt) x, (p.2 v).1.f x = 1 → ∃! q, (p.2 v).IsUp x q := by
  refine ⟨fun p => ⟨?_, ?_⟩, fun g p p₁ => ⟨M.inc_smul v g p p₁, fun h => ?_⟩,
    fun p x hx => LocF.incf_up_existsUnique _ x hx⟩
  · refine Set.Finite.of_finite_image (f := fun a : M.Pt => a.2 v) ((LocF.incf_fin_up (p.2 v)).subset ?_) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ha.2.2
    · intro a ha b hb hab
      refine Prod.ext (ha.1.trans hb.1.symm) (funext fun v' => ?_)
      by_cases hv : v' = v
      · subst hv; exact hab
      · exact (ha.2.1 v' hv).trans (hb.2.1 v' hv).symm
  · refine Set.Finite.of_finite_image (f := fun a : M.Pt => a.2 v) ((LocF.incf_fin_dn (p.2 v)).subset ?_) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ha.2.2
    · intro a ha b hb hab
      refine Prod.ext (ha.1.symm.trans hb.1) (funext fun v' => ?_)
      by_cases hv : v' = v
      · subst hv; exact hab
      · exact (ha.2.1 v' hv).symm.trans (hb.2.1 v' hv)
  · simpa using M.inc_smul v g⁻¹ _ _ h

end GlobalTheory.LvT
