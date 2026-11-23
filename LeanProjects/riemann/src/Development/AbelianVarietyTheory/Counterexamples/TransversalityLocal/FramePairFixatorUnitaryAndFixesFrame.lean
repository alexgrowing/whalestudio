import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.NonGenericLocalCheck

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}

theorem exists_transv {α : Type*} (rel : α → α → Prop) (hr : Equivalence rel) (S : Set α) :
    ∃ R, IsTransv rel S R := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, Set.empty_subset _, fun x => isEmptyElim x, fun y hy => hy.elim⟩

  obtain ⟨pick, hpk⟩ : ∃ pick : α → α, ∀ x, pick x = Classical.epsilon (fun y => y ∈ S ∧ rel y x) :=
    ⟨_, fun _ => rfl⟩
  have hpick : ∀ x ∈ S, pick x ∈ S ∧ rel (pick x) x := fun x hx => by
    rw [hpk]
    exact Classical.epsilon_spec (p := fun y => y ∈ S ∧ rel y x) ⟨x, hx, hr.refl x⟩
  have hcongr : ∀ x x', rel x x' → pick x = pick x' := by
    intro x x' h
    have hset : (fun y => y ∈ S ∧ rel y x) = (fun y => y ∈ S ∧ rel y x') := by
      funext y
      exact propext ⟨fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx h⟩,
        fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx (hr.symm h)⟩⟩
    rw [hpk, hpk, hset]
  refine ⟨pick '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hpick x hx).1
  · intro x hx
    exact ⟨pick x, ⟨x, hx, rfl⟩, (hpick x hx).2⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    exact hcongr x x' (hr.trans (hr.symm (hpick x hx).2) (hr.trans h (hpick x' hx').2))

section General
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * g') Λ = img g (img g' Λ) := by
  ext x
  simp only [img, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [img, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem trel_equiv (P : FPair H r) : Equivalence (TRel P) where
  refl t := ⟨1, P.St.one_mem, (img_one _).symm⟩
  symm := by
    rintro t t' ⟨s, hs, h⟩
    refine ⟨s⁻¹, P.St.inv_mem hs, ?_⟩
    rw [h, ← img_mul, inv_mul_cancel, img_one]
  trans := by
    rintro t t' t'' ⟨s, hs, h⟩ ⟨s', hs', h'⟩
    exact ⟨s' * s, P.St.mul_mem hs' hs, by rw [h', h, img_mul]⟩

theorem framePairFixator_unitary_and_fixes_frame (P : FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    have hyu : ∀ u w, H.h (y u) (y w) = H.h u w := hy.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x (y u)) (x (y w)) = H.h u w
      rw [hxu, hyu]
    · change x (y _) = _
      rw [(hy.2 b).1, (hx.2 b).1]
    · change x (y _) = _
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x.symm u) (x.symm w) = H.h u w
      have key := hxu (x.symm u) (x.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at key
      exact key.symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).1).symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).2).symm

theorem perp_stable {g : V ≃ₗ[E] V} (hu : IsUnitary H g) (f : Fin (r + 1) → V)
    (hf : ∀ b, g (f b) = f b) {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  have hfix : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_eqLocus.mpr (hf _)
  have hv' : ∀ x ∈ H.X f, H.h v x = 0 := hv
  have hu' : ∀ x y, H.h (g x) (g y) = H.h x y := hu
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' : g x = x := LinearMap.mem_eqLocus.mp (hfix hx)
  rw [← hx', hu']
  exact hv' x hx

theorem rel_equiv (P : FPair H r) : Equivalence (Datum.Rel (P := P)) where
  refl d := ⟨1, P.UW0.one_mem, by
    refine ⟨fun x y h => ?_, fun x y h => ?_, fun x' y' x y h' h => ?_⟩
    · rw [show y = x from Subtype.ext h]
    · rw [show y = x from Subtype.ext h]
    · rw [show y' = x' from Subtype.ext h', show y = x from Subtype.ext h]⟩
  symm := by
    rintro d d' ⟨g, hg, h1, h2, h3⟩
    refine ⟨g⁻¹, P.UW0.inv_mem hg, fun x y hxy => ?_, fun x y hxy => ?_,
      fun x' y' x y hx' hx => ?_⟩
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h1 y x e).symm
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h2 y x e).symm
    · have e1 : (x' : V) = g y' := by rw [hx']; exact (g.apply_symm_apply (x' : V)).symm
      have e2 : (x : V) = g y := by rw [hx]; exact (g.apply_symm_apply (x : V)).symm
      exact (h3 y' x' y x e1 e2).symm
  trans := by
    rintro d d' d'' ⟨g, hg, h1, h2, h3⟩ ⟨g', hg', k1, k2, k3⟩
    have sA : ∀ u : ↥(H.perp (H.X P.A.f)), g u ∈ H.perp (H.X P.A.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.A.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).1) u.2
    have sB : ∀ u : ↥(H.perp (H.X P.B.f)), g u ∈ H.perp (H.X P.B.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.B.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).2) u.2
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, fun x z hz => ?_, fun x z hz => ?_,
      fun x' z' x z hz' hz => ?_⟩
    · exact (h1 x ⟨g x, sA x⟩ rfl).trans (k1 ⟨g x, sA x⟩ z hz)
    · exact (h2 x ⟨g x, sB x⟩ rfl).trans (k2 ⟨g x, sB x⟩ z hz)
    · exact (h3 x' ⟨g x', sB x'⟩ x ⟨g x, sA x⟩ rfl rfl).trans (k3 ⟨g x', sB x'⟩ z' ⟨g x, sA x⟩ z hz' hz)

theorem reps_nonempty (P : FPair H r) : Nonempty (Reps P) := by
  choose RT hRT using fun d : Datum P =>
    exists_transv (TRel P) (trel_equiv P) {t | IsTermOver P d t}
  obtain ⟨RD, hRD⟩ := exists_transv (Datum.Rel (P := P)) (rel_equiv P) Set.univ
  exact ⟨⟨RD, RT, hRD, hRT⟩⟩

theorem wt_self {P : FPair H r} (d : Datum P) : Datum.wt d d = 1 := by
  unfold Datum.wt volRel
  rw [Subgroup.relIndex_self]
  norm_num

theorem X_zero (f : Fin 1 → V) : H.X (r := 0) f = ⊥ := by
  change Submodule.span E (Set.range fun a : Fin 0 => f a.castSucc) = ⊥
  rw [Set.range_eq_empty, Submodule.span_empty]

theorem mem_perp_zero (f : Fin 1 → V) (v : V) : v ∈ H.perp (H.X (r := 0) f) := by
  show ∀ x ∈ H.X (r := 0) f, H.h v x = 0
  intro x hx
  rw [X_zero, Submodule.mem_bot] at hx
  subst hx
  rw [H.h_herm, H.h_zero_left, map_zero]

theorem mkW_inj (f : Fin 1 → V) : Function.Injective (H.mkW (r := 0) f) := by
  intro a b hab
  simp only [HermSp.mkW, Submodule.mkQ_apply] at hab
  have hXb : ∀ v : V, v ∈ H.X (r := 0) f → v = 0 := fun v hv => by
    rw [X_zero] at hv
    exact (Submodule.mem_bot E).mp hv
  have hmem := (Submodule.Quotient.eq _).mp hab
  have h0 : ((a - b : H.perp (H.X (r := 0) f)) : V) = 0 := hXb _ (Submodule.mem_comap.mp hmem)
  exact sub_eq_zero.mp (Subtype.ext h0)

end General

section Model
variable (M) (m : ℕ)

def stdH : HermSp M (Fin (m + 2) → E) where
  h x y := ∑ i, x i * M.L.cj (y i)
  h_add_left x x' y := by simp [add_mul, Finset.sum_add_distrib]
  h_smul_left a x y := by simp [Finset.mul_sum, mul_assoc]
  h_herm x y := by simp [map_sum, M.L.cj_cj, mul_comm]
  nondeg x hx := by
    funext i
    simpa [Pi.single_apply, apply_ite M.L.cj] using hx (Pi.single i 1)
  free := inferInstance
  fin := inferInstance

theorem stdH_single (x : Fin (m + 2) → E) (i) : (stdH M m).h x (Pi.single i 1) = x i := by
  change ∑ j, x j * M.L.cj ((Pi.single i (1 : E) : Fin (m + 2) → E) j) = x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

def vec (c : F) : Fin (m + 2) → E := Pi.single 0 1 + Pi.single 1 (algebraMap F E c)

theorem vec_zero (c : F) : vec (E := E) m c 0 = 1 := by
  have h : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
  simp [vec, Pi.single_apply, h]
theorem vec_one (c : F) : vec (E := E) m c 1 = algebraMap F E c := by
  have h : (1 : Fin (m + 2)) ≠ 0 := by simp [Fin.ext_iff]
  simp [vec, Pi.single_apply, h]

theorem h_vec (c c' : F) : (stdH M m).h (vec m c) (vec m c') = algebraMap F E (1 + c * c') := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
  change ∑ i, vec m c i * M.L.cj (vec m c' i) = _
  rw [Finset.sum_eq_add (0 : Fin (m + 2)) 1 h01]
  · rw [vec_zero, vec_zero, vec_one, vec_one]
    simp [map_add, map_mul]
  · intro i _ hi
    simp [vec, Pi.single_apply, hi.1, hi.2]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h

def frame (c : F) : FrameD (stdH M m) 0 where
  f _ := vec m c
  es := Fin.elim0
  T := -(1 + c * c)
  h_iso a b h := by
    rcases h with h | h <;> exact absurd (Subsingleton.elim (α := Fin 1) _ _) h
  h_zz := by rw [h_vec, map_neg, neg_neg]
  h_ss i := i.elim0
  h_es i := i.elim0
  h_sz i := i.elim0

def pair : FPair (stdH M m) 0 := ⟨frame M m 0, frame M m (theta M)⟩

theorem theta_int : theta M ∈ 𝒪[F] := by
  rcases h : M.split with _ | g <;> simp only [theta, h]
  · exact one_mem _
  · exact g.q.2

theorem theta_ne : theta M ≠ 0 := by
  rcases h : M.split with _ | g <;> simp only [theta, h]
  · exact one_ne_zero
  · intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)

theorem theta_some {g} (h : M.split = some g) : theta M = (g.q : F) := by
  simp only [theta, h]

theorem unit_some (g : SplitG M.L) : ∃ v : 𝒪[F], (v : F) * -(1 + (g.q : F) * g.q) = 1 := by
  have hle : valuation F (g.q : F) ≤ 1 := g.q.2
  have hq1 : valuation F (g.q : F) < 1 := by
    refine lt_of_le_of_ne hle fun h1 => g.q_irr.not_isUnit ?_
    exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mpr h1
  have hnu : ¬ IsUnit (g.q * g.q) := fun h => g.q_irr.not_isUnit (isUnit_of_mul_isUnit_left h)
  have hqq : valuation F ((g.q : F) * g.q) < 1 := by
    have hle2 : valuation F ((g.q * g.q : 𝒪[F]) : F) ≤ 1 := (g.q * g.q).2
    refine lt_of_le_of_ne hle2 fun h1 => hnu ?_
    exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mpr h1
  have hv : valuation F (1 + (g.q : F) * g.q) = 1 := Valuation.map_one_add_of_lt (valuation F) hqq
  have hne : (1 + (g.q : F) * g.q) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨⟨-(1 + (g.q : F) * g.q)⁻¹, ?_⟩, ?_⟩
  · change valuation F _ ≤ 1
    simp only [Valuation.map_neg, map_inv₀, hv, inv_one, le_refl]
  · change -(1 + (g.q : F) * g.q)⁻¹ * -(1 + (g.q : F) * g.q) = 1
    rw [neg_mul_neg, inv_mul_cancel₀ hne]

theorem D0 : (pair M m).Dm 0 = 1 := by
  simp [FPair.Dm, HermSp.Dl]
theorem D1 : (pair M m).Dm 1 = 1 := by
  simp [FPair.Dm, HermSp.Dl, HermSp.Zhat, pair, frame, h_vec, Matrix.det_fin_one]

theorem relG [CharZero F] : (pair M m).RelG (theta M) := by
  haveI : Nontrivial E := by
    by_contra hE
    rw [not_nontrivial_iff_subsingleton] at hE
    have h2 := M.L.rank
    rw [Module.finrank_zero_of_subsingleton] at h2
    norm_num at h2
  have hθ := theta_ne M
  have hd1 : (pair M m).Dm 1 = 1 := D1 M m
  have hd0 : (pair M m).Dm 0 = 1 := D0 M m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨h1, h2⟩ := hx
    simp only [HermSp.Xp, pair, frame, Set.range_const, Submodule.mem_span_singleton] at h1 h2
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hc := congrFun hb 1
    simp only [Pi.smul_apply, smul_eq_mul, vec_one, map_zero, mul_zero] at hc
    have hu : IsUnit (algebraMap F E (theta M)) := (isUnit_iff_ne_zero.mpr hθ).map _
    have hb0 : b = 0 := (hu.mul_left_eq_zero).mp hc
    rw [Submodule.mem_bot, ← hb, hb0, zero_smul]
  · change IsUnit ((pair M m).Dm 1)
    rw [hd1]
    exact isUnit_one
  · have hG : (pair M m).Gv = -algebraMap F E (theta M * theta M) := by
      simp only [FPair.Dm] at hd1 hd0
      simp only [FPair.Gv, HermSp.Gdet, HermSp.normE, zero_add, hd1, hd0, map_one, mul_one]
      simp only [pair, frame, map_mul, map_neg, map_add, map_one, mul_zero, add_zero]
      ring
    rw [hG, neg_ne_zero]
    exact (map_ne_zero _).mpr (mul_ne_zero hθ hθ)
  · intro l hl
    interval_cases l
    · exact Or.inr (by rw [hd0]; exact isUnit_one)
    · exact Or.inr (by rw [hd1]; exact isUnit_one)
  · intro g _
    simp [FrameD.psiN, FrameD.psiOf, FrameD.coefSum]
  · refine ⟨⟨[(1, 1)], by simp⟩, fun a b => ?_⟩
    fin_cases a
    fin_cases b
    simp [Pt.mat, ptEntryL, HermSp.Zhat, pair, frame, h_vec]
  · have hT : (1 + theta M * theta M) ≠ 0 := by
      rcases h : M.split with _ | g
      · have e : theta M = 1 := by simp only [theta, h]
        rw [e]
        norm_num
      · obtain ⟨v, hv⟩ := unit_some M g
        rw [theta_some M h]
        intro h0
        rw [h0, neg_zero, mul_zero] at hv
        exact zero_ne_one hv
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · change -(1 + (0 : F) * 0) ∈ 𝒪[F]
      exact neg_mem (add_mem (one_mem _) (mul_mem (zero_mem _) (zero_mem _)))
    · change -(1 + (0 : F) * 0) ≠ 0
      norm_num
    · change -(1 + theta M * theta M) ∈ 𝒪[F]
      exact neg_mem (add_mem (one_mem _) (mul_mem (theta_int M) (theta_int M)))
    · change -(1 + theta M * theta M) ≠ 0
      exact neg_ne_zero.mpr hT
    · obtain ⟨v, hv⟩ := unit_some M g
      refine ⟨-1, v, ?_, ?_⟩
      · change ((-1 : 𝒪[F]) : F) * -(1 + (0 : F) * 0) = 1
        simp
      · change (v : F) * -(1 + theta M * theta M) = 1
        rw [theta_some M hg]
        exact hv
    · refine ⟨1, ?_⟩
      change -(1 + (0 : F) * 0) - -(1 + theta M * theta M) = (g.q : F) ^ 2 * ((1 : 𝒪[F]) : F)
      rw [theta_some M hg]
      push_cast
      ring

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem alg_mem {c : F} (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have e : algebraMap F E c = algebraMap 𝒪[F] E ⟨c, hc⟩ := by
    rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    rfl
  rw [e]
  exact isIntegral_algebraMap

def inn (c : F) : Submodule M.L.O ((stdH M m).Wb (r := 0) (frame M m c).f) :=
  Submodule.span M.L.O (Set.range fun i : Fin (m + 2) =>
    (stdH M m).mkW (r := 0) (frame M m c).f ⟨Pi.single i 1, mem_perp_zero _ _⟩)

theorem mem_inn (c : F) (x : (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f)) :
    (stdH M m).mkW (r := 0) (frame M m c).f x ∈ inn M m c ↔ ∀ i, x.1 i ∈ M.L.O := by
  constructor
  · intro hx

    suffices key : ∀ w ∈ inn M m c, ∃ y : (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f),
        (stdH M m).mkW (r := 0) (frame M m c).f y = w ∧ ∀ i, y.1 i ∈ M.L.O by
      obtain ⟨y, hy, hyO⟩ := key _ hx
      have hxy : y = x := mkW_inj _ hy
      rw [← hxy]
      exact hyO
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      refine ⟨_, rfl, fun j => ?_⟩
      change (Pi.single i (1 : E) : Fin (m + 2) → E) j ∈ M.L.O
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => exact ⟨0, map_zero _, fun j => zero_mem _⟩
    | add w w' _ _ hw hw' =>
      obtain ⟨y, rfl, hy⟩ := hw
      obtain ⟨y', rfl, hy'⟩ := hw'
      exact ⟨y + y', map_add _ _ _, fun j => add_mem (hy j) (hy' j)⟩
    | smul a w _ hw =>
      obtain ⟨y, rfl, hy⟩ := hw
      refine ⟨(a : E) • y, (map_smul _ _ _).trans rfl, fun j => ?_⟩
      change (a : E) * y.1 j ∈ M.L.O
      exact mul_mem a.2 (hy j)
  · intro hx
    have hsum : x = ∑ i, x.1 i • (⟨Pi.single i 1, mem_perp_zero _ _⟩ :
        (stdH M m).perp ((stdH M m).X (r := 0) (frame M m c).f)) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    change ((⟨x.1 i, hx i⟩ : M.L.O) : E) • _ ∈ inn M m c
    exact Submodule.smul_mem _ (⟨x.1 i, hx i⟩ : M.L.O) (Submodule.subset_span ⟨i, rfl⟩)

theorem vec_mem {c : F} (hc : c ∈ 𝒪[F]) (i) : vec (E := E) m c i ∈ M.L.O := by
  simp only [vec, Pi.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · rw [Pi.single_apply]
    split_ifs
    exacts [alg_mem M hc, zero_mem _]

theorem isInner {c : F} (hc : c ∈ 𝒪[F]) : (frame M m c).IsInner (inn M m c) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_, ?_⟩
  · rw [mem_inn]
    constructor
    · intro hx y hy
      rw [mem_inn] at hy
      change ∑ i, x.1 i * M.L.cj (y.1 i) ∈ M.L.O
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (cj_mem M (hy i))
    · intro h i
      have hi := h ⟨Pi.single i 1, mem_perp_zero _ _⟩ ((mem_inn M m c _).mpr fun j => by
        show (Pi.single i (1 : E) : Fin (m + 2) → E) j ∈ M.L.O
        rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _])
      change (stdH M m).h x.1 (Pi.single i 1) ∈ M.L.O at hi
      rwa [stdH_single] at hi
  · refine ⟨⟨vec m c, mem_perp_zero _ _⟩, rfl, (mem_inn M m c _).mpr (vec_mem M m hc), ?_⟩
    intro a y hy hxy
    rw [mem_inn] at hy
    rw [← map_smul] at hxy
    have e := congrArg (fun u => u.1 0) (mkW_inj _ hxy)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, vec_zero] at e
    exact isUnit_iff_exists_inv.mpr ⟨⟨y.1 0, hy 0⟩, Subtype.ext e.symm⟩

theorem lamStd (c : F) : (frame M m c).LamStd (inn M m c) =
    Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O} := by
  unfold FrameD.LamStd
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, IsEmpty.forall_iff, true_and]
  constructor
  · rintro ⟨w, hw, hwL⟩
    have hv : v = w.1 := by
      rw [hw]
      simp [FrameD.prF]
    rw [hv]
    exact (mem_inn M m c w).mp hwL
  · intro hv
    exact ⟨⟨v, mem_perp_zero _ _⟩, by simp [FrameD.prF], (mem_inn M m c _).mpr hv⟩

def term : Term (Fin (m + 2) → E) M 0 :=
  ⟨Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O}, (pair M m).A.f, (pair M m).B.f,
    (pair M m).A.T, (pair M m).B.T⟩

def datum : Datum (pair M m) where
  L := inn M m 0
  L' := inn M m (theta M)
  hL := isInner M m (zero_mem _)
  hL' := isInner M m (theta_int M)
  io := {p | ∃ g, M.split = some g ∧ p ∈ (stdH M m).iotaGraph g (term M m)}
  io_L h := by ext p; simp [h]

theorem isTermOver : IsTermOver (pair M m) (datum M m) (term M m) := by
  refine ⟨rfl, rfl, ⟨1, Subgroup.one_mem _, rfl, ?_⟩, ⟨1, Subgroup.one_mem _, rfl, ?_⟩,
    fun g hg => ⟨?_, ?_⟩⟩
  · rw [img_one]
    exact (lamStd M m 0).symm
  · rw [img_one]
    exact (lamStd M m (theta M)).symm
  · intro b
    change vec m (theta M) - vec m (0 : F) ∈ (stdH M m).smulLat (algebraMap F E (g.q : F))
      (Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O})
    have hv : vec (E := E) m (theta M) - vec m (0 : F) = algebraMap F E (g.q : F) • Pi.single 1 1 := by
      have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
      rw [theta_some M hg]
      funext j
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [vec, Pi.single_apply, h0, h1, h01, h01.symm]
    rw [hv]
    apply Submodule.subset_span
    refine ⟨Pi.single 1 1, Submodule.subset_span fun j => ?_, rfl⟩
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · ext p
    simp only [datum, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨g, hg, hp⟩
    · rintro ⟨g', hg', hp⟩
      rw [hg] at hg'
      cases Option.some.inj hg'
      exact hp

end Model

end GlobalTheory.NonGenericLocalCheck
