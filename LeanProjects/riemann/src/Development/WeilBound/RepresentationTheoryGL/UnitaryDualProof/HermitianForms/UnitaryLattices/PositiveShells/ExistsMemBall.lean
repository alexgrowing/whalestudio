import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.ContinuousColElVal

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Avg

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)

def IsTr (A H : AddSubgroup (Fin (m + 1) → k)) (T : Finset (Fin (m + 1) → k)) : Prop :=
  H ≤ A ∧ IsOpen (H : Set (Fin (m + 1) → k)) ∧ (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H

def FixH (H : AddSubgroup (Fin (m + 1) → k)) (v : V) : Prop := ∀ a ∈ H, π (colEl k m N h a) v = v

def avgL (T : Finset (Fin (m + 1) → k)) : V →ₗ[ℂ] V := ((T.card : ℂ)⁻¹) • ∑ t ∈ T, π (colEl k m N h t)

theorem avgL_apply (T : Finset (Fin (m + 1) → k)) (v : V) :
    avgL h π T v = ((T.card : ℂ)⁻¹) • ∑ t ∈ T, π (colEl k m N h t) v := by
  rw [avgL, LinearMap.smul_apply, LinearMap.sum_apply]

theorem pi_colEl_add (x y : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h (x + y)) v = π (colEl k m N h x) (π (colEl k m N h y) v) := by
  rw [colEl_add, map_mul, Module.End.mul_apply]

def stab (v : V) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {a | π (colEl k m N h a) v = v}
  zero_mem' := by
    show π (colEl k m N h 0) v = v
    rw [colEl_zero, map_one, Module.End.one_apply]
  add_mem' := by
    intro a b ha hb
    show π (colEl k m N h (a + b)) v = v
    rw [pi_colEl_add, hb, ha]
  neg_mem' := by
    intro a ha
    show π (colEl k m N h (-a)) v = v
    conv_lhs => rw [← (show π (colEl k m N h a) v = v from ha)]
    rw [← pi_colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]

theorem isOpen_stab (hπ : IsSmooth π) (v : V) : IsOpen (stab h π v : Set (Fin (m + 1) → k)) :=
  (hπ v).preimage (continuous_colEl h)

variable {h π}

theorem IsTr.card_ne {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) :
    (T.card : ℂ) ≠ 0 := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hT.2.2.2 0 A.zero_mem
  exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem ht)

private theorem sum_transversal_add_eq_sum_of_periodic {G M : Type*} [AddCommGroup G] [AddCommMonoid M] (A H : AddSubgroup G)
    (T : Finset G) (hTA : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (f : G → M)
    (hf : ∀ x y, y ∈ H → f (x + y) = f x) (a : G) (ha : a ∈ A) :
    ∑ t ∈ T, f (t + a) = ∑ t ∈ T, f t := by
  classical
  have key : ∀ x ∈ A, ∃ t, t ∈ T ∧ x - t ∈ H := fun x hx => (hu x hx).exists
  choose! r hrT hrH using key
  have hfr : ∀ x ∈ A, f x = f (r x) := by
    intro x hx
    have := hf (r x) (x - r x) (hrH x hx)
    rw [add_sub_cancel] at this
    exact this
  have huniq : ∀ x ∈ A, ∀ t ∈ T, x - t ∈ H → r x = t := by
    intro x hx t ht hxt
    exact (hu x hx).unique ⟨hrT x hx, hrH x hx⟩ ⟨ht, hxt⟩
  refine Finset.sum_nbij' (fun t => r (t + a)) (fun t => r (t - a)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact hrT _ (A.add_mem (hTA t ht) ha)
  · intro t ht
    exact hrT _ (A.sub_mem (hTA t ht) ha)
  · intro t ht
    have hx : t + a ∈ A := A.add_mem (hTA t ht) ha
    apply huniq _ (A.sub_mem (hTA _ (hrT _ hx)) ha) t ht
    have := H.neg_mem (hrH _ hx)
    convert this using 1
    abel
  · intro t ht
    have hx : t - a ∈ A := A.sub_mem (hTA t ht) ha
    apply huniq _ (A.add_mem (hTA _ (hrT _ hx)) ha) t ht
    have := H.neg_mem (hrH _ hx)
    convert this using 1
    abel
  · intro t ht
    exact hfr _ (A.add_mem (hTA t ht) ha)

theorem sum_translate {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) :
    ∑ t ∈ T, π (colEl k m N h (t + a)) v = ∑ t ∈ T, π (colEl k m N h t) v := by
  apply sum_transversal_add_eq_sum_of_periodic A H T hT.2.2.1 hT.2.2.2 (fun x => π (colEl k m N h x) v) _ a ha
  intro x y hy
  beta_reduce
  rw [pi_colEl_add, hv y hy]

theorem avgL_colEl {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) : avgL h π T (π (colEl k m N h a) v) = avgL h π T v := by
  rw [avgL_apply, avgL_apply]
  congr 1
  rw [← sum_translate hT hv ha]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pi_colEl_add]

theorem colEl_avgL {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) {a : Fin (m + 1) → k} (ha : a ∈ A) : π (colEl k m N h a) (avgL h π T v) = avgL h π T v := by
  rw [avgL_apply, map_smul, map_sum]
  congr 1
  rw [← sum_translate hT hv ha]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [add_comm, pi_colEl_add]

theorem avgL_of_inv {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {y : V}
    (hy : ∀ a ∈ A, π (colEl k m N h a) y = y) : avgL h π T y = y := by
  rw [avgL_apply, Finset.sum_congr rfl fun t ht => hy t (hT.2.2.1 t ht), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hT.card_ne, one_smul]

theorem avgL_eq {A H H' : AddSubgroup (Fin (m + 1) → k)} {T T' : Finset (Fin (m + 1) → k)} {v : V} (hT : IsTr A H T)
    (hv : FixH h π H v) (hT' : IsTr A H' T') (hv' : FixH h π H' v) : avgL h π T v = avgL h π T' v := by
  have h1 : avgL h π T (avgL h π T' v) = avgL h π T' v :=
    avgL_of_inv hT fun a ha => colEl_avgL hT' hv' ha
  rw [← h1, avgL_apply h π T' v, map_smul, map_sum,
    Finset.sum_congr rfl fun t ht => avgL_colEl hT hv (hT'.2.2.1 t ht), Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hT'.card_ne, one_smul]

theorem avg_eq {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v : V}
    (hv : FixH h π H v) : avg (1 : AddChar k Circle) h π 0 A v = avgL h π T v := by
  have hd : ∃ p, AvgData (1 : AddChar k Circle) h π 0 A v p :=
    ⟨(H, T), hT.1, hT.2.1, hv, fun a _ => by simp, hT.2.2.1, hT.2.2.2⟩
  rw [avg, dif_pos hd]
  obtain ⟨p1, p2, p3, -, p5, p6⟩ := hd.choose_spec
  have e := avgL_eq (h := h) (π := π) (v := v) ⟨p1, p2, p5, p6⟩ p3 hT hv
  rw [← e, avgL_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

theorem avgL_sub_mem (ψ : AddChar k Circle) {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)}
    (hT : IsTr A H T) (v : V) : v - avgL h π T v ∈ DerKer k ψ π m := by
  have hc := hT.card_ne
  have e : v - avgL h π T v = ((T.card : ℂ)⁻¹) • ∑ t ∈ T, (v - π (colEl k m N h t) v) := by
    rw [avgL_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => sub_colEl_mem ψ h π t v)

theorem IsTr.neg [DecidableEq (Fin (m + 1) → k)] {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) :
    IsTr A H (T.image Neg.neg) := by
  refine ⟨hT.1, hT.2.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact A.neg_mem (hT.2.2.1 s hs)
  · intro a ha
    obtain ⟨s, ⟨hs, hsH⟩, huniq⟩ := hT.2.2.2 (-a) (A.neg_mem ha)
    refine ⟨-s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · have := H.neg_mem hsH
      convert this using 1
      abel
    · rintro t ⟨ht, htH⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have hH' : -a - s' ∈ H := by
        have := H.neg_mem htH
        convert this using 1
        abel
      rw [huniq s' ⟨hs', hH'⟩]

theorem B_avgL {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B) {A H : AddSubgroup (Fin (m + 1) → k)}
    {T : Finset (Fin (m + 1) → k)} (hT : IsTr A H T) {v w : V} (hw : FixH h π H w) :
    B (avgL h π T v) w = B v (avgL h π T w) := by
  classical
  have hTn := hT.neg
  have hcard : (T.image Neg.neg).card = T.card := Finset.card_image_of_injective _ neg_injective
  rw [← avgL_eq hTn hw hT hw, avgL_apply, avgL_apply, Finset.sum_image (fun x _ y _ hxy => neg_injective hxy),
    hcard, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, map_sum,
    LinearMap.sum_apply]
  simp only [map_inv₀, map_natCast, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have ew : w = π (colEl k m N h t) (π (colEl k m N h (-t)) w) := by
    rw [← pi_colEl_add, add_neg_cancel, colEl_zero, map_one, Module.End.one_apply]
  conv_lhs => rw [ew]
  rw [B_colEl h hB]

private theorem exists_tr_lemma {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (A H : AddSubgroup G) (hA : IsCompact (A : Set G)) (hH : IsOpen (H : Set G)) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  obtain ⟨S, hS⟩ := hA.elim_finite_subcover (fun a : A => (fun x => x - (a : G)) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [H.zero_mem]⟩)
  set S' : Finset G := S.image (fun a : A => (a : G)) with hS'
  have hS'A : ∀ s ∈ S', s ∈ A := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    exact a.2
  have hcov : ∀ x ∈ A, ∃ s ∈ S', x - s ∈ H := by
    intro x hx
    have := hS hx
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨a, Finset.mem_image_of_mem _ ha, hxa⟩
  let r : G → G := fun x => Classical.epsilon fun s => s ∈ S' ∧ x - s ∈ H
  have hr : ∀ x ∈ A, r x ∈ S' ∧ x - r x ∈ H := fun x hx => by
    obtain ⟨s, hs, hxs⟩ := hcov x hx
    exact Classical.epsilon_spec (p := fun s => s ∈ S' ∧ x - s ∈ H) ⟨s, hs, hxs⟩
  have hreq : ∀ x y, x - y ∈ H → r x = r y := by
    intro x y hxy
    show Classical.epsilon _ = Classical.epsilon _
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := H.sub_mem h2 hxy
      convert this using 1
      abel
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := H.add_mem hxy h2
      convert this using 1
      abel
  refine ⟨S'.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact hS'A _ (hr s (hS'A s hs)).1
  · intro a ha
    obtain ⟨s, hs, has⟩ := hcov a ha
    refine ⟨r a, ⟨?_, (hr a ha).2⟩, ?_⟩
    · rw [hreq a s has]
      exact Finset.mem_image_of_mem _ hs
    · rintro t ⟨ht, hat⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have h1 := (hr s' (hS'A s' hs')).2
      apply hreq
      have := H.sub_mem h1 hat
      convert this using 1
      abel

theorem exists_tr {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {H₀ : AddSubgroup (Fin (m + 1) → k)}
    (hH₀ : IsOpen (H₀ : Set (Fin (m + 1) → k))) : ∃ H T, IsTr A H T ∧ H ≤ H₀ := by
  have hHo : IsOpen ((H₀ ⊓ A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) := by
    rw [AddSubgroup.coe_inf]
    exact hH₀.inter hA.2
  obtain ⟨T, hTA, hu⟩ := exists_tr_lemma A (H₀ ⊓ A) hA.1 hHo
  exact ⟨H₀ ⊓ A, T, ⟨inf_le_right, hHo, hTA, hu⟩, inf_le_left⟩

def scl (z : kˣ) (A : AddSubgroup (Fin (m + 1) → k)) : AddSubgroup (Fin (m + 1) → k) :=
  A.map (DistribMulAction.toAddEquiv (Fin (m + 1) → k) z).toAddMonoidHom

theorem mem_scl (z : kˣ) (A : AddSubgroup (Fin (m + 1) → k)) (x : Fin (m + 1) → k) :
    x ∈ scl z A ↔ (z⁻¹ : kˣ) • x ∈ A :=
  AddSubgroup.mem_map_equiv

theorem IsTr.smul [DecidableEq (Fin (m + 1) → k)] {A H : AddSubgroup (Fin (m + 1) → k)} {T : Finset (Fin (m + 1) → k)}
    (hT : IsTr A H T) (z : kˣ) : IsTr (scl z A) (scl z H) (T.image fun t => z • t) := by
  have hc : Continuous fun x : Fin (m + 1) → k => (z⁻¹ : kˣ) • x := by
    simp only [Units.smul_def]
    exact continuous_const_smul _
  refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [mem_scl] at hx ⊢
    exact hT.1 hx
  · have e : (scl z H : Set (Fin (m + 1) → k)) =
        (fun x => (z⁻¹ : kˣ) • x) ⁻¹' (H : Set (Fin (m + 1) → k)) := by
      ext x
      exact mem_scl z H x
    rw [e]
    exact hT.2.1.preimage hc
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_scl, inv_smul_smul]
    exact hT.2.2.1 s hs
  · intro a ha
    rw [mem_scl] at ha
    obtain ⟨s, ⟨hs, hsH⟩, huniq⟩ := hT.2.2.2 _ ha
    refine ⟨z • s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · rw [mem_scl, smul_sub, inv_smul_smul]
      exact hsH
    · rintro t ⟨ht, htH⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      rw [mem_scl, smul_sub, inv_smul_smul] at htH
      rw [huniq s' ⟨hs', htH⟩]

end Avg

section Ball

def ball (m : ℕ) (u : kˣ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k (u : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_ball (m : ℕ) (u : kˣ) : (ball m u : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball u := by
  ext x
  exact ⟨fun hx i _ => hx i, fun hx i => hx i (Set.mem_univ i)⟩

theorem isLat_ball (m : ℕ) (u : kˣ) : IsLat (ball m u) := by
  refine ⟨?_, ?_⟩ <;> rw [coe_ball]
  · exact isCompact_univ_pi fun _ => isCompact_cball u
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball u

theorem ball_mono (m : ℕ) {u u' : kˣ} (hu : valuation k (u : k) ≤ valuation k (u' : k)) : ball m u ≤ ball m u' :=
  fun _ hx i => (hx i).trans hu

theorem scl_ball (m : ℕ) (z u : kˣ) : scl z (ball m u) = ball m (z * u) := by
  ext x
  rw [mem_scl]
  have hz : 0 < valuation k (z : k) := by simp [zero_lt_iff]
  refine forall_congr' fun i => ?_
  show valuation k (((z⁻¹ : kˣ) • x) i) ≤ valuation k (u : k) ↔ valuation k (x i) ≤ valuation k ((z * u : kˣ) : k)
  rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_le_iff₀ hz]

theorem ball_pow_mono (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) {t t' : ℕ} (htt' : t ≤ t') :
    ball m (z⁻¹ ^ t * u₀) ≤ ball m (z⁻¹ ^ t' * u₀) := by
  apply ball_mono
  have hz0 : valuation k (z : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr z.ne_zero
  have h1 : 1 ≤ (valuation k (z : k))⁻¹ := by
    calc 1 = valuation k (z : k) * (valuation k (z : k))⁻¹ := (mul_inv_cancel₀ hz0).symm
      _ ≤ 1 * (valuation k (z : k))⁻¹ := mul_le_mul_of_nonneg_right hz.le zero_le'
      _ = (valuation k (z : k))⁻¹ := one_mul _
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 htt') zero_le'

theorem exists_mem_ball (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) (x : Fin (m + 1) → k) :
    ∃ t : ℕ, x ∈ ball m (z⁻¹ ^ t * u₀) := by
  have hz0 : valuation k (z : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr z.ne_zero
  have hu0 : 0 < valuation k (u₀ : k) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr u₀.ne_zero)
  have h1 : 1 < (valuation k (z : k))⁻¹ := (one_lt_inv₀ (zero_lt_iff.mpr hz0)).mpr hz
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hi : ∀ i, ∃ t : ℕ, valuation k (x i) ≤ (valuation k (z : k))⁻¹ ^ t * valuation k (u₀ : k) := by
    intro i
    obtain ⟨t, ht⟩ := MulArchimedean.arch (valuation k (x i) * (valuation k (u₀ : k))⁻¹) h1
    exact ⟨t, (mul_inv_le_iff₀ hu0).mp ht⟩
  choose t ht using hi
  refine ⟨Finset.univ.sup t, fun i => ?_⟩
  show valuation k (x i) ≤ valuation k ((z⁻¹ ^ Finset.univ.sup t * u₀ : kˣ) : k)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  exact (ht i).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ h1.le (Finset.le_sup (Finset.mem_univ i))) zero_le')

theorem tendsto_ball (m : ℕ) (z : kˣ) (hz : valuation k (z : k) < 1) (u₀ : kˣ) :
    Filter.Tendsto (fun t : ℕ => (⟨ball m (z⁻¹ ^ t * u₀), isLat_ball m _⟩ : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A}))
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  rintro ⟨A, hA⟩
  obtain ⟨T0, hT0⟩ := hA.1.elim_directed_cover
    (fun t : ℕ => (ball m (z⁻¹ ^ t * u₀) : Set (Fin (m + 1) → k)))
    (fun t => (isLat_ball m _).2)
    (fun x _ => Set.mem_iUnion.mpr (exists_mem_ball m z hz u₀ x))
    (Monotone.directed_le fun t t' htt' x hx => ball_pow_mono m z hz u₀ htt' hx)
  rw [Filter.eventually_atTop]
  exact ⟨T0, fun t ht x hx => ball_pow_mono m z hz u₀ ht (hT0 hx)⟩

end Ball

section Scal

variable {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem FixH.smul {H : AddSubgroup (Fin (m + 1) → k)} {v : V} (hv : FixH h π H v) (z : kˣ) :
    FixH h π (scl z H) (π (scalAt k (m + 1) N (by omega) z) v) := by
  intro a ha
  rw [mem_scl] at ha
  have e : colEl k m N h a * scalAt k (m + 1) N (by omega) z =
      scalAt k (m + 1) N (by omega) z * colEl k m N h ((z⁻¹ : kˣ) • a) := by
    rw [scalAt_mul_colEl, Units.smul_def, smul_smul, Units.mul_inv, one_smul]
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv _ ha]

theorem avgL_smul [DecidableEq (Fin (m + 1) → k)] (T : Finset (Fin (m + 1) → k)) (z : kˣ) (v : V) :
    avgL h π (T.image fun t => z • t) (π (scalAt k (m + 1) N (by omega) z) v) =
      π (scalAt k (m + 1) N (by omega) z) (avgL h π T v) := by
  rw [avgL_apply, avgL_apply, Finset.card_image_of_injective _ (MulAction.injective z),
    Finset.sum_image (fun x _ y _ hxy => MulAction.injective z hxy), map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : π (colEl k m N h ((z : k) • t)) * π (scalAt k (m + 1) N (by omega) z) =
      π (scalAt k (m + 1) N (by omega) z) * π (colEl k m N h t) := by
    rw [← map_mul, ← map_mul, scalAt_mul_colEl]
  beta_reduce
  rw [Units.smul_def]
  exact LinearMap.congr_fun e v

end Scal

end PositivityTheory.RgUd.Form.U.Shell
