import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import GroundTheory.AutomorphicForms.GLnLocal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisExtra

noncomputable section

open Matrix ValuativeRel Topology Filter Set

namespace PositivityTheory.RgUd.T.Nil.Orb.Ozn

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb GroundTheory.Automorphic.GLnLocal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def ball (n : ℕ) (γ : ValueGroupWithZero k) : Set (Matrix (Fin n) (Fin n) k) :=
  {M | ∀ i j, valuation k (M i j) ≤ γ}

theorem isCompact_ball (γ : ValueGroupWithZero k) : IsCompact (ball (k := k) n γ) := by
  have h : ball (k := k) n γ =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n => {x : k | valuation k x ≤ γ})) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem continuous_entry' (i j : Fin n) : Continuous fun M : Matrix (Fin n) (Fin n) k => M i j :=
  (continuous_apply j).comp (continuous_apply i)

theorem isOpen_ball {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) : IsOpen (ball (k := k) n γ) := by
  have h : ball (k := k) n γ =
      ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ} := by
    ext M; simp [ball]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valuation_le k hγ).preimage (continuous_entry' i j)

theorem add_mem_ball {γ : ValueGroupWithZero k} {M M' : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ)
    (h' : M' ∈ ball n γ) : M + M' ∈ ball n γ :=
  fun i j => (Valuation.map_add _ _ _).trans (max_le (h i j) (h' i j))

theorem neg_mem_ball {γ : ValueGroupWithZero k} {M : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ) :
    -M ∈ ball n γ :=
  fun i j => by simpa [Valuation.map_neg] using h i j

theorem ball_mono {γ γ' : ValueGroupWithZero k} (hγ : γ ≤ γ') : ball (k := k) n γ ⊆ ball n γ' :=
  fun _ h i j => (h i j).trans hγ

theorem smul_mem_ball (a : k) {γ : ValueGroupWithZero k} {M : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ) :
    a • M ∈ ball n (valuation k a * γ) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul_right (h i j) _

abbrev ϖ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : k :=
  (uniformizer k : k)

theorem q_lt_one : valuation k (ϖ k) < 1 := valuation_uniformizer_lt_one k

theorem q_ne_zero : valuation k (ϖ k) ≠ 0 := valuation_uniformizer_ne_zero k

theorem ϖ_ne_zero : ϖ k ≠ 0 := (Valuation.ne_zero_iff _).1 q_ne_zero

theorem q_pow_anti {a b : ℕ} (h : a ≤ b) : valuation k (ϖ k) ^ b ≤ valuation k (ϖ k) ^ a :=
  pow_le_pow_right_of_le_one' q_lt_one.le h

theorem exists_pow_le_one (x : k) : ∃ j : ℕ, valuation k (ϖ k) ^ j * valuation k x ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hx' : valuation k x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨j, hj⟩ := exists_pow_lt₀ (q_lt_one (k := k)) (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hx'))
  refine ⟨j, ?_⟩
  calc valuation k (ϖ k) ^ j * valuation k x ≤ (valuation k x)⁻¹ * valuation k x :=
        mul_le_mul_left (by simpa using hj.le) _
    _ = 1 := inv_mul_cancel₀ hx'

theorem exists_pow_smul_mem (M : Matrix (Fin n) (Fin n) k) : ∃ j : ℕ, (ϖ k ^ j) • M ∈ ball n 1 := by
  choose f hf using fun p : Fin n × Fin n => exists_pow_le_one (M p.1 p.2)
  refine ⟨Finset.univ.sup f, fun i j => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
  exact (mul_le_mul_left (q_pow_anti (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))) _).trans (hf (i, j))

theorem pow_smul_mem_mono {M : Matrix (Fin n) (Fin n) k} {a b : ℕ} (hab : a ≤ b) (h : (ϖ k ^ a) • M ∈ ball n 1) :
    (ϖ k ^ b) • M ∈ ball n 1 := by
  have e : (ϖ k ^ b) • M = (ϖ k ^ (b - a)) • ((ϖ k ^ a) • M) := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hab]
  rw [e]
  refine ball_mono ?_ (smul_mem_ball _ h)
  rw [map_pow, mul_one]
  exact pow_le_one₀ zero_le q_lt_one.le

theorem exists_pow_smul_mem_of_isCompact {K : Set (Matrix (Fin n) (Fin n) k)} (hK : IsCompact K) :
    ∃ j : ℕ, ∀ M ∈ K, (ϖ k ^ j) • M ∈ ball n 1 := by
  have hU : ∀ j : ℕ, IsOpen {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1} := fun j =>
    (isOpen_ball one_ne_zero).preimage (continuous_const_smul _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun j : ℕ => {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1})
    hU fun M _ => Set.mem_iUnion.2 (exists_pow_smul_mem M)
  refine ⟨t.sup id, fun M hM => ?_⟩
  obtain ⟨j, hj, hMj⟩ := Set.mem_iUnion₂.1 (ht hM)
  exact pow_smul_mem_mono (Finset.le_sup (f := id) hj) hMj

theorem isNilpotent_iff_pow (M : Matrix (Fin n) (Fin n) k) : IsNilpotent M ↔ M ^ n = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨n, h⟩⟩
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : M.charpoly = Polynomial.X ^ Fintype.card (Fin n) := sub_eq_zero.1 h1.eq_zero
  have h3 := Matrix.aeval_self_charpoly M
  rw [h2] at h3
  simpa using h3

theorem isClosed_nilpotent : IsClosed {M : Matrix (Fin n) (Fin n) k | IsNilpotent M} := by
  have e : {M : Matrix (Fin n) (Fin n) k | IsNilpotent M} = (fun M => M ^ n) ⁻¹' {0} := by
    ext M; simp [isNilpotent_iff_pow]
  rw [e]
  exact isClosed_singleton.preimage (continuous_pow n)

theorem continuous_dual (f : Module.Dual k (Matrix (Fin n) (Fin n) k)) : Continuous f :=
  _root_.UpperTheory.Reformulated.B.DYlb5.main f

theorem isClosed_subalgebra (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    IsClosed (Z : Set (Matrix (Fin n) (Fin n) k)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule Z) hx inferInstance
  refine ⟨{y | f y ≠ 0}, fun y hy hyZ => hy ?_, isOpen_ne_fun (continuous_dual f) continuous_const, hfx⟩
  have : f y ∈ (Subalgebra.toSubmodule Z).map f := ⟨y, hyZ, rfl⟩
  rw [hf] at this
  simpa using this

theorem eq_zero_of_mem_of_isNilpotent {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : IsNilpotent c) : c = 0 := by
  haveI := hZ.2
  obtain ⟨m, hm⟩ := h
  have h' : IsNilpotent (⟨c, hc⟩ : Z) := ⟨m, Subtype.ext (by simpa using hm)⟩
  simpa using congrArg Subtype.val h'.eq_zero

theorem exists_sep {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) : ∃ J : ℕ,
    ∀ s ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), s ∈ ball n 1 → s ∉ ball n (valuation k (ϖ k)) →
      ∀ w ∈ ball n (valuation k (ϖ k) ^ J), ¬ IsNilpotent (s + w) := by
  set S : Set (Matrix (Fin n) (Fin n) k) := (Z : Set _) ∩ ball n 1 ∩ (ball n (valuation k (ϖ k)))ᶜ with hS
  have hSc : IsCompact S :=
    (isCompact_ball 1).inter_left (isClosed_subalgebra Z) |>.inter_right (isOpen_ball q_ne_zero).isClosed_compl
  have hloc : ∀ s ∈ S, ∃ J : ℕ, ∀ w ∈ ball n (valuation k (ϖ k) ^ J), ¬ IsNilpotent (s + w) := by
    intro s hs
    have hsN : ¬ IsNilpotent s := fun h =>
      hs.2 (by rw [eq_zero_of_mem_of_isNilpotent hZ hs.1.1 h]; exact fun i j => by simp)
    by_contra hcon
    push_neg at hcon
    let C : ℕ → Set (Matrix (Fin n) (Fin n) k) := fun J =>
      {M | M - s ∈ ball n (valuation k (ϖ k) ^ J)} ∩ {M | IsNilpotent M}
    have hCc : ∀ J, IsClosed (C J) := fun J =>
      ((isCompact_ball _).isClosed.preimage (continuous_id.sub continuous_const)).inter isClosed_nilpotent
    have hC0 : IsCompact (C 0) := by
      have h1 : IsCompact ((fun w => w + s) '' ball n (valuation k (ϖ k) ^ 0)) :=
        (isCompact_ball _).image (continuous_id.add continuous_const)
      refine h1.of_isClosed_subset (hCc 0) fun M hM => ⟨M - s, hM.1, by simp⟩
    have hCd : ∀ J, C (J + 1) ⊆ C J := fun J M hM =>
      ⟨ball_mono (q_pow_anti (Nat.le_succ J)) hM.1, hM.2⟩
    have hCn : ∀ J, (C J).Nonempty := fun J => by
      obtain ⟨w, hw, hnil⟩ := hcon J
      exact ⟨s + w, by simpa using hw, hnil⟩
    obtain ⟨M, hM⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCd hCn hC0 hCc
    have hMs : M - s = 0 := by
      ext i j
      exact eq_zero_of_forall_valuation_le k fun J => (Set.mem_iInter.1 hM J).1 i j
    have hMeq : M = s := sub_eq_zero.1 hMs
    exact hsN (hMeq ▸ (Set.mem_iInter.1 hM 0).2)
  choose! Js hJs using hloc
  have hopen : ∀ s ∈ S, IsOpen ((fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s)) := fun s _ =>
    (Homeomorph.addLeft s).isOpenMap _ (isOpen_ball (pow_ne_zero _ q_ne_zero))
  obtain ⟨t, ht⟩ := hSc.elim_nhds_subcover' (fun s hs => (fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s))
    fun s hs => (hopen s hs).mem_nhds ⟨0, fun i j => by simp, by simp⟩
  refine ⟨t.sup (fun s : S => Js s), fun s hsZ hs1 hsq w hw hnil => ?_⟩
  have hsS : s ∈ S := ⟨⟨hsZ, hs1⟩, hsq⟩
  obtain ⟨⟨s', hs'⟩, hmem, hss'⟩ := Set.mem_iUnion₂.1 (ht hsS)
  obtain ⟨u, hu, rfl⟩ := hss'
  have hw' : w ∈ ball n (valuation k (ϖ k) ^ Js s') :=
    ball_mono (q_pow_anti (Finset.le_sup (f := fun s : S => Js s) hmem)) hw
  exact hJs s' hs' (u + w) (add_mem_ball hu hw') (by simpa [add_assoc] using hnil)

theorem exists_bound {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {K : Set (Matrix (Fin n) (Fin n) k)}
    (hK : IsCompact K) : ∃ T : ℕ, ∀ c ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), ∀ m : Matrix (Fin n) (Fin n) k,
      IsNilpotent m → c + m ∈ K → (ϖ k ^ T) • c ∈ ball n 1 := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_pow_smul_mem_of_isCompact hK
  obtain ⟨J, hJ⟩ := exists_sep hZ
  refine ⟨j₀ + J, fun c hc m hm hcm => ?_⟩
  let e := Nat.find (exists_pow_smul_mem c)
  have he : (ϖ k ^ e) • c ∈ ball n 1 := Nat.find_spec (exists_pow_smul_mem c)
  by_cases hle : e ≤ j₀ + J
  · exact pow_smul_mem_mono hle he
  exfalso
  push_neg at hle
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hmin : ¬ (ϖ k ^ e') • c ∈ ball n 1 := Nat.find_min (exists_pow_smul_mem c) (by omega)
  have hs1 : (ϖ k ^ e) • c ∈ ball n 1 := he
  have hsq : (ϖ k ^ e) • c ∉ ball n (valuation k (ϖ k)) := by
    intro h
    apply hmin
    intro i j
    have h1 := h i j
    simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
    calc valuation k (ϖ k ^ e' * c i j)
        = (valuation k (ϖ k))⁻¹ * (valuation k (ϖ k) * valuation k (ϖ k ^ e' * c i j)) := by
          rw [inv_mul_cancel_left₀ q_ne_zero]
      _ = (valuation k (ϖ k))⁻¹ * valuation k (ϖ k ^ e * c i j) := by
          rw [he', pow_succ', mul_assoc, map_mul (valuation k) (ϖ k)]
      _ ≤ (valuation k (ϖ k))⁻¹ * valuation k (ϖ k) := mul_le_mul_right h1 _
      _ = 1 := inv_mul_cancel₀ q_ne_zero
  have hsZ : (ϖ k ^ e) • c ∈ (Z : Set (Matrix (Fin n) (Fin n) k)) := Z.smul_mem hc _
  have hw : (ϖ k ^ e) • (c + m) ∈ ball n (valuation k (ϖ k) ^ J) := by
    have e1 : (ϖ k ^ e) • (c + m) = (ϖ k ^ (e - j₀)) • ((ϖ k ^ j₀) • (c + m)) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [e1]
    refine ball_mono ?_ (smul_mem_ball _ (hj₀ _ hcm))
    rw [map_pow, mul_one]
    exact q_pow_anti (by omega)
  apply hJ _ hsZ hs1 hsq _ (neg_mem_ball hw)
  have : (ϖ k ^ e) • c + -((ϖ k ^ e) • (c + m)) = -((ϖ k ^ e) • m) := by
    rw [smul_add]; abel
  rw [this]
  exact (hm.smul _).neg

theorem isCompact_inter {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {K : Set (Matrix (Fin n) (Fin n) k)} (hK : IsCompact K) : IsCompact (ZN Z ∩ K) := by
  obtain ⟨T, hT⟩ := exists_bound hZ hK
  set CZ : Set (Matrix (Fin n) (Fin n) k) :=
    (Z : Set (Matrix (Fin n) (Fin n) k)) ∩ (fun c => (ϖ k ^ T) • c) ⁻¹' ball n 1 with hCZdef
  have hCZ : IsCompact CZ := by
    have h1 : IsCompact ((fun c : Matrix (Fin n) (Fin n) k => (ϖ k ^ T) • c) ⁻¹' ball n 1) :=
      (Homeomorph.smulOfNeZero (ϖ k ^ T) (pow_ne_zero _ ϖ_ne_zero)).isCompact_preimage.2 (isCompact_ball 1)
    exact h1.inter_left (isClosed_subalgebra Z)
  let A : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) :=
    {p | p.1 ∈ (Z : Set (Matrix (Fin n) (Fin n) k)) ∧ IsNilpotent p.2 ∧ p.1 + p.2 ∈ K}
  have hAsub : A ⊆ CZ ×ˢ ((fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 - p.2) '' (K ×ˢ CZ)) := by
    rintro ⟨c, m⟩ ⟨hc, hm, hcm⟩
    have hcz : c ∈ CZ := ⟨hc, hT c hc m hm hcm⟩
    exact ⟨hcz, ⟨(c + m, c), ⟨hcm, hcz⟩, by simp⟩⟩
  have hAc : IsClosed A := ((isClosed_subalgebra Z).preimage continuous_fst).inter
    ((isClosed_nilpotent.preimage continuous_snd).inter (hK.isClosed.preimage (continuous_fst.add continuous_snd)))
  have hA : IsCompact A :=
    (hCZ.prod ((hK.prod hCZ).image (continuous_fst.sub continuous_snd))).of_isClosed_subset hAc hAsub
  have e : ZN Z ∩ K = (fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 + p.2) '' A := by
    ext x
    constructor
    · rintro ⟨⟨c, hc, hxc⟩, hxK⟩
      exact ⟨(c, x - c), ⟨hc, hxc, by simpa using hxK⟩, by simp⟩
    · rintro ⟨⟨c, m⟩, ⟨hc, hm, hcm⟩, rfl⟩
      exact ⟨⟨c, hc, by simpa using hm⟩, hcm⟩
  rw [e]
  exact hA.image (continuous_fst.add continuous_snd)

theorem zNClosed : ZNClosed (k := k) := by
  intro n Z hZ
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  have h1 : x ∈ closure (ZN Z ∩ K) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro U hU
    obtain ⟨y, hyU, hyZ⟩ := hx (U ∩ K) (inter_mem hU hKx)
    exact ⟨y, hyU.1, hyZ, hyU.2⟩
  rw [(isCompact_inter hZ hKc).isClosed.closure_eq] at h1
  exact h1.1

end PositivityTheory.RgUd.T.Nil.Orb.Ozn
