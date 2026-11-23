import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩

theorem mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm

theorem exists_map_wave₂ {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) {L L' : AddSubgroup G}
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hY : ∀ y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', σ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, ∀ x y, T (wave χ L x y) = ρ x (σ y f₀) := by
  have hli := linearIndependent_wave (X := ⊤) (Y := ⊤) (L := L) (L' := L') h fun y _ => hY y
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Module.Basis.span hli).constr ℂ
    fun i => ρ (i.1.out : (⊤ : AddSubgroup G)) (σ (i.2.out : (⊤ : AddSubgroup G)) f₀))
  have hT' : ∀ i : ((⊤ : AddSubgroup G) ⧸ L.addSubgroupOf ⊤) × ((⊤ : AddSubgroup G) ⧸ L'.addSubgroupOf ⊤),
      T (wave χ L (i.1.out : (⊤ : AddSubgroup G)) (i.2.out : (⊤ : AddSubgroup G))) =
        ρ (i.1.out : (⊤ : AddSubgroup G)) (σ (i.2.out : (⊤ : AddSubgroup G)) f₀) := fun i => by
    have := LinearMap.congr_fun hT (Module.Basis.span hli i)
    rw [Module.Basis.constr_basis] at this
    simpa using this
  refine ⟨T, fun x y => ?_⟩
  let p : (⊤ : AddSubgroup G) ⧸ L.addSubgroupOf ⊤ := QuotientAddGroup.mk ⟨x, trivial⟩
  let q : (⊤ : AddSubgroup G) ⧸ L'.addSubgroupOf ⊤ := QuotientAddGroup.mk ⟨y, trivial⟩
  have hp : -((p.out : (⊤ : AddSubgroup G)) : G) + x ∈ L :=
    (QuotientAddGroup.eq (s := L.addSubgroupOf ⊤) (a := p.out) (b := ⟨x, trivial⟩)).1 p.out_eq'
  have hq : -((q.out : (⊤ : AddSubgroup G)) : G) + y ∈ L' :=
    (QuotientAddGroup.eq (s := L'.addSubgroupOf ⊤) (a := q.out) (b := ⟨y, trivial⟩)).1 q.out_eq'
  have := hT' (p, q)
  simp only at this
  generalize ((p.out : (⊤ : AddSubgroup G)) : G) = x0 at *
  generalize ((q.out : (⊤ : AddSubgroup G)) : G) = y0 at *
  have ex : x = x0 + (-x0 + x) := by abel
  have ey : y = y0 + (-y0 + y) := by abel
  generalize -x0 + x = l at *
  generalize -y0 + y = l' at *
  rw [ex, ey, wave_add h hLL' _ _ hp hq, map_smul, this, ← hρ, ← hσ, hf' _ hq, hc l, hf _ hp, map_smul]

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem eventually_invariant {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm

theorem invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']

theorem exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩

theorem sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩

theorem ind_box_mem (a : kˣ) : ind (box Y Y' a) ∈ SB (Matrix Y Y' k) := by
  have hcl : IsClopen (box Y Y' a : Set (Matrix Y Y' k)) := ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_box a), isOpen_box a⟩
  have e : ind (box Y Y' a) = (box Y Y' a : Set (Matrix Y Y' k)).indicator fun _ => (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ box Y Y' a <;> simp [ind, ht]
  rw [e]
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box a) fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_embedding {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {g : V} (hg : g ∈ P) (g0 : g ≠ 0)
    (hg1 : ∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g)
    (hg2 : ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g) :
    ∃ T : (Matrix Y Y' k → ℂ) →ₗ[ℂ] V, ∀ Φ ∈ SB (Matrix Y Y' k), (T Φ = 0 → Φ = 0) ∧ T Φ ∈ P ∧
      (∀ x, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y, T (fun t => pairing ψ t y * Φ t) = σ y (T Φ) := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨T, hT⟩ := exists_map_wave₂ hb (L := box Y Y' 1) (L' := box Y Y' (d / 1))
    (fun u hu y hy => pairing_box hd hu hy)
    (fun y hy => by_contra fun hn => by
      obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
      rw [div_one, div_self'] at hx
      exact hne ((pairing_comm ψ y x).trans (hy x hx)))
    ρ σ hρ hσ hc g hg1 fun u hu => hg2 u fun x hx => pairing_box hd hx hu
  have h0 : T (ind (box Y Y' 1)) = g := by
    rw [← wave_zero hb, hT, hg2 0 fun x _ => hb.zero_right x, hg1 0 (zero_mem _)]
  have hne : ind (box Y Y' (1 : kˣ)) ≠ 0 := fun e => g0 (by rw [← h0, e, map_zero])
  have key : ∀ Φ ∈ waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)), T Φ ∈ P ∧
      (∀ x, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y, T (fun t => pairing ψ t y * Φ t) = σ y (T Φ) := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨a, -, b, -, rfl⟩ := hh
      refine ⟨hT a b ▸ hP _ _ (hP' _ _ hg), fun x => ?_, fun y => ?_⟩
      · rw [wave_trans, hT, hT, hρ]
      · rw [wave_modul hb, map_smul, hT, hT, ← hσ, hc a y, smul_smul, hb.neg_mul, one_smul]
    | zero =>
      refine ⟨by rw [map_zero]; exact P.zero_mem, fun x => ?_, fun y => ?_⟩
      · rw [map_zero, map_zero]; exact map_zero T
      · rw [map_zero, map_zero, ← map_zero T]; congr 1; funext t; simp
    | add f g _ _ hf hg =>
      refine ⟨by rw [map_add]; exact P.add_mem hf.1 hg.1, fun x => ?_, fun y => ?_⟩
      · rw [map_add, map_add, ← hf.2.1 x, ← hg.2.1 x, ← map_add]; rfl
      · rw [map_add, map_add, ← hf.2.2 y, ← hg.2.2 y, ← map_add]; congr 1; funext t; simp [mul_add]
    | smul c f _ hf =>
      refine ⟨by rw [map_smul]; exact P.smul_mem c hf.1, fun x => ?_, fun y => ?_⟩
      · rw [map_smul, map_smul, ← hf.2.1 x, ← map_smul]; rfl
      · rw [map_smul, map_smul, ← hf.2.2 y, ← map_smul]; congr 1; funext t; simp [mul_left_comm]
  have hle : SB (Matrix Y Y' k) ≤ waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)) :=
    sb_le hd (fun x _ h => trans_mem h trivial) (fun y _ h => modul_mem hb h trivial) (ind_box_mem 1) hne
      (Submodule.subset_span ⟨0, trivial, 0, trivial, (wave_zero hb).symm⟩)
  refine ⟨T, fun Φ hΦ => ⟨fun hz => by_contra fun hn => g0 ?_, key Φ (hle hΦ)⟩⟩
  have := sb_le hd (N := waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)) ⊓ LinearMap.ker T)
    (fun x Ψ h => ⟨trans_mem h.1 trivial, by
      change T _ = 0
      rw [(key Ψ h.1).2.1, show T Ψ = 0 from h.2, map_zero]⟩)
    (fun y Ψ h => ⟨modul_mem hb h.1 trivial, by
      change T _ = 0
      rw [(key Ψ h.1).2.2, show T Ψ = 0 from h.2, map_zero]⟩) hΦ hn ⟨hle hΦ, hz⟩ (ind_box_mem 1)
  rw [← h0]
  exact this.2

end GlobalTheory.LocMod.Inhab
end
