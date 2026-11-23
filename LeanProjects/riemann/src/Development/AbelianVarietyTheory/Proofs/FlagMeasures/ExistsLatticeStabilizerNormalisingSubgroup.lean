import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameStabLat

section General
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)

theorem mem_stab_iff (Λ : Submodule O V) (h : V ≃ₗ[E] V) :
    h ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ↔ (∀ v ∈ Λ, h v ∈ Λ) ∧ ∀ v ∈ Λ, h⁻¹ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro H
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [← H]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨v, hv, rfl⟩
    · rw [← H] at hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
      have : h⁻¹ (h • u) = u := h.symm_apply_apply u
      rwa [this]
  · rintro ⟨H1, H2⟩
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact H1 u hu
    · intro hv
      exact ⟨h⁻¹ v, H2 v hv, h.apply_symm_apply v⟩

theorem mem_stab_set_iff {G X : Type} [Group G] [MulAction G X] (C : Set X) (h : G) :
    h ∈ MulAction.stabilizer G C ↔ (∀ v ∈ C, h • v ∈ C) ∧ ∀ v ∈ C, h⁻¹ • v ∈ C := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro H
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [← H]
      exact Set.smul_mem_smul_set hv
    · rw [← H] at hv
      exact Set.mem_smul_set_iff_inv_smul_mem.1 hv
  · rintro ⟨H1, H2⟩
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hv
      simpa using H1 _ hv
    · exact H2 v

theorem span_le {ι : Type} (g : ι → V) {x : V} (hx : x ∈ Submodule.span O (Set.range g)) :
    x ∈ Submodule.span E (Set.range g) :=
  Submodule.span_le_restrictScalars O E _ hx

theorem map_span {ι : Type} (g : ι → V) (h : V ≃ₗ[E] V) (Λ : Submodule O V) (H : ∀ i, h (g i) ∈ Λ)
    {x : V} (hx : x ∈ Submodule.span O (Set.range g)) : h x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact H i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
  | smul c x _ hx =>
    have : h (c • x) = c • h x := h.map_smul (c : E) x
    rw [this]; exact Λ.smul_mem c hx

theorem map_spanE {ι : Type} (g : ι → V) (h : V ≃ₗ[E] V) (Λ : Submodule E V) (H : ∀ i, h (g i) ∈ Λ)
    {x : V} (hx : x ∈ Submodule.span E (Set.range g)) : h x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact H i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Λ.smul_mem c hx

theorem map_mem_of_mem_sup_three_submodules (A A' B Λ : Submodule O V) (h : V ≃ₗ[E] V) (H1 : ∀ x ∈ A, h x ∈ Λ)
    (H2 : ∀ x ∈ A', h x ∈ Λ) (H3 : ∀ x ∈ B, h x ∈ Λ) : ∀ x ∈ A ⊔ A' ⊔ B, h x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, map_add]
  exact Λ.add_mem (Λ.add_mem (H1 a ha) (H2 a' ha')) (H3 w hw)

theorem inter (A A' B : Submodule O V) (P P' W : Submodule E V) (hA : ∀ x ∈ A, x ∈ P)
    (hA' : ∀ x ∈ A', x ∈ P') (hB : ∀ x ∈ B, x ∈ W)
    (H : ∀ a ∈ P, ∀ a' ∈ P', ∀ w ∈ W, a + a' + w = 0 → a = 0 ∧ a' = 0) {x : V} (hx : x ∈ A ⊔ A' ⊔ B) :
    (x ∈ P → x ∈ A) ∧ (x ∈ P' → x ∈ A') := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hy
  constructor
  · intro hP
    have := (H (a - (a + a' + w)) (P.sub_mem (hA a ha) hP) a' (hA' a' ha') w (hB w hw) (by abel)).1
    rw [← sub_eq_zero.1 this]; exact ha
  · intro hP
    have := (H a (hA a ha) (a' - (a + a' + w)) (P'.sub_mem (hA' a' ha') hP) w (hB w hw) (by abel)).2
    rw [← sub_eq_zero.1 this]; exact ha'

theorem uni_mul {m : ℕ} {s t : Matrix (Fin m) (Fin m) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hs.1 i l h, zero_mul]
    · rw [ht.1 l j (lt_of_lt_of_le hij h), mul_zero]
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, ht.2, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hs.1 i l h, zero_mul]
      · rw [ht.1 l i h, mul_zero]
    · simp

theorem map_comb {m : ℕ} (g : Fin m → V) (h : V ≃ₗ[E] V) (s t : Matrix (Fin m) (Fin m) E)
    (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (j : Fin m) :
    h (∑ i, t i j • g i) = ∑ i, (s * t) i j • g i := by
  simp only [map_sum, map_smul, hs, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem cong_coef {m : ℕ} (g : Fin m → V) (hg : LinearIndependent E g) (h : V ≃ₗ[E] V)
    (s : Matrix (Fin m) (Fin m) E) (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (π : E) (hπ : IsUnit π)
    (Λ : Submodule O V)
    (hΛ : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range g) → x ∈ Submodule.span O (Set.range g))
    (hc : ∀ j, ∃ w ∈ Λ, h (g j) - g j = π • w) (i j : Fin m) :
    ∃ c ∈ O, s i j = (1 : Matrix (Fin m) (Fin m) E) i j + π * c := by
  obtain ⟨w, hw, e⟩ := hc j
  obtain ⟨u, rfl⟩ := hπ
  have h1 : h (g j) - g j ∈ Submodule.span E (Set.range g) := by
    rw [hs]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.subset_span ⟨j, rfl⟩)
  have h2 : w ∈ Submodule.span E (Set.range g) := by
    have := Submodule.smul_mem _ ((u⁻¹ : Eˣ) : E) h1
    rwa [e, smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hΛ w hw h2)
  refine ⟨c i, (c i).2, ?_⟩
  have h3 : ∑ l, (s l j - ((1 : Matrix (Fin m) (Fin m) E) l j + u * c l)) • g l = 0 := by
    have h4 : ∑ l, (1 : Matrix (Fin m) (Fin m) E) l j • g l = g j := by
      simp [Matrix.one_apply]
    have h5 : ∑ l, ((u : E) * c l) • g l = (u : E) • w := by
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_smul]; rfl
    simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [h4, h5, ← hs, ← e]; abel
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hg _ h3 i)

theorem frame_facts {m : ℕ} (f : Fin m → V) (hf : LinearIndependent E f) (N : Subgroup (V ≃ₗ[E] V))
    (hN : ∀ n ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧ ∀ j, n (f j) = ∑ i, s i j • f i)
    (n : V ≃ₗ[E] V) (hn : n ∈ N) :
    LinearIndependent E (fun b => n (f b)) ∧
      Submodule.span E (Set.range fun b => n (f b)) = Submodule.span E (Set.range f) ∧
      ∀ h ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧ ∀ j, h (n (f j)) = ∑ i, s i j • n (f i) := by
  have key : ∀ h ∈ N, ∃ s : Matrix (Fin m) (Fin m) E, IsUni s ∧
      ∀ j, h (n (f j)) = ∑ i, s i j • n (f i) := by
    intro h hh
    obtain ⟨s, hs, e⟩ := hN (n⁻¹ * h * n) (N.mul_mem (N.mul_mem (N.inv_mem hn) hh) hn)
    refine ⟨s, hs, fun j => ?_⟩
    have h1 : h (n (f j)) = n ((n⁻¹ * h * n) (f j)) := (n.apply_symm_apply _).symm
    rw [h1, e]; simp
  refine ⟨hf.map' n.toLinearMap n.ker, le_antisymm ?_ ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, -, e⟩ := hN n hn
    show n (f j) ∈ Submodule.span E (Set.range f)
    rw [e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, -, e⟩ := key n⁻¹ (N.inv_mem hn)
    have h1 : f j = n⁻¹ (n (f j)) := (n.symm_apply_apply _).symm
    show f j ∈ Submodule.span E (Set.range fun b => n (f b))
    rw [h1, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem spanTo_top (S : Frames L r k) (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  unfold Frames.spanTo
  have : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := Set.eq_univ_of_forall fun i => i.2
  rw [this, Set.image_univ]

theorem move_perp (S : Frames L r k) (g : Fin (r + 1) → S.V) (h : S.GLV) (hh : h ∈ S.Nof g) (w : S.V)
    (hw : w ∈ perp L S.Hm S.ME) (hg : Submodule.span E (Set.range g) ≤ S.ME) :
    h w - w ∈ Submodule.span E (Set.range g) := by
  have h1 : S.spanTo g r ≤ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _)
  exact h1 (hh.2.2 w fun y hy => hw y (hg (h1 hy)))

theorem cls_map (S : Frames L r k) (g g' : Fin (r + 1) → S.V) (h : S.GLV)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (e : ∀ j, h (g j) = ∑ i, s i j • g i) (e' : ∀ j, h (g' j) = ∑ i, s' i j • g' i)
    (π : E) (hπ : π ∈ L.O) (hth : ∃ d ∈ L.O, π = algebraMap F E S.th * d)
    (c : ∀ i j, ∃ c ∈ L.O, s i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c)
    (c' : ∀ i j, ∃ c ∈ L.O, s' i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c) :
    ∀ p ∈ S.frameCls g g', h • p ∈ S.frameCls g g' := by
  rintro p ⟨A, A', hA, hA', h0, h1, hc, hp, hp'⟩
  have one : ∀ i j, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  choose c hcO hce using c
  choose c' hcO' hce' using c'
  choose a haO hae using hc
  obtain ⟨d, hd, hπd⟩ := hth
  have u1 := uni_mul hs (t := A) ⟨fun i j hij => (h0 i j hij).1, fun i => (h1 i).1⟩
  have u2 := uni_mul hs' (t := A') ⟨fun i j hij => (h0 i j hij).2, fun i => (h1 i).2⟩
  refine ⟨s * A, s' * A', fun i j => ?_, fun i j => ?_, fun i j hij => ⟨u1.1 i j hij, u2.1 i j hij⟩,
    fun i => ⟨u1.2 i, u2.2 i⟩, fun i j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.mul_apply]
    refine L.O.sum_mem fun l _ => L.O.mul_mem ?_ (hA l j)
    rw [hce]; exact L.O.add_mem (one _ _) (L.O.mul_mem hπ (hcO _ _))
  · rw [Matrix.mul_apply]
    refine L.O.sum_mem fun l _ => L.O.mul_mem ?_ (hA' l j)
    rw [hce']; exact L.O.add_mem (one _ _) (L.O.mul_mem hπ (hcO' _ _))
  · refine ⟨∑ l, ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i l * a l j +
      d * (c' i l * A' l j - c i l * A l j)), L.O.sum_mem fun l _ => ?_, ?_⟩
    · exact L.O.add_mem (L.O.mul_mem (one _ _) (haO _ _)) (L.O.mul_mem hd
        (L.O.sub_mem (L.O.mul_mem (hcO' _ _) (hA' _ _)) (L.O.mul_mem (hcO _ _) (hA _ _))))
    · rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hce, hce', hπd]
      linear_combination (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i l * hae l j
  · show h (p.1 j) = _
    rw [hp, map_comb g h s A e]
  · show h (p.2 j) = _
    rw [hp', map_comb g' h s' A' e']

theorem self_mem_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have one : ∀ i j, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  refine ⟨1, 1, one, one, fun i j hij => ?_, fun i => ?_, fun i j => ⟨0, L.O.zero_mem, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne hij.ne']
  · simp
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

theorem mem_of_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) (p : S.FrP) (hp : p ∈ S.frameCls g g') :
    (∀ j, p.1 j ∈ Submodule.span L.O (Set.range g)) ∧ ∀ j, p.2 j ∈ Submodule.span L.O (Set.range g') := by
  obtain ⟨A, A', hA, hA', -, -, -, hp, hp'⟩ := hp
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O)
      (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hp']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨A' i j, hA' i j⟩ : L.O)
      (Submodule.subset_span ⟨i, rfl⟩)

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -, -, -, -, -, b, -, hb⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  obtain ⟨hf, hf', hdis⟩ := linearIndependent_sum.1 hli
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hf hf' hdis
  obtain ⟨hg, hP, hs⟩ := frame_facts S.f hf S.N hN n hn
  obtain ⟨hg', hP', hs'⟩ := frame_facts S.f' hf' S.N' hN' n' hn'
  set g : Fin (r + 1) → S.V := fun b => n (S.f b) with hgdef
  set g' : Fin (r + 1) → S.V := fun b => n' (S.f' b) with hgdef'
  have hME : S.ME = Submodule.span E (Set.range S.f) ⊔ Submodule.span E (Set.range S.f') := by
    unfold Frames.ME
    rw [spanTo_top, spanTo_top]
  have hfix : ∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w := by
    intro h hh w hw
    have h1 := move_perp S S.f h hh.1 w hw (hME ▸ le_sup_left)
    have h2 := move_perp S S.f' h hh.2 w hw (hME ▸ le_sup_right)
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hdis _ h1 h2)
  rw [← hP, ← hP'] at hME hdis
  set P := Submodule.span E (Set.range g) with hPdef
  set P' := Submodule.span E (Set.range g') with hPdef'
  set A := Submodule.span L.O (Set.range g) with hAdef
  set A' := Submodule.span L.O (Set.range g') with hAdef'
  set B := Submodule.span L.O (Set.range b) with hBdef
  have hA : ∀ x ∈ A, x ∈ P := fun x hx => span_le L.O g hx
  have hA' : ∀ x ∈ A', x ∈ P' := fun x hx => span_le L.O g' hx
  have hB : ∀ x ∈ B, x ∈ S.W0 := fun x hx => hb ▸ span_le L.O b hx
  have hind : ∀ a ∈ P, ∀ a' ∈ P', ∀ w ∈ S.W0, a + a' + w = 0 → a = 0 ∧ a' = 0 := by
    intro a ha a' ha' w hw e
    have h1 : a + a' ∈ S.ME := hME ▸ Submodule.add_mem_sup ha ha'
    have h2 : a + a' ∈ S.W0 := by
      rw [eq_neg_of_add_eq_zero_left e]; exact S.W0.neg_mem hw
    have h3 := Submodule.disjoint_def.1 hcompl.disjoint _ h1 h2
    have h4 : a = 0 := Submodule.disjoint_def.1 hdis a ha (by
      rw [eq_neg_of_add_eq_zero_left h3]; exact P'.neg_mem ha')
    exact ⟨h4, by simpa [h4] using h3⟩
  have hint := fun x (hx : x ∈ A ⊔ A' ⊔ B) => inter L.O A A' B P P' S.W0 hA hA' hB hind hx
  have lA : ∀ x ∈ A, x ∈ A ⊔ A' ⊔ B := fun x hx =>
    Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have lA' : ∀ x ∈ A', x ∈ A ⊔ A' ⊔ B := fun x hx =>
    Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have lB : ∀ x ∈ B, x ∈ A ⊔ A' ⊔ B := fun x hx => Submodule.mem_sup_right hx
  have presP : ∀ h ∈ S.St, (∀ x ∈ P, h x ∈ P) ∧ ∀ x ∈ P', h x ∈ P' := by
    intro h hh
    obtain ⟨s, -, e⟩ := hs h hh.1
    obtain ⟨s', -, e'⟩ := hs' h hh.2
    refine ⟨fun x hx => map_spanE g h P (fun j => ?_) hx, fun x hx => map_spanE g' h P' (fun j => ?_) hx⟩
    · rw [show h (g j) = ∑ i, s i j • g i from e j]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [show h (g' j) = ∑ i, s' i j • g' i from e' j]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have down : ∀ h ∈ S.St, (∀ x ∈ A ⊔ A' ⊔ B, h x ∈ A ⊔ A' ⊔ B) →
      (∀ x ∈ A, h x ∈ A) ∧ ∀ x ∈ A', h x ∈ A' := fun h hh H =>
    ⟨fun x hx => (hint _ (H x (lA x hx))).1 ((presP h hh).1 x (hA x hx)),
      fun x hx => (hint _ (H x (lA' x hx))).2 ((presP h hh).2 x (hA' x hx))⟩
  have up : ∀ h ∈ S.St, (∀ x ∈ A, h x ∈ A) → (∀ x ∈ A', h x ∈ A') →
      ∀ x ∈ A ⊔ A' ⊔ B, h x ∈ A ⊔ A' ⊔ B := fun h hh H H' =>
    map_mem_of_mem_sup_three_submodules L.O A A' B _ h (fun x hx => lA _ (H x hx)) (fun x hx => lA' _ (H' x hx))
      fun x hx => by rw [hfix h hh x (hB x hx)]; exact lB x hx
  refine ⟨A ⊔ A' ⊔ B, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ((Submodule.fg_span (Set.finite_range _)).sup (Submodule.fg_span (Set.finite_range _))).sup
      (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff, ← hcompl.sup_eq_top, hME, hb]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Submodule.span_mono fun x hx => lA x (Submodule.subset_span hx)
    · exact Submodule.span_mono fun x hx => lA' x (Submodule.subset_span hx)
    · exact Submodule.span_mono fun x hx => lB x (Submodule.subset_span hx)
  · ext h
    simp only [Subgroup.mem_inf, mem_stab_iff]
    constructor
    · rintro ⟨hh, H1, H2⟩
      have d1 := down h hh H1
      have d2 := down h⁻¹ (S.St.inv_mem hh) H2
      exact ⟨⟨hh, d1.1, d2.1⟩, d1.2, d2.2⟩
    · rintro ⟨⟨hh, a1, a2⟩, a3, a4⟩
      exact ⟨hh, up h hh a1 a3, up h⁻¹ (S.St.inv_mem hh) a2 a4⟩
  · rintro h ⟨hh, H⟩
    obtain ⟨H1, H2⟩ := (mem_stab_set_iff _ h).1 H
    have m1 := mem_of_cls S g g' _ (H1 _ (self_mem_cls S g g'))
    have m2 := mem_of_cls S g g' _ (H2 _ (self_mem_cls S g g'))
    refine ⟨hh, (mem_stab_iff L.O _ h).2 ⟨?_, ?_⟩⟩
    · exact up h hh (fun x hx => map_span L.O g h A m1.1 hx) fun x hx => map_span L.O g' h A' m1.2 hx
    · exact up h⁻¹ (S.St.inv_mem hh) (fun x hx => map_span L.O g h⁻¹ A m2.1 hx)
        fun x hx => map_span L.O g' h⁻¹ A' m2.2 hx
  · have hϖ : ((S.ϖ : F) ^ 1) ≠ 0 := by
      rw [pow_one]
      exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
    have hu : IsUnit (algebraMap F E ((S.ϖ : F) ^ 1)) := (IsUnit.mk0 _ hϖ).map _
    have hO : algebraMap F E ((S.ϖ : F) ^ 1) ∈ L.O := by
      rw [L.O_def, pow_one]
      exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := S.ϖ)
    have hth : ∃ d ∈ L.O, algebraMap F E ((S.ϖ : F) ^ 1) = algebraMap F E S.th * d := by
      unfold Frames.th
      split_ifs
      · exact ⟨1, L.O.one_mem, by simp⟩
      · exact ⟨_, hO, by simp⟩
    have step : ∀ h ∈ S.St, CongId L S.ϖ (A ⊔ A' ⊔ B) 1 h →
        ∀ p ∈ S.frameCls g g', h • p ∈ S.frameCls g g' := by
      intro h hh hc
      obtain ⟨s, us, e⟩ := hs h hh.1
      obtain ⟨s', us', e'⟩ := hs' h hh.2
      exact cls_map S g g' h s s' us us' e e' _ hO hth
        (cong_coef L.O g hg h s e _ hu _ (fun x hx => (hint x hx).1)
          fun j => hc _ (lA _ (Submodule.subset_span ⟨j, rfl⟩)))
        (cong_coef L.O g' hg' h s' e' _ hu _ (fun x hx => (hint x hx).2)
          fun j => hc _ (lA' _ (Submodule.subset_span ⟨j, rfl⟩)))
    rintro h ⟨hh, H⟩ hc
    obtain ⟨-, H2⟩ := (mem_stab_iff L.O _ h).1 H
    refine (mem_stab_set_iff _ h).2 ⟨step h hh hc, step h⁻¹ (S.St.inv_mem hh) fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hc _ (H2 v hv)
    refine ⟨-w, Submodule.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, show h (h⁻¹ v) = v from h.apply_symm_apply v, neg_sub]

end GlobalTheory.HL.FrameStabLat
