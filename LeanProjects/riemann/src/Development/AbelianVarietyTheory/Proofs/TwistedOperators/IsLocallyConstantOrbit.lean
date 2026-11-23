import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwistedKernelFixed

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.IwahoriInj

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem mem_fixed {H : Subgroup G} {v : V} : v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v :=
  ⟨fun hv h hh => by simpa using hv ⟨h, hh⟩, fun hv h => by simpa using hv h h.2⟩

theorem sub_mem_twKer {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h v - v ∈ twKer π H 1 :=
  Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩

theorem twKer_mono {H K : Subgroup G} (hle : H ≤ K) : twKer π H 1 ≤ twKer π K 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, v, rfl⟩
  simpa using sub_mem_twKer (hle h.2) v

theorem apply_mem_twKer {H : Subgroup G} {h : G} (hh : h ∈ H) {v : V} (hv : v ∈ twKer π H 1) :
    π h v ∈ twKer π H 1 := by
  simpa using add_mem (sub_mem_twKer hh v) hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isLocallyConstant_orbit (hπ : IsSmooth π) (v : V) : IsLocallyConstant fun g : G => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g v = v}) := (hπ v).preimage (by fun_prop)
  filter_upwards [h.mem_nhds (show x ∈ _ by simp)] with g hg
  have hg' : π (x⁻¹ * g) v = v := hg
  conv_rhs => rw [← hg']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem eq_zero_of_fixed (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V}
    (hv : v ∈ fixed π H) (hv' : v ∈ twKer π H 1) : v = 0 :=
  _root_.UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed hπ hH hv hv'

theorem exists_orbit (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) (v : V) :
    ∃ S : Finset V, (∀ u, u ∈ S ↔ ∃ h ∈ H, π h v = u) ∧ ∑ u ∈ S, u ∈ fixed π H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hf := ((isLocallyConstant_orbit hπ v).comp_continuous (f := fun h : H => (h : G))
    continuous_subtype_val).range_finite
  have hS : ∀ u, u ∈ hf.toFinset ↔ ∃ h ∈ H, π h v = u := fun u => by simp
  refine ⟨hf.toFinset, hS, mem_fixed.2 fun g hg => ?_⟩
  rw [map_sum]
  have key : ∀ g ∈ H, ∀ u ∈ hf.toFinset, π g u ∈ hf.toFinset := fun g hg u hu => by
    obtain ⟨h, hh, rfl⟩ := (hS u).1 hu
    exact (hS _).2 ⟨g * h, mul_mem hg hh, by simp⟩
  refine Finset.sum_nbij' (fun u => π g u) (fun u => π g⁻¹ u) (key g hg) (key _ (inv_mem hg))
    (fun u _ => ?_) (fun u _ => ?_) fun _ _ => rfl
  · rw [← Module.End.mul_apply, ← map_mul]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp

variable (π) in

def Inj (I J : Subgroup G) : Prop := ∀ v ∈ fixed π I, v ∈ twKer π J 1 → v = 0

theorem Inj.trans (hπ : IsSmooth π) {I J K : Subgroup G} (hJ : IsCompact (J : Set G))
    (hfac : ∀ x ∈ J, ∃ a ∈ K, ∃ b ∈ I, x = a * b) (h1 : Inj π I J) (h2 : Inj π J K) : Inj π I K := by
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hJ v
  have hz0 : ∑ u ∈ S, u = 0 := h2 _ hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hfac x hx
    rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
    exact apply_mem_twKer ha hv')
  have h3 : ∑ u ∈ S, (u - v) ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact sub_mem_twKer hx v
  rw [Finset.sum_sub_distrib, hz0, zero_sub, neg_mem_iff, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  have hne : (S.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, (hS v).2 ⟨1, one_mem _, by simp⟩⟩)
  exact h1 v hv ((Submodule.smul_mem_iff _ hne).1 h3)

theorem inj_of_rank_one (hπ : IsSmooth π) {I J P : Subgroup G} (hJ : IsCompact (J : Set G))
    (hP : IsCompact (P : Set G)) (hJP : J ≤ P) {s : G} (hs : s ∈ P) (hconj : ∀ x ∈ J, s⁻¹ * x * s ∈ I)
    (hdec : ∀ p ∈ P, (∃ a ∈ J, ∃ b ∈ I, p = a * b) ∨ s⁻¹ * p ∈ I) : Inj π I J := by
  classical
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hP v
  have hz0 : ∑ u ∈ S, u = 0 := eq_zero_of_fixed hπ hP hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact apply_mem_twKer hx (twKer_mono hJP hv'))
  have hw : π s v ∈ S := (hS _).2 ⟨s, hs, rfl⟩
  have h3 : ∑ u ∈ S.erase (π s v), u ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨hne, hu⟩ := Finset.mem_erase.1 hu
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    rcases hdec x hx with ⟨a, ha, b, hb, rfl⟩ | h
    · rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
      exact apply_mem_twKer ha hv'
    · refine absurd ?_ hne
      conv_rhs => rw [← mem_fixed.1 hv _ h]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [← Finset.add_sum_erase _ _ hw, add_eq_zero_iff_eq_neg] at hz0
  have h4 : π s v = 0 := eq_zero_of_fixed hπ hJ (mem_fixed.2 fun x hx => by
    conv_rhs => rw [← mem_fixed.1 hv _ (hconj x hx)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group) (by rw [hz0]; exact neg_mem h3)
  have := congrArg (π s⁻¹) h4
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this

end Abstract

section Depth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Deep (a : ℤ) (x : k) : Prop := valuation k x ≤ uniformizer k ^ a

theorem unif_pos : 0 < uniformizer k := uniformizer_pos

theorem deep_zero (a : ℤ) : Deep a (0 : k) := by simp [Deep]

theorem deep_zero_iff {x : k} : Deep 0 x ↔ valuation k x ≤ 1 := by simp [Deep]

theorem deep_one_iff {x : k} : Deep 1 x ↔ valuation k x < 1 := by simp [Deep, le_uniformizer_iff]

theorem Deep.mono {a b : ℤ} {x : k} (h : Deep a x) (hab : b ≤ a) : Deep b x :=
  le_trans h (zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le hab)

theorem Deep.mul {a b : ℤ} {x y : k} (hx : Deep a x) (hy : Deep b y) : Deep (a + b) (x * y) := by
  unfold Deep at *
  rw [map_mul, zpow_add₀ unif_pos.ne']
  exact mul_le_mul' hx hy

theorem Deep.neg {a : ℤ} {x : k} (hx : Deep a x) : Deep a (-x) := by simpa [Deep] using hx

theorem Deep.sum {ι : Type} {s : Finset ι} {a : ℤ} {x : ι → k} (h : ∀ i ∈ s, Deep a (x i)) :
    Deep a (∑ i ∈ s, x i) := Valuation.map_sum_le _ h

theorem deep_inv {u : k} (h1 : ¬ Deep 1 u) : u ≠ 0 ∧ Deep 0 u⁻¹ := by
  rw [deep_one_iff, not_lt] at h1
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [deep_zero_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h1

theorem exists_deep (a : ℤ) : ∃ c : k, c ≠ 0 ∧ Deep a c ∧ Deep (-a) c⁻¹ := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k ^ a)
  refine ⟨c, fun h => ?_, hc.le, ?_⟩
  · rw [h, map_zero] at hc
    exact (zpow_pos unif_pos a).ne hc
  · simp [Deep, hc]

theorem eventually_deep (x : k) : ∀ᶠ m : ℕ in Filter.atTop, Deep (-(m : ℤ)) x := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, valuation k x ≤ (uniformizer k)⁻¹ ^ m := by
    exact MulArchimedean.arch _ ((one_lt_inv₀ unif_pos).2 uniformizer_lt_one)
  filter_upwards [Filter.eventually_ge_atTop m] with m' hm'
  have : Deep (-(m : ℤ)) x := by simpa [Deep] using hm
  exact this.mono (by omega)

end Depth

section Chambers

variable {n : Type}

def Conc (f : n → n → ℤ) : Prop := (∀ i, f i i = 0) ∧ ∀ i j l, f i j ≤ f i l + f l j

def Chamber (f : n → n → ℤ) : Prop := Conc f ∧ ∀ i j, i ≠ j → f i j + f j i = 1

theorem exists_wall [Fintype n] {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) (hne : f ≠ F) :
    ∃ i j, i ≠ j ∧ f j i < F j i ∧ ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i := by
  classical
  let ht : n × n → ℤ := fun p => ∑ l, (f p.1 p.2 + f p.2 l - f p.1 l)
  have hpos : ∀ a b, a ≠ b → 0 < ht (a, b) := fun a b hab =>
    Finset.sum_pos' (fun l _ => by have := hf.1.2 a l b; simp only; omega)
      ⟨a, Finset.mem_univ _, by have := hf.2 a b hab; have := hf.1.1 a; simp only; omega⟩
  have hdiag : ∀ a b, f a b < F a b → a ≠ b := by
    rintro a _ h rfl
    rw [hf.1.1, hF.1.1] at h
    exact lt_irrefl _ h
  have hex : (Finset.univ.filter fun p : n × n => f p.1 p.2 < F p.1 p.2).Nonempty := by
    by_contra hc
    apply hne
    have hle : ∀ a b, F a b ≤ f a b := fun a b => by
      by_contra h
      exact hc ⟨(a, b), by simpa using h⟩
    funext a b
    by_cases hab : a = b
    · rw [hab, hf.1.1, hF.1.1]
    · have := hle a b; have := hle b a; have := hf.2 a b hab; have := hF.2 a b hab; omega
  obtain ⟨⟨j, i⟩, hp, hmin⟩ := Finset.exists_min_image _ ht hex
  have hp' : f j i < F j i := by simpa using hp
  refine ⟨i, j, (hdiag _ _ hp').symm, hp', fun l hli hlj => ?_⟩
  by_contra hc
  have he : f j i = f j l + f l i := le_antisymm (hf.1.2 _ _ _) (not_lt.1 hc)
  have hadd : ht (j, i) = ht (j, l) + ht (l, i) := by
    simp only [ht, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by omega
  have h1 := hpos j l hlj.symm
  have h2 := hpos l i hli
  have h3 := hF.1.2 j i l
  by_cases h : f j l < F j l
  · have := hmin (j, l) (by simpa using h); omega
  · have := hmin (l, i) (by simp; omega); omega

theorem exists_flip {f : n → n → ℤ} (hf : Chamber f) {i j : n} (hij : i ≠ j)
    (hw : ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i) :
    ∃ g f' : n → n → ℤ, Conc g ∧ Chamber f' ∧ f i j = g i j + 1 ∧
      (∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) ∧ f' j i = g j i + 1 ∧
      (∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) := by
  classical
  let g : n → n → ℤ := fun a b => if a = i ∧ b = j then f a b - 1 else f a b
  let f' : n → n → ℤ := fun a b => if a = j ∧ b = i then g a b + 1 else g a b
  have g1 : f i j = g i j + 1 := by simp [g]
  have g2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b := fun a b h => by simp only [g, if_neg h]
  have f1 : f' j i = g j i + 1 := by simp [f']
  have f2 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b := fun a b h => by simp only [f', if_neg h]
  have gle : ∀ a b, g a b ≤ f a b := fun a b => by simp only [g]; split_ifs <;> omega
  have fle : ∀ a b, g a b ≤ f' a b := fun a b => by simp only [f']; split_ifs <;> omega
  clear_value f' g
  obtain ⟨⟨h0, h1⟩, h2⟩ := hf
  have h3 := h2 i j hij
  have hg0 : ∀ a, g a a = 0 := fun a => by rw [← g2 a a (by grind), h0]
  have hg : Conc g := by
    refine ⟨hg0, fun a b l => ?_⟩
    by_cases c1 : a = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := c1
      have := g2 l b (by grind)
      by_cases c : b = l
      · subst c; have := hg0 b; omega
      by_cases c' : b = a
      · subst c'; have := hg0 b; omega
      have := hw b c' c; have := h2 b a c'; have := gle a b; omega
    by_cases c2 : l = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2
      have := g2 a l (by grind)
      by_cases c : a = l
      · subst c; have := hg0 a; omega
      by_cases c' : a = b
      · subst c'; have := hg0 a; omega
      have := hw a c c'; have := h2 a b c'; have := gle a b; omega
    have := g2 a l c1; have := g2 l b c2; have := gle a b; have := h1 a b l; omega
  have hf0 : ∀ a, f' a a = 0 := fun a => by rw [f2 a a (by grind), hg0]
  refine ⟨g, f', hg, ⟨⟨hf0, fun a b l => ?_⟩, fun a b hab => ?_⟩, g1, g2, f1, f2⟩
  · by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1
      by_cases c : l = b
      · subst c; have := hf0 l; omega
      by_cases c' : l = a
      · subst c'; have := hf0 l; omega
      have := hw l c c'; have := fle a l; have := fle l b
      have := g2 a b (by grind); have := g2 a l (by grind); have := g2 l b (by grind); omega
    have := f2 a b c1; have := hg.2 a b l; have := fle a l; have := fle l b; omega
  · have := g2 j i (by grind)
    have := f2 i j (by grind)
    by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1; omega
    by_cases c2 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2; omega
    have := f2 a b c1; have := f2 b a (by grind); have := g2 a b c2; have := g2 b a (by grind)
    have := h2 a b hab; omega

end Chambers

section Groups

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable (k) in

def grp {f : n → n → ℤ} (hf : Conc f) : Subgroup (GL n k) where
  carrier := {g | (∀ i j, Deep (f i j) (g.val i j)) ∧ ∀ i j, Deep (f i j) ((g⁻¹).val i j)}
  one_mem' := by
    have : ∀ i j, Deep (f i j) ((1 : Matrix n n k) i j) := fun i j => by
      by_cases h : i = j
      · subst h; simp [hf.1, deep_zero_iff]
      · simp [one_apply_ne h, deep_zero]
    exact ⟨this, this⟩
  mul_mem' := by
    have : ∀ A B : Matrix n n k, (∀ i j, Deep (f i j) (A i j)) → (∀ i j, Deep (f i j) (B i j)) →
        ∀ i j, Deep (f i j) ((A * B) i j) := fun A B hA hB i j => by
      rw [mul_apply]
      exact Deep.sum fun l _ => ((hA i l).mul (hB l j)).mono (hf.2 i j l)
    intro a b ha hb
    refine ⟨this _ _ ha.1 hb.1, ?_⟩
    rw [_root_.mul_inv_rev]
    exact this _ _ hb.2 ha.2
  inv_mem' := fun h => ⟨h.2, by simpa using h.1⟩

theorem grp_mono {f g : n → n → ℤ} (hf : Conc f) (hg : Conc g) (h : ∀ a b, g a b ≤ f a b) :
    grp k hf ≤ grp k hg := fun _ hx =>
  ⟨fun i j => (hx.1 i j).mono (h i j), fun i j => (hx.2 i j).mono (h i j)⟩

theorem isCompact_grp {f : n → n → ℤ} (hf : Conc f) : IsCompact (grp k hf : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  rfl

def elem {i j : n} (h : i ≠ j) (y : k) : GL n k :=
  ⟨transvection i j y, transvection i j (-y), by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem elem_mem {f : n → n → ℤ} (hf : Conc f) {i j : n} (h : i ≠ j) {y : k} (hy : Deep (f i j) y) :
    elem h y ∈ grp k hf := by
  have : ∀ y : k, Deep (f i j) y → ∀ a b, Deep (f a b) (transvection i j y a b) := fun y hy a b => by
    have h1 := (grp k hf).one_mem.1 a b
    by_cases c : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := c
      simpa [transvection, one_apply_ne h] using hy
    · simpa [transvection, single_apply, c] using h1
  exact ⟨this y hy, this _ hy.neg⟩

theorem diag_unit {f : n → n → ℤ} (hf : Chamber f) {p : GL n k} {i : n}
    (h1 : ∀ l, Deep (f i l) (p.val i l)) (h2 : ∀ l, Deep (f l i) ((p⁻¹).val l i)) :
    ¬ Deep 1 (p.val i i) := by
  intro h
  have h3 : Deep 1 ((p.val * (p⁻¹).val) i i) := by
    rw [mul_apply]
    refine Deep.sum fun l _ => ?_
    by_cases c : l = i
    · subst c
      exact (h.mul (h2 l)).mono (by rw [hf.1.1]; omega)
    · exact ((h1 l).mul (h2 l)).mono (hf.2 i l (Ne.symm c)).ge
  simp [deep_one_iff] at h3

variable {g f f' : n → n → ℤ} {i j : n}

theorem mem_of_entry (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : Deep (f i j) (p.val i j)) : p ∈ grp k hf.1 := by
  have h1 : ∀ a b, Deep (f a b) (p.val a b) := fun a b => by
    by_cases c : a = i ∧ b = j
    · rw [c.1, c.2]; exact h
    · rw [hfg a b c]; exact hp.1 a b
  have h2 : ∀ a b, ¬ (a = i ∧ b = j) → Deep (f a b) ((p⁻¹).val a b) := fun a b c => by
    rw [hfg a b c]; exact hp.2 a b
  refine ⟨h1, fun a b => ?_⟩
  by_cases c : a = i ∧ b = j
  swap
  · exact h2 a b c
  rw [c.1, c.2]
  obtain ⟨hu0, hu⟩ := deep_inv (diag_unit hf (h1 i) fun l => h2 l i (by grind))
  have h3 : (p.val * (p⁻¹).val) i j = 0 := by simp [one_apply_ne hij]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at h3
  have h4 : Deep (f i j) (p.val i i * (p⁻¹).val i j) := by
    rw [h3]
    exact (Deep.sum fun l hl => ((h1 i l).mul (h2 l j (by grind))).mono (hf.1.2 i j l)).neg
  simpa only [zero_add, inv_mul_cancel_left₀ hu0] using hu.mul h4

theorem exists_factor (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : ¬ Deep 1 (p.val j j)) : ∃ y : k, Deep (g i j) y ∧ ∃ b ∈ grp k hf.1, p = elem hij y * b := by
  obtain ⟨hu0, hu⟩ := deep_inv h
  have hy : Deep (g i j) (p.val i j * (p.val j j)⁻¹) := by simpa using (hp.1 i j).mul hu
  refine ⟨_, hy, (elem hij _)⁻¹ * p, mem_of_entry hg hf hij hfg
    (mul_mem (inv_mem (elem_mem hg hij hy)) hp) ?_, (mul_inv_cancel_left _ _).symm⟩
  have : ((elem hij (p.val i j * (p.val j j)⁻¹))⁻¹ * p).val i j = 0 := by
    show (transvection i j (-(p.val i j * (p.val j j)⁻¹)) * p.val) i j = 0
    rw [transvection_mul_apply_same]
    field_simp
    ring
  rw [this]
  exact deep_zero _

variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}

theorem inj_adjacent (hπ : IsSmooth π) (hg : Conc g) (hf : Chamber f) (hf' : Chamber f') (hij : i ≠ j)
    (h1 : f i j = g i j + 1) (h2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b)
    (h3 : f' j i = g j i + 1) (h4 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) :
    Inj π (grp k hf.1) (grp k hf'.1) := by
  have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    · exact (h4 a b c).ge
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  obtain ⟨c, hc0, hc, hc'⟩ := exists_deep (k := k) (g i j)
  let s : GL n k := elem hij.symm c⁻¹ * elem hij (-c)
  have hs : s ∈ grp k hg :=
    mul_mem (elem_mem hg _ (hc'.mono (by omega))) (elem_mem hg _ hc.neg)
  have hl : ∀ (p : GL n k) (b : n), (s⁻¹ * p).val i b = c * p.val j b := fun p b => by
    rw [_root_.mul_inv_rev, mul_assoc]
    show (transvection i j (-(-c)) * (transvection j i (-c⁻¹) * p.val)) i b = _
    rw [transvection_mul_apply_same, transvection_mul_apply_same, transvection_mul_apply_of_ne _ _ _ _ hij]
    field_simp
    ring
  have hr : ∀ (p : GL n k) (a : n), (p * s).val a j = -c * p.val a i := fun p a => by
    rw [← mul_assoc]
    show (p.val * transvection j i c⁻¹ * transvection i j (-c)) a j = _
    rw [mul_transvection_apply_same, mul_transvection_apply_same,
      mul_transvection_apply_of_ne _ _ _ _ hij.symm]
    field_simp
    ring
  refine inj_of_rank_one hπ (isCompact_grp _) (isCompact_grp hg) hle hs (fun x hx => ?_) fun p hp => ?_
  · refine mem_of_entry hg hf hij h2 (mul_mem (mul_mem (inv_mem hs) (hle hx)) hs) ?_
    rw [mul_assoc, hl, hr]
    exact (hc.mul (hc.neg.mul (hx.1 j i))).mono (by omega)
  · by_cases hu : Deep 1 (p.val j j)
    · refine Or.inr (mem_of_entry hg hf hij h2 (mul_mem (inv_mem hs) hp) ?_)
      rw [hl]
      exact (hc.mul hu).mono (by omega)
    · obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 hp hu
      exact Or.inl ⟨_, elem_mem hf'.1 hij (by rwa [h7]), b, hb, e⟩

theorem inj_chambers (hπ : IsSmooth π) {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) :
    Inj π (grp k hf.1) (grp k hF.1) := by
  generalize hd : ∑ p : n × n, (f p.1 p.2 - F p.1 p.2).toNat = d
  induction d using Nat.strong_induction_on generalizing f with
  | _ d ih =>
  by_cases hne : f = F
  · subst hne
    exact fun v hv hv' => eq_zero_of_fixed hπ (isCompact_grp _) hv hv'
  obtain ⟨i, j, hij, hlt, hw⟩ := exists_wall hf hF hne
  obtain ⟨g, f', hg, hf', h1, h2, h3, h4⟩ := exists_flip hf hij hw
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  have h8 := hF.2 i j hij
  refine (inj_adjacent hπ hg hf hf' hij h1 h2 h3 h4).trans hπ (isCompact_grp _) (fun x hx => ?_)
    (ih _ ?_ hf' rfl)
  · have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
      by_cases c : a = j ∧ b = i
      · rw [c.1, c.2]; omega
      · exact (h4 a b c).ge
    obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 (hle hx)
      (diag_unit hf' (hx.1 j) fun l => hx.2 l j)
    exact ⟨_, elem_mem hF.1 hij (hy.mono (by omega)), b, hb, e⟩
  · rw [← hd]
    refine Finset.sum_lt_sum (fun p _ => ?_) ⟨(i, j), Finset.mem_univ _, by simp only; omega⟩
    obtain ⟨a, b⟩ := p
    simp only
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    by_cases c' : a = i ∧ b = j
    · rw [c'.1, c'.2]; omega
    rw [h4 a b c, h2 a b c']

variable [LinearOrder n]

def ray (m : ℕ) (i j : n) : ℤ :=
  (if j < i then 1 else 0) + m * (((Finset.univ.filter (· < i)).card : ℤ) - (Finset.univ.filter (· < j)).card)

theorem chamber_ray (m : ℕ) : Chamber (ray (n := n) m) := by
  refine ⟨⟨fun i => by simp [ray], fun i j l => ?_⟩, fun i j h => ?_⟩
  · have : (if j < i then 1 else 0 : ℤ) ≤ (if l < i then 1 else 0) + if j < l then 1 else 0 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith
  · have : (if j < i then 1 else 0 : ℤ) + (if i < j then 1 else 0) = 1 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith

theorem grp_ray_zero_le : grp k (chamber_ray (n := n) 0).1 ≤ iwahori k n := fun x hx => by
  have h0 : ∀ i j : n, 0 ≤ ray 0 i j := fun i j => by simp only [ray]; split_ifs <;> simp
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff x).2
    ⟨fun i j => deep_zero_iff.1 ((hx.1 i j).mono (h0 i j)),
      fun i j => deep_zero_iff.1 ((hx.2 i j).mono (h0 i j))⟩, fun i j h => ?_⟩
  exact deep_one_iff.1 ((hx.1 i j).mono (by simp [ray, h]))

theorem eventually_mem_ray {u : GL n k} (hu : u ∈ unipB k n) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ grp k (chamber_ray (n := n) m).1 := by
  have key : ∀ u ∈ unipB k n, ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep (ray m i j) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      have h1 : ((Finset.univ.filter (· < i)).card : ℤ) < (Finset.univ.filter (· < j)).card := by
        refine Int.ofNat_lt.2 (Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun a ha => ?_).2
          ⟨i, by simpa using h, by simp⟩))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.trans h
      simp only [ray, if_neg h.not_gt]
      nlinarith
    · simp [((mem_unipB k).1 hu).2, ray, deep_zero_iff]
    · simp [((mem_unipB k).1 hu).1 i j h, deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem eventually_mem_twKer {v : V} (hv : v ∈ twKer π (unipB k n) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, v ∈ twKer π (grp k (chamber_ray (n := n) m).1) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_ray u.2] with m hm
    simpa using sub_mem_twKer hm w
  | zero => simp
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with m h1 h2 using add_mem h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with m h1 using Submodule.smul_mem _ a h1

end Groups

theorem iwahoriProj_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (hπ : IsSmooth π) :
    Function.Injective (iwahoriProj π) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext ?_
  have h1 : v.1 ∈ twKer π (unipB k n) 1 := (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hv)
  obtain ⟨m, hm⟩ := (eventually_mem_twKer h1).exists
  exact inj_chambers hπ (chamber_ray 0) (chamber_ray m) v.1
    (mem_fixed.2 fun h hh => mem_fixed.1 v.2 h (grp_ray_zero_le hh)) hm

end GlobalTheory.IwahoriInj
