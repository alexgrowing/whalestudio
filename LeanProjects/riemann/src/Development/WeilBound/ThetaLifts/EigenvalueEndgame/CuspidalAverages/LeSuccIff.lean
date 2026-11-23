import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.LocB

open ValuativeRel GlobalTheory.WeilM GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {ϖ : kˣ}

def Le (ϖ : kˣ) (e : ℤ) (x : k) : Prop := valuation k x ≤ valuation k (ϖ : k) ^ e

theorem u_pos (ϖ : kˣ) : 0 < valuation k (ϖ : k) := by
  rw [Valuation.pos_iff]; exact ϖ.ne_zero

theorem u_lt (h : IsUnif ϖ) : valuation k (ϖ : k) < 1 := by rw [h]; exact uniformizer_lt_one

theorem Le.mono (h : IsUnif ϖ) {e e' : ℤ} {x : k} (hx : Le ϖ e x) (he : e' ≤ e) : Le ϖ e' x :=
  le_trans hx (zpow_le_zpow_right_of_le_one₀ (u_pos ϖ) (u_lt h).le he)

theorem Le.add {e : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ e y) : Le ϖ e (x + y) := (valuation k).map_add_le hx hy

theorem Le.sub {e : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ e y) : Le ϖ e (x - y) := (valuation k).map_sub_le hx hy

theorem Le.zero (e : ℤ) : Le ϖ e 0 := by simp [Le]

theorem Le.mul {e f : ℤ} {x y : k} (hx : Le ϖ e x) (hy : Le ϖ f y) : Le ϖ (e + f) (x * y) := by
  unfold Le at *
  rw [map_mul, zpow_add₀ (u_pos ϖ).ne']
  exact mul_le_mul' hx hy

theorem le_mul_iff {e f : ℤ} {x y : k} (hy : valuation k y = valuation k (ϖ : k) ^ f) : Le ϖ (e + f) (x * y) ↔ Le ϖ e x := by
  unfold Le
  rw [map_mul, zpow_add₀ (u_pos ϖ).ne', hy]
  exact mul_le_mul_iff_left₀ (zpow_pos (u_pos ϖ) f)

theorem le_one_iff (h : IsUnif ϖ) {x : k} : Le ϖ 1 x ↔ valuation k x < 1 := by
  unfold Le; rw [zpow_one, h, le_uniformizer_iff]

theorem le_zero_iff {x : k} : Le ϖ 0 x ↔ valuation k x ≤ 1 := by unfold Le; rw [zpow_zero]

theorem val_zpow (e : ℤ) : valuation k ((ϖ : k) ^ e) = valuation k (ϖ : k) ^ e := map_zpow₀ _ _ _

theorem le_succ_iff (h : IsUnif ϖ) {e : ℤ} {x : k} : Le ϖ (e + 1) x ↔ Le ϖ e x ∧ valuation k x ≠ valuation k (ϖ : k) ^ e := by
  have h0 : (ϖ : k) ^ e ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
  have hx : x = x / (ϖ : k) ^ e * (ϖ : k) ^ e := (div_mul_cancel₀ _ h0).symm
  have hp := zpow_pos (u_pos ϖ) e
  rw [hx, add_comm, le_mul_iff (val_zpow e), le_one_iff h]
  unfold Le
  rw [← lt_iff_le_and_ne, map_mul, val_zpow]
  exact (mul_lt_iff_lt_one_left hp).symm

theorem exists_reps (h : IsUnif ϖ) : ∃ R : Finset k, R.card = GlobalTheory.SplitWeil.resCard k ∧ (∀ ρ ∈ R, Le ϖ 0 ρ) ∧
    ∀ x, Le ϖ 0 x → ∃ ρ ∈ R, Le ϖ 1 (x - ρ) ∧ ∀ ρ' ∈ R, Le ϖ 1 (x - ρ') → ρ' = ρ := by
  classical
  have : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨s, hs⟩ := (IsLocalRing.residue_surjective (R := 𝒪[k])).hasRightInverse
  have key : ∀ (x : 𝒪[k]) (z : 𝓀[k]), Le ϖ 1 ((x : k) - (s z : k)) ↔ IsLocalRing.residue _ x = z := by
    intro x z
    rw [le_one_iff h, ← hs z, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hs z,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rfl
  refine ⟨Finset.univ.image fun z => (s z : k), ?_, ?_, fun x hx => ?_⟩
  · rw [Finset.card_image_of_injective (f := fun z => (s z : k)) _ (Subtype.val_injective.comp hs.injective), Finset.card_univ,
      GlobalTheory.SplitWeil.resCard, Nat.card_eq_fintype_card]
  · intro ρ hρ
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hρ
    exact le_zero_iff.2 (s z).2
  · let x' : 𝒪[k] := ⟨x, le_zero_iff.1 hx⟩
    refine ⟨s (IsLocalRing.residue _ x'), Finset.mem_image_of_mem _ (Finset.mem_univ _), (key x' _).2 rfl, fun ρ' hρ' h' => ?_⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hρ'
    rw [(key x' z).1 h']

theorem count (h : IsUnif ϖ) {M : Type} (l : (M → ℂ) →ₗ[ℂ] ℂ) (S S' : Set M) (f : M → k) (s : k → M → M)
    (h1 : ∀ Y ∈ S', Le ϖ 0 (f Y)) (h2 : ∀ ρ, Le ϖ 0 ρ → ∀ Y, s ρ Y ∈ S ↔ Y ∈ S' ∧ Le ϖ 1 (f Y - ρ))
    (h3 : ∀ ρ, Le ϖ 0 ρ → l (fun Y => S.indicator 1 (s ρ Y)) = l (S.indicator 1)) :
    l (S'.indicator 1) = (GlobalTheory.SplitWeil.resCard k : ℂ) * l (S.indicator 1) := by
  classical
  obtain ⟨R, hc, hR, hx⟩ := exists_reps h
  have : S'.indicator (1 : M → ℂ) = ∑ ρ ∈ R, fun Y => S.indicator (1 : M → ℂ) (s ρ Y) := by
    funext Y
    rw [Finset.sum_apply]
    by_cases hY : Y ∈ S'
    · obtain ⟨ρ, hρ, h4, h5⟩ := hx _ (h1 Y hY)
      rw [Finset.sum_eq_single_of_mem ρ hρ, Set.indicator_of_mem hY, Set.indicator_of_mem ((h2 ρ (hR ρ hρ) Y).2 ⟨hY, h4⟩)]
      · rfl
      · intro ρ' hρ' hne
        exact Set.indicator_of_notMem (fun hm => hne (h5 ρ' hρ' ((h2 ρ' (hR ρ' hρ') Y).1 hm).2)) _
    · rw [Set.indicator_of_notMem hY, Finset.sum_eq_zero]
      intro ρ hρ
      exact Set.indicator_of_notMem (fun hm => hY ((h2 ρ (hR ρ hρ) Y).1 hm).1) _
  rw [this, map_sum, Finset.sum_congr rfl fun ρ hρ => h3 ρ (hR ρ hρ), Finset.sum_const, hc, nsmul_eq_mul]

def Box (ϖ : kˣ) (e : Fin n → Fin d → ℤ) : Set (Matrix (Fin n) (Fin d) k) := {Y | ∀ x y, Le ϖ (e x y) (Y x y)}

def Piv (ϖ : kˣ) (a : Fin n) (i : Fin d) (e : Fin n → Fin d → ℤ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | Y ∈ Box ϖ e ∧ valuation k (Y a i) = valuation k (ϖ : k) ^ e a i}

theorem box_SB (ϖ : kˣ) (e : Fin n → Fin d → ℤ) : (Box ϖ e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (Box ϖ e) := by
    have h : IsCompact (Set.pi Set.univ fun x : Fin n => Set.pi Set.univ fun y : Fin d =>
        {z : k | valuation k z ≤ valuation k (ϖ : k) ^ e x y}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e' : Box ϖ e = (Set.pi Set.univ fun x : Fin n => Set.pi Set.univ fun y : Fin d =>
        {z : k | valuation k z ≤ valuation k (ϖ : k) ^ e x y}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e']; exact h
  have ho : IsOpen (Box ϖ e) := by
    simp only [Box, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    convert GlobalTheory.SplitWeil.Model.isOpen_int.preimage
      (f := fun A : Matrix (Fin n) (Fin d) k => A i j * (ϖ : k) ^ (-e i j)) (by fun_prop) using 1
    ext A
    have := le_mul_iff (ϖ := ϖ) (e := e i j) (x := A i j) (val_zpow (-e i j))
    rw [add_neg_cancel, le_zero_iff] at this
    exact this.symm
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem piv_eq (h : IsUnif ϖ) (a : Fin n) (i : Fin d) (e e' : Fin n → Fin d → ℤ)
    (he : ∀ x y, e' x y = e x y + if x = a ∧ y = i then 1 else 0) :
    (Piv ϖ a i e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) = (Box ϖ e).indicator 1 - (Box ϖ e').indicator 1 := by
  have key : ∀ Y, Y ∈ Box ϖ e' ↔ Y ∈ Box ϖ e ∧ valuation k (Y a i) ≠ valuation k (ϖ : k) ^ e a i := by
    intro Y
    constructor
    · intro hY
      refine ⟨fun x y => (hY x y).mono h (by rw [he]; split_ifs <;> omega), ?_⟩
      have := hY a i
      rw [he, if_pos ⟨rfl, rfl⟩] at this
      exact ((le_succ_iff h).1 this).2
    · rintro ⟨hY, hn⟩ x y
      rw [he]
      split_ifs with hxy
      · obtain ⟨rfl, rfl⟩ := hxy
        exact (le_succ_iff h).2 ⟨hY _ _, hn⟩
      · simpa using hY x y
  funext Y
  by_cases h1 : Y ∈ Box ϖ e <;> by_cases h2 : valuation k (Y a i) = valuation k (ϖ : k) ^ e a i <;>
    simp [Set.indicator, Piv, key, h1, h2]

theorem piv_SB (h : IsUnif ϖ) (a : Fin n) (i : Fin d) (e : Fin n → Fin d → ℤ) :
    (Piv ϖ a i e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  rw [piv_eq h a i e (fun x y => e x y + if x = a ∧ y = i then 1 else 0) fun _ _ => rfl]
  exact Submodule.sub_mem _ (box_SB _ _) (box_SB _ _)

theorem move (h : IsUnif ϖ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) (a : Fin n) (i : Fin d) (e e' : Fin n → Fin d → ℤ)
    (x₀ : Fin n) (y₀ : Fin d) (hne : ¬ (a = x₀ ∧ i = y₀)) (he : ∀ x y, e x y = e' x y + if x = x₀ ∧ y = y₀ then 1 else 0)
    (δ : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k) (h0 : ∀ Y, δ Y x₀ y₀ = Y a i) (h1 : ∀ Y, δ Y a i = 0)
    (h2 : ∀ (t : k) Y, δ (Y + t • δ Y) = δ Y)
    (h3 : ∀ Y ∈ Box ϖ e', ∀ x y, Le ϖ (e' x y - (e' x₀ y₀ - e' a i)) (δ Y x y))
    (h4 : ∀ t : k, Le ϖ (e' x₀ y₀ - e' a i) t →
      l (fun Y => (Piv ϖ a i e).indicator 1 (Y + t • δ Y)) = l ((Piv ϖ a i e).indicator 1)) :
    l ((Piv ϖ a i e').indicator 1) = (GlobalTheory.SplitWeil.resCard k : ℂ) * l ((Piv ϖ a i e).indicator 1) := by
  set w := e' x₀ y₀ - e' a i with hw
  have hai : e a i = e' a i := by rw [he, if_neg hne, add_zero]
  have ht : ∀ ρ, Le ϖ 0 ρ → Le ϖ w (-(ρ * (ϖ : k) ^ w)) := fun ρ hρ => by
    have := (le_mul_iff (val_zpow w)).2 hρ
    rw [zero_add] at this
    simpa using (Le.zero w).sub this
  have hd : ∀ z : k, valuation k z = valuation k (ϖ : k) ^ e' a i →
      valuation k ((ϖ : k) ^ w * z) = valuation k (ϖ : k) ^ e' x₀ y₀ ∧ (ϖ : k) ^ w * z ≠ 0 := fun z hz => by
    have : valuation k ((ϖ : k) ^ w * z) = valuation k (ϖ : k) ^ e' x₀ y₀ := by
      rw [map_mul, val_zpow, hz, ← zpow_add₀ (u_pos ϖ).ne', hw, sub_add_cancel]
    refine ⟨this, fun h0 => ?_⟩
    rw [h0, map_zero] at this
    exact (zpow_pos (u_pos ϖ) _).ne this
  have hb : ∀ t, Le ϖ w t → ∀ Y ∈ Box ϖ e', Y + t • δ Y ∈ Box ϖ e' := fun t ht Y hY x y => by
    have := ht.mul (h3 Y hY x y)
    rw [add_sub_cancel] at this
    exact (hY x y).add this
  refine count h l _ _ (fun Y => Y x₀ y₀ / ((ϖ : k) ^ w * Y a i)) (fun ρ Y => Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) ?_ ?_
    fun ρ hρ => h4 _ (ht ρ hρ)
  · rintro Y ⟨hY, hp⟩
    obtain ⟨h5, h6⟩ := hd _ hp
    rw [← le_mul_iff h5, div_mul_cancel₀ _ h6, zero_add]
    exact hY _ _
  · intro ρ hρ Y
    have hpiv : (Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) a i = Y a i := by simp [h1]
    have hent : ∀ h6 : (ϖ : k) ^ w * Y a i ≠ 0, (Y x₀ y₀ / ((ϖ : k) ^ w * Y a i) - ρ) * ((ϖ : k) ^ w * Y a i) =
        (Y + (-(ρ * (ϖ : k) ^ w)) • δ Y) x₀ y₀ := fun h6 => by
      rw [sub_mul, div_mul_cancel₀ _ h6]; simp [h0]; ring
    constructor
    · rintro ⟨hZ, hp⟩
      rw [hpiv, hai] at hp
      obtain ⟨h5, h6⟩ := hd _ hp
      have hZ' : Y + (-(ρ * (ϖ : k) ^ w)) • δ Y ∈ Box ϖ e' := fun x y =>
        (hZ x y).mono h (by rw [he]; split_ifs <;> omega)
      have := hb (-(-(ρ * (ϖ : k) ^ w))) (by simpa using (Le.zero w).sub (ht ρ hρ)) _ hZ'
      rw [h2, neg_smul (-(ρ * (ϖ : k) ^ w)), add_neg_cancel_right] at this
      refine ⟨⟨this, hp⟩, ?_⟩
      rw [← le_mul_iff h5, hent h6, add_comm 1]
      have := hZ x₀ y₀
      rwa [he, if_pos ⟨rfl, rfl⟩] at this
    · rintro ⟨⟨hY, hp⟩, h7⟩
      obtain ⟨h5, h6⟩ := hd _ hp
      rw [← le_mul_iff h5, hent h6, add_comm 1] at h7
      refine ⟨fun x y => ?_, by rw [hpiv, hai]; exact hp⟩
      rw [he]
      split_ifs with hxy
      · obtain ⟨rfl, rfl⟩ := hxy
        exact h7
      · rw [add_zero]; exact hb _ (ht ρ hρ) Y hY x y

end PositivityTheory.ThKEnd.Cusp.LocB

end
