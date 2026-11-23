import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

namespace UpperTheory.affineWeylIwahoriData

section Tv
variable {k : Type} [Field k] {n : ℕ}

private def tv (a b : Fin n) (h : a ≠ b) (c : k) : GL (Fin n) k where
  val := transvection a b c
  inv := transvection a b (-c)
  val_inv := by rw [transvection_mul_transvection_same a b h]; simp
  inv_val := by rw [transvection_mul_transvection_same a b h]; simp

private theorem tv_val (a b : Fin n) (h : a ≠ b) (c : k) :
    (tv a b h c : Matrix (Fin n) (Fin n) k) = 1 + single a b c := rfl

private theorem tv_mul_apply (a b : Fin n) (h : a ≠ b) (c : k) (M : Matrix (Fin n) (Fin n) k)
    (i j : Fin n) :
    ((tv a b h c : Matrix (Fin n) (Fin n) k) * M) i j =
      M i j + if i = a then c * M b j else 0 := by
  rw [tv_val, add_mul, one_mul, Matrix.add_apply]
  congr 1
  split_ifs with hi
  · subst hi; simp [single_mul_apply_same]
  · simp [single_mul_apply_of_ne _ _ _ _ _ hi]

private theorem mul_tv_apply (a b : Fin n) (h : a ≠ b) (c : k) (M : Matrix (Fin n) (Fin n) k)
    (i j : Fin n) :
    (M * (tv a b h c : Matrix (Fin n) (Fin n) k)) i j =
      M i j + if j = b then M i a * c else 0 := by
  rw [tv_val, mul_add, mul_one, Matrix.add_apply]
  congr 1
  split_ifs with hj
  · subst hj; simp [mul_single_apply_same]
  · simp [mul_single_apply_of_ne _ _ _ _ _ hj]

private theorem tv_apply (a b : Fin n) (h : a ≠ b) (c : k) (i j : Fin n) :
    (tv a b h c : Matrix (Fin n) (Fin n) k) i j =
      (1 : Matrix (Fin n) (Fin n) k) i j + if i = a ∧ j = b then c else 0 := by
  have e : (a = i ∧ b = j) ↔ (i = a ∧ j = b) := by
    constructor <;> (rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩)
  rw [tv_val, Matrix.add_apply, single_apply]
  simp only [e]

private theorem tv_mul_neg (a b : Fin n) (h : a ≠ b) (c : k) :
    tv a b h c * tv a b h (-c) = 1 := by
  refine Units.ext ?_
  show transvection a b c * transvection a b (-c) = 1
  rw [transvection_mul_transvection_same a b h]; simp

private theorem tv_neg_mul (a b : Fin n) (h : a ≠ b) (c : k) :
    tv a b h (-c) * tv a b h c = 1 := by
  refine Units.ext ?_
  show transvection a b (-c) * transvection a b c = 1
  rw [transvection_mul_transvection_same a b h]; simp

end Tv

section Loc
open ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

private theorem tv_mem (a b : Fin n) (h : a ≠ b) (c : F) (hc : valuation F c ≤ 1)
    (hlt : b < a → valuation F c < 1) : tv a b h c ∈ iwahori F n := by
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [tv_apply]
    by_cases hij : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hij
      simpa [one_apply_ne h] using hc
    · rw [if_neg hij, add_zero, one_apply]
      split_ifs <;> simp
  · rw [tv_apply, one_apply_ne hij.ne', zero_add]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact hlt hij
    · simp
  · rw [tv_apply, one_apply_eq, if_neg (fun e => h (e.1.symm.trans e.2)), add_zero, map_one]

private theorem perm_mul_tv (σ : Equiv.Perm (Fin n)) (a b a' b' : Fin n) (ha : σ a = a')
    (hb : σ b = b') (h : a ≠ b) (h' : a' ≠ b') (c : F) :
    permGL F σ * tv a b h c = tv a' b' h' c * permGL F σ := by
  subst ha hb
  refine Units.ext ?_
  ext x y
  rw [Units.val_mul, Units.val_mul, mul_tv_apply, tv_mul_apply]
  simp only [permGL_apply]
  congr 1
  by_cases hy : y = b
  · subst hy
    by_cases hx : x = σ a
    · subst hx; simp
    · simp [hx]
  · have : σ b ≠ σ y := fun e => hy (σ.injective e).symm
    simp [hy, this]

private theorem affine_mul_tv (w : ExtendedAffineWeyl n) (a b : Fin n) (h : a ≠ b)
    (h' : w.right a ≠ w.right b) (c : F) :
    affineWeylGL F n w * tv a b h c =
      tv (w.right a) (w.right b) h'
        (ϖ ^ ((w.left (w.right a)).toAdd - (w.left (w.right b)).toAdd) * c) *
        affineWeylGL F n w := by
  refine Units.ext ?_
  ext x y
  rw [Units.val_mul, Units.val_mul, mul_tv_apply, tv_mul_apply]
  simp only [affineWeylGL_apply]
  congr 1
  by_cases hy : y = b
  · subst hy
    by_cases hx : x = w.right a
    · subst hx
      have h0 := uniformizer_ne_zero F
      simp only [if_true]
      rw [zpow_sub₀ h0]
      field_simp
    · simp [hx]
  · have : w.right b ≠ w.right y := fun e => hy (w.right.injective e).symm
    simp [hy, this]

private theorem swap_lt {m : ℕ} (i : Fin m) (a b : Fin (m + 1)) (hab : b < a)
    (hn : ¬(a = i.succ ∧ b = i.castSucc)) :
    Equiv.swap i.castSucc i.succ b < Equiv.swap i.castSucc i.succ a := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.lt_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at * <;> omega

private theorem swap_conj_mem {m : ℕ} (i : Fin m) (κ : GL (Fin (m + 1)) F)
    (hκ : κ ∈ iwahori F (m + 1)) (hz : valuation F (κ i.castSucc i.succ) < 1) :
    permGL F (Equiv.swap i.castSucc i.succ) * κ * permGL F (Equiv.swap i.castSucc i.succ) ∈
      iwahori F (m + 1) := by
  have entry : ∀ a b, ((permGL F (Equiv.swap i.castSucc i.succ) * κ *
      permGL F (Equiv.swap i.castSucc i.succ) : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b =
      κ (Equiv.swap i.castSucc i.succ a) (Equiv.swap i.castSucc i.succ b) := by
    intro a b
    rw [Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply, Equiv.swap_inv]
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F (m + 1)).1 hκ
  refine (mem_iwahori_iff F (m + 1)).2 ⟨fun a b => ?_, fun a b hab => ?_, fun a => ?_⟩
  · rw [entry]; exact h1 _ _
  · rw [entry]
    by_cases hn : a = i.succ ∧ b = i.castSucc
    · obtain ⟨rfl, rfl⟩ := hn
      simpa using hz
    · exact h2 _ _ (swap_lt i a b hab hn)
  · rw [entry]; exact h3 _

private theorem step_one {m : ℕ} (i : Fin m) (h : i.castSucc ≠ i.succ) (κ : GL (Fin (m + 1)) F)
    (hκ : κ ∈ iwahori F (m + 1)) :
    ∃ c : F, valuation F c ≤ 1 ∧ ∃ κ' ∈ iwahori F (m + 1), κ = tv i.castSucc i.succ h c * κ' ∧
      permGL F (Equiv.swap i.castSucc i.succ) * κ' * permGL F (Equiv.swap i.castSucc i.succ) ∈
        iwahori F (m + 1) := by
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F (m + 1)).1 hκ
  have hr : κ i.succ i.succ ≠ 0 := by
    intro e
    have := h3 i.succ
    rw [e, map_zero] at this
    exact zero_ne_one this
  have hc : valuation F (κ i.castSucc i.succ / κ i.succ i.succ) ≤ 1 := by
    rw [map_div₀, h3, div_one]
    exact h1 _ _
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hneg : valuation F (-(κ i.castSucc i.succ / κ i.succ i.succ)) ≤ 1 := by
    rwa [Valuation.map_neg]
  refine ⟨_, hc, tv i.castSucc i.succ h (-(κ i.castSucc i.succ / κ i.succ i.succ)) * κ,
    (iwahori F (m + 1)).mul_mem (tv_mem F _ _ h _ hneg (fun e => absurd e hlt.not_gt)) hκ, ?_, ?_⟩
  · rw [← mul_assoc, tv_mul_neg, one_mul]
  · refine swap_conj_mem F i _ ((iwahori F (m + 1)).mul_mem
      (tv_mem F _ _ h _ hneg (fun e => absurd e hlt.not_gt)) hκ) ?_
    rw [Units.val_mul, tv_mul_apply, if_pos rfl]
    have : κ i.castSucc i.succ + -(κ i.castSucc i.succ / κ i.succ i.succ) * κ i.succ i.succ = 0 := by
      field_simp
      ring
    rw [this, map_zero]
    exact zero_lt_one

private theorem unit_decomp (p r : Fin n) (h : p ≠ r) (h' : r ≠ p) (c : F)
    (hc : valuation F c = 1) :
    ∃ H ∈ iwahori F n, tv p r h c =
      tv r p h' c⁻¹ * H * permGL F (Equiv.swap p r) * tv r p h' c⁻¹ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact zero_ne_one hc
  have hs : permGL F (Equiv.swap p r) * permGL F (Equiv.swap p r) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hentry : ∀ i j, ((tv r p h' (-c⁻¹) * tv p r h c * tv r p h' (-c⁻¹) *
      permGL F (Equiv.swap p r) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      if i = j then (if i = p then c else if i = r then -c⁻¹ else 1) else 0 := by
    intro i j
    rw [Units.val_mul, mul_permGL_apply, Units.val_mul, mul_tv_apply, Units.val_mul,
      tv_mul_apply, tv_mul_apply]
    simp only [tv_apply, one_apply]
    by_cases hip : i = p
    · subst hip
      by_cases hjp : j = i
      · subst hjp
        simp [h, h', hc0]
      · by_cases hjr : j = r
        · subst hjr
          simp [h, h', hc0]
        · simp [h, h', hc0, Equiv.swap_apply_of_ne_of_ne hjp hjr, hjp, hjr, Ne.symm hjp, Ne.symm hjr]
    · by_cases hir : i = r
      · subst hir
        by_cases hjp : j = p
        · subst hjp
          simp [h, h', hc0]
        · by_cases hjr : j = i
          · subst hjr
            simp [h, h', hc0]
          · simp [h, h', hc0, Equiv.swap_apply_of_ne_of_ne hjp hjr, hjp, hjr, Ne.symm hjp, Ne.symm hjr]
      · by_cases hjp : j = p
        · subst hjp
          simp [h, h', hc0, hip, hir, Ne.symm hip, Ne.symm hir]
        · by_cases hjr : j = r
          · subst hjr
            simp [h, h', hc0, hip, hir, Ne.symm hip, Ne.symm hir]
          · simp [h, h', hc0, hip, hir, Equiv.swap_apply_of_ne_of_ne hjp hjr]
  refine ⟨tv r p h' (-c⁻¹) * tv p r h c * tv r p h' (-c⁻¹) * permGL F (Equiv.swap p r), ?_, ?_⟩
  · refine (mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
    · rw [hentry]
      split_ifs <;> simp [hc]
    · rw [hentry, if_neg hij.ne']
      simp
    · rw [hentry, if_pos rfl]
      split_ifs <;> simp [hc]
  · calc tv p r h c
        = (tv r p h' c⁻¹ * tv r p h' (-c⁻¹)) * tv p r h c * tv r p h' (-c⁻¹) *
            (permGL F (Equiv.swap p r) * permGL F (Equiv.swap p r)) * tv r p h' c⁻¹ := by
          rw [tv_mul_neg, hs, one_mul, mul_one, mul_assoc, tv_neg_mul, mul_one]
      _ = _ := by simp only [mul_assoc]

private theorem core {m : ℕ} (w : ExtendedAffineWeyl (m + 1)) (i : Fin m)
    (h : i.castSucc ≠ i.succ) (c : F) (hc : valuation F c ≤ 1) :
    affineWeylGL F (m + 1) w * tv i.castSucc i.succ h c *
        permGL F (Equiv.swap i.castSucc i.succ) ∈
      DoubleCoset.doubleCoset (affineWeylGL F (m + 1) w) (iwahori F (m + 1) : Set _)
        (iwahori F (m + 1) : Set _) ∨
    affineWeylGL F (m + 1) w * tv i.castSucc i.succ h c *
        permGL F (Equiv.swap i.castSucc i.succ) ∈
      DoubleCoset.doubleCoset (affineWeylGL F (m + 1) w * permGL F (Equiv.swap i.castSucc i.succ))
        (iwahori F (m + 1) : Set _) (iwahori F (m + 1) : Set _) := by
  have h' : i.succ ≠ i.castSucc := h.symm
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hP : w.right i.castSucc ≠ w.right i.succ := fun e => h (w.right.injective e)
  have hP' : w.right i.succ ≠ w.right i.castSucc := hP.symm
  have hs : permGL F (Equiv.swap i.castSucc i.succ) * permGL F (Equiv.swap i.castSucc i.succ) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  set W := affineWeylGL F (m + 1) w with hW
  set s := permGL F (Equiv.swap i.castSucc i.succ) with hsdef
  set e : ℤ := (w.left (w.right i.castSucc)).toAdd - (w.left (w.right i.succ)).toAdd with he
  set t := valuation F ϖ ^ e with ht
  have htpos : 0 < t := zpow_pos (valuation_uniformizer_pos F) _
  have hvt : ∀ x : F, valuation F (ϖ ^ e * x) = t * valuation F x := by
    intro x
    rw [map_mul, map_zpow₀]
  have hvt' : ∀ x : F, valuation F (ϖ ^ (-e) * x) = t⁻¹ * valuation F x := by
    intro x
    rw [map_mul, map_zpow₀, _root_.zpow_neg]
  by_cases hA : t ≤ 1 ∧ (w.right i.succ < w.right i.castSucc → t < 1)
  · right
    refine DoubleCoset.mem_doubleCoset.2 ⟨tv _ _ hP (ϖ ^ e * c), ?_, 1,
      (iwahori F (m + 1)).one_mem, ?_⟩
    · have hle : t * valuation F c ≤ t := by simpa using mul_le_mul' (le_refl t) hc
      refine tv_mem F _ _ hP _ ?_ (fun hl => ?_)
      · rw [hvt]; exact hle.trans hA.1
      · rw [hvt]; exact hle.trans_lt (hA.2 hl)
    · rw [affine_mul_tv F w _ _ h hP c, mul_one, mul_assoc]
  · have hB : t⁻¹ ≤ 1 ∧ (w.right i.castSucc < w.right i.succ → t⁻¹ < 1) := by
      rcases lt_or_ge 1 t with h1 | h1
      · have h2 : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 h1
        exact ⟨h2.le, fun _ => h2⟩
      · have hRP : w.right i.succ < w.right i.castSucc := by
          by_contra hn
          exact hA ⟨h1, fun hl => absurd hl hn⟩
        have ht1 : t = 1 := le_antisymm h1 (by
          by_contra hn
          exact hA ⟨h1, fun _ => not_le.1 hn⟩)
        exact ⟨by simp [ht1], fun hl => absurd hl hRP.not_gt⟩
    by_cases hc1 : valuation F c < 1
    · right
      refine DoubleCoset.mem_doubleCoset.2 ⟨1, (iwahori F (m + 1)).one_mem, tv _ _ h' c,
        tv_mem F _ _ h' c hc (fun _ => hc1), ?_⟩
      have hsy : s * tv _ _ h' c = tv _ _ h c * s :=
        perm_mul_tv F _ _ _ _ _ (Equiv.swap_apply_right _ _) (Equiv.swap_apply_left _ _) h' h c
      rw [one_mul, mul_assoc, mul_assoc, hsy]
    · left
      have hc2 : valuation F c = 1 := le_antisymm hc (not_lt.1 hc1)
      obtain ⟨H, hH, hx⟩ := unit_decomp F _ _ h h' c hc2
      rw [← hsdef] at hx
      have hb : valuation F c⁻¹ = 1 := by rw [map_inv₀, hc2, inv_one]
      have hsy : s * tv _ _ h' c⁻¹ = tv _ _ h c⁻¹ * s :=
        perm_mul_tv F _ _ _ _ _ (Equiv.swap_apply_right _ _) (Equiv.swap_apply_left _ _) h' h c⁻¹
      have hWy : W * tv _ _ h' c⁻¹ = tv _ _ hP' (ϖ ^ (-e) * c⁻¹) * W := by
        have he' : (w.left (w.right i.succ)).toAdd - (w.left (w.right i.castSucc)).toAdd = -e := by
          rw [he]; ring
        rw [hW, affine_mul_tv F w _ _ h' hP' c⁻¹, he']
      refine DoubleCoset.mem_doubleCoset.2 ⟨tv _ _ hP' (ϖ ^ (-e) * c⁻¹), ?_,
        H * tv _ _ h c⁻¹, (iwahori F (m + 1)).mul_mem hH ?_, ?_⟩
      · refine tv_mem F _ _ hP' _ ?_ (fun hl => ?_)
        · rw [hvt', hb, mul_one]; exact hB.1
        · rw [hvt', hb, mul_one]; exact hB.2 hl
      · exact tv_mem F _ _ h _ hb.le (fun e => absurd e hlt.not_gt)
      · rw [hx]
        calc W * (tv _ _ h' c⁻¹ * H * s * tv _ _ h' c⁻¹) * s
            = (W * tv _ _ h' c⁻¹) * H * (s * tv _ _ h' c⁻¹) * s := by simp only [mul_assoc]
          _ = tv _ _ hP' (ϖ ^ (-e) * c⁻¹) * W * H * (tv _ _ h c⁻¹ * s) * s := by rw [hWy, hsy]
          _ = tv _ _ hP' (ϖ ^ (-e) * c⁻¹) * W * (H * tv _ _ h c⁻¹) := by
            simp only [mul_assoc]
            rw [hs, mul_one]

private theorem main {m : ℕ} (w : ExtendedAffineWeyl (m + 1)) (i : Fin m)
    (κ : GL (Fin (m + 1)) F) (hκ : κ ∈ iwahori F (m + 1)) :
    affineWeylGL F (m + 1) w * κ * permGL F (Equiv.swap i.castSucc i.succ) ∈
      DoubleCoset.doubleCoset (affineWeylGL F (m + 1) w) (iwahori F (m + 1) : Set _)
        (iwahori F (m + 1) : Set _) ∨
    affineWeylGL F (m + 1) w * κ * permGL F (Equiv.swap i.castSucc i.succ) ∈
      DoubleCoset.doubleCoset (affineWeylGL F (m + 1) w * permGL F (Equiv.swap i.castSucc i.succ))
        (iwahori F (m + 1) : Set _) (iwahori F (m + 1) : Set _) := by
  have h : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  obtain ⟨c, hc, κ', -, rfl, hz⟩ := step_one F i h κ hκ
  have hs : permGL F (Equiv.swap i.castSucc i.succ) * permGL F (Equiv.swap i.castSucc i.succ) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have key : affineWeylGL F (m + 1) w * (tv _ _ h c * κ') * permGL F (Equiv.swap i.castSucc i.succ) =
      (affineWeylGL F (m + 1) w * tv _ _ h c * permGL F (Equiv.swap i.castSucc i.succ)) *
        (permGL F (Equiv.swap i.castSucc i.succ) * κ' * permGL F (Equiv.swap i.castSucc i.succ)) := by
    calc _ = affineWeylGL F (m + 1) w * tv _ _ h c * 1 * κ' *
            permGL F (Equiv.swap i.castSucc i.succ) := by simp only [mul_one, mul_assoc]
      _ = _ := by rw [← hs]; simp only [mul_assoc]
  rw [key]
  rcases core F w i h c hc with hd | hd
  · left
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hd
    exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * _, (iwahori F (m + 1)).mul_mem hb hz,
      by rw [e]; simp only [mul_assoc]⟩
  · right
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hd
    exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * _, (iwahori F (m + 1)).mul_mem hb hz,
      by rw [e]; simp only [mul_assoc]⟩

end Loc

end UpperTheory.affineWeylIwahoriData

theorem UpperTheory.affine_weyl_simple_reflection_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
        (w : ExtendedAffineWeyl (m + 1)) (i : Fin m) (κ : GL (Fin (m + 1)) k), κ ∈ iwahori k (m + 1) →
        affineWeylGL k (m + 1) w * κ * permGL k (Equiv.swap i.castSucc i.succ) ∈
            DoubleCoset.doubleCoset (affineWeylGL k (m + 1) w) (iwahori k (m + 1) : Set (GL (Fin (m + 1)) k))
              (iwahori k (m + 1) : Set (GL (Fin (m + 1)) k)) ∨
        affineWeylGL k (m + 1) w * κ * permGL k (Equiv.swap i.castSucc i.succ) ∈
            DoubleCoset.doubleCoset (affineWeylGL k (m + 1) w * permGL k (Equiv.swap i.castSucc i.succ))
              (iwahori k (m + 1) : Set (GL (Fin (m + 1)) k)) (iwahori k (m + 1) : Set (GL (Fin (m + 1)) k)) := by
  intro k _ _ _ _ m w i κ hκ
  exact UpperTheory.affineWeylIwahoriData.main k w i κ hκ
