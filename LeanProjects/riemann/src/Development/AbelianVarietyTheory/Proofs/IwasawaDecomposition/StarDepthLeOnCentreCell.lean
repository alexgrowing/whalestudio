import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan.StarOnCell

variable {X : Type} [AddCommGroup X]

theorem ell_of_eq {n : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    {u : Fin n → LinearMap.BilinForm ℤ X} {c : Fin n → ℝ} (h : toReal β = ∑ i, c i • toReal (u i)) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) c : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, h]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem ell_of_sub_mem {m : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β v : LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {t : ℝ} (h : toReal β - t • toReal v ∈ rcone γ) :
    ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ (ℓ β : ℝ) = t * ℓ v + ∑ j, d j * ℓ (γ j) := by
  obtain ⟨d, hd, e⟩ := h
  refine ⟨d, hd, ?_⟩
  have e' : toReal β = ∑ i : Fin (m + 1), (Fin.cons t d : Fin (m + 1) → ℝ) i •
      toReal ((Fin.cons v γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← e]
    abel
  rw [ell_of_eq ℓ e', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem inRCone_of_sum {p n : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {u : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i) (e : toReal β = ∑ i, x i • toReal (δ i))
    (h : ∀ i, x i ≠ 0 → InRCone u (δ i)) : InRCone u β := by
  classical
  have hi : ∀ i, ∃ g : Fin n → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (u j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨c, hc, hcs⟩ := h i h0
    exact ⟨fun j => x i * c j, fun j => mul_nonneg (hx i) (hc j), by
      rw [hcs, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [e, Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem exists_nat_of_inRCone {n : ℕ} (u : Fin n → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : InRCone u β) : ∃ (k : ℕ) (c : Fin n → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  obtain ⟨r, v, hiff, -⟩ := GlobalTheory.MinkWeylReal.cone_orthant_fg (n + 1) ∅
    (Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ))
    Set.finite_empty
  have h1 : (∀ i, 0 ≤ (Fin.cons 1 c : Fin (n + 1) → ℝ) i) ∧
      (∀ a ∈ (∅ : Set (Fin (n + 1) → ℤ)), ∑ i, (a i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i ≤ 0) ∧
      (∀ b ∈ Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ),
        ∑ i, (b i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i = 0) := by
    refine ⟨fun i => Fin.cases (by simp) (fun j => by simpa using hc j) i, by simp, ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have he := LinearMap.congr_fun₂ e a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg, mul_one]
    rw [he]
    rw [show ∑ i, (u i a b : ℝ) * c i = ∑ i, c i * (u i a b : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨e', he', ht⟩ := (hiff _).1 h1
  have h0 := congr_fun ht 0
  simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  obtain ⟨k, hk⟩ : ∃ k, v k 0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    simp [hne] at h0
  have hv := (hiff fun i => (v k i : ℝ)).2 ⟨Pi.single k 1, fun j => by
    by_cases h : j = k <;> simp [Pi.single_apply, h], by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp⟩
  obtain ⟨-, -, hV⟩ := hv
  refine ⟨v k 0, fun i => v k i.succ, Nat.pos_of_ne_zero hk, ?_⟩
  ext a b
  have h2 := hV _ ⟨(a, b), rfl⟩
  rw [Fin.sum_univ_succ] at h2
  simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg] at h2
  have h3 : ((v k 0 : ℤ) * β a b : ℝ) = ((∑ i, (v k i.succ : ℤ) * u i a b : ℤ) : ℝ) := by
    push_cast
    rw [show ∑ i, ((v k i.succ : ℝ) * (u i a b : ℝ)) = ∑ i, (u i a b : ℝ) * (v k i.succ : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    linarith
  have h4 : (v k 0 : ℤ) * β a b = ∑ i, (v k i.succ : ℤ) * u i a b := by exact_mod_cast h3
  simpa [LinearMap.sum_apply] using h4

end GlobalTheory.PolFan.StarOnCell

namespace GlobalTheory.PolFan.StarOnCell

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem mul_starDepth_le (hγ : IsCell bar ψ γ) {β₀ : LinearMap.BilinForm ℤ X}
    (huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hh : ∀ j, 0 ≤ h (γ j)) (hpos : 0 < h β₀)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hhβ : (0 : ℝ) ≤ h β := by
    rw [ell_of_eq h e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hh i)
  have key := evalR_starDepth_le O bar ψ w X m γ (toReal β) ((h β : ℝ) / h β₀) hγ ⟨c, hc, e⟩
    (div_nonneg hhβ hpos'.le) (fun v hv hvp hwv hvin t ht hrest => by
      obtain rfl := huniq v hv hvp hwv hvin
      obtain ⟨d, hd, hrel⟩ := ell_of_sub_mem h hrest
      rw [le_div_iff₀ hpos']
      have : (0 : ℝ) ≤ ∑ j, d j * h (γ j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (by exact_mod_cast hh j)
      linarith)
  rw [evalR_toReal] at key
  calc (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β₀ * ((h β : ℝ) / h β₀) :=
        mul_le_mul_of_nonneg_left key hpos'.le
    _ = h β := by field_simp

end GlobalTheory.PolFan.StarOnCell

open GlobalTheory.PolFan.StarOnCell in

theorem GlobalTheory.PolFan.starDepth_on_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X,
    (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧
    (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β →
      ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧
        k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro E _ _ _ H q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := GlobalTheory.T.centreDepth_le_starDepth_of_cell (𝓞 E) H.bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth H.bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
    nlinarith
  ·
    intro β _ _ hβ heq
    have hβr : toReal β ∈ rcone γ := by obtain ⟨c, hc0, e⟩ := hβ; exact ⟨c, hc0, e⟩
    obtain ⟨m'', s'', h'', hf'', hpos'', t, ht, e⟩ :=
      GlobalTheory.StarCover.star_cover X m γ β₀ (toReal β) (fun i => (hγ.mem i).1) hγ.nonneg hne hin hβr
    have hpos''' : (0 : ℝ) < h'' β₀ := by exact_mod_cast hpos''

    have r2 := ell_of_eq h'' e
    rw [Fin.sum_univ_succ] at r2
    simp only [Fin.cons_zero, Fin.cons_succ] at r2
    have z2 : ∀ j, (h'' (γ (s'' j)) : ℝ) = 0 := fun j => by
      rw [(hf''.2 (s'' j)).2 ⟨j, rfl⟩, Int.cast_zero]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero] at r2
    have hle : (starDepth H.bar ψ w).evalZ β ≤ t 0 := by
      have := mul_starDepth_le hγ huniq h'' hf''.1 hpos'' hβ
      rw [r2] at this
      nlinarith

    have r1 := ell_of_eq h e
    rw [Fin.sum_univ_succ] at r1
    simp only [Fin.cons_zero, Fin.cons_succ] at r1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ t j.succ * (h (γ (s'' j)) : ℝ) := fun j _ =>
      mul_nonneg (ht _) (by exact_mod_cast hf.1 _)
    have hsum : ∑ j, t j.succ * (h (γ (s'' j)) : ℝ) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have hcone : InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) β := by
      refine inRCone_of_sum t ht e fun i hi => ?_
      refine Fin.cases (fun _ => ?_) (fun j hj => ?_) i hi
      · simpa using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) 0
      · have h0 : (h (γ (s'' j)) : ℝ) = 0 := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_left hj
        have h0' : h (γ (s'' j)) = 0 := by exact_mod_cast h0
        obtain ⟨k, hk⟩ := (hf.2 (s'' j)).1 h0'
        simpa [hk] using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k.succ
    exact exists_nat_of_inRCone _ β hcone
