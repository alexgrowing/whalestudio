import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeSeriesCellHasSumStatement
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.DoublingLength

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem int_mul_of_mem_KO {g x : GL (Fin n) k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hx : x ∈ KO k (Fin n)) :
    ∀ i j, (g * x).1 i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hg i l) (((SplitFlip.mem_KO_iff x).1 hx).1 l j)

theorem ord_det_of_mem_KO {x : GL (Fin n) k} (hx : x ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det x) = 0 := by
  obtain ⟨g, rfl⟩ := hx
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

variable (k n) in

def pairEquiv : ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) ≃
    ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) where
  toFun p := (p.2, (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)))
  invFun p := ((QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)), p.1)
  left_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.2.out⁻¹ * p.1.out)
    refine Prod.ext ?_ rfl
    show (QuotientGroup.mk (p.2.out * (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.1
    rw [hx, mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']
  right_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.1.out * p.2.out)
    refine Prod.ext rfl ?_
    show (QuotientGroup.mk (p.1.out⁻¹ * (QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.2
    rw [hx, mul_assoc, inv_mul_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']

theorem pairEquiv_apply (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) :
    pairEquiv k n p = (p.2, (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n))) := rfl

open scoped Classical in

def pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) : ℂ :=
  if (∀ i j, (p.1.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (p.2.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
    X ^ ((-ord k (Matrix.GeneralLinearGroup.det p.1.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det p.2.out)).toNat) * φ (p.1.out * p.2.out)
  else 0

theorem hasSum_of_subtype {β : Type} {P : β → Prop} (f : β → ℂ) {g : β → ℂ} {a b : ℂ} (c : ℂ)
    (h : HasSum (fun x : {x // P x} => f x.1) a) (h1 : ∀ x, P x → g x = f x * c) (h0 : ∀ x, ¬ P x → g x = 0)
    (hb : b = a * c) : HasSum g b := by
  have h2 : HasSum (fun x => Set.indicator {x | P x} f x * c) (a * c) :=
    ((hasSum_subtype_iff_indicator (s := {x | P x}) (f := f)).1 h).mul_right c
  have h3 : g = fun x => Set.indicator {x | P x} f x * c := funext fun x => by
    by_cases hx : P x
    · rw [h1 x hx, Set.indicator_of_mem (by exact hx)]
    · rw [h0 x hx, Set.indicator_of_notMem (by exact hx), zero_mul]
  rw [h3, hb]
  exact h2

open scoped Classical in

theorem hasSum_pairTerm_fiber {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (h : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun c => pairTerm X φ (h, c))
      (if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out *
          ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹ else 0) := by
  by_cases hA : ∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]
  · rw [if_pos hA]
    refine hasSum_of_subtype (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])
      (fun c => X ^ (ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ (h.out * c.out))
      (X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat)
      (GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction k n γ φ hφ hγ X hX h.out) (fun c hB => ?_) (fun c hB => ?_) (by ring)
    · rw [pairTerm, if_pos ⟨hA, hB⟩]
      ring
    · rw [pairTerm, if_neg fun H => hB H.2]
  · rw [if_neg hA]
    have : (fun c => pairTerm X φ (h, c)) = fun _ => 0 := funext fun c => by
      rw [pairTerm, if_neg fun H => hA H.1]
    rw [this]
    exact hasSum_zero

open scoped Classical in

theorem hasSum_pairTerm_total {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) (a : ℂ) :
    HasSum (fun h : GL (Fin n) k ⧸ KO k (Fin n) =>
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out * a else 0)
      (a * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  exact hasSum_of_subtype
    (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])
    (fun c => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ c.out) a
    (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n γ φ hφ hγ X hX) (fun c hB => if_pos hB) (fun c hB => if_neg hB) (mul_comm _ _)

theorem norm_pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) :
    ((‖pairTerm X φ p‖ : ℝ) : ℂ) = pairTerm (‖X‖ : ℂ) (fun g => (‖φ g‖ : ℂ)) p := by
  unfold pairTerm
  split_ifs
  · rw [norm_mul, norm_pow, Complex.ofReal_mul, Complex.ofReal_pow]
  · simp

theorem isBorelSph_norm {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ) :
    IsBorelSph k (fun i => (‖γ i‖ : ℂ)) (fun g => (‖φ g‖ : ℂ)) := by
  refine ⟨fun g x hx => by simp only [h.1 g x hx], fun b hb t ht => ?_⟩
  simp only [h.2 b hb t ht, norm_prod, norm_zpow, Complex.ofReal_prod, Complex.ofReal_zpow]

theorem summable_pairTerm {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) : Summable (pairTerm X φ) := by
  have hψ := isBorelSph_norm hφ
  have hγ' : ∀ i, (‖γ i‖ : ℂ) ≠ 0 := fun i => by simpa using hγ i
  have hX1' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX1 i
  have hX2' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * ((‖γ i‖ : ℂ))⁻¹ * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX2 i
  refine Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun h => ?_, ?_⟩)
  · have := (hasSum_pairTerm_fiber hψ hγ' hX1' h).summable
    simp_rw [← norm_pairTerm] at this
    exact Complex.summable_ofReal.1 this
  · refine Complex.summable_ofReal.1 ((hasSum_pairTerm_total hψ hγ' hX2'
      (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ))⁻¹)).summable.congr
        fun h => ?_)
    rw [Complex.ofReal_tsum]
    simp_rw [norm_pairTerm]
    exact (hasSum_pairTerm_fiber hψ hγ' hX1' h).tsum_eq.symm

open scoped Classical in

theorem pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (X : ℂ)
    (g h : GL (Fin n) k ⧸ KO k (Fin n)) :
    pairTerm X φ (pairEquiv k n (g, h)) =
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
          (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
          (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat) * φ g.out
      else 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (h.out⁻¹ * g.out)
  have hiff : (∀ i j, (h.out⁻¹ * g.out * x : GL (Fin n) k).1 i j ∈ 𝒪[k]) ↔
      ∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k] :=
    ⟨fun H => by
      have := int_mul_of_mem_KO H (inv_mem x.2)
      rwa [mul_inv_cancel_right] at this, fun H => int_mul_of_mem_KO H x.2⟩
  have hord : ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out * x : GL (Fin n) k)) =
      ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out)) := by
    rw [map_mul, ord_mul, ord_det_of_mem_KO x.2, add_zero]
  have hval : φ (h.out * (h.out⁻¹ * g.out * x)) = φ g.out := by
    rw [mul_assoc, mul_inv_cancel_left, hφ.1 _ _ x.2]
  rw [pairEquiv_apply, pairTerm]
  dsimp only
  rw [hx, hord, hval]
  exact if_congr (and_congr Iff.rfl hiff) rfl rfl

theorem hasSum_pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {len : GL (Fin n) k → ℕ}
    (hlen : ∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) (g : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun h => pairTerm X φ (pairEquiv k n (g, h)))
      (X ^ len g.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ g.out) := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 (show g.out ∈ ⋃ e : {e : Fin n → ℤ // Antitone e}, cell k (Fin n) ϖ e by
    rw [iUnion_cell hϖ]; trivial)
  rw [hlen e.1 e.2 g.out he]
  refine hasSum_of_subtype
    (P := fun h : GL (Fin n) k ⧸ KO k (Fin n) => (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
      (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]))
    (fun h => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat)) (φ g.out)
    (GlobalTheory.T.hecke_series_cell_has_sum k n ϖ hϖ e.1 g.out he X hX) (fun h hB => ?_) (fun h hB => ?_) rfl
  · rw [pairTerm_pairEquiv hφ, if_pos hB]
  · rw [pairTerm_pairEquiv hφ, if_neg hB]

theorem exists_small (q : ℝ) (hq0 : 0 ≤ q) (γ : Fin n → ℂ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → ∀ i : Fin n,
    q ^ (n - 1 - (i : ℕ)) * ‖γ i‖ * x < 1 ∧ q ^ (i : ℕ) * ‖γ i‖⁻¹ * x < 1 ∧ q ^ (i : ℕ) * x ^ 2 < 1 := by
  obtain ⟨S, hS, hS0⟩ : ∃ S : ℝ, (∀ i, ‖γ i‖ + ‖γ i‖⁻¹ ≤ S) ∧ 0 ≤ S :=
    ⟨∑ i, (‖γ i‖ + ‖γ i‖⁻¹), fun i => Finset.single_le_sum (f := fun i => ‖γ i‖ + ‖γ i‖⁻¹)
      (fun j _ => by positivity) (Finset.mem_univ i), Finset.sum_nonneg fun j _ => by positivity⟩
  have hq1 : 1 ≤ q + 1 := by linarith
  have hM1 : 1 ≤ (q + 1) ^ n * (1 + S) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) (by linarith)
  have hM0 : 0 < (q + 1) ^ n * (1 + S) := by linarith
  have hpow : ∀ m ≤ n, q ^ m ≤ (q + 1) ^ n := fun m hm =>
    (pow_le_pow_left₀ hq0 (by linarith) m).trans (pow_le_pow_right₀ hq1 hm)
  have key : ∀ m ≤ n, ∀ c : ℝ, 0 ≤ c → c ≤ 1 + S → ∀ x : ℝ, 0 ≤ x → x < ((q + 1) ^ n * (1 + S))⁻¹ →
      q ^ m * c * x < 1 := by
    intro m hm c hc0 hc x hx0 hx
    have h1 : q ^ m * c ≤ (q + 1) ^ n * (1 + S) := mul_le_mul (hpow m hm) hc hc0 (by positivity)
    calc q ^ m * c * x ≤ (q + 1) ^ n * (1 + S) * x := mul_le_mul_of_nonneg_right h1 hx0
      _ < (q + 1) ^ n * (1 + S) * ((q + 1) ^ n * (1 + S))⁻¹ := mul_lt_mul_of_pos_left hx hM0
      _ = 1 := mul_inv_cancel₀ hM0.ne'
  refine ⟨_, inv_pos.2 hM0, fun x hx0 hx i => ⟨?_, ?_, ?_⟩⟩
  · exact key _ (by omega) _ (norm_nonneg _) (by linarith [hS i, inv_nonneg.2 (norm_nonneg (γ i))]) x hx0 hx
  · exact key _ i.2.le _ (by positivity) (by linarith [hS i, norm_nonneg (γ i)]) x hx0 hx
  · have hx1 : x ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ hM1)
    rw [sq, ← mul_assoc]
    exact key _ i.2.le _ hx0 (by linarith) x hx0 hx

theorem hasSum_doublingLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  intro k _ _ _ _ n γ φ hφ hγ ϖ hϖ len hlen
  obtain ⟨δ, hδ, hsm⟩ := exists_small (resCard k : ℝ) (Nat.cast_nonneg _) γ
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).1
  have hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.1
  have hX3 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.2
  have hsum := (summable_pairTerm hφ hγ hX1 hX2).hasSum
  rw [(hsum.prod_fiberwise (hasSum_pairTerm_fiber hφ hγ hX1)).unique (hasSum_pairTerm_total hφ hγ hX2 _)] at hsum
  have hmain := ((pairEquiv k n).hasSum_iff.2 hsum).prod_fiberwise (hasSum_pairTerm_pairEquiv hφ hϖ hlen hX3)
  have hR : ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ H => by
      have := hX3 i
      rw [← sub_eq_zero.1 H, norm_one] at this
      exact lt_irrefl _ this
  have hfun : (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) = fun c =>
      X ^ len c.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ c.out *
        ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) := funext fun c => by
    rw [Finset.prod_inv_distrib, mul_right_comm _ _ (φ c.out), inv_mul_cancel_right₀ hR]
  rw [hfun]
  exact hmain.mul_right _

end GlobalTheory.DoublingLength
