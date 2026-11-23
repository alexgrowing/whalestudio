import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarDen

section Cone

variable {X : Type} [AddCommGroup X] {m m' : ℕ}

theorem rcone_add {γ : Fin m → LinearMap.BilinForm ℤ X} {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone γ)
    (h' : B' ∈ rcone γ) : B + B' ∈ rcone γ := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨t', ht', rfl⟩ := h'
  exact ⟨t + t', fun i => add_nonneg (ht i) (ht' i), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem rcone_smul {γ : Fin m → LinearMap.BilinForm ℤ X} {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone γ) {a : ℝ}
    (ha : 0 ≤ a) : a • B ∈ rcone γ := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨a • t, fun i => mul_nonneg ha (ht i), by simp [Finset.smul_sum, smul_smul]⟩

theorem rcone_zero (γ : Fin m → LinearMap.BilinForm ℤ X) : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ rcone γ :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem rcone_gen (γ : Fin m → LinearMap.BilinForm ℤ X) (j : Fin m) : toReal (γ j) ∈ rcone γ := by
  obtain ⟨c, hc, e⟩ := inRCone_self γ j
  exact ⟨c, hc, e⟩

theorem rcone_sum {γ : Fin m → LinearMap.BilinForm ℤ X} {ι : Type} (S : Finset ι) (f : ι → X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hf : ∀ i ∈ S, f i ∈ rcone γ) : ∑ i ∈ S, f i ∈ rcone γ :=
  Finset.sum_induction _ (· ∈ rcone γ) (fun _ _ => rcone_add) (rcone_zero γ) hf

theorem rcone_mono {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (h : ∀ i, ∃ j, γ i = γ' j) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ rcone γ) : B ∈ rcone γ' := by
  obtain ⟨t, ht, rfl⟩ := hB
  refine rcone_sum _ _ fun i _ => ?_
  obtain ⟨j, hj⟩ := h i
  rw [hj]
  exact rcone_smul (rcone_gen γ' j) (ht i)

theorem lin_cons (u : LinearMap.BilinForm ℤ X) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (β : LinearMap.BilinForm ℤ X) (a : ℝ) (c : Fin m → ℝ)
    (h : toReal β = a • toReal u + ∑ i, c i • toReal (γ i)) : (ℓ β : ℝ) = a * ℓ u + ∑ i, c i * ℓ (γ i) := by
  have h1 : ∑ i : Fin (m + 2), (Fin.cons (-1) (Fin.cons a c) : Fin (m + 2) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β (Fin.cons u γ) : Fin (m + 2) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, h]
    simp only [neg_smul, one_smul]
    abel
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  linarith

end Cone

section Depth

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ}

theorem depth_eq_of_star {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ)
    {v : LinearMap.BilinForm ℤ X} (hvb : v ∈ balForms bar X) (hvp : ∀ y, 0 ≤ v y y) (hvw : w.evalZ v = 1)
    (hvc : InRCone γ v) (hv0 : v ≠ 0)
    (huniq : ∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v)
    {m' : ℕ} {s : Fin m' ↪ Fin m} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hF : IsFaceCut γ s h) (hhv : 0 < h v)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β ∈ rcone (Fin.cons v fun j => γ (s j))) :
    (h v : ℝ) * (starDepth bar ψ w).evalZ β = h β := by
  obtain ⟨t, ht, hβt⟩ := hβ
  rw [Fin.sum_univ_succ] at hβt
  simp only [Fin.cons_zero, Fin.cons_succ] at hβt
  have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hF.2 (s j)).2 ⟨j, rfl⟩
  have hhβ : (h β : ℝ) = t 0 * h v := by
    rw [lin_cons v (fun j => γ (s j)) h β (t 0) (fun j => t j.succ) hβt]
    simp [hs0]
  have hvR : (0 : ℝ) < h v := by exact_mod_cast hhv
  have hface : ∑ j, t j.succ • toReal (γ (s j)) ∈ rcone γ :=
    rcone_sum _ _ fun j _ => rcone_smul (rcone_gen γ (s j)) (ht j.succ)
  have hvR' : toReal v ∈ rcone γ := by
    obtain ⟨c, hc, e⟩ := hvc
    exact ⟨c, hc, e⟩
  have hBγ : toReal β ∈ rcone γ := by
    rw [hβt]; exact rcone_add (rcone_smul hvR' (ht 0)) hface
  have hlow : t 0 ≤ evalR (starDepth bar ψ w) (toReal β) :=
    GlobalTheory.T.centreDepth_le_starDepth_of_cell O bar ψ w X m γ (toReal β) v (t 0) hγ hBγ hvb hvp hvw hvc hv0 huniq (ht 0)
      (by rw [hβt, add_sub_cancel_left]; exact hface)
  have hup : evalR (starDepth bar ψ w) (toReal β) ≤ t 0 := by
    refine GlobalTheory.PolFan.evalR_starDepth_le O bar ψ w X m γ (toReal β) (t 0) hγ hBγ (ht 0) ?_
    intro v' hb hp hw1 hc t' ht' hmem
    obtain rfl := huniq v' hb hp hw1 hc
    obtain ⟨e, he, hee⟩ := hmem
    have h1 := lin_cons v' γ h β t' e (by rw [← hee]; abel)
    have h2 : 0 ≤ ∑ i, e i * (h (γ i) : ℝ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (he i) (by exact_mod_cast hF.1 i)
    rw [hhβ] at h1
    nlinarith
  rw [evalR_toReal] at hlow hup
  rw [hhβ, le_antisymm hup hlow]
  ring

end Depth

section Den

theorem common_den {ι : Type} [Finite ι] (A : ι → Set ℝ)
    (h : ∀ i, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A i, ∃ n : ℤ, (D : ℝ) * x = n) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∀ x ∈ A i, ∃ n : ℤ, (D : ℝ) * x = n := by
  classical
  choose D hD hA using h
  haveI := Fintype.ofFinite ι
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i x hx => ?_⟩
  obtain ⟨n, hn⟩ := hA i x hx
  refine ⟨(∏ j ∈ Finset.univ.erase i, D j : ℕ) * n, ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)]
  push_cast
  rw [← hn]
  ring

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem cell_den {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ)
    (hw : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1)
    (hu : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
      w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β') :
    ∃ D : ℕ, 0 < D ∧ ∀ β : LinearMap.BilinForm ℤ X, toReal β ∈ rcone γ →
      ∃ n : ℤ, (D : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  classical
  by_cases hc : ∃ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hvb, hvp, hvw, hvc⟩ := hc
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact absurd (hw 0 hvb hvp hvw 0 0 (by simp)) (by norm_num)
    have huniq : ∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v :=
      fun v' hb hp hw1 hc' => hu v' hb hp v hvb hvp hw1 hvw hc' hvc
    let A : Set (Fin m) → Set ℝ := fun Z => {x | ∃ β : LinearMap.BilinForm ℤ X, x = (starDepth bar ψ w).evalZ β ∧
      ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), Set.range s = Z ∧ IsFaceCut γ s h ∧
        0 < h v ∧ toReal β ∈ rcone (Fin.cons v fun j => γ (s j))}
    have hA : ∀ Z, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A Z, ∃ n : ℤ, (D : ℝ) * x = n := by
      intro Z
      by_cases hne : ∃ x, x ∈ A Z
      · obtain ⟨-, β₀, -, m₀, s₀, h₀, hs₀, hF₀, hh₀, -⟩ := hne
        refine ⟨(h₀ v).toNat, by omega, ?_⟩
        rintro x ⟨β, rfl, m', s, h, hs, hF, hh, hβ⟩
        have hF' : IsFaceCut γ s h₀ := ⟨hF₀.1, fun j => by rw [hF₀.2 j, hs₀, hs]⟩
        have key := depth_eq_of_star hγ hvb hvp hvw hvc hv0 huniq hF' hh₀ hβ
        refine ⟨h₀ β, ?_⟩
        have e : (((h₀ v).toNat : ℤ) : ℝ) = (h₀ v : ℝ) := by rw [Int.toNat_of_nonneg hh₀.le]
        rw [← key, ← e]
        norm_cast
      · push_neg at hne
        exact ⟨1, one_pos, fun x hx => (hne x hx).elim⟩
    obtain ⟨D, hD, hall⟩ := common_den A hA
    refine ⟨D, hD, fun β hβ => ?_⟩
    obtain ⟨m', s, h, hF, hh, hβ'⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i y z => (hγ.mem i).1 y z)
      hγ.nonneg hv0 hvc hβ
    exact hall (Set.range s) _ ⟨β, rfl, m', s, h, rfl, hF, hh, hβ'⟩
  · push_neg at hc
    refine ⟨1, one_pos, fun β hβ => ⟨0, ?_⟩⟩
    have hup := GlobalTheory.PolFan.evalR_starDepth_le O bar ψ w X m γ (toReal β) 0 hγ hβ le_rfl
      fun v hb hp hw1 hc' => absurd hc' (hc v hb hp hw1)
    rw [evalR_toReal] at hup
    have h0 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    rw [le_antisymm hup h0]
    simp

end Den

section Module

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem module_den (hX : IsPolyFanOn bar ψ X)
    (hw : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1)
    (hu : ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β') :
    ∃ D : ℕ, 0 < D ∧ ∀ β : LinearMap.BilinForm ℤ X, toReal β ∈ psdCone bar X →
      ∃ n : ℤ, (D : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  haveI : Finite {T : Set (LinearMap.BilinForm ℤ X) | T ⊆ S} := hS.finite_subsets.to_subtype
  let A : {T : Set (LinearMap.BilinForm ℤ X) | T ⊆ S} → Set ℝ := fun T =>
    {x | ∃ β : LinearMap.BilinForm ℤ X, x = (starDepth bar ψ w).evalZ β ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell bar ψ γ ∧ Set.range γ = T.1 ∧ toReal β ∈ rcone γ}
  have hA : ∀ T, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A T, ∃ n : ℤ, (D : ℝ) * x = n := by
    intro T
    by_cases hne : ∃ x, x ∈ A T
    · obtain ⟨-, -, -, m₀, γ₀, hγ₀, hr₀, -⟩ := hne
      obtain ⟨D, hD, hden⟩ := cell_den hγ₀ hw (hu m₀ γ₀ hγ₀)
      refine ⟨D, hD, ?_⟩
      rintro x ⟨β, rfl, m, γ, -, hr, hβ⟩
      refine hden β (rcone_mono (fun i => ?_) hβ)
      have : γ i ∈ Set.range γ₀ := by rw [hr₀, ← hr]; exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    · push_neg at hne
      exact ⟨1, one_pos, fun x hx => (hne x hx).elim⟩
  obtain ⟨D, hD, hall⟩ := common_den A hA
  refine ⟨D, hD, fun β hβ => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hβ
  have hpull : toReal (pull e.toLinearMap β) = ∑ i, c i • toReal (γ i) := by
    rw [← hsum]
    exact LinearMap.ext₂ fun a b => by simp
  have hval : (starDepth bar ψ w).evalZ (pull e.toLinearMap β) = (starDepth bar ψ w).evalZ β :=
    evalZ_pull _ e.surjective β
  rw [← hval]
  exact hall ⟨Set.range γ, by rintro _ ⟨i, rfl⟩; exact hγS i⟩ _
    ⟨pull e.toLinearMap β, rfl, m, γ, hγ, rfl, c, hc, hpull⟩

end Module

theorem starDepth_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)),
    IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X,
        (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = n := by
  intro E _ _ _ H q ψ w hψ hw
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key : ∀ k : Fin n, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ {x : ℝ | ∃ β ∈ balForms H.bar (R k), (∀ y, 0 ≤ β y y) ∧
      haveI := (hR k).1; x = (starDepth H.bar ψ w).evalZ β}, ∃ z : ℤ, (D : ℝ) * x = z := fun k => by
    haveI := (hR k).1
    haveI := (hR k).2.1
    obtain ⟨-, h2, h3⟩ := hw (R k) (hR k).2.2
    obtain ⟨D, hD, hA⟩ := module_den (hψ (R k) (hR k).2.2) h2 h3
    refine ⟨D, hD, ?_⟩
    rintro x ⟨β, hβ, hp, rfl⟩
    exact hA β (toReal_mem_psdCone_of_nonneg E H (R k) β hβ hp)
  obtain ⟨D₀, hD₀, hall⟩ := common_den _ key
  refine ⟨D₀, hD₀, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  haveI := (hR k).1
  have hval : (starDepth H.bar ψ w).evalZ (pull f.symm.toLinearMap β) = (starDepth H.bar ψ w).evalZ β :=
    evalZ_pull _ f.symm.surjective β
  rw [← hval]
  exact hall k _ ⟨_, pull_mem _ hβ, fun y => hp _, rfl⟩

example (n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) : (starDepth id (InvFun.minVal ℤ) (zeroFun ℤ)).toFun n B = 0 :=
  starDepth_zeroFun n B

end GlobalTheory.PolFan.StarDen
