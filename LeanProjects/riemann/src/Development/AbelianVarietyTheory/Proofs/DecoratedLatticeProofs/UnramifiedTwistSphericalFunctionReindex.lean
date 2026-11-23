import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_torusElt_eq {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]

theorem sum_indic {n : Type} [Fintype n] [DecidableEq n] (s : Finset n) : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic, Finset.sum_ite_mem]

theorem reGL_symm_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m k) : GlobalTheory.ChainStepSupp.reGL k e.symm (GlobalTheory.ChainStepSupp.reGL k e g) = g := by
  ext i j
  simp [GlobalTheory.ChainStepSupp.val_reGL]

theorem reGL_mem_KO_iff {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} : GlobalTheory.ChainStepSupp.reGL k e g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => reGL_symm_reGL e g ▸ GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm h, GlobalTheory.ChainStepSupp.reGL_mem_KO e⟩

theorem unram_det_KO {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ KO k n) : μ₀ (GeneralLinearGroup.det κ) = 1 :=
  hμ _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hκ))

theorem unram_det_dcoset {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ}
    {s : Finset n} {g : GL n k}
    (h : ∃ κ ∈ KO k n, ∃ κ' ∈ KO k n, g = κ * torusElt k n ϖ (indic s) * κ') :
    μ₀ (GeneralLinearGroup.det g) = μ₀ ϖ ^ s.card := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := h
  rw [map_mul, map_mul, map_mul, map_mul, unram_det_KO hμ hκ, unram_det_KO hμ hκ', det_torusElt_eq, sum_indic,
    map_zpow, one_mul, mul_one, zpow_natCast]

open Classical in

theorem isRepsK_image {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g₀ : GL m k} {R : Finset (GL m k)} (hR : IsRepsK g₀ R) :
    IsRepsK (GlobalTheory.ChainStepSupp.reGL k e g₀) (R.image (GlobalTheory.ChainStepSupp.reGL k e)) := by
  refine ⟨fun g' hg' => ?_, fun κ hκ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hR.1 g hg
    exact ⟨_, GlobalTheory.ChainStepSupp.reGL_mem_KO e ha, _, GlobalTheory.ChainStepSupp.reGL_mem_KO e hb, by simp only [map_mul]⟩
  · obtain ⟨g, ⟨hg, hgK⟩, huniq⟩ := hR.2 (GlobalTheory.ChainStepSupp.reGL k e.symm κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm hκ)
    have key : ∀ x : GL m k, (GlobalTheory.ChainStepSupp.reGL k e x)⁻¹ * (κ * GlobalTheory.ChainStepSupp.reGL k e g₀) =
        GlobalTheory.ChainStepSupp.reGL k e (x⁻¹ * (GlobalTheory.ChainStepSupp.reGL k e.symm κ * g₀)) := by
      intro x
      rw [map_mul, map_mul, map_inv, GlobalTheory.ChainStepSupp.reGL_reGL_symm]
    refine ⟨GlobalTheory.ChainStepSupp.reGL k e g, ⟨Finset.mem_image_of_mem _ hg, ?_⟩, ?_⟩
    · rw [key]; exact GlobalTheory.ChainStepSupp.reGL_mem_KO e hgK
    · rintro y ⟨hy, hyK⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      rw [key, reGL_mem_KO_iff] at hyK
      rw [huniq x ⟨hx, hyK⟩]

theorem twist_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  intro k _ _ _ _ D _ _ N ε ϖ hϖ μ₀ hμ β f hf hH f₂ hf₂
  classical
  refine ⟨fun κ hκ m => ?_, fun s R hR m => ?_⟩
  · have hk1 := unram_det_KO hμ hκ
    have hρ := hf (GlobalTheory.ChainStepSupp.reGL k ε κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO ε hκ) (GlobalTheory.ChainStepSupp.reGL k ε m)
    simp only [hf₂, map_mul, hk1, one_mul, mul_one, hρ.1, hρ.2, and_self]
  · set ρ := GlobalTheory.ChainStepSupp.reGL k ε with hρdef
    set s' := s.map ε.toEmbedding with hs'
    have ht : ρ (torusElt k (Fin N) ϖ (indic s)) = torusElt k D ϖ (indic s') := by
      rw [hρdef, GlobalTheory.ChainStepSupp.reGL_torusElt]
      congr 1
      funext d
      simp [indic, hs', Finset.mem_map_equiv]
    have hR' : IsRepsK (torusElt k D ϖ (indic s')) (R.image ρ) := ht ▸ isRepsK_image ε hR
    have hcard : Fintype.card D = N := (Fintype.card_congr ε).symm.trans (Fintype.card_fin N)
    have hH' := hH s' _ hR' (ρ m)
    rw [Finset.sum_image (fun x _ y _ h => ρ.injective h), hs', Finset.card_map, hcard] at hH'
    have hterm : ∀ g ∈ R, f₂ (m * g) = ((((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
        (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card) * f (ρ m * ρ g) := by
      intro g hg
      rw [hf₂, map_mul, map_mul, map_mul, unram_det_dcoset hμ (hR.1 g hg), mul_inv, Units.val_mul, ← inv_pow,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hH', hf₂]
    ring

end GlobalTheory.TwistRenumber

end
