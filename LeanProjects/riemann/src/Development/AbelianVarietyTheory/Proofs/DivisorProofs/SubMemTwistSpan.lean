import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def twistSpan (ν β : kˣ →* ℂˣ) : Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL A k) (Ψ : Matrix A D k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧
    z = omA ν β g 1 Ψ - Ψ}

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

theorem omA_one_apply (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) (X : Matrix A D k) :
    omA ν β g 1 Φ X = (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
      Φ ((g⁻¹).val * X) := by
  simp [omA, invT_val]

theorem sub_mem_twistSpan (ν β : kˣ →* ℂˣ) (g : GL A k) {Ψ : Matrix A D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k)) : omA ν β g 1 Ψ - Ψ ∈ twistSpan ν β :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

def boxFn (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Matrix A D k → ℂ := (box ϖ C e).indicator 1

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_preimage (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ e i)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [box, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ e i : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_image (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ e i : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [box_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY

omit [DecidableEq A] [DecidableEq D] in

theorem isCompact_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsCompact (box ϖ C e) := by
  rw [box_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)

omit [DecidableEq A] [DecidableEq D] in

theorem isClopen_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsClopen (box ϖ C e) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_box ϖ C e).isClosed, ?_⟩
  rw [box_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)

omit [DecidableEq A] [DecidableEq D] in

theorem boxFn_mem_SB (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    boxFn ϖ C e ∈ GlobalTheory.WeilM.SB (Matrix A D k) :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_box ϖ C e)).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box ϖ C e) fun _ hx => Set.indicator_of_notMem hx _⟩

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) : box ϖ X e = box ϖ C e := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem boxFn_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) :
    boxFn ϖ X e = boxFn ϖ C e := by
  rw [boxFn, boxFn, box_eq_of_mem hX]

end GlobalTheory.RankCoinv
