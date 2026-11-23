import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mono (χ : kˣ →* ℂˣ) (x y : k) (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y := fun u hu hle => hx u hu (hle.trans h)

theorem triv_add (χ : kˣ →* ℂˣ) (x y : k) (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  intro u hu hle
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact hy u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le h le_rfl)))
  · exact hx u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le le_rfl h)))

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ hle
  have : (u : k) - 1 = 0 := by simpa using hle
  have hu : u = 1 := Units.ext (by simpa [sub_eq_zero] using this)
  simp [hu]

theorem triv_neg (χ : kˣ →* ℂˣ) (x : k) (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono χ x (-x) (by rw [Valuation.map_neg]) hx

theorem triv_mul (χ η : kˣ →* ℂˣ) (x : k) (h1 : Triv χ x) (h2 : Triv η x) : Triv (χ * η) x := by
  intro u hu hle
  simp [h1 u hu hle, h2 u hu hle]

theorem triv_inv (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ x) : Triv χ⁻¹ x := by
  intro u hu hle
  simp [h u hu hle]

def trivSubgroup (χ : kˣ →* ℂˣ) : AddSubgroup k where
  carrier := {x | Triv χ x}
  add_mem' := fun {a b} ha hb => triv_add χ a b ha hb
  zero_mem' := triv_zero χ
  neg_mem' := fun {a} ha => triv_neg χ a ha

theorem triv_mem_nhds (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : {x : k | Triv χ x} ∈ nhds (0 : k) := by
  have hemb : Topology.IsEmbedding (Units.val : kˣ → k) := Units.isEmbedding_val₀
  obtain ⟨U, hUo, hU⟩ := hemb.isOpen_iff.mp hχ
  have h1 : (1 : k) ∈ U := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' U) := by rw [hU]; simp
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hUo.mem_nhds h1)
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  refine ⟨γ, fun x hx u _ hle => ?_⟩
  have hmem : (u : k) ∈ U := hγ (lt_of_le_of_lt hle hx)
  have : u ∈ (Units.val ⁻¹' U) := hmem
  rw [hU] at this
  simpa using this

theorem triv_isOpen_isClosed (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x} := by
  have ho : IsOpen ((trivSubgroup χ : AddSubgroup k) : Set k) :=
    AddSubgroup.isOpen_of_mem_nhds _ (triv_mem_nhds χ hχ)
  exact ⟨ho, AddSubgroup.isClosed_of_isOpen _ ho⟩

theorem ev_of_val (χ : kˣ →* ℂˣ) (x : k) (h : valuation k x = 1) :
    ev χ x = (χ (Units.mk0 x (fun h0 => by simp [h0] at h)) : ℂ) := by
  simp [ev, h]

theorem ev_mul (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by simp [hx, hy]
  rw [ev_of_val χ _ hxy, ev_of_val χ _ hx, ev_of_val χ _ hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext
  simp

theorem ev_congr (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h : Triv χ (x - y)) : ev χ x = ev χ y := by
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  set u : kˣ := Units.mk0 x hx0 / Units.mk0 y hy0 with hu
  have huv : (u : k) = x / y := by simp [hu]
  have hu1 : valuation k (u : k) = 1 := by rw [huv, map_div₀, hx, hy, div_one]
  have hsub : (u : k) - 1 = (x - y) / y := by rw [huv]; field_simp
  have hle : valuation k ((u : k) - 1) ≤ valuation k (x - y) := by
    rw [hsub, map_div₀, hy, div_one]
  have hχu : χ u = 1 := h u hu1 hle
  have hxe : Units.mk0 x hx0 = u * Units.mk0 y hy0 := by rw [hu]; simp
  rw [ev_of_val χ _ hx, ev_of_val χ _ hy, hxe, map_mul, hχu, one_mul]

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ 1) : ev χ x = 1 := by
  by_cases hx : valuation k x = 1
  · rw [ev_of_val χ _ hx]
    have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
    have hle : valuation k ((Units.mk0 x hx0 : k) - 1) ≤ valuation k (1 : k) := by
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> simp [hx]
    rw [h _ (by simpa using hx) hle]
    simp
  · simp [ev, hx]

end

theorem triv_ev_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  intro k _ _ _ _
  exact ⟨fun χ x y h hx => triv_mono χ x y h hx, fun χ x y => triv_add χ x y, triv_zero,
    fun χ η x => triv_mul χ η x, fun χ x => triv_inv χ x, fun χ hχ => triv_isOpen_isClosed χ hχ,
    fun χ x y => ev_mul χ x y, fun χ x y => ev_congr χ x y, fun χ x => ev_of_triv_one χ x⟩

end GlobalTheory.PsType
