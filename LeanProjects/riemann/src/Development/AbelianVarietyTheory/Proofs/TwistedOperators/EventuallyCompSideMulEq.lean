import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem om_smul_add (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by
  funext x
  simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eventually_comp_sideMul_eq {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by
  have hc : Continuous fun q : (GL a k × GL b k) × Matrix b a k => sideMul q.1.1 q.1.2 q.2 := by
    show Continuous fun q : (GL a k × GL b k) × Matrix b a k =>
      (q.1.2⁻¹ : GL b k).val * q.2 * q.1.1.val
    exact ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  have h1 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x ∈ tsupport Φ, Φ (sideMul gh.1 gh.2 x) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (GL a k × GL b k) × Matrix b a k =>
        (Φ (sideMul q.1.1 q.1.2 q.2), Φ q.2) :=
      (hΦ.1.comp_continuous hc).prodMk (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    congr 1
    show ((1 : GL b k)⁻¹ : GL b k).val * x * (1 : GL a k).val = x
    simp
  have h2 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1,
      ∀ x ∈ tsupport Φ, Φ (sideMul gh⁻¹.1 gh⁻¹.2 x) = Φ x := by
    have ht : Filter.Tendsto (fun gh : GL a k × GL b k => gh⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL a k × GL b k)).tendsto 1
    exact ht.eventually h1
  filter_upwards [h1, h2] with gh hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : sideMul gh.1 gh.2 x ∈ tsupport Φ
  · rw [← hs' _ hx']
    congr 1
    have := (sideMul gh.1 gh.2).left_inv x
    refine Eq.trans ?_ this
    show (gh.2⁻¹⁻¹ : GL b k).val * sideMul gh.1 gh.2 x * (gh.1⁻¹ : GL a k).val = _
    rw [inv_inv]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem isOpen_valuation_eq_one : IsOpen {x : kˣ | valuation k (x : k) = 1} := by
  have : {x : kˣ | valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩ (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  rw [this]
  exact ((isOpen_int k).preimage Units.continuous_val).inter
    ((isOpen_int k).preimage Units.continuous_coe_inv)

theorem eventually_det_trivial (n : Type*) [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) :
    ∀ᶠ g : GL n k in 𝓝 1, μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
      nabs k (Matrix.GeneralLinearGroup.det g) = 1 := by
  have hU := (hμ.inter isOpen_valuation_eq_one).preimage
    (Matrix.GeneralLinearGroup.continuous_det (n := n) (R := k))
  filter_upwards [hU.mem_nhds (x := 1) (by simp)] with g hg
  exact ⟨hg.1, nabs_eq_one_of_valuation_eq_one hg.2⟩

theorem isOpen_stabilizer_om {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) {Φ : Matrix b a k → ℂ}
    (hΦ : Φ ∈ SB (Matrix b a k)) : IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by
  let S : Subgroup (GL a k × GL b k) :=
    { carrier := {gh | om μ gh.1 gh.2 Φ = Φ}
      one_mem' := om_one μ Φ
      mul_mem' := fun {x y} hx hy => by
        show om μ (x.1 * y.1) (x.2 * y.2) Φ = Φ
        rw [om_mul, hy, hx]
      inv_mem' := fun {x} hx => by
        show om μ x.1⁻¹ x.2⁻¹ Φ = Φ
        conv_lhs => rw [← hx]
        rw [← om_mul, inv_mul_cancel, inv_mul_cancel, om_one] }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have h1 := (continuous_fst.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial a hμ)
  have h2 := (continuous_snd.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial b hμ)
  filter_upwards [h1, h2, eventually_comp_sideMul_eq hΦ] with gh hg hh hs
  show om μ gh.1 gh.2 Φ = Φ
  funext x
  have := hs x
  simp only [om, hg.1, hg.2, hh.1, hh.2, Real.one_rpow, inv_one, Units.val_one, Complex.ofReal_one,
    one_mul]
  exact this

end

theorem om_isSmoothRepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ hμ =>
    ⟨om_one μ, om_mul μ, om_smul_add μ, fun g h _ hΦ => om_mem_SB μ g h hΦ,
      fun _ hΦ => isOpen_stabilizer_om hμ hΦ⟩

end GlobalTheory.SplitWeil
