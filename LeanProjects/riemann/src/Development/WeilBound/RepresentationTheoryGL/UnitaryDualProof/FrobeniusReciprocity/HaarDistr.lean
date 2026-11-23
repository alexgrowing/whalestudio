import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import GroundTheory.AutomorphicForms.LocallyConstantCompact
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.PowNear

noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise

namespace PositivityTheory.RgUd.T2.HaarDistr

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_openSubgroup_char_eq_one (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, (χ k : ℂ) = 1 := by
  have hU : IsOpen {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have h1 : (1 : G) ∈ {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} := by simp
  obtain ⟨K, -, hKU⟩ := exists_openSubgroup_isCompact_subset (hU.mem_nhds h1)
  refine ⟨K, fun k hk => PositivityTheory.RgUd.T2.eq_one_of_pow_near fun n => ?_⟩
  have h2 : k ^ n ∈ K := pow_mem hk n
  have h3 := hKU h2
  simp only [Set.mem_setOf_eq, map_pow, Units.val_pow_eq_pow_val] at h3
  exact h3.le

theorem isLocallyConstant_char (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  obtain ⟨K, hK⟩ := exists_openSubgroup_char_eq_one χ hχ
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
  refine ⟨g • (K : Set G), K.isOpen.smul g, Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩, ?_⟩
  rintro _ hy
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  simp [hK k hk]

def mulLC (ψ : G → ℂ) (hψ : IsLocallyConstant ψ) : SB G →ₗ[ℂ] SB G where
  toFun α := ⟨fun x => ψ x * (α : G → ℂ) x,
    hψ.comp₂ α.2.1 (· * ·), HasCompactSupport.mul_left α.2.2⟩
  map_add' α β := by
    apply Subtype.ext; funext x
    show ψ x * ((α : G → ℂ) x + (β : G → ℂ) x) = ψ x * (α : G → ℂ) x + ψ x * (β : G → ℂ) x
    ring
  map_smul' c α := by
    apply Subtype.ext; funext x
    show ψ x * (c * (α : G → ℂ) x) = c * (ψ x * (α : G → ℂ) x)
    ring

@[simp]
theorem mulLC_apply (ψ : G → ℂ) (hψ : IsLocallyConstant ψ) (α : SB G) (x : G) :
    ((mulLC ψ hψ α : SB G) : G → ℂ) x = ψ x * (α : G → ℂ) x :=
  rfl

def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨(K : Set G).indicator (fun _ => (1 : ℂ)),
    indicator_mem_locallyConstantCompactSupport (R := ℂ) hK K.isOpen 1⟩

theorem exists_sum_eq (K : OpenSubgroup G) (hKc : IsCompact (K : Set G)) (f : SB G)
    (hK : ∀ g, ∀ k ∈ K, (f : G → ℂ) (g * k) = (f : G → ℂ) g) :
    ∃ s : ℂ, ∀ Φ : SB G →ₗ[ℂ] ℂ, (∀ (g : G) (α : SB G), Φ (transl g α) = Φ α) →
      Φ f = s * Φ (ind K hKc) := by
  classical
  have hf : HasCompactSupport (f : G → ℂ) := f.2.2
  set t := (finite_image_mk_tsupport K hf).toFinset with ht
  have key : f = ∑ x ∈ t, ((f : G → ℂ) x.out) • transl x.out (ind K hKc) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    refine (eq_sum_indicator_coset K hf hK).trans (Finset.sum_congr rfl fun x _ => ?_)
    funext y
    show (x.out • (K : Set G)).indicator (fun _ => (f : G → ℂ) x.out) y =
      (f : G → ℂ) x.out * (K : Set G).indicator (fun _ => (1 : ℂ)) (x.out⁻¹ • y)
    by_cases hy : y ∈ x.out • (K : Set G)
    · have hy' : x.out⁻¹ • y ∈ (K : Set G) := Set.mem_smul_set_iff_inv_smul_mem.1 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy', mul_one]
    · have hy' : x.out⁻¹ • y ∉ (K : Set G) := fun h => hy (Set.mem_smul_set_iff_inv_smul_mem.2 h)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero]
  refine ⟨∑ x ∈ t, (f : G → ℂ) x.out, fun Φ hΦ => ?_⟩
  conv_lhs => rw [key]
  rw [_root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, hΦ, smul_eq_mul]

theorem exists_eq_const_mul (Φ Ψ : SB G →ₗ[ℂ] ℂ)
    (hΦ : ∀ (g : G) (α : SB G), Φ (transl g α) = Φ α)
    (hΨ : ∀ (g : G) (α : SB G), Ψ (transl g α) = Ψ α)
    (h0 : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), Ψ (ind K hK) ≠ 0) :
    ∃ c : ℂ, ∀ α : SB G, Φ α = c * Ψ α := by
  obtain ⟨K₀, hK₀, -⟩ := exists_openSubgroup_isCompact_subset (G := G) (Filter.univ_mem)
  refine ⟨Φ (ind K₀ hK₀) / Ψ (ind K₀ hK₀), fun α => ?_⟩
  obtain ⟨K₁, -, hK₁⟩ := exists_forall_mul_right (R := ℂ) (show (α : G → ℂ) ∈
    locallyConstantCompactSupport G ℂ ℂ from α.2)
  have hKc : IsCompact ((K₁ ⊓ K₀ : OpenSubgroup G) : Set G) :=
    hK₀.of_isClosed_subset (K₁ ⊓ K₀).isClosed fun x hx => (OpenSubgroup.mem_inf.1 hx).2
  obtain ⟨s, hs⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc α
    (fun g k hk => hK₁ g k (OpenSubgroup.mem_inf.1 hk).1)
  obtain ⟨r, hr⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc (ind K₀ hK₀) (fun g k hk => by
    have hk' : k ∈ K₀ := (OpenSubgroup.mem_inf.1 hk).2
    change (K₀ : Set G).indicator (fun _ => (1 : ℂ)) (g * k) =
      (K₀ : Set G).indicator (fun _ => (1 : ℂ)) g
    by_cases hg : g ∈ (K₀ : Set G)
    · have : g * k ∈ (K₀ : Set G) := K₀.mul_mem hg hk'
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
    · have : g * k ∉ (K₀ : Set G) := fun h => hg (by
        simpa using K₀.mul_mem h (K₀.inv_mem hk'))
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem this])
  have a1 := hs Φ hΦ
  have a2 := hs Ψ hΨ
  have b1 := hr Φ hΦ
  have b2 := hr Ψ hΨ
  have hne := h0 _ hK₀
  have hne' := h0 _ hKc
  have hrne : r ≠ 0 := by
    rintro rfl
    exact hne (by simpa using b2)
  rw [a1, a2, b1, b2]
  field_simp

variable [MeasurableSpace G] [BorelSpace G]

def intLC (μ : Measure G) [μ.IsHaarMeasure] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (α.2.1.continuous.integrable_of_hasCompactSupport α.2.2)
    (β.2.1.continuous.integrable_of_hasCompactSupport β.2.2)
  map_smul' c α := integral_const_mul c _

theorem intLC_apply (μ : Measure G) [μ.IsHaarMeasure] (α : SB G) :
    intLC μ α = ∫ x, (α : G → ℂ) x ∂μ :=
  rfl

theorem intLC_transl (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    intLC μ (transl g α) = intLC μ α :=
  integral_mul_left_eq_self (fun x => (α : G → ℂ) x) g⁻¹

theorem intLC_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : intLC μ (ind K hK) ≠ 0 := by
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hpos : 0 < μ (K : Set G) := K.isOpen.measure_pos μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ⊤ := hK.measure_lt_top.ne
  show ∫ x, (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ ≠ 0
  rw [integral_indicator_const _ hm]
  simp only [measureReal_def, Complex.real_smul, mul_one, ne_eq, Complex.ofReal_eq_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin).ne'

end Group

theorem eq_const_mul_integral_char :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
      Continuous (fun g => (χ g : ℂ)) → ∀ L : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), L (transl g α) = (χ g : ℂ) * L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ := by
  intro G _ _ _ _ _ _ _ _ _ μ _ χ hχ L hL
  have hc : IsLocallyConstant (fun g => (χ g : ℂ)) := isLocallyConstant_char χ hχ
  have hci : IsLocallyConstant (fun g => ((χ g)⁻¹ : ℂˣ).val) := by
    have hχ' : Continuous (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) := by
      have : (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) = fun g => (χ g : ℂ)⁻¹ := by
        funext g; simp
      rw [this]
      exact hχ.inv₀ fun g => (χ g).ne_zero
    exact isLocallyConstant_char χ⁻¹ hχ'
  have hinv : ∀ x, ((χ x)⁻¹ : ℂˣ).val * (χ x : ℂ) = 1 := fun x => by simp
  let T := mulLC _ hci
  let S := mulLC _ hc
  have hTS : ∀ β : SB G, T (S β) = β := fun β => by
    apply Subtype.ext; funext x
    show ((χ x)⁻¹ : ℂˣ).val * ((χ x : ℂ) * (β : G → ℂ) x) = (β : G → ℂ) x
    rw [← mul_assoc, hinv, one_mul]
  have hM : ∀ (g : G) (α : SB G), (L ∘ₗ T) (transl g α) = (L ∘ₗ T) α := by
    intro g α
    have e : T (transl g α) = ((χ g)⁻¹ : ℂˣ).val • transl g (T α) := by
      apply Subtype.ext; funext x
      show ((χ x)⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x) =
        ((χ g)⁻¹ : ℂˣ).val * (((χ (g⁻¹ • x))⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x))
      have e2 : (χ x)⁻¹ = (χ g)⁻¹ * (χ (g⁻¹ • x))⁻¹ := by
        rw [smul_eq_mul, map_mul, map_inv, mul_inv, inv_inv, inv_mul_cancel_left]
      rw [e2, Units.val_mul, mul_assoc]
    simp only [LinearMap.comp_apply]
    rw [e, map_smul, hL, smul_eq_mul, ← mul_assoc, hinv g, one_mul]
  obtain ⟨c, hcM⟩ := exists_eq_const_mul (L ∘ₗ T) (intLC μ) hM (intLC_transl μ)
    (intLC_ind_ne_zero μ)
  refine ⟨c, fun α => ?_⟩
  have h1 := hcM (S α)
  rw [LinearMap.comp_apply, hTS, intLC_apply] at h1
  rw [h1]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end PositivityTheory.RgUd.T2.HaarDistr
