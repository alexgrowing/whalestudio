import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

def cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) : MvPolynomial σ L :=
  ∑ m ∈ y.support, monomial m (f (y.coeff m))

def RestFunY : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (f : KK O →+ ℚ_[p]),
    (∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x) →
    ∀ y ∈ Yjt (KK O) (r := r) LL J M, cmap f y ∈ Formalism.GM.M.Y p (r := r) (Formalism.MainNotions.G.SymmetricFormBlocks.gmL LL) J M

def RestDecomp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (σ : Type)
    (y : MvPolynomial σ (KK O)),
    ∃ (n : ℕ) (b : Fin n → KK O) (f : Fin n → (KK O →+ ℚ_[p])),
      (∀ k (a : ℚ_[p]) (x : KK O), f k (ι a * x) = a * f k x) ∧
      y = ∑ k, b k • map ι (cmap (f k) y)

def RestClear : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Formalism.GM.M.Letters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), ∀ F ∈ Formalism.GM.M.Y p (r := r) LL J M,
      ∃ e : ℕ, ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.YZ p (r := r) LL J M

theorem restClear_proved : RestClear := by
  intro p _ N r _ LL q J M F hF
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ m, ‖(p : ℚ_[p]) ^ e * F.coeff m‖ ≤ 1 := by
    set B : ℝ := ∑ m ∈ F.support, ‖F.coeff m‖ with hB
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨e, fun m => ?_⟩
    rw [norm_mul, Padic.norm_p_pow]
    have hcm : ‖F.coeff m‖ ≤ B := by
      by_cases hm : m ∈ F.support
      · exact Finset.single_le_sum (f := fun m => ‖F.coeff m‖) (fun _ _ => norm_nonneg _) hm
      · rw [MvPolynomial.notMem_support_iff.1 hm, norm_zero]
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hp0 : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hp0, mul_one]
    linarith
  refine ⟨e, ?_⟩
  have hY : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Y p (r := r) LL J M := Submodule.smul_mem _ _ hF
  have hPol : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Pol p r LL := (Submodule.mem_inf.1 hY).1
  have hInt : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := by
    have hr : ((p : ℚ_[p]) ^ e) • F ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ : ∃ m ∈ (((p : ℚ_[p]) ^ e) • F).support, c = (((p : ℚ_[p]) ^ e) • F).coeff m := by
        simpa [MvPolynomial.coeffs, eq_comm] using hc
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact ⟨⟨_, he m⟩, rfl⟩
    obtain ⟨G, hG⟩ := hr
    exact ⟨G, hG⟩
  exact Submodule.mem_inf.2 ⟨hY, Submodule.mem_inf.2 ⟨hPol, hInt⟩⟩

theorem restYbc_of (hF : RestFunY) (hD : RestDecomp) (hC : RestClear) : RestYbc := by
  intro O _ _ p _ ι N r _ LL q J M y hy
  have hyK : y ∈ Yjt (KK O) (r := r) LL J M := hy.1
  obtain ⟨n, b, f, hf, hdec⟩ := hD O p ι _ y
  rw [hdec]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have h1 := hF O p ι N r LL q J M (f k) (hf k) y hyK
  obtain ⟨e, he⟩ := hC p N r (gmL LL) q J M _ h1
  have hp0 : ((p : ℚ_[p]) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : map ι (cmap (f k) y) = (ι ((p : ℚ_[p]) ^ e))⁻¹ • map ι (((p : ℚ_[p]) ^ e) • cmap (f k) y) := by
    rw [MvPolynomial.smul_eq_C_mul (a := (ι ((p : ℚ_[p]) ^ e))⁻¹), MvPolynomial.smul_eq_C_mul (a := (p : ℚ_[p]) ^ e), map_mul,
      map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ((map_ne_zero ι).2 hp0), C_1, one_mul]
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, he, rfl⟩)

theorem coeff_cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (cmap f y) = f (y.coeff m) := by
  classical
  unfold cmap
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem restDecomp_proved : RestDecomp := by
  intro O _ _ p _ ι σ y
  classical
  letI : Algebra ℚ_[p] (KK O) := ι.toAlgebra
  let V : Submodule ℚ_[p] (KK O) := Submodule.span ℚ_[p] (y.coeffs : Set (KK O))
  let bV := Module.finBasis ℚ_[p] V
  obtain ⟨rV, hrV⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  refine ⟨Module.finrank ℚ_[p] V, fun k => (bV k : KK O),
    fun k => ((bV.coord k).comp rV).toAddMonoidHom, ?_, ?_⟩
  · intro k a x
    have hx : ι a * x = a • x := by rw [Algebra.smul_def]; rfl
    show ((bV.coord k).comp rV) (ι a * x) = a * ((bV.coord k).comp rV) x
    rw [hx, map_smul, smul_eq_mul]
  · ext m
    have hc : y.coeff m ∈ V := by
      by_cases h0 : y.coeff m = 0
      · rw [h0]; exact V.zero_mem
      · exact Submodule.subset_span (MvPolynomial.coeff_mem_coeffs _ h0)
    have hrc : rV (y.coeff m) = ⟨y.coeff m, hc⟩ := by
      have := LinearMap.congr_fun hrV ⟨y.coeff m, hc⟩
      simpa using this
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_cmap, smul_eq_mul]
    have hsum := congrArg Subtype.val (bV.sum_repr ⟨y.coeff m, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show (bV.repr ⟨y.coeff m, hc⟩ k) • (bV k : KK O) = (bV k : KK O) * ι ((bV.coord k) (rV (y.coeff m)))
    rw [hrc, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
    rfl

theorem restYbc_of_funY (hF : RestFunY) : RestYbc := restYbc_of hF restDecomp_proved restClear_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
