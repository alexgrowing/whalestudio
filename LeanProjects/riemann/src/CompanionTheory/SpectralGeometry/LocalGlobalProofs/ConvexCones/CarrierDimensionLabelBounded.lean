import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity

private theorem exists_int_ne_zero_eq_mul_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O]
    (s : O) (hs : s ≠ 0) : ∃ n : ℤ, n ≠ 0 ∧ ∃ o : O, o * s = (n : O) := by
  have hI : Ideal.comap (algebraMap ℤ O) (Ideal.span {s}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
      (Algebra.IsIntegral.isIntegral s)
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff _).mp hI
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hn)
  exact ⟨n, hn0, o, by rw [ho]; exact eq_intCast (algebraMap ℤ O) n⟩

private theorem isLocalizedModule_int_restrictScalars_mkLinearMap (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    IsLocalizedModule (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨n, hn⟩
    rw [Module.End.isUnit_iff]
    have hn0 : (n : O) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hn)
    have hu : algebraMap O (FractionRing O) (n : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn0)
    have key : ∀ v : LocalizedModule (nonZeroDivisors O) X,
        (algebraMap ℤ (Module.End ℤ (LocalizedModule (nonZeroDivisors O) X)) n) v =
          algebraMap O (FractionRing O) (n : O) • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul, Int.cast_smul_eq_zsmul]
    constructor
    · intro a b h
      rw [key, key] at h
      have h2 := congrArg (fun w => (algebraMap O (FractionRing O) (n : O))⁻¹ • w) h
      simpa only [smul_smul, inv_mul_cancel₀ hu, one_smul] using h2
    · intro v
      exact ⟨(algebraMap O (FractionRing O) (n : O))⁻¹ • v, by
        rw [key, smul_smul, mul_inv_cancel₀ hu, one_smul]⟩
  · intro y
    refine LocalizedModule.induction_on (fun m s => ?_) y
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O s (nonZeroDivisors.ne_zero s.2)
    refine ⟨⟨o • m, ⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply]
    rw [← Int.cast_smul_eq_zsmul O, LocalizedModule.smul'_mk, ← ho, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, mul_smul]
    exact smul_comm _ _ _
  · intro x₁ x₂ h
    simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O u (nonZeroDivisors.ne_zero u.2)
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] at hu ⊢
    rw [← Int.cast_smul_eq_zsmul O, ← Int.cast_smul_eq_zsmul O, ← ho, mul_smul, mul_smul, hu]

private theorem finrank_int_eq_mul_finrank (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  haveI := isLocalizedModule_int_restrictScalars_mkLinearMap O X
  haveI : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  letI : Module ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.compHom _ (algebraMap ℚ (FractionRing O))
  haveI : IsScalarTower ℚ (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have e1 : Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) = Module.finrank ℤ X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) le_rfl
  have e2 : Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  have e3 : Module.finrank ℚ (FractionRing O) *
      Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.finrank_mul_finrank ℚ (FractionRing O) _
  haveI : @IsScalarTower ℤ ℚ (FractionRing O) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have e4 : Module.finrank ℚ (FractionRing O) = Module.finrank ℤ O :=
    IsFractionRing.finrank_eq ℤ ℚ O (FractionRing O)
  have e5 : Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank O (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq O (FractionRing O) _
  have e6 : Module.finrank O (LocalizedModule (nonZeroDivisors O) X) = Module.finrank O X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors O)
      (LocalizedModule.mkLinearMap (nonZeroDivisors O) X) le_rfl
  rw [← e1, ← e2, ← e3, e4, e5, e6]

theorem finrank_int_eq_fraction_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℚ K * Module.finrank O X := by
  rw [finrank_int_eq_mul_finrank O X, IsFractionRing.finrank_eq ℤ ℚ O K]

theorem finrank_int_eq_finrank_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  have : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  have h := finrank_int_eq_fraction_mul O (FractionRing O) O
  rw [Module.finrank_self, mul_one] at h
  rw [finrank_int_eq_fraction_mul O (FractionRing O) X, h]

private theorem isTorsionFree_int_of_isTorsionFree (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.IsTorsionFree O Y] :
    Module.IsTorsionFree ℤ Y :=
  Module.IsTorsionFree.comap (S := O) (fun r : ℤ => (r : O))
    (fun r hr => IsRegular.of_ne_zero (Int.cast_ne_zero.mpr hr.ne_zero))
    (fun r m => Int.cast_smul_eq_zsmul O r m)

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] : Module.Free ℤ Y := by
  haveI : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := fun a b h => by
    have ha := LinearMap.congr_fun hs a
    have hb := LinearMap.congr_fun hs b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, h]
  haveI : Module.IsTorsionFree O Y :=
    Function.Injective.moduleIsTorsionFree s hinj (fun r m => s.map_smul r m)
  haveI : Module.IsTorsionFree ℤ Y := isTorsionFree_int_of_isTorsionFree O Y
  exact Module.free_of_finite_type_torsion_free'

theorem genRank_le_sq (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    genRank γ ≤ (q * Module.finrank ℤ O) ^ 2 := by
  haveI : Module.IsTorsionFree ℤ O := isTorsionFree_int_of_isTorsionFree O O
  haveI : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  haveI : Module.Free ℤ X := free_int_of_projective O
  have hX' : Module.finrank ℤ X ≤ q * Module.finrank ℤ O := by
    rw [finrank_int_eq_finrank_mul O X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  show Module.finrank ℤ (Submodule.span ℤ (Set.range γ)) ≤ _
  calc Module.finrank ℤ (Submodule.span ℤ (Set.range γ))
      ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) := Submodule.finrank_le _
    _ = Module.finrank ℤ X * Module.finrank ℤ X := by
      show Module.finrank ℤ (X →ₗ[ℤ] X →ₗ[ℤ] ℤ) = _
      rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_self, mul_one]
    _ ≤ (q * Module.finrank ℤ O) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hX' hX'

private theorem nat_sInf_le_of_forall_le {s : Set ℕ} {N : ℕ} (h : ∀ k ∈ s, k ≤ N) : sInf s ≤ N := by
  rcases s.eq_empty_or_nonempty with hs | ⟨k, hk⟩
  · rw [hs, Nat.sInf_empty]
    exact Nat.zero_le _
  · exact (Nat.sInf_le hk).trans (h k hk)

theorem carrierDim_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro O _ _ _ _ bar _ q ψ lab hC
  refine ⟨(q * Module.finrank ℤ O) ^ 2, ?_⟩
  intro X _ _ _ _ hX β hβ hpos
  rw [hC X hX β hβ hpos]
  exact_mod_cast nat_sInf_le_of_forall_le (fun k hk => by
    obtain ⟨m, γ, -, -, rfl⟩ := hk
    exact genRank_le_sq O q X hX γ)

end GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity
