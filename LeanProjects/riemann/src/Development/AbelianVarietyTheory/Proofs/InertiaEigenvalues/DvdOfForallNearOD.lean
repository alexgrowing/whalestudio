import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SepFil

variable {l : ℕ} [Fact l.Prime]

theorem ev_eq_zero_iff_pt {e : Per.Fl l} (he : GlobalTheory.MemLoc.IsEps e) (m : ℕ) (y : Per.BdRp l) :
    Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y := by
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hfil := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1 1
  have hx : GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e)) := by
    rw [GlobalTheory.MemLoc.aDp, RingHom.comp_apply]
  have hmem : ∀ (n : ℕ) (a : Per.AinfP l), a ∈ Per.kerP l ^ n ↔
      algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n ∣ a := by
    intro n a
    rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hback : ∀ (n : ℕ) (w : Per.BdRp l), GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n ∣ w → Per.ev l n w = 0 := by
    rintro n w ⟨z, rfl⟩
    rw [map_mul, hx, ← map_pow (algebraMap (Per.AinfP l) (Per.BdRp l)), GlobalTheory.MemLoc.CrisUnique.ev_alg,
      Ideal.Quotient.eq_zero_iff_mem.2 ((hmem n _).2 dvd_rfl), zero_mul]
  have hnu : ¬ IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e)) := by
    intro h
    have h1 := (hθ _).2 ((hfil (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e))).2 (by rw [pow_one]))
    exact (h.map (Per.θD l)).ne_zero h1
  have hone : ∀ w : Per.BdRp l, Per.ev l 1 w = 0 → GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ∣ w := by
    intro w hw
    by_cases h0 : Per.θD l w = 0
    · have h1 := (hfil w).1 ((hθ w).1 h0)
      rwa [pow_one] at h1
    · exfalso
      have h1 := (hu w h0).map (Per.ev l 1)
      rw [hw, isUnit_zero_iff, eq_comm, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)),
        Ideal.Quotient.eq_zero_iff_mem, hmem, pow_one] at h1
      apply hnu
      rw [hx]
      exact (isUnit_of_dvd_one h1).map _
  have hdense : ∀ (n : ℕ) (w : Per.BdRp l), ∃ (a : Per.AinfP l) (z : Per.BdRp l),
      w = algebraMap (Per.AinfP l) (Per.BdRp l) a + GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n * z := by
    intro n w
    induction n with
    | zero => exact ⟨0, w, by rw [map_zero, pow_zero, one_mul, zero_add]⟩
    | succ n ih =>
      obtain ⟨a, z, hz⟩ := ih
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 z)
      obtain ⟨z', hz'⟩ := hone (z - algebraMap (Per.AinfP l) (Per.BdRp l) b) (by
        rw [map_sub, GlobalTheory.MemLoc.CrisUnique.ev_alg, hb, sub_self])
      refine ⟨a + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n * b, z', ?_⟩
      rw [map_add, map_mul, map_pow, ← hx, pow_succ, mul_assoc, ← hz', hz]
      ring
  refine ⟨fun hy ↦ ?_, hback m y⟩
  obtain ⟨a, z, hz⟩ := hdense m y
  have h1 := hback m _ (dvd_mul_right (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m) z)
  rw [hz, map_add, h1, add_zero, GlobalTheory.MemLoc.CrisUnique.ev_alg, Ideal.Quotient.eq_zero_iff_mem, hmem] at hy
  rw [hz]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [hx, ← map_pow]
  exact map_dvd _ hy

theorem dvd_of_forall_near {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ)
    (c : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (a : Ainf l) (z : Per.BdRp l),
      c - (l : Per.BdRp l) ^ r * GlobalTheory.MemLoc.aDp l a = GlobalTheory.MemLoc.aDp l d ^ m * z) :
    GlobalTheory.MemLoc.aDp l d ^ m ∣ c := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.CrisUnique.exists_isEps l
  have hk := GlobalTheory.MemLoc.ker_theta_eq_span_xi he
  have hxd : GlobalTheory.MemLoc.xi e ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hk, ← hd]
    exact Ideal.mem_span_singleton_self d
  have hdx : d ∣ GlobalTheory.MemLoc.xi e := by
    rw [← Ideal.mem_span_singleton, hd, hk]
    exact Ideal.mem_span_singleton_self _
  have hev : ∀ y : Per.BdRp l, Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y :=
    ev_eq_zero_iff_pt he m
  have h0 : Per.ev l m c = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r ↦ ?_
    obtain ⟨a, z, hz⟩ := h r
    refine ⟨a, ?_⟩
    have h1 : Per.ev l m (GlobalTheory.MemLoc.aDp l d ^ m * z) = 0 :=
      (hev _).2 (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (map_dvd _ hxd) m) z)
    rw [← hz, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast,
      GlobalTheory.MemLoc.CrisUnique.ev_aDp] at h1
    exact h1
  exact (pow_dvd_pow_of_dvd (map_dvd _ hdx) m).trans ((hev c).1 h0)

end GlobalTheory.BKReal.SepFil

namespace GlobalTheory.BKReal.SepFil

theorem dvd_of_forall_near_OD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O),
    (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) →
    ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m w h
  have hE : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  set d := ϖ.ev 1 (eis l 1 e) with hd_def
  have hd : Ideal.span {d} = RingHom.ker (Per.θ l) := ϖ.span_ev_eis 1
  have hξ : ϖ.iAl O K (EIn l e _) ^ m = (1 : O) ⊗ₜ[ℤ_[l]] (GlobalTheory.MemLoc.aDp l d ^ m) := by
    rw [hE, Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  rw [hξ] at h ⊢
  let b := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ i, GlobalTheory.MemLoc.aDp l d ^ m ∣ GlobalTheory.Decompl.crd b i w := by
    intro i
    refine dvd_of_forall_near hd m _ fun r ↦ ?_
    obtain ⟨y, z, hz⟩ := h r
    refine ⟨GlobalTheory.Decompl.crd b i y, GlobalTheory.Decompl.crd b i z, ?_⟩
    have h1 := congrArg (GlobalTheory.Decompl.crd b i) hz
    have h2 : GlobalTheory.Decompl.crd b i (toOD l O y) = GlobalTheory.MemLoc.aDp l (GlobalTheory.Decompl.crd b i y) :=
      GlobalTheory.Decompl.crd_map b (ainfToBdRp l) i y
    rw [LinearMap.map_sub, ← Nat.cast_pow, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_mul, h2,
      Nat.cast_pow] at h1
    exact h1
  choose c hc using key
  refine ⟨∑ j, b j ⊗ₜ[ℤ_[l]] c j, GlobalTheory.Decompl.ext_crd b fun i ↦ ?_⟩
  rw [GlobalTheory.Decompl.crd_mul, GlobalTheory.Decompl.crd_sum, ← hc i]

end GlobalTheory.BKReal.SepFil
