import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToODStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearODStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.TwoMaps

theorem toHatS_eq_of_hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → toHatS O K l e f = x := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f x hfx
  let fR : Rpi O K l e := ⟨(f : K⟦X⟧), invL_S_le_Rpi l e f.2⟩
  have h0 : hat O l e (fR : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHat O K l e fR) := hat_coe_Rpi l e fR
  have h1 : toHatS O K l e f = toHat O K l e fR := rfl
  have h2 : hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHatS O K l e f) := by
    rw [h1]; exact h0
  rw [h2] at hfx
  have hE0 : EIn l e (invL l (A O K)) ≠ 0 := fun h => by
    have h3 : E K l e = 0 := congrArg Subtype.val h
    exact (isUnit_E (K := K) l e).ne_zero h3
  have hreg : ∀ y : Ahat O K l e, Ehat O K l e * y = 0 → y = 0 := fun y hy =>
    GlobalTheory.MemLoc.FilPrincipal.regular_of_isDomain rfl hE0 y hy
  have hmem : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro y hy <;> apply hreg <;> first | exact hy | (rw [mul_comm]; exact hy)
  have hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
    IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) (AhatE O K l e) (Submonoid.powers_le.2 hmem)
  exact hinj hfx

theorem iSD_eq_of_mem_invL_A : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)), (f : K⟦X⟧) ∈ invL l (A O K) → ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f hf
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]

theorem iSD_eq_iHat_of_hat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K], ∀ (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → ϖ.iSD O K f = ϖ.iHat O K x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ f x hfx
  obtain rfl := toHatS_eq_of_hat l e O K ϖ f x hfx
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ

  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
    fun s => ϖ.iSD_of_mem O K s.2 _
  have key : ∀ s : S O K e, crisToOD l O (ϖ.iS O K s) =
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
    intro s
    rw [← sub_eq_zero]
    set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
    have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
      simp only [hD, map_add]; ring
    have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
      simp only [hD, map_mul, map_pow, map_natCast]; ring
    have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
      intro m
      obtain ⟨N, hN⟩ := GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd l e O K ϖ m
      have hw : ∀ k : ℕ, ∃ y : OA l O, ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
        intro k
        obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
        obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
        set hS' : S O K e := ⟨h, hh⟩
        have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
          sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
        set P : S O K e := ⟨_, hP⟩
        have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
        have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
          have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
            simp only [P]; linear_combination hs
          rw [this]
          exact sum_mem fun n _ => monomial_mem_invL l n _
        have hDP : D P = 0 := by
          simp only [hD, sub_eq_zero]
          rw [← hS]
          exact iSD_eq_of_mem_invL_A l e O K ϖ _ hPA
        obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
        obtain ⟨y2, hy2⟩ := GlobalTheory.T.exists_pow_iHat_toHatS_sub_toOD_dvd l e O K ϖ m hS'
        refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
        have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
            (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') - toOD l O y1) -
              (l : OD l O) ^ N * ((l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
          rw [hsP, hDadd, hDP, zero_add, hDmul]
          simp only [hD, map_sub, map_mul, map_pow, map_natCast]
          ring
        rw [e1]
        exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
      have h1 := GlobalTheory.T.dvd_of_forall_approx_toOD l e O K ϖ m _ hw
      rw [pow_add, mul_assoc] at h1
      exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
    have hc := ϖ.complete_OD O K
    exact hc.toIsHausdorff.haus' _ fun n => by
      simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
      exact Ideal.mem_span_singleton.2 (hdiv n)
  have hext : ϖ.iSD O K = (ϖ.iHat O K).toRingHom.comp (toHatS O K l e) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact (hS s).trans (key s))
  exact RingHom.congr_fun hext f

end GlobalTheory.BKReal.TwoMaps
