import Mathlib
import Formalism.EllipticTorsion.JetsCube
import Formalism.FormalGroupLog.LogDeterminesLaw

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupCubeJets

open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem integral_mul {σ : Type} {f g : MvPowerSeries σ K} (hf : IntegralMv f) (hg : IntegralMv g) :
    IntegralMv (f * g) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem integral_pderiv {σ : Type} (i : σ) {f : MvPowerSeries σ K} (hf : IntegralMv f) :
    IntegralMv (MvPowerSeries.pderiv K i f) := by
  classical
  intro d
  rw [coeff_pderiv, norm_mul]
  have h1 : ((d i : K) + 1) = ((d i + 1 : ℕ) : K) := by push_cast; rfl
  rw [h1]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)

theorem integral_map {σ : Type} (g : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype g) := by
  intro d
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d g).2

theorem pderiv_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (i : σ)
    (g : MvPowerSeries σ R) :
    MvPowerSeries.pderiv S i (MvPowerSeries.map f g) =
      MvPowerSeries.map f (MvPowerSeries.pderiv R i g) := by
  ext d
  rw [coeff_pderiv, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, coeff_pderiv, map_mul,
    map_add, map_natCast, map_one]

variable (F : FormalGroup (unitBall K))

theorem omegaF_eq : omegaF F = Formalism.G.LogP.omegaF (FK F) := rfl

theorem FK_eq : (FK F).toPowerSeries = MvPowerSeries.map (unitBall K).subtype F.toPowerSeries :=
  rfl

theorem omega_map : omegaF F = PowerSeries.map (unitBall K).subtype
    (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (unitBall K)), 0]
      (MvPowerSeries.pderiv (unitBall K) 1 F.toPowerSeries)) := by
  have hb : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries (unitBall K)), 0] := hb0
  rw [PowerSeries.map, MvPowerSeries.map_subst hb, ← pderiv_map, ← FK_eq, omegaF]
  congr 1
  funext i
  fin_cases i
  · simp [PowerSeries.X]
  · simp

theorem integral_omegaX (j : Fin 3) :
    IntegralMv ((omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 3) (unitBall K)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have : (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) =
      MvPowerSeries.map (unitBall K).subtype
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) (unitBall K))
          (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (unitBall K)), 0]
          (MvPowerSeries.pderiv (unitBall K) 1 F.toPowerSeries) : PowerSeries (unitBall K))) := by
    rw [PowerSeries.map_subst hX, MvPowerSeries.map_X, ← omega_map]
  rw [this]
  exact integral_map _

def Dj (j : Fin 3) (g : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) * MvPowerSeries.pderiv K j g

theorem integral_Dj (j : Fin 3) {g : MvPowerSeries (Fin 3) K} (hg : IntegralMv g) :
    IntegralMv (Dj F j g) :=
  integral_mul (integral_omegaX F j) (integral_pderiv j hg)

theorem Dj_sub (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) : Dj F j (a - b) = Dj F j a - Dj F j b := by
  rw [Dj, Dj, Dj, map_sub, mul_sub]

theorem Dj_add (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) : Dj F j (a + b) = Dj F j a + Dj F j b := by
  rw [Dj, Dj, Dj, map_add, mul_add]

theorem Dj_C (j : Fin 3) (c : K) : Dj F j (MvPowerSeries.C c) = 0 := by
  rw [Dj, MvPowerSeries.pderiv_C, mul_zero]

theorem Dj_const (j : Fin 3) (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst A) = 0 := by
  rw [Dj, pderiv_psubst hA, hdA, mul_zero, mul_zero]

theorem Dj_X (j : Fin 3) (ψ : PowerSeries K) :
    Dj F j (ψ.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) =
      (invD F ψ).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by simp
  rw [Dj, pderiv_psubst hX, pderiv_X_self, mul_one, invD,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hX)]

theorem rti (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (j : Fin 3) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j])) =
      (invD F ψ).subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) := by
  have hXj : MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by
    simp
  have hB : MvPowerSeries.constantCoeff ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp [hA]),
      (FK F).zero_constantCoeff]
  have hs := hs2 hA hXj
  have dB : MvPowerSeries.pderiv K j ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) =
      (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries).subst ![A, MvPowerSeries.X j] := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp [hA])]
    simp [Fin.sum_univ_two, hdA]
  have hω : (omegaF F).subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) =
      (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries).subst ![A, MvPowerSeries.X j] *
        (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) := by
    have := congrArg (MvPowerSeries.subst ![A, MvPowerSeries.X j]) (omega_key (FK F))
    rw [MvPowerSeries.subst_mul hs, psubst_subst _ (FK F).zero_constantCoeff hs, atY,
      psubst_subst _ hX1 hs, MvPowerSeries.subst_X hs] at this
    simpa [omegaF_eq] using this
  rw [Dj, pderiv_psubst hB, dB, invD,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hB), hω]
  ring

theorem ccX (i : Fin 3) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 := by
  simp

theorem hsX (i : Fin 3) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (ccX i)

theorem constantCoeff_two_variable_law (a b : Fin 3) : MvPowerSeries.constantCoeff (F2 F a b) = 0 := by
  rw [F2, constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp [Y3]),
    (FK F).zero_constantCoeff]

theorem constantCoeff_three_variable_law : MvPowerSeries.constantCoeff (F3 F) = 0 := by
  rw [F3, constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp [Y3, constantCoeff_two_variable_law]),
    (FK F).zero_constantCoeff]

theorem pderiv_two_variable_law_other (a b k : Fin 3) (ha : a ≠ k) (hb : b ≠ k) :
    MvPowerSeries.pderiv K k (F2 F a b) = 0 := by
  rw [F2, pderiv_subst (fun i => by fin_cases i <;> simp [Y3])]
  simp [Fin.sum_univ_two, Y3, pderiv_X_of_ne ha, pderiv_X_of_ne hb]

theorem three_variable_law_eq_subst_second : F3 F = (FK F).toPowerSeries.subst ![F2 F 0 2, MvPowerSeries.X 1] := by
  have : (FK F).IsComm := Formalism.G.isCommOfRat K (FK F)
  have e1 := (FK F).assoc' (hsX (K := K) 0) (hsX 1) (hsX 2)
  have e2 := (FK F).assoc' (hsX (K := K) 0) (hsX 2) (hsX 1)
  have c := (FK F).comm' (hsX (K := K) 1) (hsX 2)
  rw [F3, F2, F2]
  simp only [Y3]
  rw [e1, c, ← e2]

theorem two_variable_law_one_two_eq : F2 F 1 2 = (FK F).toPowerSeries.subst ![MvPowerSeries.X 2, MvPowerSeries.X 1] := by
  have : (FK F).IsComm := Formalism.G.isCommOfRat K (FK F)
  exact (FK F).comm' (hsX (K := K) 1) (hsX 2)

theorem three_variable_law_eq_subst_first : F3 F = (FK F).toPowerSeries.subst ![F2 F 1 2, MvPowerSeries.X 0] := by
  have : (FK F).IsComm := Formalism.G.isCommOfRat K (FK F)
  have e1 := (FK F).assoc' (hsX (K := K) 0) (hsX 1) (hsX 2)
  have h12 : PowerSeries.HasSubst (F2 F 1 2) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_two_variable_law F 1 2)
  have c := (FK F).comm' (hsX (K := K) 0) h12
  rw [F3, F2]
  simp only [Y3]
  rw [e1]
  exact c

theorem pderiv_zero_subst_three_variable_law (ψ : PowerSeries K) : Dj F 0 (ψ.subst (F3 F)) = (invD F ψ).subst (F3 F) := by
  rw [three_variable_law_eq_subst_first]
  exact rti F ψ (constantCoeff_two_variable_law F 1 2) 0 (pderiv_two_variable_law_other F 1 2 0 (by decide) (by decide))

theorem step2 (φ : PowerSeries K) : Dj F 2 (triDiff F φ) =
    (invD F φ).subst (F3 F) - (invD F φ).subst (F2 F 0 2) - (invD F φ).subst (F2 F 1 2)
      + (invD F φ).subst (Y3 2) := by
  have h3 : Dj F 2 (φ.subst (F3 F)) = (invD F φ).subst (F3 F) :=
    rti F φ (constantCoeff_two_variable_law F 0 1) 2 (pderiv_two_variable_law_other F 0 1 2 (by decide) (by decide))
  have h01 : Dj F 2 (φ.subst (F2 F 0 1)) = 0 :=
    Dj_const F 2 φ (constantCoeff_two_variable_law F 0 1) (pderiv_two_variable_law_other F 0 1 2 (by decide) (by decide))
  have h02 : Dj F 2 (φ.subst (F2 F 0 2)) = (invD F φ).subst (F2 F 0 2) :=
    rti F φ (ccX 0) 2 (pderiv_X_of_ne (by decide))
  have h12 : Dj F 2 (φ.subst (F2 F 1 2)) = (invD F φ).subst (F2 F 1 2) :=
    rti F φ (ccX 1) 2 (pderiv_X_of_ne (by decide))
  have hx0 : Dj F 2 (φ.subst (Y3 0 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 2 φ (ccX 0) (pderiv_X_of_ne (by decide))
  have hx1 : Dj F 2 (φ.subst (Y3 1 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 2 φ (ccX 1) (pderiv_X_of_ne (by decide))
  have hx2 : Dj F 2 (φ.subst (Y3 2 : MvPowerSeries (Fin 3) K)) =
      (invD F φ).subst (Y3 2 : MvPowerSeries (Fin 3) K) := Dj_X F 2 φ
  rw [triDiff]
  simp only [Dj_sub, Dj_add, Dj_C, h3, h01, h02, h12, hx0, hx1, hx2]
  ring

theorem step1 (φ : PowerSeries K) : Dj F 1
    ((invD F φ).subst (F3 F) - (invD F φ).subst (F2 F 0 2) - (invD F φ).subst (F2 F 1 2)
      + (invD F φ).subst (Y3 2)) =
    (invD F (invD F φ)).subst (F3 F) - (invD F (invD F φ)).subst (F2 F 1 2) := by
  have h3 : Dj F 1 ((invD F φ).subst (F3 F)) = (invD F (invD F φ)).subst (F3 F) := by
    rw [three_variable_law_eq_subst_second]
    exact rti F _ (constantCoeff_two_variable_law F 0 2) 1 (pderiv_two_variable_law_other F 0 2 1 (by decide) (by decide))
  have h02 : Dj F 1 ((invD F φ).subst (F2 F 0 2)) = 0 :=
    Dj_const F 1 _ (constantCoeff_two_variable_law F 0 2) (pderiv_two_variable_law_other F 0 2 1 (by decide) (by decide))
  have h12 : Dj F 1 ((invD F φ).subst (F2 F 1 2)) = (invD F (invD F φ)).subst (F2 F 1 2) := by
    rw [two_variable_law_one_two_eq]
    exact rti F _ (ccX 2) 1 (pderiv_X_of_ne (by decide))
  have hx2 : Dj F 1 ((invD F φ).subst (Y3 2 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 1 _ (ccX 2) (pderiv_X_of_ne (by decide))
  simp only [Dj_sub, Dj_add, h3, h02, h12, hx2]
  ring

theorem step0 (φ : PowerSeries K) : Dj F 0
    ((invD F (invD F φ)).subst (F3 F) - (invD F (invD F φ)).subst (F2 F 1 2)) =
    (invD F (invD F (invD F φ))).subst (F3 F) := by
  have h12 : Dj F 0 ((invD F (invD F φ)).subst (F2 F 1 2)) = 0 :=
    Dj_const F 0 _ (constantCoeff_two_variable_law F 1 2) (pderiv_two_variable_law_other F 1 2 0 (by decide) (by decide))
  rw [Dj_sub, pderiv_zero_subst_three_variable_law, h12, sub_zero]

theorem chain (φ : PowerSeries K) (k : ℕ) :
    (Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ)))) = ((invD F)^[k + 3] φ).subst (F3 F) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, step2, step1, step0]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_zero_subst_three_variable_law]
    rw [← Function.iterate_succ_apply' (invD F) (k + 3) φ]

theorem integral_chain (hN : NPderiv.{u}) (φ : PowerSeries K) (h : InN (triDiff F φ)) (k : ℕ) :
    IntegralMv ((Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ))))) := by
  have h2 : IntegralMv (Dj F 2 (triDiff F φ)) :=
    integral_mul (integral_omegaX F 2) (hN K (Fin 3) _ h 2)
  have h0 := integral_Dj F 0 (integral_Dj F 1 h2)
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact integral_Dj F 0 ih

theorem constantCoeff_subst_three_variable_law (ψ : PowerSeries K) :
    MvPowerSeries.constantCoeff (ψ.subst (F3 F)) = PowerSeries.constantCoeff ψ := by
  rw [PowerSeries.subst_def, constantCoeff_subst_of_zero _ (fun _ => constantCoeff_three_variable_law F)]
  rfl

end Formalism.ELL.FormalGroupCubeJets

namespace Formalism.ELL

theorem jetsCube_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsCube.{u} := by
  intro K _ _ _ F φ h i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have hI := FormalGroupCubeJets.integral_chain F hN φ h k
  rw [FormalGroupCubeJets.chain] at hI
  have := hI 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, FormalGroupCubeJets.constantCoeff_subst_three_variable_law] at this
  exact this

end Formalism.ELL
