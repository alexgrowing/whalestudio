import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_gal_ev_E_unit {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (g : GQ l) :
    ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem WSeed.exists_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  intro l _ K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGA : ∀ y, G (bk.iA y) = bk.iA (Per.σA (g : GQ l) y) := hG.ext
  have hevE : bk.ev bk.E ≠ 0 := fun h => bk.frobenius_ev_E_ne_zero hτ (by rw [h, map_zero])
  have hE : bk.iS bk.E ≠ 0 := fun h => hevE (hinj (h.trans (map_zero _).symm))
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  obtain ⟨w, hw⟩ := exists_gal_ev_E_unit bk (g : GQ l)
  have hvu : bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hv0 : bk.iA (w : Ainf l) ≠ 0 := left_ne_zero_of_mul_eq_one hvu
  have hGE : G (bk.iS bk.E) = bk.iS bk.E * bk.iA (w : Ainf l) := by
    change G (bk.iA (bk.ev bk.E)) = _
    rw [hGA, hw, map_mul]
    rfl
  obtain ⟨li, hli⟩ : ∃ li : bk.DA bk.ρ₀, li * (l : bk.DA bk.ρ₀) = 1 := by
    obtain ⟨x, hx⟩ := (isUnit_l_disc l (bk.ev (PowerSeries.X : bk.S)) bk.ρ₀).exists_left_inv
    exact ⟨x, hx⟩
  have hnp : ∀ a b, ∃ c, (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) a b = bk.iS bk.E ^ (2 * s.N) * c :=
    fun a b => s.nopole g G hG a b
  choose Q hQ using hnp
  have hQm : s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G = bk.iS bk.E ^ (2 * s.N) • Matrix.of Q := by
    ext a b; rw [hQ a b]; rfl
  have hXX : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N) ≠ 0 := mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ hE)
  have hX'X := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hXX

  have hC1 : s.X.map bk.iS * Matrix.of Q = (l : bk.DA bk.ρ₀) ^ s.c₂ • (s.κ g * (s.X.map bk.iS).map G) := by
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero (2 * s.N) hE) ?_
    dsimp only
    rw [← Matrix.mul_smul, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_comm ((l : bk.DA bk.ρ₀) ^ s.c₂)]
  have hZi : IsUnit (Z.map i) := hZ.map (RingHom.mapMatrix i)
  have hZZ : Z.map i * (Z.map i)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hZi)
  refine ⟨(li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G), ?_, ?_⟩
  · have h3 : s.X.map bk.iS * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.X.map bk.iS * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (s.X.map bk.iS) (Z.map i), hZZ,
        Matrix.mul_one]
    have hs : G (bk.iS bk.E) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ =
        bk.iS bk.E ^ s.N := by
      rw [hGE]
      calc (bk.iS bk.E * bk.iA (w : Ainf l)) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) *
            (l : bk.DA bk.ρ₀) ^ s.c₂
          = bk.iS bk.E ^ s.N * (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N *
            (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli, one_pow, one_pow, mul_one, mul_one]
    rw [h3, hC1, Matrix.smul_mul, smul_smul, smul_smul, hs, Matrix.map_mul, ← Matrix.mul_assoc]
  · have hGXX : (s.X'.map bk.iS).map G * (s.X.map bk.iS).map G =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
      rw [← Matrix.map_mul, hX'X, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = s.W.map G * (Z.map i).map G := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_map, Matrix.map_map]
      congr 1
      funext y
      exact (hGA y).symm
    have hρ : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) =
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA := by
      rw [Matrix.map_map]; rfl
    have hL : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (s.W * s.X'.map bk.iS).map G *
        ((s.X.map bk.iS).map G * (Z.map i).map G) =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) •
          ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G * (Z.map i).map G) := by
      rw [Matrix.map_mul]
      calc _ = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G *
            ((s.X'.map bk.iS).map G * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hGXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have hR : s.W * s.X'.map bk.iS * s.κ g * ((s.X.map bk.iS).map G * (Z.map i).map G) =
        bk.iS bk.E ^ (2 * s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      calc _ = s.W * (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQm, Matrix.mul_smul, Matrix.smul_mul]
    have h5 := congrArg (· * ((s.X.map bk.iS).map G * (Z.map i).map G)) (s.gal g G hG)
    rw [Matrix.smul_mul, Matrix.smul_mul, hL, hR, smul_smul, smul_smul] at h5
    have h6 : s.W * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s.W (Z.map i), hZZ, Matrix.mul_one]
    rw [hYG, ← hρ, ← hWZ, h6, smul_smul, ← Matrix.mul_assoc]
    have hk : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hv0)) (pow_ne_zero _ hL0)
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) hk ?_
    dsimp only
    have hσE : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) =
        bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ) := by
      rw [map_mul, hw, map_mul, map_mul]; rfl
    have hE2 : bk.iA (bk.ev bk.E * τ) = bk.iS bk.E * bk.iA τ := by rw [map_mul]; rfl
    have hGc : G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) =
        (l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N) := by
      rw [map_mul, map_pow, map_pow, map_natCast, hGE]
    rw [hσE, hE2, hGc] at h5
    rw [smul_smul, smul_smul]
    have hs1 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ *
        (bk.iA (Per.σA (g : GQ l) τ) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N)) =
        (bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ)) ^ s.N * bk.iS bk.E ^ (2 * s.N) := by
      calc _ = bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ s.N * bk.iA (Per.σA (g : GQ l) τ) ^ s.N *
            (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N * (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli]; ring
    have hs2 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA τ ^ s.N =
        (bk.iS bk.E * bk.iA τ) ^ s.N * ((l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N)) := by
      ring
    rw [hs1, hs2]
    exact h5.symm

end GlobalTheory.BKLim
