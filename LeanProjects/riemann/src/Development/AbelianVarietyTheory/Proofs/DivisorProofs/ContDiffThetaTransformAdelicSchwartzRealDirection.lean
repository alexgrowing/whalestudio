import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivCexpPhaseLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzShiftIteratedFDerivBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableRationalSchwartzBruhatMulPolynomialDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinearStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical ContDiff

noncomputable section

namespace GlobalTheory.ThetaSmooth

theorem norm_iteratedFDeriv_exp_mul_schwartz_le {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hre : ∀ y t, (B y t + h t).re = 0) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t) * f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  choose C1 hC1 using fun j => GlobalTheory.T.norm_iteratedFDeriv_cexp_phase_le' B h hh hre j R
  choose C2 hC2 using fun j => GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le f a p j (M + n) R
  refine ⟨∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |C1 j| * |C2 (n - j)|, fun y t ht => ?_⟩
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have s1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => Complex.exp (B y t + h t) :=
    Complex.contDiff_exp.comp ((B y).contDiff.add hh)
  have s2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => f (y + a + p t) :=
    (f.smooth ⊤).comp (contDiff_const.add p.contDiff)
  refine (norm_iteratedFDeriv_mul_le s1 s2 t (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e1 := hC1 j y t ht
  have e2 := hC2 (n - j) y t ht
  have hpow : (1 + ‖y‖) ^ j * ((1 + ‖y‖) ^ (M + n))⁻¹ ≤ ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), pow_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ hy1 hjn
  calc (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun t => Complex.exp (B y t + h t)) t‖ *
        ‖iteratedFDeriv ℝ (n - j) (fun t => f (y + a + p t)) t‖
      ≤ (n.choose j : ℝ) * (|C1 j| * (1 + ‖y‖) ^ j) * (|C2 (n - j)| * ((1 + ‖y‖) ^ (M + n))⁻¹) := by
        gcongr
        · exact e1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        · exact e2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ = (n.choose j : ℝ) * |C1 j| * |C2 (n - j)| * ((1 + ‖y‖) ^ j * ((1 + ‖y‖) ^ (M + n))⁻¹) := by ring
    _ ≤ (n.choose j : ℝ) * |C1 j| * |C2 (n - j)| * ((1 + ‖y‖) ^ M)⁻¹ := by gcongr

set_option maxHeartbeats 2000000 in

theorem contDiff_thetaTr_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L →
          (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) := by
  intro D ψ hψ S T JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  obtain ⟨P, Q, hPQ⟩ := GlobalTheory.T.darbouxCoords_real_family_archimedean_linear D S T κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear D ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1

  suffices key : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ w,
      Summable (fun x : κ → D.host.F => co.rho ψ w Φ (fun i => algebraMap D.host.F (AF D.host.F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF D.host.F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF D.host.F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF D.host.F) → ℂ) = 0 := by
    intro w; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M, hM⟩ := GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay D.host.F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    let yv : (κ → D.host.F) → (κ → mixedEmbedding.mixedSpace D.host.F) := fun x i => mixedEmbedding D.host.F (x i)
    let ah : κ → mixedEmbedding.mixedSpace D.host.F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace D.host.F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace D.host.F := eM (⅟(2 : AF D.host.F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace D.host.F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace D.host.F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)
    have hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i) := fun y t => rfl
    let hfun : (Fin k → ℝ) → ℂ := fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))
    have hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i :=
      fun i => ((ContinuousLinearMap.proj i).comp P).contDiff
    have hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i :=
      fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
      Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
        ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))
    have hre : ∀ y t, (B y t + hfun t).re = 0 := by
      intro y t; rw [hB, ← map_add]; exact hΛre _
    let K : (κ → D.host.F) → ℂ := fun x =>
      ψ ((fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) *
        g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2)
    let G : (κ → D.host.F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → D.host.F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t

    have hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA D.host.F f g)
        (fun i => algebraMap D.host.F (AF D.host.F) (x i)) = term x t := by
      intro x t
      have he : co.e (w + L t) = ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0,
          (co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) := by
        rw [map_add, hPQ t]; rfl
      have hy : ∀ i, eM (algebraMap D.host.F (AF D.host.F) (x i)).1 = yv x i := by
        intro i; simp only [yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
          (((fun i => algebraMap D.host.F (AF D.host.F) (x i)) +
            ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t := by
        funext i
        change eM ((algebraMap D.host.F (AF D.host.F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add, map_add, RingEquiv.apply_symm_apply, hy i, ← add_assoc]
        rfl
      have h2 : (fun i => (((fun i => algebraMap D.host.F (AF D.host.F) (x i)) +
            ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0)) i).2) =
          fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2 := by
        funext i
        change (algebraMap D.host.F (AF D.host.F) (x i)).2 + (((co.e w).1 i).2 + 0) = _
        rw [add_zero]
        rfl
      have hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA D.host.F f g) (fun i => algebraMap D.host.F (AF D.host.F) (x i)) =
          ψ ((fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
            ⅟2 * (((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ
              ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0))) *
          (f (yv x + ah + P t) * g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
            ((co.e w).1 i).2)) := by
        rw [← h1, ← h2]
        show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _
        rw [he]
        rfl
      rw [hL]
      let φ : AF D.host.F →+* mixedEmbedding.mixedSpace D.host.F := eM.toRingHom.comp (fstA D.host.F).toRingHom
      let φf : AF D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F := (sndA D.host.F).toRingHom
      have hφx : ∀ i, φ (algebraMap D.host.F (AF D.host.F) (x i)) = yv x i := hy
      have hφP : ∀ i, φ (pairA D.host.F (eM.symm (P t i)) 0) = P t i := fun i => eM.apply_symm_apply _
      have hφQ : ∀ i, φ (pairA D.host.F (eM.symm (Q t i)) 0) = Q t i := fun i => eM.apply_symm_apply _
      have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun i => rfl
      have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun i => rfl
      have hφ2 : φ ⅟2 = c2 := rfl
      have hφdef : ∀ z : AF D.host.F, eM z.1 = φ z := fun _ => rfl
      have hφfdef : ∀ z : AF D.host.F, z.2 = φf z := fun _ => rfl
      have hφpair : ∀ n, φ (pairA D.host.F (eM.symm n) 0) = n := fun n => eM.apply_symm_apply _
      have hφfpair : ∀ n, φf (pairA D.host.F (eM.symm n) 0) = 0 := fun n => rfl
      have hφfP : ∀ i, φf (pairA D.host.F (eM.symm (P t i)) 0) = 0 := fun i => rfl
      have hφfQ : ∀ i, φf (pairA D.host.F (eM.symm (Q t i)) 0) = 0 := fun i => rfl
      set X := (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)
        with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ
            ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
          ⅟2 * (((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ
            ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0)) = X + pairA D.host.F (eM.symm m) 0 := by
        have hY : (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
            ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
              (fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 +
              (fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0)) =
            pairA D.host.F (eM.symm m) 0 := by
          refine Prod.ext ?_ ?_
          · apply eM.injective
            rw [hφdef, hφdef, hφpair, hm]
            simp only [dotProduct, map_add, map_mul, map_sum, hφx, hφP, hφQ, hφa, hφb, hφ2, Finset.sum_add_distrib]
          · rw [hφfdef, hφfdef, hφfpair]
            simp only [dotProduct, map_add, map_mul, map_sum, hφfP, hφfQ, mul_zero, zero_mul, Finset.sum_const_zero,
              add_zero]
        rw [← hY, hX]
        simp only [dotProduct_add, add_dotProduct]
        ring
      have hψY : ψ (pairA D.host.F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf D.host.F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F = eM from rfl, RingEquiv.apply_symm_apply, hm,
          map_add]
        rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]
      simp only [term, K, G]
      ring
    have hK : ∀ x, ‖K x‖ =
        ‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2)‖ := by
      intro x; simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → D.host.F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
        ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      have h1 := hC (yv x) t ht
      calc _ ≤ ‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
            ((co.e w).1 i).2)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.WeilM.pureA D.host.F f g) (w + L t)) =
          fun t => ∑' x, term x t := funext fun t => tsum_congr fun x => hid x t
      rw [e]
      exact GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds term hsmooth hbd
  | zero =>
    intro w
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, rho_zero, Pi.zero_apply]
    exact ⟨summable_zero, by simpa [GlobalTheory.WeilM.thetaSum] using contDiff_const⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    intro w
    refine ⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₁ (w + L t) +
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2

end GlobalTheory.ThetaSmooth

end
