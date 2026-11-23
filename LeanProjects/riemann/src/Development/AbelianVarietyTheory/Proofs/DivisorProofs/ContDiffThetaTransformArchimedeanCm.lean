import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

open scoped Classical ContDiff

noncomputable section

namespace GlobalTheory.ThetaSmoothF

theorem psiInf_eq_exp_linearF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (ψ : AddChar (AF F) ℂ) (h : IsStdCharF tauE ψ (-1)) :
    ∃ Λ : mixedEmbedding.mixedSpace F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing F,
      psiInf F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) := by
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E))
    refine continuous_const.mul (continuous_finset_sum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (GlobalTheory.PsiInfLinear.continuous_ringEquiv_mixedSpace_symm F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[F] (1 : E))
  rw [e.symm_apply_apply]

theorem darboux_real_coordsF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ] (e : WOF F E nS nT ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (k : ℕ)
    (L : (Fin k → ℝ) →+ WOF F E nS nT) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPartF F E) = 0) :
    ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace F), ∀ t, e (L t) =
      (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (P t i)) 0,
        fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Q t i)) 0) := by
  have hε : ∀ t, (pairA F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, GlobalTheory.RealDirCoord.eps_smul_gen]
    change LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F)) (finPartF F E (L t i j)) = 0
    rw [h0, LinearMap.map_zero]
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h1, (GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h2⟩
  have he : Continuous e := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin _ → Fin _ → AF F ⊗[F] E))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF F) × (κ → AF F)) → (κ → AF F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        map_add' := by
          intro a b
          funext i
          rw [map_add, LinearEquiv.map_add, hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (GlobalTheory.RealDirCoord.continuous_ringEquiv_mixed F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

set_option maxHeartbeats 2000000 in

theorem contDiff_thetaTr_realF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (w + L t) := by
  intro F E _ _ _ _ _ σ B0' hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  set ψ := B0'.ψ
  obtain ⟨P, Q, hPQ⟩ := darboux_real_coordsF (F := F) (E := E) nS nT κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := psiInf_eq_exp_linearF _ ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1

  suffices key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ w,
      Summable (fun x : κ → F => co.rho ψ w Φ (fun i => algebraMap F (AF F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF F) → ℂ) = 0 := by
    intro w; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M, hM⟩ := GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace F
    let yv : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun x i => mixedEmbedding F (x i)
    let ah : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace F := eM (⅟(2 : AF F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
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
    let K : (κ → F) → ℂ := fun x =>
      ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) *
        g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)
    let G : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t

    have hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g)
        (fun i => algebraMap F (AF F) (x i)) = term x t := by
      intro x t
      have he : co.e (w + L t) = ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0,
          (co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) := by
        rw [map_add, hPQ t]; rfl
      have hy : ∀ i, eM (algebraMap F (AF F) (x i)).1 = yv x i := by
        intro i; simp only [yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
          (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t := by
        funext i
        change eM ((algebraMap F (AF F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add, map_add, RingEquiv.apply_symm_apply, hy i, ← add_assoc]
        rfl
      have h2 : (fun i => (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).2) =
          fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2 := by
        funext i
        change (algebraMap F (AF F) (x i)).2 + (((co.e w).1 i).2 + 0) = _
        rw [add_zero]
        rfl
      have hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g) (fun i => algebraMap F (AF F) (x i)) =
          ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
              ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0))) *
          (f (yv x + ah + P t) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)) := by
        rw [← h1, ← h2]
        show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _
        rw [he]
        rfl
      rw [hL]
      let φ : AF F →+* mixedEmbedding.mixedSpace F := eM.toRingHom.comp (fstA F).toRingHom
      let φf : AF F →+* FiniteAdeleRing (𝓞 F) F := (sndA F).toRingHom
      have hφx : ∀ i, φ (algebraMap F (AF F) (x i)) = yv x i := hy
      have hφP : ∀ i, φ (pairA F (eM.symm (P t i)) 0) = P t i := fun i => eM.apply_symm_apply _
      have hφQ : ∀ i, φ (pairA F (eM.symm (Q t i)) 0) = Q t i := fun i => eM.apply_symm_apply _
      have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun i => rfl
      have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun i => rfl
      have hφ2 : φ ⅟2 = c2 := rfl
      have hφdef : ∀ z : AF F, eM z.1 = φ z := fun _ => rfl
      have hφfdef : ∀ z : AF F, z.2 = φf z := fun _ => rfl
      have hφpair : ∀ n, φ (pairA F (eM.symm n) 0) = n := fun n => eM.apply_symm_apply _
      have hφfpair : ∀ n, φf (pairA F (eM.symm n) 0) = 0 := fun n => rfl
      have hφfP : ∀ i, φf (pairA F (eM.symm (P t i)) 0) = 0 := fun i => rfl
      have hφfQ : ∀ i, φf (pairA F (eM.symm (Q t i)) 0) = 0 := fun i => rfl
      set X := (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)
        with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
          ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0)) = X + pairA F (eM.symm m) 0 := by
        have hY : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0)) =
            pairA F (eM.symm m) 0 := by
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
      have hψY : ψ (pairA F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace F = eM from rfl, RingEquiv.apply_symm_apply, hm,
          map_add]
        rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]
      simp only [term, K, G]
      ring
    have hK : ∀ x, ‖K x‖ =
        ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)‖ := by
      intro x; simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := GlobalTheory.ThetaSmooth.norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
        ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      have h1 := hC (yv x) t ht
      calc _ ≤ ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (GlobalTheory.WeilM.pureA F f g) (w + L t)) =
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
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) +
          GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2

end GlobalTheory.ThetaSmoothF

end
