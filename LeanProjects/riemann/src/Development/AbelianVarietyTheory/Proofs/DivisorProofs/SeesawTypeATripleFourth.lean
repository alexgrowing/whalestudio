import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeminormWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartFoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATwoTriplesIdentityFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATwoTriplesIdentitySecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.ArchEigen

theorem schrF_comm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : V → V → ℝ}
    (hP : GlobalTheory.ArchUniq.IsPairing P) (w w' : V × V) (f : V → ℂ) (z : V) :
    GlobalTheory.ArchUniq.schrF P w (GlobalTheory.ArchUniq.schrF P w' f) z =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((GlobalTheory.ArchUniq.omega P w w' : ℝ) : ℂ)) *
        GlobalTheory.ArchUniq.schrF P w' (GlobalTheory.ArchUniq.schrF P w f) z := by
  simp only [GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.omega]
  rw [add_right_comm z w'.1 w.1, hP.addL z w.1 w'.2, hP.addL z w'.1 w.2]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc (Complex.exp _), ← Complex.exp_add, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem omega_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : V → V → ℝ}
    (hP : GlobalTheory.ArchUniq.IsPairing P) {ι : Type} (w : V × V) (S : Finset ι) (s : ι → ℝ) (d : ι → V × V) :
    GlobalTheory.ArchUniq.omega P w (∑ i ∈ S, s i • d i) = ∑ i ∈ S, s i * GlobalTheory.ArchUniq.omega P w (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [GlobalTheory.ArchUniq.omega, hP.zero_left, hP.zero_right]
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    simp only [GlobalTheory.ArchUniq.omega, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hP.addR, hP.addL,
      hP.smulR, hP.smulL]
    ring

end GlobalTheory.ArchEigen

namespace GlobalTheory.ArchEigen

theorem exists_param_eigen : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (f₀ : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
    ∃ (m : ℕ) (Λ₁ Λ₂ : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F))
      (π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m)) (W' : Set (EuclideanSpace ℝ (Fin m))),
      Continuous π ∧ IsOpen W' ∧ π (1, 1) ∈ W' ∧ (∀ S, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) ∧
      (∀ p, π p = π (1, 1) → mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • incV F H.x) = incV F H.x) ∧
      ∀ (p : KAt K (evI F) × idelesAt E (evI F)) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
        ∃ ℓ : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] ℂ,
          (∀ g, ℓ g = ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' p.2.1))) (locOpInf (om (p.1.1, 1)) g)) y) ∧
          ∀ (s : EuclideanSpace ℝ (Fin m)) (g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
            ⇑g = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) (Λ₁ s, Λ₂ s) ⇑f₀ →
            ℓ g = Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ s (π p) : ℝ) : ℂ)) * ℓ f₀ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK f₀
  have hP : GlobalTheory.ArchUniq.IsPairing (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) :=
    GlobalTheory.ArchUniq.Coord.isPairing_trP _
  have hcont := GlobalTheory.T.config_a_two_triples_identity_first F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ K
  obtain ⟨m, yv, W', hW'o, h1W, hprop, hfib⟩ :=
    GlobalTheory.T.config_a_two_triples_identity_second F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ K hK hcont
  have h0 : GlobalTheory.ArchUniq.Coord.coordI G.M 0 = 0 := by
    have h := GlobalTheory.ArchUniq.Coord.coordI_add G.M 0 0
    rw [add_zero] at h
    simpa using h
  have hsum : ∀ (z : Fin m → Fin (b + 2) → AE F E) (s : Fin m → ℝ) (S : Finset (Fin m)),
      GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (∑ i ∈ S, realAd F (s i) • z i) (incV F H'.x)) =
        ∑ i ∈ S, s i • GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (z i) (incV F H'.x)) := by
    intro z s S
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Matrix.zero_vecMulVec, h0]
    | insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_vecMulVec, GlobalTheory.ArchUniq.Coord.coordI_add, ih,
        Matrix.smul_vecMulVec, GlobalTheory.ArchUniq.Coord.coordI_smul]
  set c : Fin m → (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) :=
    fun i => GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (yv i) (incV F H'.x)) with hc
  let Λ₁ : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) :=
    ∑ i, (EuclideanSpace.proj i).smulRight (c i).1
  let Λ₂ : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) :=
    ∑ i, (EuclideanSpace.proj i).smulRight (c i).2
  have hΛ : ∀ s : EuclideanSpace ℝ (Fin m), (Λ₁ s, Λ₂ s) =
      GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (∑ i, realAd F (s i) • yv i) (incV F H'.x)) := by
    intro s
    rw [hsum yv (fun i => s i) Finset.univ]
    refine Prod.ext ?_ ?_
    · simp [Λ₁, Prod.fst_sum, hc]
    · simp [Λ₂, Prod.snd_sum, hc]
  refine ⟨m, Λ₁, Λ₂, _, W', ?_, hW'o, h1W, hprop, hfib, ?_⟩
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hcont (yv i)).neg)
  intro p y
  have hkK : p.1.1 ∈ KAt K (evI F) := p.1.2
  have hkU : p.1.1 ∈ UAt σ G.V (evI F) := p.1.2.2
  have hψ : IsStd B.ψ := hT.base.std
  have hex : ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      Acts (evI F) (om (p.1.1, 1)) f f₁ :=
    GlobalTheory.ThK.ArchActs.acts_inf hKP F E σ B (b + 2) a' G X om om' hT p.1.1 hkU
  let Alin : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')) :=
    { toFun := locOpInf (om (p.1.1, 1))
      map_add' := fun f f' => by simpa using locOpInf_lin (om (p.1.1, 1)).isLinear hex 1 1 f f'
      map_smul' := fun a f => by simpa using locOpInf_lin (om (p.1.1, 1)).isLinear hex a 0 f 0 }
  have hAc : Continuous Alin := by
    refine Seminorm.continuous_from_bounded (schwartz_withSeminorms ℂ _ ℂ) (schwartz_withSeminorms ℂ _ ℂ) Alin ?_
    intro i
    obtain ⟨s', C, hC⟩ := GlobalTheory.ArchKX.locOpInf_unif_bound hKP F E σ B (b + 2) a' G X om om' hT K hK {i}
    refine ⟨s', ⟨max C 0, le_max_right _ _⟩, Seminorm.le_def.2 fun f => ?_⟩
    have h := hC p.1.1 hkK f
    simp only [Finset.sup_singleton] at h
    simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_mk]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg _ _))
  let Acl : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')) := ⟨Alin, hAc⟩
  have hAcl : ∀ f, Acl f = locOpInf (om (p.1.1, 1)) f := fun f => rfl
  set wt := GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1) with hwt
  have hR : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' p.2.1))) h = GlobalTheory.SchrPairing.schrSch hP wt h := fun h =>
    DFunLike.coe_injective ((locOpInf_rho G.M.co hψ _ h).2.trans (GlobalTheory.SchrPairing.coe_schrSch hP wt h).symm)
  let ℓ : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM ℂ y).comp
    ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ).comp (ei.comp ((GlobalTheory.SchrPairing.schrSch hP wt).comp Acl)))
  have hℓ : ∀ g, ℓ g = ei (GlobalTheory.SchrPairing.schrSch hP wt (Acl g)) y := fun g => rfl
  refine ⟨ℓ, fun g => by rw [hℓ, hAcl, hR], fun s g hg => ?_⟩
  set ys : Fin (b + 2) → AE F E := ∑ i, realAd F (s i) • yv i with hys
  set u := Matrix.vecMulVec ys (incV F H'.x) with hu
  have hg' : g = locOpInf (G.M.co.rho B.ψ (partInf F u)) f₀ :=
    DFunLike.coe_injective (hg.trans (by rw [hΛ s]; exact (locOpInf_rho G.M.co hψ u f₀).2.symm))
  have hIsLoc : GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev := ⟨hei, hev, hpure⟩
  have t4 := GlobalTheory.T.config_A_local_part_fold hKP.base F E σ B b a' G G₁ H H' hCfg e he ei ev hIsLoc X om om' om₁ om₁' hT hT₁ p.1.1 hkU u f₀
  have hact : actAB (cA σ) ((p.1.1, 1) : UA σ G.V.J × UA σ G.W.J) u =
      Matrix.vecMulVec (mat p.1.1 *ᵥ ys) (incV F H'.x) := by
    have h := Matrix.mul_vecMulVec (mat p.1.1) ys (incV F H'.x)
    simp only [actAB, hu, Units.val_one, Prod.snd_one, Prod.fst]
    simpa [mat] using h
  set w'' := GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ ys) (incV F H'.x)) with hw''
  have hAg : Acl g = GlobalTheory.SchrPairing.schrSch hP w'' (Acl f₀) := by
    rw [hAcl, hAcl, hg', t4, hact]
    exact DFunLike.coe_injective ((locOpInf_rho G.M.co hψ _ _).2.trans (GlobalTheory.SchrPairing.coe_schrSch hP w'' _).symm)
  set h₁ := GlobalTheory.SchrPairing.schrSch hP wt (Acl f₀) with hh₁
  set h₂ := GlobalTheory.SchrPairing.schrSch hP w'' h₁ with hh₂
  have hcomm : GlobalTheory.SchrPairing.schrSch hP wt (Acl g) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) wt w'' : ℝ) : ℂ)) • h₂ := by
    apply DFunLike.coe_injective
    funext z
    rw [hAg, GlobalTheory.SchrPairing.coe_schrSch, GlobalTheory.SchrPairing.coe_schrSch, GlobalTheory.ArchEigen.schrF_comm hP, SchwartzMap.smul_apply,
      smul_eq_mul, hh₂, hh₁, GlobalTheory.SchrPairing.coe_schrSch, GlobalTheory.SchrPairing.coe_schrSch]
  have hei2 : ei h₂ = ei h₁ := GlobalTheory.ThK.HeisInvInf.ei_schr_eq F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he
    ei ev hev hpure (mat p.1.1 *ᵥ ys) h₁ h₂ (GlobalTheory.SchrPairing.coe_schrSch hP w'' h₁)
  have hw''s : w'' = ∑ i, s i • GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ yv i) (incV F H'.x)) := by
    rw [hw'', hys, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    exact hsum (fun i => mat p.1.1 *ᵥ yv i) (fun i => s i) Finset.univ
  have hphase : inner ℝ s (WithLp.toLp 2 fun i => -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
      (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
      (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ yv i) (incV F H'.x))) : EuclideanSpace ℝ (Fin m)) =
      -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) wt w'' := by
    rw [hw''s, GlobalTheory.ArchEigen.omega_sum hP]
    simp [PiLp.inner_apply, hwt, Finset.sum_neg_distrib, mul_comm]
  rw [hℓ, hℓ, hcomm, map_smul, SchwartzMap.smul_apply, hei2, smul_eq_mul, hphase]
  congr 1
  push_cast
  ring_nf

end GlobalTheory.ArchEigen
