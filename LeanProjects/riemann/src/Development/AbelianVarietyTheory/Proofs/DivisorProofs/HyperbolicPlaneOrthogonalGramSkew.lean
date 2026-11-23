import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.DescGenCusp

open GlobalTheory.LeviPlane in

theorem exists_continuous_levi {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d d₁ : ℕ} (Y : Spc F E d) (Y₁ : Spc F E d₁) (H : Plane E d d₁)
    (hY : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx' : form σ Y.J H.x H.x = 0) (hyy' : form σ Y.J H.y H.y = 0)
    (hxy' : form σ Y.J H.x H.y = 1) (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) :
    ∃ m : (AE F E)ˣ → UA σ Y.J, Continuous m ∧ ∀ t, IsLevi (W₁ := Y₁) H t 1 (m t) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hcA : Continuous (cA (F := F) (E := E) σ) :=
    IsModuleTopology.continuous_of_linearMap (cA (F := F) (E := E) σ).toLinearMap
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F Y.J j i) = -incM F Y.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hY, map_neg]
  have hxx : fm c (incM F Y.J) (incV F H.x) (incV F H.x) = 0 := by rw [fm_inc, hxx', map_zero]
  have hyy : fm c (incM F Y.J) (incV F H.y) (incV F H.y) = 0 := by rw [fm_inc, hyy', map_zero]
  have hxy : fm c (incM F Y.J) (incV F H.x) (incV F H.y) = 1 := by rw [fm_inc, hxy', map_one]
  have hι : ∀ j, fm c (incM F Y.J) (fun i => incM F H.ι i j) (incV F H.x) = 0 ∧
      fm c (incM F Y.J) (fun i => incM F H.ι i j) (incV F H.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H.ι i j) = incV F (H.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM]
    rw [hcol, fm_inc, fm_inc, (horth _).1, (horth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E) :=
    fun s r => lev c (incM F Y.J) (incV F H.x) (incV F H.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : (AE F E)ˣ → GL (Fin d) (AE F E) := fun t =>
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : ∀ t, g t ∈ GlobalTheory.WeilM.UG (cA σ) (incM F Y.J) := by
    intro t
    show (L _ _)ᵀ * incM F Y.J * (L _ _).map (cA σ) = incM F Y.J
    exact lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
  refine ⟨fun t => ⟨g t, hg t⟩, ?_, fun t => ⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩⟩
  · have hLc : Continuous fun p : AE F E × AE F E => L p.1 p.2 := by
      simp only [L, lev]
      fun_prop
    apply Continuous.subtype_mk
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (hLc.comp (Units.continuous_val.prodMk (hcA.comp Units.continuous_coe_inv))).congr fun t => rfl
    · have e2 : ∀ t, (((g t)⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
          L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)) := fun t => rfl
      exact (hLc.comp (Units.continuous_coe_inv.prodMk (hcA.comp Units.continuous_val))).congr fun t => (e2 t).symm
  · have : mat (1 : UA σ Y₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _

theorem det_ne_zero_of_isHermND {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c₀ : E) (hJ : IsHermND σ (c₀ • J.map σ)) : J.det ≠ 0 := by
  intro h0
  apply hJ.2
  rw [Matrix.det_smul]
  have : (J.map σ).det = σ J.det := by
    rw [AlgHom.map_det]; rfl
  rw [this, h0, map_zero, mul_zero]

theorem continuous_law {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁)
    (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hn : n = n₁ + 2) (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0)
    (hxy : form σ W.J H.x H.y = 1) (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) (hd : W.J.det ≠ 0) (hd₁ : W₁.J.det ≠ 0)
    (hdom : ∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (χa : Chr F E) (za : ℝ) (f fa : UA σ W.J → ℂ) (hf : Continuous f) (hfi : ∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x)
    (hct : IsCT H f fa) (hlaw : HasLaw W₁ H χa za fa) (hne : ∃ x, fa x ≠ 0) :
    Continuous fun t : (AE F E)ˣ => (χa t : ℂ) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  obtain ⟨i1, -, i3, -⟩ := GlobalTheory.UnipCT.topFacts σ W.J
  haveI := i1
  haveI : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hcc := GlobalTheory.UnipCocptForm.cocompact_unip_form W W₁ H hCM hsk hn hxx hyy hxy horth hgram hd hd₁
  have hfa : Continuous fa := by
    have e : fa = fun h => ∫ u in 𝓕, f (u.1 * h) ∂μ := funext fun h => hct μ 𝓕 hμ h𝓕 h1 h
    rw [e]
    exact GlobalTheory.CtLeviCont.continuous_setIntegral_of_cocompact hcc hfi hf μ 𝓕 (by rw [h1]; exact ENNReal.one_ne_top)
  obtain ⟨m, hmc, hm⟩ := exists_continuous_levi σ (GlobalTheory.SiegelSet.sigma_sigma hCM) W W₁ H hsk hxx hyy hxy horth
  have hpos : ∀ t : (AE F E)ˣ, (0 : ℝ) < (GlobalTheory.Doubling.absE F E t : ℝ) := fun t => by
    have h : GlobalTheory.Doubling.absE F E t * GlobalTheory.Doubling.absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h))
  have hne : ∀ t : (AE F E)ˣ, (((GlobalTheory.Doubling.absE F E t : ℝ) ^ za : ℝ) : ℂ) * fa x₀ ≠ 0 := fun t =>
    mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hpos t) za).ne') hx₀
  have e : (fun t : (AE F E)ˣ => (χa t : ℂ)) =
      fun t => fa (m t * x₀) / ((((GlobalTheory.Doubling.absE F E t : ℝ) ^ za : ℝ) : ℂ) * fa x₀) := funext fun t => by
    rw [eq_div_iff (hne t), hlaw t (m t) (hm t) x₀, mul_assoc]
  rw [e]
  refine (hfa.comp (hmc.mul continuous_const)).div (Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const) hne
  exact (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).rpow_const fun t => Or.inl (hpos t).ne'

theorem cuspComp_generator_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      (∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1) →
      ∀ (χa : Chr F E) (za : ℝ) (f fa : UA σ W.J → ℂ), Continuous f → (∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) →
      IsCT H f fa → HasLaw W₁ H χa za fa →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) → ∀ (h : UA σ W.J) (c₀ : E), c₀ ≠ 0 →
      IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      (∀ φ' : GAd σ (c₀ • W.J.map σ) → ℂ, (∀ (g : UA σ W.J) (g' : GAd σ (c₀ • W.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W.J.map σ) Xf Yf S' K φ' 0) →
      ∀ φ' : GAd σ (c₀ • W₁.J.map σ) → ℂ,
        (∀ (g : UA σ W₁.J) (g' : GAd σ (c₀ • W₁.J.map σ)), g.1 = g'.1 → φ' g' = fa (M g * h)) →
        ∀ K : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W₁.J.map σ) Xf Yf S' K φ' 0 := by
  intro hKP F E _ _ _ _ _ σ hCM n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hdom χa za f fa hfc hfinv hCT hLaw M hMc hML hMr
    h c₀ hc₀ hH₁ hH hyp φ₁ hφ₁ K₁ hK₁ r Xf Yf hW₁ S' hS'
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hCM
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ with he
  set e₁ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ with he₁
  have hφ₁' : φ₁ = fun y => fa (M (e₁.symm y) * h) := funext fun y => hφ₁ (e₁.symm y) y rfl
  subst hφ₁'
  have hzero : GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ 0 :=
    ⟨GlobalTheory.StdPar.isAutOn_const _ _ _ _ _ K₁ 0, fun S₂ _ => GlobalTheory.StdPar.isConstAlong_const _ _ _ S₂ 0⟩
  by_cases hfa : ∀ x, fa x = 0
  · have e0 : (fun y => fa (M (e₁.symm y) * h)) = fun _ => (0 : ℂ) := funext fun y => hfa _
    rw [e0]
    refine ⟨hzero, fun _ => 0, GlobalTheory.StdPar.isConstAlong_const _ _ _ S' 0, fun ψ _ μ 𝓕 _ _ g g' => ?_⟩
    simp
  push_neg at hfa
  have hχ := GlobalTheory.CTLawRat.law_trivial_rat F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH hdom χa za f fa hfc hfinv hCT hLaw hfa
  have hχc := continuous_law σ hCM W W₁ H hsk hn hxx hyy hxy horth hgram (det_ne_zero_of_isHermND σ W.J c₀ hH)
    (det_ne_zero_of_isHermND σ W₁.J c₀ hH₁) hdom χa za f fa hfc hfinv hCT hLaw hfa
  obtain ⟨X', Y', hW', hx0, hy0, hsucc⟩ :=
    GlobalTheory.PlaneFrameCons.exists_isWittFrame_cons F E σ hCM n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH r Xf Yf hW₁
  have hS'' : ¬ ∀ k ∈ (insert 0 (S'.map (Fin.succEmb r))), ∀ l ≤ k, l ∈ (insert 0 (S'.map (Fin.succEmb r))) := by
    intro hall
    push_neg at hS'
    obtain ⟨k, hk, l, hlk, hl⟩ := hS'
    have := hall k.succ (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hk)) l.succ (Fin.succ_le_succ_iff.2 hlk)
    rcases Finset.mem_insert.1 this with h0 | h1
    · exact Fin.succ_ne_zero _ h0
    · obtain ⟨l', hl', el⟩ := Finset.mem_map.1 h1
      exact hl (Fin.succ_injective _ (by simpa using el) ▸ hl')
  obtain ⟨hMmul, hMcomm⟩ := GlobalTheory.LeviPlaneHom.levi_section_hom F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH M hML
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1₀⟩ := GlobalTheory.StdPar.exists_haar_fundamentalDomain_mass_one F E σ hCM n₁ _ hH₁ r Xf Yf hW₁ S'
  obtain ⟨μB, 𝓕B, hμB, h𝓕B, h1B⟩ := GlobalTheory.StdPar.exists_haar_fundamentalDomain_mass_one F E σ hCM n _ hH (r + 1) X' Y' hW' (insert 0 (S'.map (Fin.succEmb r)))
  have hfinv' : ∀ γ ∈ ratPts σ (c₀ • W.J.map σ), ∀ g, (fun x => f (e.symm x)) (γ * g) = (fun x => f (e.symm x)) g := by
    intro γ hγ g
    show f (e.symm (γ * g)) = f (e.symm g)
    rw [map_mul]
    exact hfinv _ ((GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ W.J hc₀ _).1 (by simpa [e] using hγ)) _
  have hfc' : Continuous (fun x => f (e.symm x)) := hfc.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W.J hc₀).2
  obtain ⟨c'', hc''⟩ := GlobalTheory.StdPar.exists_isConstAlong F E σ hCM n _ hH (r + 1) X' Y' hW' (insert 0 (S'.map (Fin.succEmb r))) _ hfc' hfinv'
  have hstage := GlobalTheory.T.hyperbolic_plane_complement_second F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH hdom M hMc hML hMr
    r Xf Yf hW₁ X' Y' hW' hx0 hy0 hsucc S' f fa hfc hfinv hCT c'' hc''
  have hlaw : ∀ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m → ∀ X,
      c'' (e (m * X)) = (χa t : ℂ) * (((GlobalTheory.Doubling.absE F E t : ℝ) ^ za : ℝ) : ℂ) * c'' (e X) := by
    intro t m hm X
    rw [hstage μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀, hstage μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [← mul_assoc, ← hMcomm t m hm, mul_assoc, hLaw t m hm]
  refine ⟨hzero, fun y => c'' (e (M (e₁.symm y) * h)), ?_, fun ψ hψ μ 𝓕 hμ h𝓕 g g' => ?_⟩
  · intro μ₁ 𝓕₁ hμ₁ h𝓕₁ h1₁ y
    show c'' (e (M (e₁.symm y) * h)) = _
    rw [hstage μ₁ 𝓕₁ hμ₁ h𝓕₁ h1₁]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [map_mul, hMmul, mul_assoc]
    rfl
  obtain ⟨K', hK', Ψ, hΨ, hΨv⟩ := GlobalTheory.T.hyperbolic_plane_complement_third hKP F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH
    M hMc hML hMr r Xf Yf hW₁ X' Y' hW' hx0 hy0 hsucc S' χa hχ hχc K₁ hK₁ ψ hψ
  have hlift : ∀ (g : UA σ W.J) (g' : GAd σ (c₀ • W.J.map σ)), g.1 = g'.1 → (fun x => f (e.symm x)) g' = f g := by
    intro g g' hg
    show f (e.symm g') = f g
    congr 1
    exact Subtype.ext hg.symm
  obtain ⟨-, c₃, hc₃, hpair⟩ := hyp (fun x => f (e.symm x)) hlift K' hK' (r + 1) X' Y' hW' (insert 0 (S'.map (Fin.succEmb r))) hS''
  have hceq : c₃ = c'' := funext fun G => by rw [hc₃ μB 𝓕B hμB h𝓕B h1B, hc'' μB 𝓕B hμB h𝓕B h1B]
  subst hceq
  set G := e (M (e₁.symm g) * h)
  set G' := e (M (e₁.symm g'))
  have key := GlobalTheory.T.hyperbolic_plane_complement_fourth F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH M hMc hML hMr
    r Xf Yf hW₁ X' Y' hW' hx0 hy0 hsucc S' (fun m => c₃ (m * G) * conj (Ψ (m * G')))
    (fun m => c₃ (e (M (e₁.symm (m * g)) * h)) * conj (ψ (m * g'))) ?_ ?_ μ 𝓕 hμ h𝓕
  · refine ⟨key.1, by simp, ?_⟩
    rw [key.2]; simp
  · intro t m y hm ht
    show c₃ (e (m * M (e₁.symm y)) * G) * conj (Ψ (e (m * M (e₁.symm y)) * G')) = c₃ (e (M (e₁.symm (y * g)) * h)) * conj (ψ (y * g'))
    have e1 : e (m * M (e₁.symm y)) * G = e (m * (M (e₁.symm (y * g)) * h)) := by
      simp only [G]
      rw [← map_mul, map_mul e₁.symm, hMmul]
      simp only [mul_assoc]
    have e2 : e (m * M (e₁.symm y)) * G' = e (m * M (e₁.symm (y * g'))) := by
      simp only [G']
      rw [← map_mul, map_mul e₁.symm, hMmul]
      simp only [mul_assoc]
    rw [e1, e2, hlaw t m hm, hΨv t m _ hm, ht]
    have hu : (χa t : ℂ) * conj (χa t : ℂ) = 1 := by
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, map_mul]
    linear_combination (c₃ (e (M (e₁.symm y * e₁.symm g)) * e h) * conj (ψ (y * g'))) * hu
  · intro μ'' 𝓕'' hμ'' h𝓕''
    obtain ⟨i1, -, i3⟩ := hpair Ψ hΨ μ'' 𝓕'' hμ'' h𝓕'' G G'
    refine ⟨i1, ?_⟩
    rw [i3]; simp

end GlobalTheory.ThK.DescGenCusp
