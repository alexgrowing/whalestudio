import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinBarUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalFunctionalScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarValuationIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramUnitaryOfAbsEq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.WRightChar

theorem unitaryW_char : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∃ (χW : (Fv F B.v₁)ˣ →* ℂˣ) (ε : Bool) (C : GL (Fin (a + a')) (Fv F B.v₁)), IsUnram χW ∧
      (∀ y, ‖((χW y : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ g M : GL (Fin (a + a')) (Fv F B.v₁),
        (mat h).map (piW B.τ₁) = g.1 →
        M.1 = C.1 * (if ε then ((g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1)ᵀ else g.1) * (C⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1 →
        ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ ∧
          ι φ₁ = ((χW (GlobalTheory.SplitFlip.gdet M) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet M) ((a' : ℂ) / 2)) •
            fun Y => ι φ (Y * M.1) := by
  intro kp F E _ _ _ _ _ σ B a a' G X om om' hT
  have hP : GlobalTheory.FunPr.Hypotheses₂ := kp.base
  classical
  by_cases hex : ∃ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι
  swap
  · exact ⟨1, false, 1, fun _ _ => rfl, fun y => by simp, fun ι hι => absurd ⟨ι, hι⟩ hex⟩
  obtain ⟨ι₀, hι₀⟩ := hex
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F B.v₁) := fun u _ => by simp [mat]
  obtain ⟨hexU, -, -⟩ := GlobalTheory.ThK.LocalOps.actsEx hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) B.v₁
  have hEx : ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      ∃! φ₁, φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧ Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ :=
    fun h hh φ hφ => hexU 1 hone h hh φ hφ
  let P : (((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ)) →
      UA σ G.W.J → ℂ → Prop :=
    fun ι h c => ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))
  have hJ := GlobalTheory.SplitTransport.isUnit_det_map_J_of_isTriple hT B.v₁ B.τ₁
  have hts : ∀ h : UA σ G.W.J, (mat h).map (piW (B.τ₁.comp σ)) =
      (G.W.J.map B.τ₁)⁻¹ * (((GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val)ᵀ * G.W.J.map B.τ₁ := by
    intro h
    have u := GlobalTheory.UnitaryInjAtPlace.unitary_at_components B.v₁ B.τ₁ h
    have hg : IsUnit ((mat h).map (piW B.τ₁)).det := GlobalTheory.LocalUnitSubgroupClosure.isUnit_det_cmp (Y := G.W) B.τ₁ h
    have hgT : IsUnit ((mat h).map (piW B.τ₁))ᵀ.det := by rw [Matrix.det_transpose]; exact hg
    rw [Matrix.coe_units_inv, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val, Matrix.transpose_nonsing_inv]
    calc (mat h).map (piW (B.τ₁.comp σ))
        = (G.W.J.map B.τ₁)⁻¹ * (((mat h).map (piW B.τ₁))ᵀ⁻¹ * (((mat h).map (piW B.τ₁))ᵀ * G.W.J.map B.τ₁ *
            (mat h).map (piW (B.τ₁.comp σ)))) := by
          rw [Matrix.mul_assoc ((mat h).map (piW B.τ₁))ᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hgT,
            Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
      _ = _ := by rw [u, Matrix.mul_assoc]
  have hc0 : ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∃ c : ℂ, P ι₀ h c := by
    intro h hh
    obtain ⟨S, hS, hlin, hcov, -⟩ := GlobalTheory.WeilTransferW.local_weil_operator_second_space hP F E σ B a a' G X om om' hT B.v₁ h hh
    obtain ⟨c, hc⟩ := GlobalTheory.WeilTransferW.linBar_right_mul F E σ B a a' G X om om' hT B.v₁ B.τ₁ h
      (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h) hh rfl (hts h) S (fun φ hφ => (hS φ hφ).1) hlin hcov ι₀ hι₀
    refine ⟨c, fun φ hφ φ₁ hφ₁ hA => ?_⟩
    have e : φ₁ = S φ := (hEx h hh φ hφ).unique ⟨hφ₁, hA⟩ (hS φ hφ)
    rw [e, hc φ hφ]
    rfl
  have hPι : ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ h c, P ι₀ h c → P ι h c := by
    intro ι hι h c hc φ hφ φ₁ hφ₁ hA
    obtain ⟨l, hl⟩ := GlobalTheory.LinModelUniq.linBar_unique F E σ B a a' G X om om' hT ι₀ ι hι₀ hι
    rw [hl φ₁ hφ₁, hl φ hφ, hc φ hφ φ₁ hφ₁ hA]
    funext Y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hvac := hT.geo.hM'.vac B.v₁
  have hιv : ι₀ (G.M'.vac B.v₁) ≠ 0 := by
    intro h0
    exact hvac.2.1 (hι₀.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 hιv
  have uniq : ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ c c', P ι₀ h c → P ι₀ h c' → c = c' := by
    intro h hh c c' hc hc'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hEx h hh _ hvac.1
    have key : Y₀ * ((GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val * (mat h).map (piW B.τ₁) = Y₀ := by
      rw [← GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have e1 := congrFun (hc _ hvac.1 φ₁ hφ₁ hA) (Y₀ * ((GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val)
    have e2 := congrFun (hc' _ hvac.1 φ₁ hφ₁ hA) (Y₀ * ((GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).val)
    simp only [Pi.smul_apply, smul_eq_mul, key] at e1 e2
    exact mul_right_cancel₀ hY₀ (e1.symm.trans e2)
  choose! c hc using hc0
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have acts_comp : ∀ {h₁ h₂ : UA σ G.W.J} {φ φ₂ φ₃ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ},
      Acts (evFin F B.v₁) (om' (1, h₂)) φ φ₂ → Acts (evFin F B.v₁) (om' (1, h₁)) φ₂ φ₃ →
      Acts (evFin F B.v₁) (om' (1, h₁ * h₂)) φ φ₃ := by
    intro h₁ h₂ φ φ₂ φ₃ h2 h1 r hr
    have hr2 : Rest (evFin F B.v₁) φ₂ r := ⟨hr.1, by rw [← h2 r hr]; exact hSplit.pres _ _ hr.2⟩
    have e : om' (1, h₁ * h₂) = om' (1, h₁) * om' (1, h₂) := by rw [← map_mul]; simp
    rw [e, Module.End.mul_apply, h2 r hr, h1 r hr2]
  have cmul : ∀ h₁ ∈ UAt σ G.W (evFin F B.v₁), ∀ h₂ ∈ UAt σ G.W (evFin F B.v₁), c (h₁ * h₂) = c h₁ * c h₂ := by
    intro h₁ hh₁ h₂ hh₂
    refine uniq _ (GlobalTheory.LocalUnitSubgroupClosure.mul_mem_UAt hh₁ hh₂) _ _ (hc _ (GlobalTheory.LocalUnitSubgroupClosure.mul_mem_UAt hh₁ hh₂)) ?_
    intro φ hφ φ₁₂ hφ₁₂ hA
    obtain ⟨φ₂, ⟨hφ₂, hA2⟩, -⟩ := hEx h₂ hh₂ φ hφ
    obtain ⟨φ₃, ⟨hφ₃, hA3⟩, -⟩ := hEx h₁ hh₁ φ₂ hφ₂
    have : φ₁₂ = φ₃ := (hEx (h₁ * h₂) (GlobalTheory.LocalUnitSubgroupClosure.mul_mem_UAt hh₁ hh₂) φ hφ).unique ⟨hφ₁₂, hA⟩ ⟨hφ₃, acts_comp hA2 hA3⟩
    subst this
    rw [hc h₁ hh₁ φ₂ hφ₂ φ₁₂ hφ₁₂ hA3, hc h₂ hh₂ φ hφ φ₂ hφ₂ hA2]
    funext Y
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.LocalUnitSubgroupClosure.mat_mul, Matrix.map_mul, Matrix.mul_assoc, mul_assoc]
  have c1 : c 1 = 1 := by
    refine uniq 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) _ _ (hc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)) ?_
    intro φ hφ φ₁ hφ₁ hA
    have : φ₁ = φ := (hEx 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ, fun r _ => by
      rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]⟩
    subst this
    rw [GlobalTheory.LocalUnitSubgroupClosure.mat_one, Matrix.map_one (piW B.τ₁) (map_zero _) (map_one _), one_smul]
    funext Y
    rw [Matrix.mul_one]
  choose sec hsec hsecv using GlobalTheory.SplitTransport.surjW hT B.v₁ B.τ₁
  have hinj := GlobalTheory.SplitTransport.injW hT B.v₁ B.τ₁
  have secmul : ∀ g₁ g₂, sec (g₁ * g₂) = sec g₁ * sec g₂ := fun g₁ g₂ =>
    hinj _ (hsec _) _ (GlobalTheory.LocalUnitSubgroupClosure.mul_mem_UAt (hsec g₁) (hsec g₂)) (by
      rw [hsecv, GlobalTheory.LocalUnitSubgroupClosure.mat_mul, Matrix.map_mul, hsecv, hsecv, Units.val_mul])
  have sec1 : sec 1 = 1 := hinj _ (hsec _) _ (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) (by
    rw [hsecv, GlobalTheory.LocalUnitSubgroupClosure.mat_one, Matrix.map_one (piW B.τ₁) (map_zero _) (map_one _), Units.val_one])
  let κ : GL (Fin (a + a')) (Fv F B.v₁) →* ℂ :=
    { toFun := fun g => c (sec g)
      map_one' := by simp only [sec1, c1]
      map_mul' := fun g₁ g₂ => by simp only [secmul, cmul _ (hsec g₁) _ (hsec g₂)] }
  have hcmp : ∀ g, GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ (sec g) = g := fun g => Units.ext (by rw [GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val, hsecv])
  have hN : ∀ g, ‖κ g‖ = ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((a' : ℂ) / 2)‖ := by
    intro g
    have := GlobalTheory.T.linear_bar_local_functional_scalar hP F E σ B a a' G X om om' hT ι₀ hι₀ (sec g) (hsec g) (c (sec g)) (hc _ (hsec g))
    rw [hcmp] at this
    exact this
  have hU : ∀ g : GL (Fin (a + a')) (Fv F B.v₁), (∀ i j, ValuativeRel.valuation (Fv F B.v₁) (g.1 i j) ≤ 1) →
      ValuativeRel.valuation (Fv F B.v₁) g.1.det = 1 → κ g = 1 := by
    intro g hg hd
    exact GlobalTheory.T.linear_bar_valuation_integral_bound hP F E σ B a a' G X om om' hT ι₀ hι₀ (sec g) (hsec g) (by rw [hsecv]; exact hg)
      (by rw [hsecv]; exact hd) _ (hc _ (hsec g))
  obtain ⟨ν, hνu, hνn, hν⟩ := GlobalTheory.LocalDetChar.exists_unram_unitary_of_abs_eq (GlobalTheory.LocalUnitSubgroupClosure.two_ne_zero_Fv B.v₁) (a + a') a' κ hN hU
  refine ⟨ν, false, 1, hνu, hνn, fun ι hι h hh g M hg hM φ hφ => ?_⟩
  have hMg : M = GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h := Units.ext (by rw [hM, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val, hg]; simp)
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hEx h hh φ hφ
  refine ⟨φ₁, hφ₁, hA, ?_⟩
  have hch : c h = κ (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h) := by
    show c h = c (sec _)
    rw [hinj _ (hsec _) _ hh (by rw [hsecv, GlobalTheory.LocalUnitSubgroupClosure.cmpGL_val])]
  rw [hPι ι hι h (c h) (hc h hh) φ hφ φ₁ hφ₁ hA, hch, hν, hMg]
  rfl

end GlobalTheory.WRightChar
