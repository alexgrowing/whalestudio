import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaQZeroRealMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMinorMulDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealFrameTwistedCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCharacterExponentArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharactersParityStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwCoef

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem opsK (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a') (hm : IsMatched B G X om om' R Rf) :
    ∃ T : UA σ G.W.J → (R.Pi →ₗ[ℂ] R.Pi),
      (∀ k ∈ KInf σ G.W B.emb, ∀ f : SInf F (Fin a × Fin (a + a')), ∃ f₁ : SInf F (Fin a × Fin (a + a')),
        Acts (evI F) (om (1, k)) f f₁) ∧
      (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        Acts (evI F) (om (1, k)) f f₁ → R.p f₁ = T k (R.p f)) ∧
      (∀ k ∈ KInf σ G.W B.emb, ∀ k' ∈ KInf σ G.W B.emb, ∀ v, T (k * k') v = T k (T k' v)) ∧
      (∀ v, T 1 v = v) ∧
      (∀ k ∈ KInf σ G.W B.emb, ∀ v ∈ lowPartInf B G.M R.p, T k v ∈ lowPartInf B G.M R.p) := by
  have hB := hm.triple.base
  have hM := hm.triple.geo.hM
  have hw := hm.triple.weil
  have hL := GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))
  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
      (∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f (A f)) ∧
      ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ g ∈ G.M.Pol B.ψ B.emb, R.p (A g) = T (R.p g) := by
    intro k hk
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk
    refine ⟨A, hA, GlobalTheory.TwPartStab.descent R.p hm.real.quot.onto A fun f hf hpf => ?_⟩
    have h0 := hm.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (GlobalTheory.TwPartStab.acts_zero _) (by rw [hpf, map_zero])
    rw [h0, map_zero]
  choose! A hA T hT using hop
  have hpol : ∀ k ∈ KInf σ G.W B.emb, ∀ g ∈ G.M.Pol B.ψ B.emb, A k g ∈ G.M.Pol B.ψ B.emb := fun k hk g hg =>
    GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk g hg (A k g) (hA k hk g)
  have onto : ∀ v : R.Pi, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = v := fun v => by
    have hv : v ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hm.real.quot.onto]; trivial
    obtain ⟨g, hg, e⟩ := hv
    exact ⟨g, hg, e⟩
  refine ⟨T, fun k hk f => ⟨A k f, hA k hk f⟩, ?_, ?_, ?_, ?_⟩
  · intro k hk f hf f₁ h
    rw [(hL f f₁ (A k f)).2.2.2.1 _ h (hA k hk f), hT k hk f hf]
  · intro k hk k' hk' v
    obtain ⟨g, hg, rfl⟩ := onto v
    have hkk := GlobalTheory.HwCoef.kInf_mul_mem hk hk'
    have c := GlobalTheory.TwPartStab.acts_mul hw k' k (hA k' hk' g) (hA k hk (A k' g))
    have e := (hL _ _ _).2.2.2.1 _ c (hA _ hkk g)
    rw [← hT _ hkk g hg, ← e, hT k hk _ (hpol k' hk' g hg), hT k' hk' g hg]
  · intro v
    obtain ⟨g, hg, rfl⟩ := onto v
    have h1 : Acts (evI F) (om (1, 1)) g g := fun r _ => by
      rw [show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]; rfl
    have e := (hL _ _ _).2.2.2.1 _ h1 (hA 1 GlobalTheory.HwCoef.one_mem_kInf g)
    rw [← hT 1 GlobalTheory.HwCoef.one_mem_kInf g hg, ← e]
  · intro k hk v hv
    obtain ⟨g, hg, rfl⟩ := hv
    exact ⟨A k g, GlobalTheory.TwPartStab.fockDeg_stable hB hw hk (hA k hk) _ hg,
      hT k hk g (fockDeg_le_pol _ _ _ _ hg)⟩

end GlobalTheory.TwCoef

namespace GlobalTheory.TwCoef

open Formalism.BasicNotions.TH

theorem twPart_coef : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ C : InfinitePlace F → Matrix (Fin (b + a')) (Formalism.BasicNotions.TH.Ix (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) ℂ,
        (∀ w, GlobalTheory.ThK.RealK.IsAdapted B.emb w G₁.W (C w)) →
        twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ≠ ⊥ →
        ∃ y ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∃ η : R.Pi →ₗ[ℂ] ℂ, η y = 1 ∧
          ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ k ∈ KInf σ G.W B.emb, IsLevi H' 1 k₁ k →
            ∀ g, GlobalTheory.HwCoef.IsReading B.emb C k₁ g → ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = y →
              ∀ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) f f₁ →
                η (R.p f₁) = GlobalTheory.HwCoef.hwCoef B b a' G₁.p g := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ C hCa htw
  have hq : G.q = 0 := hcfg.q0
  have hq1 : G₁.q = 0 := hcfg.q1
  have hp : G₁.p + 1 = G.p := hcfg.ep
  have hpb : G₁.p < b := by have := hm₁.triple.geo.eBig; omega
  have hcm := hm.triple.base.cm
  obtain ⟨T, hTex, hTacts, hTmul, hTone, hTlow⟩ := opsK B G X om om' R Rf hm
  have hirr := GlobalTheory.T.lowPart_invariant_submodule_equiv hKP F E σ B (b + 2) a' G X om om' R Rf hm
  have tw := GlobalTheory.T.matched_theta_q_zero_real_matrix hKP F E σ B (b + 2) a' G X om om' R Rf hm hq
  revert tw
  generalize hRb : b + 2 + a' - (G.p + G.q) = Rb
  generalize hSb : G.p + G.q = Sb
  obtain rfl : Rb = (b + a' - (G₁.p + G₁.q)) + 1 := by omega
  obtain rfl : Sb = (G₁.p + G₁.q) + 1 := by omega
  intro tw
  let A : Fin (b + a' - (G₁.p + G₁.q) + 1) := ⟨b - G₁.p, by omega⟩
  have hfr := fun w => GlobalTheory.T.adapted_real_frame_twisted_coeffs F E σ B (b + 2 + a') (b + a') _ _ 0 (b + 1) _ _ G.W G₁.W H' hcm hm.triple.geo.hW
    hcfg.hH' A w (C w) (hCa w)
  choose ε φ hCa' hεφ using hfr
  obtain ⟨x, hx, ξ, hξ, hco⟩ := tw (fun w => extFrame A (H'.ι.map (B.emb w).1 * C w) (ε w) (φ w)) hCa'
  set C' : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Ix (b + a' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1)) ℂ :=
    fun w => extFrame A (H'.ι.map (B.emb w).1 * C w) (ε w) (φ w) with hC'
  have hιmap : ∀ w, (incM F H'.ι).map (piInf (B.emb w)) = H'.ι.map (B.emb w).1 := fun w =>
    GlobalTheory.ThK.RealK.incM_map H'.ι (B.emb w)

  have hread : ∀ (t : (AE F E)ˣ) (k₁ : UA σ G₁.W.J) (k : UA σ G.W.J) (g : InfinitePlace F → Matrix
      (Ix (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) (Ix (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) ℂ),
      k ∈ KInf σ G.W B.emb → IsLevi H' t k₁ k → GlobalTheory.HwCoef.IsReading B.emb C k₁ g →
      GlobalTheory.HwCoef.IsReading B.emb C' k (fun w => extM A (g w) (piInf (B.emb w) t.1)) := by
    intro t k₁ k g hk hl hg w
    obtain ⟨hε, hφ⟩ := hεφ w t k₁ k hk hl
    refine mul_extFrame A ?_ hε hφ
    have h3 := congrArg (fun M => M.map (piInf (B.emb w))) hl.2.2
    simp only [Matrix.map_mul, hιmap] at h3
    rw [← Matrix.mul_assoc, h3, Matrix.mul_assoc, hg w, Matrix.mul_assoc]
  have hA1 : (b + 2) - G.p = (A : ℕ) + 1 := by simp only [A]; omega
  have hcoefeq : ∀ g : InfinitePlace F → Matrix (Ix (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q))
      (Ix (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) ℂ, GlobalTheory.HwCoef.hwCoef B (b + 2) a' G.p (fun w => extM A (g w) 1) = GlobalTheory.HwCoef.hwCoef B b a' G₁.p g := by
    intro g
    unfold GlobalTheory.HwCoef.hwCoef
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hA1, coef_extM_one]
    congr 1 <;> push_cast <;> omega
  have hpiu : ∀ (t : (AE F E)ˣ) w, piInf (B.emb w) t.1 ≠ 0 := fun t w => (t.isUnit.map (piInf (B.emb w))).ne_zero
  have hcoefD : ∀ (g : InfinitePlace F → Matrix (Ix (b + a' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1))
      (Ix (b + a' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1)) ℂ) (t : (AE F E)ˣ),
      GlobalTheory.HwCoef.hwCoef B (b + 2) a' G.p (fun w => g w * extM A 1 (piInf (B.emb w) t.1)) =
        GlobalTheory.HwCoef.hwCoef B (b + 2) a' G.p g * ∏ w, piInf (B.emb w) t.1 ^ B.mα w := by
    intro g t
    unfold GlobalTheory.HwCoef.hwCoef
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hA1, coef_mul_extM, ← zpow_add₀ (hpiu t w), ← zpow_add₀ (hpiu t w)]
    congr 2
    obtain ⟨r1, hr1⟩ := GlobalTheory.RealLift.even_im_hermitian_sub F E σ B (b + 2) a' G X om om' hm.triple w
    obtain ⟨r2, hr2⟩ := GlobalTheory.T.good_characters_parity F E σ B X (b + 2) a' hm.triple.base hm.triple.chars w
    obtain ⟨r3, hr3⟩ := hm.triple.geo.even
    push_cast
    clear * - hr1 hr2 hr3
    omega
  have hxl := hx
  obtain ⟨f₀, hf₀, hf₀x⟩ := hx
  have hf₀P := fockDeg_le_pol _ _ _ _ hf₀
  have hcoT : ∀ k ∈ KInf σ G.W B.emb, ∀ g, GlobalTheory.HwCoef.IsReading B.emb C' k g →
      ξ (T k x) = GlobalTheory.HwCoef.hwCoef B (b + 2) a' G.p g := by
    intro k hk g hg
    obtain ⟨f₁, hf₁⟩ := hTex k hk f₀
    rw [← hf₀x, ← hTacts k hk f₀ hf₀P f₁ hf₁]
    exact hco k hk g hg f₀ hf₀P hf₀x f₁ hf₁
  have heig : ∀ k ∈ KInf σ G.W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ G₁.W.J) k →
      T k x = (∏ w, piInf (B.emb w) t.1 ^ B.mα w) • x := by
    intro k hk t hl
    have hrk := hread t 1 k (fun _ => 1) hk hl (fun w => by
      change (mat (1 : UA σ G₁.W.J)).map _ * C w = C w * 1
      rw [show mat (1 : UA σ G₁.W.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
        Matrix.mul_one])
    have hv : ∀ k' ∈ KInf σ G.W B.emb, ξ (T k' (T k x - (∏ w, piInf (B.emb w) t.1 ^ B.mα w) • x)) = 0 := by
      intro k' hk'
      obtain ⟨g', hg'⟩ := GlobalTheory.HwCoef.exists_reading B.emb C' (fun w => (hCa' w).1.2) k'
      have h1 := hcoT _ (GlobalTheory.HwCoef.kInf_mul_mem hk' hk) (fun w => g' w * extM A 1 (piInf (B.emb w) t.1))
        (isReading_mul B.emb hg' hrk)
      rw [map_sub, map_smul, map_sub, map_smul, ← hTmul k' hk' k hk, h1, hcoT k' hk' g' hg', hcoefD, smul_eq_mul]
      ring
    let N : Submodule ℂ R.Pi :=
      lowPartInf B G.M R.p ⊓ ⨅ k' : {k' // k' ∈ KInf σ G.W B.emb}, LinearMap.ker (ξ ∘ₗ T k'.1)
    have hmemN : ∀ v, v ∈ N ↔ v ∈ lowPartInf B G.M R.p ∧ ∀ k' ∈ KInf σ G.W B.emb, ξ (T k' v) = 0 := by
      intro v; simp [N, Submodule.mem_iInf]
    rcases hirr N inf_le_left (fun k'' hk'' f hf f₁ hf₁ hpf => by
      rw [hTacts k'' hk'' f hf f₁ hf₁]
      rw [hmemN] at hpf ⊢
      refine ⟨hTlow k'' hk'' _ hpf.1, fun k' hk' => ?_⟩
      rw [← hTmul k' hk' k'' hk'']
      exact hpf.2 _ (GlobalTheory.HwCoef.kInf_mul_mem hk' hk'')) with h | h
    · have hm' : T k x - (∏ w, piInf (B.emb w) t.1 ^ B.mα w) • x ∈ N :=
        (hmemN _).2 ⟨Submodule.sub_mem _ (hTlow k hk x hxl) (Submodule.smul_mem _ _ hxl), hv⟩
      rw [h, Submodule.mem_bot, sub_eq_zero] at hm'
      exact hm'
    · exfalso
      have hm' : x ∈ N := h ▸ hxl
      have := ((hmemN x).1 hm').2 1 GlobalTheory.HwCoef.one_mem_kInf
      rw [hTone, hξ] at this
      exact one_ne_zero this
  have hxtw : x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) := by
    refine Submodule.subset_span ⟨hxl, ?_⟩
    intro k hk t hl f hf f₁ hf₁ hpf
    rw [hTacts k hk f hf f₁ hf₁, hpf, GlobalTheory.T.levi_character_exponent_archimedean F E σ B _ _ _ _ 0 (b + 1) G.W G₁.W H' hcm hm.triple.geo.hW hcfg.hH'
      X.α B.mα hm.triple.chars.expα _ t 1 k hk hl]
    exact heig k hk t hl
  refine ⟨x, hxtw, ξ, hξ, ?_⟩
  intro k₁ hk₁ k hk hl g hg f hf hpf f₁ hf₁
  have hr := hread 1 k₁ k g hk hl hg
  simp only [Units.val_one, map_one] at hr
  rw [← hcoefeq g]
  exact hco k hk _ hr f hf hpf f₁ hf₁

end GlobalTheory.TwCoef
