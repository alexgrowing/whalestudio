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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleRepPairIdentityStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LowTypeMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ops (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
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

end GlobalTheory.LowTypeMap

namespace GlobalTheory.LowTypeMap

theorem exists_lowType_map : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ s : R₁.Pi →ₗ[ℂ] R.Pi,
        (lowPartInf B G₁.M R₁.p).map s ≤ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ∧
        (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ≠ ⊥ → (lowPartInf B G₁.M R₁.p).map s ≠ ⊥) ∧
        ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ k ∈ KInf σ G.W B.emb, IsLevi H' 1 k₁ k →
          ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (1, k₁)) g g₁ →
            R₁.p g ∈ lowPartInf B G₁.M R₁.p →
          ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) f f₁ →
            s (R₁.p g) = R.p f → s (R₁.p g₁) = R.p f₁ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  obtain ⟨T, hTex, hTacts, hTmul, hTone, -⟩ := ops B G X om om' R Rf hm
  obtain ⟨T₁, hT₁ex, hT₁acts, hT₁mul, hT₁one, hT₁low⟩ := ops B G₁ X om₁ om₁' R₁ Rf₁ hm₁
  have hKS := GlobalTheory.TwPartStab.kStabL_twPart hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  obtain ⟨-, -, hirr⟩ := GlobalTheory.T.config_a_theta_local_factor hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  have onto : ∀ v : R.Pi, ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = v := fun v => by
    have hv : v ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hm.real.quot.onto]; trivial
    obtain ⟨f, hf, e⟩ := hv
    exact ⟨f, hf, e⟩
  have stabT : ∀ N : Submodule ℂ R.Pi, KStabL B G.M om R.p G₁.W H' N → ∀ k ∈ KInf σ G.W B.emb,
      ∀ k₁ ∈ KInf σ G₁.W B.emb, IsLevi H' 1 k₁ k → ∀ v ∈ N, T k v ∈ N := by
    intro N hN k hk k₁ hk₁ hl v hv
    obtain ⟨f, hf, rfl⟩ := onto v
    obtain ⟨f₁, h₁⟩ := hTex k hk f
    rw [← hTacts k hk f hf f₁ h₁]
    exact hN k hk k₁ hk₁ hl f hf f₁ h₁ hv
  by_cases htw : twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) = ⊥
  · refine ⟨0, ?_, fun h => absurd htw h, ?_⟩
    · rw [Submodule.map_zero]; exact bot_le
    · intro k₁ hk₁ k hk hl g hg g₁ hg₁ hlow f hf f₁ hf₁ he
      rw [LinearMap.zero_apply] at he ⊢
      rw [hTacts k hk f hf f₁ hf₁, ← he, map_zero]
  · choose C hC hCθ using fun w =>
      GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hm₁.triple.geo.hW.sig w) (hm₁.triple.geo.hW.cartan w)
    have hCa : ∀ w, GlobalTheory.ThK.RealK.IsAdapted B.emb w G₁.W (C w) := fun w => ⟨hC w, hCθ w⟩
    obtain ⟨x, hx, ξ, -, hxco⟩ := GlobalTheory.T.matched_theta_q_zero_real_matrix hKP F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hm₁ hcfg.q1 C hCa
    obtain ⟨y, hy, η, hη, hyco⟩ :=
      GlobalTheory.T.config_a_triple_rep_pair_identity hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ C hCa htw
    let Γ : Submonoid (UA σ G₁.W.J × UA σ G.W.J) :=
      { carrier := {q | q.1 ∈ KInf σ G₁.W B.emb ∧ q.2 ∈ KInf σ G.W B.emb ∧ IsLevi H' 1 q.1 q.2}
        mul_mem' := by
          rintro ⟨k₁, k⟩ ⟨k₁', k'⟩ ⟨h1, h2, hx1, hy1, hι1⟩ ⟨h1', h2', hx1', hy1', hι1'⟩
          have e : mat (k * k') = mat k * mat k' := rfl
          have e₁ : mat (k₁ * k₁') = mat k₁ * mat k₁' := rfl
          simp only [inv_one, Units.val_one, map_one, one_smul] at hx1 hy1 hx1' hy1'
          refine ⟨GlobalTheory.HwCoef.kInf_mul_mem h1 h1', GlobalTheory.HwCoef.kInf_mul_mem h2 h2', ?_, ?_, ?_⟩
          · simp only [inv_one, Units.val_one, one_smul]
            change mat (k * k') *ᵥ _ = _
            rw [e, ← Matrix.mulVec_mulVec, hx1', hx1]
          · simp only [inv_one, Units.val_one, map_one, one_smul]
            change mat (k * k') *ᵥ _ = _
            rw [e, ← Matrix.mulVec_mulVec, hy1', hy1]
          · change mat (k * k') * _ = _ * mat (k₁ * k₁')
            rw [e, e₁, Matrix.mul_assoc, hι1', ← Matrix.mul_assoc, hι1, Matrix.mul_assoc]
        one_mem' := by
          refine ⟨GlobalTheory.HwCoef.one_mem_kInf, GlobalTheory.HwCoef.one_mem_kInf, ?_, ?_, ?_⟩
          · simp only [Units.val_one, one_smul]
            change (1 : Matrix _ _ _) *ᵥ _ = _
            rw [Matrix.one_mulVec]
          · simp only [inv_one, Units.val_one, map_one, one_smul]
            change (1 : Matrix _ _ _) *ᵥ _ = _
            rw [Matrix.one_mulVec]
          · change (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
            rw [Matrix.one_mul, Matrix.mul_one] }
    have hx' := hx
    obtain ⟨f₀, hf₀, hf₀x⟩ := hx'
    have hf₀P := fockDeg_le_pol _ _ _ _ hf₀
    obtain ⟨e₀, he₀, he₀y⟩ := onto y
    obtain ⟨s, hs1, hsxy, hseq⟩ := GlobalTheory.HwCoef.intertwiner_of_coef (Γ := Γ) (fun q => T₁ q.1.1) (fun q => T q.1.2)
      (lowPartInf B G₁.M R₁.p) (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p))
      (fun g h v => hT₁mul _ g.2.1 _ h.2.1 v) (fun v => hT₁one v)
      (fun g h v => hTmul _ g.2.2.1 _ h.2.2.1 v) (fun v => hTone v)
      (fun g v hv => hT₁low _ g.2.1 v hv)
      (fun g v hv => stabT _ hKS _ g.2.2.1 _ g.2.1 g.2.2.2 v hv)
      (fun N hN hst => GlobalTheory.T.lowPart_invariant_submodule_equiv hKP F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hm₁ N hN fun k₁ hk₁ f hf f₁ hf₁ hpf => by
        obtain ⟨k, hk, hl⟩ := GlobalTheory.KLeviReal.exists_kInf_isLevi_one F E σ B _ _ G.W G₁.W H' _ _ _ _ hm.triple.base.cm
          hm.triple.geo.hW hcfg.hH' k₁ hk₁
        rw [hT₁acts k₁ hk₁ f hf f₁ hf₁]
        exact hst ⟨(k₁, k), hk₁, hk, hl⟩ _ hpf)
      (fun N hN hst => hirr N hN fun k hk k₁ hk₁ hl f hf f₁ hf₁ hpf => by
        rw [hTacts k hk f hf f₁ hf₁]
        exact hst ⟨(k₁, k), hk₁, hk, hl⟩ _ hpf)
      hx ξ hy η hη (fun q => by
        obtain ⟨⟨k₁, k⟩, hk₁, hk, hl⟩ := q
        obtain ⟨gr, hgr⟩ := GlobalTheory.HwCoef.exists_reading B.emb C (fun w => (hC w).2) k₁
        obtain ⟨f₁, hf₁⟩ := hT₁ex k₁ hk₁ f₀
        obtain ⟨e₁, he₁⟩ := hTex k hk e₀
        show ξ (T₁ k₁ x) = η (T k y)
        rw [← hf₀x, ← hT₁acts k₁ hk₁ f₀ hf₀P f₁ hf₁, hxco k₁ hk₁ gr hgr f₀ hf₀P hf₀x f₁ hf₁, ← he₀y,
          ← hTacts k hk e₀ he₀ e₁ he₁, hyco k₁ hk₁ k hk hl gr hgr e₀ he₀ he₀y e₁ he₁])
    refine ⟨s, hs1, fun _ hb => ?_, ?_⟩
    · have hm' : y ∈ (lowPartInf B G₁.M R₁.p).map s := ⟨x, hx, hsxy⟩
      rw [hb, Submodule.mem_bot] at hm'
      rw [hm', map_zero] at hη
      exact zero_ne_one hη
    · intro k₁ hk₁ k hk hl g hg g₁ hg₁ hlow f hf f₁ hf₁ he
      rw [hT₁acts k₁ hk₁ g hg g₁ hg₁, hTacts k hk f hf f₁ hf₁, ← he]
      exact hseq ⟨(k₁, k), hk₁, hk, hl⟩ _ hlow

end GlobalTheory.LowTypeMap
