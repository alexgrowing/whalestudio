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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JmConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterComponentDegreeLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerUpperFixedPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeLeFixedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedPartIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaPolynomialLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharactersParityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtProdForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Classical
open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.KFixIrr

namespace GlobalTheory.LowCoef

theorem sum_le_of_ne_bot {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (x : ι → ℚ) (k k' : ι → ℕ)
    (ek : ∀ w, x w - cPair R S = k w) (ek' : ∀ w, x w + cPair R S = k' w) (m : ℕ)
    (hm : chiPart ι P Q R S x ⊓ degLE ι P Q R S m ≠ ⊥) : ∑ w, (P * k w + Q * k' w) ≤ m := by
  by_contra hlt
  refine hm ((Submodule.eq_bot_iff _).2 fun T hT => ?_)
  refine (Submodule.span_eq_bot.2 ?_).le (GlobalTheory.KFixIrr.mem_span_tprod_chiOne ι P Q R S x m T hT)
  rintro _ ⟨g, hg, hs, rfl⟩
  by_contra h0
  refine hlt (le_trans (Finset.sum_le_sum fun w _ => ?_) hs)
  exact GlobalTheory.FockLowDeg.lowerDeg P Q R S (x w) (k w) (k' w) (ek w) (ek' w) (g w) (hg w)
    fun hw => h0 (MultilinearMap.map_coord_zero _ w hw)

theorem acts_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (g : UA σ Y.J × UA σ W.J) :
    Acts (evI F) (om g) (⇑(0 : SInf F (Fin n × Fin d))) (⇑(0 : SInf F (Fin n × Fin d))) := by
  intro r _
  have h0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by
    funext y; simp [tens]
  rw [h0, map_zero]

theorem exists_low_coef : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 →
    ∀ C : InfinitePlace F → Matrix (Fin (a + a')) (Formalism.BasicNotions.TH.Ix (a + a' - (G.p + G.q)) (G.p + G.q)) ℂ,
      (∀ w, GlobalTheory.ThK.RealK.IsAdapted B.emb w G.W (C w)) →
      ∃ x ∈ lowPartInf B G.M R.p, ∃ ξ : R.Pi →ₗ[ℂ] ℂ, ξ x = 1 ∧
        ∀ k ∈ KInf σ G.W B.emb, ∀ g, GlobalTheory.HwCoef.IsReading B.emb C k g → ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = x →
          ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ →
            ξ (R.p f₁) = GlobalTheory.HwCoef.hwCoef B a a' G.p g := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq0 C hCad
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact (hCad w).1
  have hCθ : ∀ w, G.W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm _ _ := fun w => (hCad w).2
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  have hfst := i_liefirst hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  let c : InfinitePlace F → ℚ := fun w => ((B.mα w - B.mβ w : ℤ) : ℚ) / 2
  have ec : (fun w => -((c w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [c]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((c w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hΦ.1
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have L2 := GlobalTheory.KFixIrr.kFix_iff_mem_chiPart i_actslaws i_lineex (i_kline i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c
    hb.cm hA1 hAθ hinj hW1' hadm
  set m := lowDegInf B G.M R.p with hmdef
  set N := chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
    degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) m with hN
  have key : fixPart B G.M om m = N.map Φ := by
    have hs : {f | f ∈ fockDeg G.M B.ψ B.emb m ∧ IsKFix B om f} = Φ '' (N : Set _) := by
      ext f
      constructor
      · rintro ⟨hf, hfix⟩
        rw [L1 m] at hf
        obtain ⟨T, hT, rfl⟩ := hf
        exact ⟨T, ⟨(L2 T).1 hfix, hT⟩, rfl⟩
      · rintro ⟨T, ⟨h1, h2⟩, rfl⟩
        exact ⟨by rw [L1 m]; exact ⟨T, h2, rfl⟩, (L2 T).2 h1⟩
    rw [fixPart, hs, Submodule.span_image, Submodule.span_eq]
  have hcov := GlobalTheory.LowFixCover.lowPartInf_le_fixPart hKP F E σ B a a' G X om om' R Rf hM
  have hstab := GlobalTheory.IndLine.fixPart_kStabUp hKP F E σ B a a' G X om om' hM.triple m
  have hP := fixPart_le_pol B G.M om m
  have hne : lowPartInf B G.M R.p ≠ ⊥ := by
    apply lowPartInf_ne_bot
    haveI := hM.real.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have hx' : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; trivial
    obtain ⟨f, hf, rfl⟩ := hx'
    exact ⟨f, hf, hx⟩
  have hker : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → R.p f = 0 → R.p f₁ = 0 := fun k hk f hf f₁ h1 h0 => by
    have := hM.real.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero om' _) (by rw [h0, map_zero])
    rwa [map_zero] at this
  have hdisj : fixPart B G.M om m ⊓ LinearMap.ker R.p = ⊥ := by
    rcases GlobalTheory.T.fixed_part_irreducible hKP F E σ B a a' G X om om' hM.triple m (GlobalTheory.T.low_degree_le_fixed_degree hKP F E σ B a a' G X om om' R Rf hM)
      (fixPart B G.M om m ⊓ LinearMap.ker R.p) inf_le_left
      (fun k hk f hf f₁ h1 => ⟨hstab k hk f hf.1 f₁ h1, hker k hk f (hP hf.1) f₁ h1 hf.2⟩) with h | h
    · exact h
    · exfalso
      refine hne (eq_bot_iff.2 (hcov.trans ?_))
      rintro _ ⟨f, hf, rfl⟩
      rw [← h] at hf
      exact hf.2
  have hNne : N ≠ ⊥ := fun h => by
    refine hne (eq_bot_iff.2 (hcov.trans ?_))
    rw [key, h, Submodule.map_bot, Submodule.map_bot]
  have hqinj : LinearMap.ker ((R.p ∘ₗ Φ) ∘ₗ N.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro T hT
    have h1 : Φ T ∈ fixPart B G.M om m ⊓ LinearMap.ker R.p := ⟨key ▸ Submodule.mem_map_of_mem T.2, hT⟩
    rw [hdisj, Submodule.mem_bot, ← map_zero Φ] at h1
    exact Subtype.ext (hinj h1)
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective _ hqinj
  have hPR : a - G.p ≤ a + a' - (G.p + G.q) := by have := hg.aBig; omega
  have hQS : G.p ≤ G.p + G.q := Nat.le_add_right _ _
  have hnum : ∀ w, ∃ k k' : ℕ, c w - cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k ∧
      c w + cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k' ∧
      (B.mα w - B.mβ w - ((a + a' : ℕ) : ℤ) + 2 * (G.p : ℤ)) / 2 = k ∧
      (((((a : ℤ) - 2 * (G.p : ℤ) + B.mβ w) / 2 : ℤ)) : ℂ) = (((a - G.p : ℕ) : ℂ) - G.p) / 2 + (B.mβ w : ℂ) / 2 ∧
      ((((B.mα w + (a' : ℤ)) / 2 : ℤ)) : ℂ) = k' + ((G.p : ℂ) - (a - G.p : ℕ)) / 2 + (B.mβ w : ℂ) / 2 := by
    intro w
    have hk := hg.kappa w
    obtain ⟨j, hj⟩ := i_parity F E σ B a a' G X om om' hM.triple w
    obtain ⟨l, hl⟩ := GlobalTheory.T.good_characters_parity F E σ B X a a' hb hc w
    obtain ⟨i, hi⟩ := hg.even
    have h1 := hg.eBig
    have h2 := hg.aBig
    have hle : G.p + G.q ≤ a + a' := by omega
    have hpa : G.p ≤ a := by omega
    have hR : ((a + a' - (G.p + G.q) : ℕ) : ℚ) = (i : ℚ) + i - ((G.p : ℚ) + G.q) := by
      rw [Nat.cast_sub hle, hi]; push_cast; ring
    have e1 : (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℤ) = j - i + (G.p + G.q : ℕ) := Int.toNat_of_nonneg (by omega)
    have e2 : (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℤ) = j + i - (G.p + G.q : ℕ) := Int.toNat_of_nonneg (by omega)
    have hβ : B.mβ w = 2 * (l - j) - a' := by omega
    have ha : (a : ℂ) = 2 * i - a' := by
      have : (a : ℤ) = 2 * i - a' := by omega
      exact_mod_cast this
    refine ⟨(j - i + (G.p + G.q : ℕ)).toNat, (j + i - (G.p + G.q : ℕ)).toNat, ?_, ?_, by omega, ?_, ?_⟩
    · rw [show (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j - i + (G.p + G.q : ℕ) : ℤ) : ℚ) from by exact_mod_cast e1]
      simp only [c, cPair, hj, hR]; push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℚ) from by exact_mod_cast e2]
      simp only [c, cPair, hj, hR]; push_cast; ring
    · rw [show ((a : ℤ) - 2 * (G.p : ℤ) + B.mβ w) / 2 = i - G.p + l - j - a' by omega, hβ, Nat.cast_sub hpa, ha]
      push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℂ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℂ) from by exact_mod_cast e2,
        show (B.mα w + (a' : ℤ)) / 2 = l by omega, hβ, Nat.cast_sub hpa, ha, hq0]
      push_cast; ring
  choose k k' ek ek' h₁ h₂ h₃ using hnum
  have hS : G.p + G.q = G.p := by omega
  let T₀ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    PiTensorProduct.tprod ℂ fun w => LowMinor.wit _ _ _ _ hPR hQS (k w) (k' w)
  have hT₀ : T₀ ∈ N := by
    refine ⟨?_, tprod_mem_degLE _ (le_trans (Finset.sum_le_sum fun w _ =>
      (LowMinor.wit_isHomogeneous hPR hQS (k w) (k' w)).totalDegree_le) (sum_le_of_ne_bot c k k' ek ek' m hNne))⟩
    rw [SetLike.mem_coe, mem_chiPart]
    intro w Z hZ
    rw [GlobalTheory.TensIrr.atPl_tprod, LowMinor.fockAct1_wit hPR hQS _ _ _ (ek w) (ek' w) Z hZ, MultilinearMap.map_update_smul,
      Function.update_eq_self]
  let ℓ := GlobalTheory.TensIrr.prodForm (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q))
    fun _ => GlobalTheory.MinorCoef.evZ (GlobalTheory.MinorCoef.base _ _ _ _)
  have hξ : ∀ T ∈ N, (ℓ ∘ₗ N.subtype ∘ₗ s) (R.p (Φ T)) = ℓ T := fun T hT => by
    have := LinearMap.congr_fun hs ⟨T, hT⟩
    change s (R.p (Φ T)) = ⟨T, hT⟩ at this
    rw [LinearMap.comp_apply, LinearMap.comp_apply, this]; rfl
  refine ⟨R.p (Φ T₀), Submodule.mem_map_of_mem (by rw [L1 m]; exact Submodule.mem_map_of_mem hT₀.2), ℓ ∘ₗ N.subtype ∘ₗ s,
    ?_, fun κ hκ g hgr f hf hfx f₁ hf₁ => ?_⟩
  · rw [hξ _ hT₀]
    exact GlobalTheory.MinorCoef.prodForm_wit hS hPR hQS k k'
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    i_kline i_lineex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ κ hκ.1 hκ.2
  obtain ⟨U, hU, hAc⟩ := GlobalTheory.FockBottom.exp_of_gen hW2 hadm hγ hgen hKC
  rw [hγ1] at hAc
  have hgY : ∀ w, g w = NormedSpace.exp (Yg w) := fun w => by
    obtain ⟨C', hC'⟩ := (hC1 w).2
    have hL := GlobalTheory.FockKStab.frame_inv (hC1 w) hC'
    have e := hgen 1 w
    rw [hγ1, one_smul] at e
    have e' : C w * g w = C w * NormedSpace.exp (Yg w) := (hgr w).symm.trans e
    have := congrArg (C' * ·) e'
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  have h0 := hker κ hκ (Φ (T - T₀)) (hr ▸ LinearMap.mem_range_self Φ _) _ (hAc (T - T₀)) (by rw [map_sub, map_sub, hfx, sub_self])
  rw [map_sub, map_sub, map_sub, sub_eq_zero] at h0
  have hUN : U T₀ ∈ N := by
    have h1 := hstab κ hκ (Φ T₀) (key ▸ Submodule.mem_map_of_mem hT₀) _ (hAc T₀)
    rw [key] at h1
    obtain ⟨T', hT', e⟩ := h1
    exact hinj e ▸ hT'
  rw [GlobalTheory.FockBottom.acts_unique hf₁ (hAc T), h0, hξ _ hUN, GlobalTheory.HwCoef.hwCoef]
  simp only [hgY]
  exact GlobalTheory.MinorCoef.prodForm_exp_wit hS hPR hQS k k' hKC _ _ _ _ h₁ h₂ h₃ hU

end GlobalTheory.LowCoef

end
