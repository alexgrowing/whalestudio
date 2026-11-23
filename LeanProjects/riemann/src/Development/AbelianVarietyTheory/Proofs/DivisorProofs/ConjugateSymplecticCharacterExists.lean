import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.HalfCsd

open Formalism.L2.Host (HChar infDiag upF etaInf)

theorem eta_infDiag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : Fˣ) :
    Circle.toUnits (η (infDiag a)) = ∏ w, etaInf F w a := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hcm.2.2.1 }
  have := hcm.1
  have := hcm.2.1
  obtain ⟨s, δ, b, -, hδ, h0, hb, h1⟩ := exists_conj_basis (F := F) (E := E) hcm.2.2.1
  have hneg : ∀ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ < 0 := fun w => by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : E →+* ℂ := ComplexEmbedding.lift E w.embedding
    have hτ : ∀ x : F, τ (algebraMap F E x) = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply E w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add, map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  have hv := GlobalTheory.HeckeBridge.coe_infDiag (E := F) a
  have e : GlobalTheory.IdeleNormChar.normSign E (infDiag a) =
      ∏ w : InfinitePlace F, GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F a w) := by
    change (∏ᶠ u : HeightOneSpectrum (𝓞 F), GlobalTheory.QuadSymbol.eta F E _ (GlobalTheory.IdeleNormChar.finComp (infDiag a) u)) *
      ∏ u : InfinitePlace F, GlobalTheory.QuadSymbol.eta F E _ (GlobalTheory.IdeleNormChar.infComp (infDiag a) u) = _
    rw [finprod_eq_one_of_forall_eq_one fun u => ?_, one_mul]
    · refine Finset.prod_congr rfl fun w _ => congrArg _ (Units.ext ?_)
      exact congrArg (GlobalTheory.IdeleNormChar.infEval w) hv
    · rw [show GlobalTheory.IdeleNormChar.finComp (infDiag a) u = 1 from
        Units.ext (congrArg (GlobalTheory.IdeleNormChar.finEval u) hv)]
      exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (one_mem _)
  rw [hη.eq_normSign, MonoidHom.comp_apply, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := IsTotallyReal.isReal w
  rw [GlobalTheory.QuadSymbol.eta_infinite_real b h0 (δ := Units.mk0 δ hδ) h1 a hw, etaInf,
    ← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  split_ifs with h
  · rw [GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 ?_]
    · exact Units.ext (congrArg (fun z : Circle => (z : ℂ)) (if_neg (by decide) :
        (if (-1 : ℤˣ) = 1 then (1 : Circle) else -1) = -1))
    · rintro ⟨x, y, hxy⟩
      have h4 := hneg w
      change _ = x ^ 2 - InfinitePlace.embedding_of_isReal hw δ * y ^ 2 at hxy
      nlinarith [sq_nonneg x, sq_nonneg y]
  · rw [GlobalTheory.HilbertRecip.hs_eq_one_iff.2 ?_, map_one, map_one]
    exact ⟨Real.sqrt _, 0, by rw [Real.sq_sqrt (not_lt.1 h)]; simp⟩

theorem exists_hchar_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (c : E ≃+* E) (hc : ∀ x, σ x = c x) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) :
    ∃ H : HChar E, H.IsUnitary ∧ (∀ u, H.1 (finId E u) * H.1 (finId E (Units.map (conjFin c).toMonoidHom u)) = 1) ∧
      (∀ k : Eˣ, H.inf k * H.inf (Units.map c.toMonoidHom k) = 1) ∧
      ∀ a : Fˣ, H.inf (upF F a) = Circle.toUnits (η (infDiag a)) := by
  obtain ⟨χ, hχ, hres⟩ := GlobalTheory.CMHeckeEta.exists_hecke_of_eta F E σ hcm η hη
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      exact Prod.ext (hj k).symm (hfin k).symm))
  let H : HChar E := ⟨Circle.toUnits.comp (χ.comp u), GlobalTheory.CMHeckeEta.continuous_toUnits.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  have hsi : ∀ y, infTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (infTens F E y) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hsf : ∀ y, finTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (finTens F E y) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have key : ∀ (x x' : Neutral.B1.Ideles E) (k : E), (x : AdeleRing (𝓞 E) E).1 = algebraMap E _ k →
      (x' : AdeleRing (𝓞 E) E).1 = algebraMap E _ (c k) →
      (x' : AdeleRing (𝓞 E) E).2 = conjFin c (x : AdeleRing (𝓞 E) E).2 → H.1 x * H.1 x' = 1 := fun x x' k h1 h2 h3 => by
    have e1 : Φ (u x : AF F ⊗[F] E) = (x : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [hΦ] at e1
    have e2 : infTens F E (u x : AF F ⊗[F] E) = (1 : Ainf F) ⊗ₜ[F] k :=
      j.injective ((congrArg Prod.fst e1).trans (h1.trans (hj k).symm))
    have e3 : (u x' : AF F ⊗[F] E) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (u x : AF F ⊗[F] E) := Φ.symm_apply_eq.2 (by
      rw [hΦ, hsi, hsf, e2, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR σ c hc]
      refine Prod.ext (h2.trans ?_) (h3.trans (congrArg (conjFin c) (congrArg Prod.snd e1).symm))
      rw [← hc]
      exact (hj (σ k)).symm)
    have e4 : u x * u x' = ideleMap F E (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (u x)) :=
      Units.ext (by rw [Units.val_mul, e3]; exact (GlobalTheory.Doubling.algebraMap_norm_eq hcm _).symm)
    change Circle.toUnits (χ (u x)) * Circle.toUnits (χ (u x')) = 1
    rw [← map_mul, ← map_mul, e4, hres, hη.2.2.1, map_one]
  have hf1 : ∀ y : (FiniteAdeleRing (𝓞 E) E)ˣ, (finId E y : AdeleRing (𝓞 E) E).1 = 1 := fun y => by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  have hf2 : ∀ y : (FiniteAdeleRing (𝓞 E) E)ˣ, (finId E y : AdeleRing (𝓞 E) E).2 = y := fun y => by
    change (1 : FiniteAdeleRing (𝓞 E) E) - 1 + y = y
    simp
  refine ⟨H, fun x => Circle.norm_coe (χ (u x)), fun y => key _ _ 1 ?_ ?_ ?_, fun k => key (infDiag k) (infDiag _) k ?_ ?_ ?_,
    fun a => ?_⟩
  · rw [hf1, map_one]
  · rw [hf1, map_one, map_one]
  · rw [hf2, hf2]; rfl
  · rw [GlobalTheory.HeckeBridge.coe_infDiag]
  · rw [GlobalTheory.HeckeBridge.coe_infDiag]; rfl
  · rw [GlobalTheory.HeckeBridge.coe_infDiag, GlobalTheory.HeckeBridge.coe_infDiag]; exact (map_one _).symm
  · have e : u (infDiag (upF F a)) = ideleMap F E (infDiag a) := Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, GlobalTheory.HeckeBridge.coe_infDiag]
      have hv := GlobalTheory.HeckeBridge.coe_infDiag (E := F) a
      have h1 : infTens F E (ideleMap F E (infDiag a) : AF F ⊗[F] E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E a := by
        change (infDiag a : AdeleRing (𝓞 F) F).1 ⊗ₜ[F] (1 : E) = _
        rw [hv, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          ← Algebra.algebraMap_eq_smul_one]
      have h2 : finTens F E (ideleMap F E (infDiag a) : AF F ⊗[F] E) = 1 := by
        change (infDiag a : AdeleRing (𝓞 F) F).2 ⊗ₜ[F] (1 : E) = _
        rw [hv]; rfl
      rw [h1, h2, hj, map_one]
      rfl))
    change Circle.toUnits (χ (u (infDiag (upF F a)))) = _
    rw [e, hres]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCsd_of_norms (H : HChar E)
    (h1 : ∀ u, H.1 (finId E u) * H.1 (finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u)) = 1)
    (h2 : ∀ k : Eˣ, H.inf k * H.inf (Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k) = 1) :
    (CG.ofChar H).IsCsd := by
  have h3 : ∀ y : (Cinf E)ˣ, chiInf H y * chiInf H (Units.map (starRingEnd (Cinf E)).toMonoidHom y) = 1 := fun y =>
    InfType.denseRange_units.induction_on
      (p := fun y : (Cinf E)ˣ => chiInf H y * chiInf H (Units.map (starRingEnd (Cinf E)).toMonoidHom y) = 1) y
      (isClosed_eq ((continuous_chiInf H).mul ((continuous_chiInf H).comp (Continuous.units_map _ continuous_star)))
        continuous_const) fun k => by
      have h := h2 k
      rw [HChar.inf, MonoidHom.comp_apply, MonoidHom.comp_apply, InfType.infDiag_eq, InfType.infDiag_eq] at h
      have e : Units.map (starRingEnd (Cinf E)).toMonoidHom (Units.map (InfType.diagInf E).toMonoidHom k) =
          Units.map (InfType.diagInf E).toMonoidHom (Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k) :=
        Units.ext (pInf_complexConj (k : E)).symm
      rw [e]
      exact h
  refine (CG.isCsd_ofChar H).2 ((CG.thetaInv_one_iff H).2 ⟨fun u => ?_, fun z => ?_⟩)
  · rw [map_inv, map_inv]
    exact (eq_inv_of_mul_eq_one_left (h1 u)).symm
  · have h4 : ∀ t : ℝ, Complex.exp (t * dchi H (z + star z)) = 1 := fun t => by
      have h5 := h3 (expU (t • z))
      have e : Units.map (starRingEnd (Cinf E)).toMonoidHom (expU (t • z)) = expU (t • star z) :=
        Units.ext (funext fun w => by
          change starRingEnd ℂ (Complex.exp (t • z w)) = Complex.exp (t • star (z w))
          rw [← Complex.exp_conj]
          simp)
      rw [e, ← map_mul, ← expU_add, ← smul_add] at h5
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h5, Units.val_one]
    have h5 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi H (z + star z))) (dchi H (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi H (z + star z))).cexp
    rw [funext h4] at h5
    have h6 := h5.unique (hasDerivAt_const _ _)
    rw [map_add] at h6
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h6).symm

theorem exists_neg_at (w₀ : InfinitePlace E) : ∃ (a : (maximalRealSubfield E)ˣ) (ρ : InfinitePlace E → ℝ),
    (∀ w : InfinitePlace E, w.embedding (algebraMap (maximalRealSubfield E) E a) = ρ w) ∧ ρ w₀ < 0 ∧
      ∀ w, w ≠ w₀ → 0 < ρ w := by
  classical
  have hU : IsOpen ({x : Cinf E | (x w₀).re < 0} ∩ ⋂ w ∈ ({w₀}ᶜ : Set (InfinitePlace E)), {x : Cinf E | 0 < (x w).re}) :=
    (isOpen_lt (by fun_prop) continuous_const).inter
      ((Set.toFinite _).isOpen_biInter fun w _ => isOpen_lt continuous_const (by fun_prop))
  obtain ⟨k, hk1, hk2⟩ := (InfType.denseRange_diagInf (E := E)).exists_mem_open hU
    ⟨fun w => if w = w₀ then -1 else 1, by simp, Set.mem_iInter₂.2 fun w hw => by
      have : w ≠ w₀ := hw
      simp [this]⟩
  have hd : ∀ w, InfType.diagInf E k w = w.embedding k := fun w => pInf_algebraMap k w
  have hm : k + IsCMField.complexConj E k ∈ maximalRealSubfield E :=
    (IsCMField.complexConj_eq_self_iff E _).1 (by rw [map_add, IsCMField.complexConj_apply_apply, add_comm])
  have he : ∀ w : InfinitePlace E, w.embedding (k + IsCMField.complexConj E k) = ((2 * (w.embedding k).re : ℝ) : ℂ) :=
    fun w => by rw [map_add, IsCMField.complexEmbedding_complexConj, Complex.add_conj]
  have hn : (w₀.embedding k).re < 0 := hd w₀ ▸ hk1
  refine ⟨Units.mk0 ⟨_, hm⟩ fun h => ?_, fun w => 2 * (w.embedding k).re, he, mul_neg_of_pos_of_neg two_pos hn, fun w hw => ?_⟩
  · have h1 := he w₀
    rw [show k + IsCMField.complexConj E k = 0 from congrArg Subtype.val h, map_zero] at h1
    have h2 : (2 * (w₀.embedding k).re : ℝ) = 0 := by exact_mod_cast h1.symm
    linarith
  · have h1 : 0 < (InfType.diagInf E k w).re := Set.mem_iInter₂.1 hk2 w hw
    rw [hd] at h1
    positivity

theorem expo_half (H : HChar E) (hH : (CG.ofChar H).IsCsd)
    (hs : ∀ a : (maximalRealSubfield E)ˣ, H.inf (upF _ a) = ∏ w, etaInf _ w a) (τ : E →+* ℂ) :
    ∃ k : ℤ, expo H τ = (k : ℂ) + 1 / 2 := by
  classical
  obtain ⟨a, ρ, ha, h0, h1⟩ := exists_neg_at (InfinitePlace.mk τ)
  have hre : ∀ w : InfinitePlace E, ((IsCMField.equivInfinitePlace E w).embedding a).re = ρ w := fun w => by
    have e : IsCMField.equivInfinitePlace E w = InfinitePlace.mk (w.embedding.comp (algebraMap _ E)) := by
      rw [IsCMField.equivInfinitePlace_apply, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    rw [e]
    rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
    · rw [h, RingHom.comp_apply, ha, Complex.ofReal_re]
    · rw [h, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ha, Complex.conj_ofReal, Complex.ofReal_re]
  have h2 : H.inf (upF _ a) = -1 := by
    rw [hs, ← (IsCMField.equivInfinitePlace E).prod_comp, Finset.prod_eq_single (InfinitePlace.mk τ)
      (fun w _ hw => by rw [etaInf, hre, if_neg (h1 w hw).le.not_gt]) (by simp), etaInf, hre, if_pos h0]
  let r : Cinf E := fun w => (Real.log |ρ w| : ℝ)
  have hr : dchi H r = 0 := by
    have h := ((CG.thetaInv_one_iff H).1 ((CG.isCsd_ofChar H).1 hH)).2 r
    rw [show star r = r from funext fun w => Complex.conj_ofReal _, map_neg] at h
    linear_combination (-1 / 2 : ℂ) * h
  have e : Units.map (InfType.diagInf E).toMonoidHom (upF _ a) = expU r * expU (atEmb τ (Real.pi * Complex.I)) :=
    Units.ext (funext fun w => by
      change InfType.diagInf E (algebraMap (maximalRealSubfield E) E a) w =
        Complex.exp (Real.log |ρ w| : ℝ) * Complex.exp (atEmb τ (Real.pi * Complex.I) w)
      rw [show InfType.diagInf E _ w = _ from pInf_algebraMap _ w, ha, ← Complex.ofReal_exp]
      by_cases hw : w = InfinitePlace.mk τ
      · subst hw
        rw [Real.exp_log (abs_pos.2 h0.ne), abs_of_neg h0, atEmb, Pi.single_eq_same]
        split_ifs
        · simp
        · rw [Complex.exp_conj]; simp
      · rw [Real.exp_log (abs_pos.2 (h1 w hw).ne'), abs_of_pos (h1 w hw), atEmb, Pi.single_eq_of_ne hw]
        simp)
  rw [HChar.inf, MonoidHom.comp_apply, InfType.infDiag_eq, e] at h2
  have h3 := congrArg Units.val h2
  change ((chiInf H _ : ℂˣ) : ℂ) = -1 at h3
  rw [map_mul, Units.val_mul, chiInf_expU, hr, Complex.exp_zero, one_mul, chiInf_expU_atEmb, CG.expo_conj_of_isCsd hH,
    ← Complex.exp_pi_mul_I, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨n, hn⟩ := h3
  refine ⟨n, mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn
  linear_combination hn

theorem exists_unitary_csd_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ η : Formalism.L2.Host.HChar E,
    η.IsUnitary ∧ (CG.ofChar η).IsCsd ∧ ∀ τ : E →+* ℂ, ∃ k : ℤ, expo η τ = (k : ℂ) + 1 / 2 := by
  intro E _ _ _
  have hcm : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨η, hη, -⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo (maximalRealSubfield E) E hcm.2.2.1
  have hη' : IsEta (maximalRealSubfield E) E η := hη
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_hchar_norm hcm (IsCMField.complexConj E).toRingEquiv (fun _ => rfl) hη'
  have h5 := isCsd_of_norms H h2 h3
  exact ⟨H, h1, h5, expo_half H h5 fun a => (h4 a).trans (eta_infDiag hcm hη' a)⟩

end GlobalTheory.HalfCsd
