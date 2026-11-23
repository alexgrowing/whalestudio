import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TupSplit
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.AlgebraMapMemIntE
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.EvalVSingleVSame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TrPairGramFE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponent

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cpow_mul_nonneg (x r : ℝ) (hr : 0 ≤ r) (w : ℂ) :
    (((x * r : ℝ)) : ℂ) ^ w = (x : ℂ) ^ w * (r : ℂ) ^ w := by
  rcases hr.lt_or_eq with hr | hr
  · by_cases hx : x = 0
    · subst hx
      by_cases hw : w = 0
      · simp [hw]
      · simp [Complex.zero_cpow hw]
    · have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hxr : ((x * r : ℝ) : ℂ) ≠ 0 := by push_cast; exact mul_ne_zero hx' hr'
      rw [Complex.cpow_def_of_ne_zero hxr, Complex.cpow_def_of_ne_zero hx', Complex.cpow_def_of_ne_zero hr',
        ← Complex.exp_add]
      congr 1
      have : Complex.log ((x * r : ℝ) : ℂ) = Complex.log (x : ℂ) + Complex.log (r : ℂ) := by
        rw [show ((x * r : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by push_cast; ring, Complex.log_ofReal_mul hr hx',
          Complex.ofReal_log hr.le]
        ring
      rw [this]
      ring
  · subst hr
    by_cases hw : w = 0
    · simp [hw]
    · simp [Complex.zero_cpow hw]

theorem cpow_mul_prod {ι : Type} (x : ℝ) (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (w : ℂ) :
    (((x * ∏ i ∈ s, r i : ℝ)) : ℂ) ^ w = (x : ℂ) ^ w * ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have e : x * (r j * ∏ i ∈ s, r i) = (x * ∏ i ∈ s, r i) * r j := by ring
    rw [e, cpow_mul_nonneg _ _ (hr j (Finset.mem_insert_self j s)),
      ih x (fun i hi => hr i (Finset.mem_insert_of_mem hi))]
    ring

theorem self_dual_measure_lattice_one (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hco : IsCO L₁) (h1 : (L₁ : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h2 : (L₂ : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hB : ∀ i j, B i j ∈ intE bs v) :
    nu2 lam L₁ L₂ B = 1 := by
  have hset : {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + B.mulVec y'} = (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      have hy'' : y' ∈ latO bs v := by rw [← h2]; exact hy'
      have hB' : B.mulVec y' ∈ (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
        rw [h1]; exact mulVec_latO σ bs J T v hv B hB y' hy''
      exact L₁.add_mem hy hB'
    · intro hx
      exact ⟨x, hx, 0, L₂.zero_mem, by simp⟩
  have hpos : lam (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ≠ 0 :=
    (hco.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin : lam (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ≠ ⊤ := hco.2.measure_lt_top.ne
  unfold nu2
  rw [hset, ENNReal.div_self hpos hfin]
  rfl

theorem psiT_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ b ∈ UH σ bs n S,
      ψ (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        psiInf F ψ (-trPair (Ainf F) (T.map (inclR (Ainf F)))
          (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) *
        ∏ v ∈ S, psiV F ψ v (-trPair (Fv F v) (T.map (inclR (Fv F v)))
          (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  classical
  obtain ⟨Sψ, hSψ⟩ := psi_split ψ hψ
  have hfin := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  refine ⟨Sψ ∪ hfin.toFinset, fun S hS b hb => ?_⟩
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h)))
  have hcomp : ∀ v, evalV F v (sndA F (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) =
      -trPair (Fv F v) (T.map (inclR (Fv F v))) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    intro v
    have h3 := trPair_T_fE bs ((evalV F v).comp (sndA F)) T (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [AlgHom.comp_apply] at h3
    rw [map_neg, map_neg, h3, hermV_val']
  have hinf : fstA F (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
      -trPair (Ainf F) (T.map (inclR (Ainf F))) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := by
    rw [map_neg, trPair_T_fE bs (fstA F) T, hermInf_val]
    rfl
  have hint : ∀ v, v ∉ S → evalV F v (sndA F (-trPair (AF F) (T.map (inclR (AF F)))
      (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) ∈ v.adicCompletionIntegers F := by
    intro v hv
    rw [hcomp v]
    have hbv : hermV σ v (hermFin σ b) ∈ latH σ bs v n := hb v hv
    exact neg_mem (trPair_int σ bs J T v (hgood v hv) _ _ (fun i j => (hgood v hv).hT i j)
      (herm_entries σ hCM bs J T v (hgood v hv) _ hbv))
  rw [hSψ S (fun v hv => hS (Finset.mem_union_left _ hv)) _ hint, hinf]
  congr 1
  exact Finset.prod_congr rfl fun v _ => by rw [hcomp v]

theorem continuous_locI (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hφ : Continuous φ) :
    Continuous (fun Y => φ Y * psiV F ψ v (trPair (Fv F v) B (gramR (Fv F v) σ J Y))) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hpsi : Continuous (psiV F ψ v) := by
    unfold psiV
    exact hψ.comp ((continuous_const.prodMk continuous_id).comp (GlobalTheory.CompanionTheory.AdelicCharLocal.continuous_singleV F v))
  refine hφ.mul (hpsi.comp ?_)
  unfold trPair
  refine continuous_const.mul (htr.comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  exact continuous_const.mul ((continuous_apply a).comp ((continuous_apply c).comp (hgr n M J)))

theorem jt_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ b ∈ UH σ bs n S,
      jtR (AF F) σ J ψ μ Φ b = jtR (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (hermInf σ b) *
        ∏ v ∈ S, jtR (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (hermV σ v (hermFin σ b)) := by
  classical
  obtain ⟨Sψ, hSψ⟩ := psi_split ψ hψ
  obtain ⟨St, hSt⟩ := tup_split σ hCM ψ hψ M n d J hJ bs μ sdW μi hμi μv hμv
  have hfing := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  have hfinp := Filter.eventually_cofinite.1 pure.2.1
  refine ⟨Sψ ∪ St ∪ hfing.toFinset ∪ hfinp.toFinset, fun S hS b hb => ?_⟩
  have hSψS : Sψ ⊆ S := fun v hv => hS (by simp [hv])
  have hStS : St ⊆ S := fun v hv => hS (by simp [hv])
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (by simp [hfing.mem_toFinset.2 h]))
  have hpv : ∀ v, v ∉ S → Φv v = (latV bs v).indicator 1 := fun v hv => by
    by_contra h
    exact hv (hS (by simp [hfinp.mem_toFinset.2 h]))
  have hbv : ∀ v, v ∉ S → hermV σ v (hermFin σ b) ∈ latH σ bs v n := fun v hv => hb v hv
  let gi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => phiInf θ l fr g P Y *
    psiInf F ψ (trPair (Ainf F) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J Y))
  let gv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ := fun v Y => Φv v Y *
    psiV F ψ v (trPair (Fv F v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y))
  have hmeas : ∀ v ∈ S, AEStronglyMeasurable (gv v) (μv v) := by
    intro v _
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
    exact (continuous_locI σ hCM ψ hψ.1 v J _ (Φv v) (pure.1 v).1.continuous).aestronglyMeasurable
  have key := hSt S hStS gi gv hmeas
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hCM d bs n M).2.2.2.2.2.1
  have hpt : ∀ Y, Φ Y * ψ (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y)) =
      (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, gv v (projV v (projFin X))) Y := by
    intro Y
    by_cases hY : Y ∈ GlobalTheory.CompanionTheory.SW.intOff bs S
    · rw [Set.indicator_of_mem hY]
      have hYv : ∀ v, v ∉ S → projV v (projFin Y) ∈ latV bs v := hY
      have hΦ : Φ Y = phiInf θ l fr g P (projInf Y) * ∏ v ∈ S, Φv v (projV v (projFin Y)) := by
        rw [prod Y, pure.2.2 (projFin Y), finprod_eq_prod_of_mulSupport_subset]
        intro v hv
        by_contra hvS
        apply hv
        show Φv v (projV v (projFin Y)) = 1
        rw [hpv v hvS, Set.indicator_of_mem (hYv v hvS)]
        rfl
      have hc : ∀ v, evalV F v (sndA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y))) =
          trPair (Fv F v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
            (gramR (Fv F v) σ J (projV v (projFin Y))) := by
        intro v
        have h3 := trPair_gram_fE bs σ ((evalV F v).comp (sndA F)) J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) Y
        rw [AlgHom.comp_apply] at h3
        rw [h3, hermV_val', projV_projFin]
      have hi : fstA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y)) =
          trPair (Ainf F) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J (projInf Y)) := by
        rw [trPair_gram_fE bs σ (fstA F) J, hermInf_val, projInf_eq]
        rfl
      have hint : ∀ v, v ∉ S → evalV F v (sndA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
          (gramR (AF F) σ J Y))) ∈ v.adicCompletionIntegers F := by
        intro v hv
        rw [hc v]
        exact trPair_int σ bs J T v (hgood v hv) _ _ (herm_entries σ hCM bs J T v (hgood v hv) _ (hbv v hv))
          (gram_entries σ bs J T v (hgood v hv) _ (hYv v hv))
      rw [hΦ, hSψ S hSψS _ hint, hi]
      simp only [gi, gv, hc]
      rw [Finset.prod_mul_distrib]
      ring
    · rw [Set.indicator_of_notMem hY]
      have hY' : ¬ ∀ v, v ∉ S → projV v (projFin Y) ∈ latV bs v := hY
      push_neg at hY'
      obtain ⟨v, hvS, hYv⟩ := hY'
      have hsupp : (Function.mulSupport fun w => Φv w (projV w (projFin Y))).Finite := by
        refine (hfinp.union (Filter.eventually_cofinite.1 (hlat (projFin Y)))).subset ?_
        intro w hw
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hw
        show Φv w (projV w (projFin Y)) = 1
        rw [hcon.1, Set.indicator_of_mem hcon.2]
        rfl
      rw [prod Y, pure.2.2 (projFin Y), finprod_eq_zero _ v _ hsupp, mul_zero, zero_mul]
      rw [hpv v hvS, Set.indicator_of_notMem hYv]
  unfold jtR
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), key]

theorem whI_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (haar : ∀ v, (lam v).IsAddHaarMeasure) (co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v))
    (std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) (z : ℂ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∀ b ∈ UH σ bs n S,
      whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b =
        whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z (hermInf σ b) *
        ∏ v ∈ S, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z
          (hermV σ v (hermFin σ b)) := by
  classical
  obtain ⟨S1, h1⟩ := jt_split σ hCM M n d J hJ T bs ψ hψ θ l fr g P Φ Φf Φv μ pure prod sdW μi hμi μv hμv
  obtain ⟨S2, h2⟩ := psiT_split σ hCM bs J T ψ hψ
  have hfing := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  have hstd := Filter.eventually_cofinite.1 std
  refine ⟨S1 ∪ S2 ∪ hfing.toFinset ∪ hstd.toFinset, fun S hS b hb => ?_⟩
  have hS1 : S1 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
  have hS2 : S2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_left _ (Finset.mem_union_right _ (hfing.mem_toFinset.2 h))))
  have hL : ∀ v, v ∉ S → (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧
      (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ (hstd.mem_toFinset.2 h)))
  have hbv : ∀ v, v ∉ S → hermV σ v (hermFin σ b) ∈ latH σ bs v n := fun v hv => hb v hv
  have hnu : nuA θ g lam L₁ L₂ (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      nuInf θ g (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        ∏ v ∈ S, nu2 (lam v) (L₁ v) (L₂ v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    unfold nuA
    rw [hermInf_val]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset]
    · exact Finset.prod_congr rfl fun v _ => by rw [hermV_val]
    · intro v hv
      by_contra hvS
      apply hv
      show nu2 (lam v) (L₁ v) (L₂ v) (matV v (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) = 1
      rw [← hermV_val]
      exact self_dual_measure_lattice_one σ bs J T v (hgood v hvS) (lam v) (haar v) (L₁ v) (L₂ v) (co v).1 (hL v hvS).1 (hL v hvS).2 _
        (herm_entries σ hCM bs J T v (hgood v hvS) _ (hbv v hvS))
  unfold whI
  rw [hnu, cpow_mul_prod _ S (fun v => nu2 (lam v) (L₁ v) (L₂ v)
      (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) (fun v _ => ENNReal.toReal_nonneg), h1 S hS1 b hb, h2 S hS2 b hb,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end PositivityTheory.SiegelWeilFormula.GFac

end
