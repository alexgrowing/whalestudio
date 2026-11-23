import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOpenCompactAtInfinity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

namespace GlobalTheory.DefiniteRealZeta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tprod_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (x : ι → V)
    (hx : ∀ i, x i ≠ 0) : PiTensorProduct.tprod ℂ (s := fun _ : ι => V) x ≠ 0 := by
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hx i)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h
  simp [hl] at this

theorem isExp_fix {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : GlobalTheory.RealLift.IsExp L U) {v : V}
    (hv : L v = 0) : U v = v := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (U v - v)).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := h v l
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) = fun n => if n = 0 then l v else 0 := by
    funext n; rcases n with _ | n
    · simp
    · simp [pow_succ, hv]
  rw [e] at a
  exact a.unique (by simpa using hasSum_ite_eq 0 (l v))

open Classical in

theorem sumPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (x : ι → V)
    (L : ι → Module.End ℂ V) (h : ∀ i, L i (x i) = 0) :
    GlobalTheory.RealLift.sumPl (V := fun _ : ι => V) L (PiTensorProduct.tprod ℂ x) = 0 := by
  simp only [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod]
  exact MultilinearMap.map_coord_zero _ i (by simp [h])

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.FockAlg in

theorem exists_eigen {P Q R S : ℕ} {x t : ℚ} {N : GKMod R S} {p : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] N.V}
    (h : IsLift x t N p) (hN : Formalism.MainNotions.SchurIrreducible.IrrGK N) :
    ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, f ≠ 0 ∧ ∀ X, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  obtain ⟨μ, -, v, hv, -⟩ := i_gen P Q R S x t N p h hN.1
  obtain ⟨f, hf⟩ := i_harm P Q R S x t N p h _ v hv
  exact ⟨f, hf.2.2.1, hf.2.1⟩

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.FockAlg Classical in

theorem exists_fixed {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (hinj : Function.Injective Φ) (x : InfinitePlace F → ℚ)
    (hx : ∀ w, ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, f ≠ 0 ∧
      ∀ X, IsKC X → fockAct1 P Q R S X f = ((x w : ℂ) * X.trace) • f) (c : InfinitePlace F → ℂ)
    (hxc : ∀ w, (x w : ℂ) + c w = 0) (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb)
    (hcm : IsCMExt F E σ) (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ)
    (hA : ∀ w, IsFrame ((1 : ℂ) • (incM F Y.J).map (piInf (B.emb w))) (A w)) (hAθ : ∀ w, Y.θ w * A w = A w * Jm P Q)
    (hact : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) :
    ∃ f ∈ M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ k ∈ KInf σ Y B.emb, Acts (evI F) (om (k, 1)) f f := by
  choose f hf0 hf using hx
  refine ⟨Φ (PiTensorProduct.tprod ℂ f), hrange ▸ LinearMap.mem_range_self Φ _,
    fun h => tprod_ne_zero f hf0 (hinj (h.trans (map_zero Φ).symm)), fun k hk => ?_⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := i_kline i_lineex F E σ (Fin n) P Q B.emb (incM F Y.J) 1 A Y.θ hcm hA hAθ k hk.1 hk.2
  have hloc := i_locfin _ _ _ (fun w => locFin_fock1 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  have h1 := (i_actslaws F _ (Φ (PiTensorProduct.tprod ℂ f)) (Φ (U (PiTensorProduct.tprod ℂ f)))
    (Φ (PiTensorProduct.tprod ℂ f))).2.1 _ (map_zero _) (hSA _)
  rw [MonoidHom.comp_apply, hγ1, isExp_fix hU (sumPl_tprod f _ fun w => ?_)] at h1
  · exact h1
  · rw [LinearMap.add_apply, hf w _ (hKC w), LinearMap.smul_apply, Module.End.one_apply, ← add_smul, ← add_mul, hxc,
      zero_mul, zero_smul]

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.FockAlg Classical in

theorem triple_fixed (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    (∃ f ∈ G.M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ k ∈ KInf σ G.V B.emb, Acts (evI F) (om (k, 1)) f f) ∧
    ∃ f ∈ G.M'.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ k ∈ KInf σ G.V' B.emb, Acts (evI F) (om' (k, 1)) f f := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := h
  have hpa : G.p + G.q < a - G.p := by have := hg.eBig; omega
  have hqa : G.p + G.q < a' - G.q := by have := hg.aBig; omega
  have hsum : a + a' - (G.p + G.q) + (G.p + G.q) = a + a' := by omega
  have hnum : ∀ w, Num (a - G.p) G.p G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) (B.mα w - B.mβ w) := fun w =>
    ⟨by omega, rfl, hpa, hqa, by rw [hsum]; exact hg.even, i_parity F E σ B a a' G X om om' ⟨hb, hg, hc, hw, hw'⟩ w,
      by rw [hsum]; exact hg.kappa w⟩
  choose N p p' hp hp' hirr hsc using fun w => onePlace _ _ _ _ _ _ _ (hnum w)
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose A' hA' hAθ' using fun w => i_frameex _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hA1' : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A' w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA' w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A' C := ⟨one_mul _, hA1', hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hP i_derex hfe hvl (i_liescalar hP i_derex hvl)
  have hfst := i_liefirst hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  obtain ⟨Φ', hΦ'⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C hb.cm hb.std fr'
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hr' := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C Φ' hb.cm hb.std fr' hAθ' hCθ hΦ'
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw'
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  obtain ⟨d', hd', hB1'⟩ := hwp'.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hW1' := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d' 1 Complex.I A' C Φ' _ _ _ hb.cm hb.std fr' hΦ' hd' hB1'
    (hasExp_div B.emb hc.expα hc.expβ)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hadm' := fun g => (hwp'.isUSplitting).adm g
  have hx : ∀ w, (((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) = 0 := fun w => by
    push_cast; ring
  have hx' : ∀ w, ((-(((B.mα w - B.mβ w : ℤ) : ℚ) / 2) : ℚ) : ℂ) + (((B.mα w - B.mβ w : ℤ) : ℂ) / 2) = 0 := fun w => by
    push_cast; ring
  exact ⟨exists_fixed B G.M om Φ hΦ.1 _ (fun w => exists_eigen (hp w) (hirr w)) _ hx hr hb.cm A hA1 hAθ hW1 hadm,
    exists_fixed B G.M' om' Φ' hΦ'.1 _ (fun w => exists_eigen (hp' w) (hirr w)) _ hx' hr' hb.cm A' hA1' hAθ' hW1' hadm'⟩

theorem integral_mul_conj_ne_zero {κ : Type} [Fintype κ] [mA : MeasurableSpace (κ → AF F)] [hb : BorelSpace (κ → AF F)]
    (m : Measure (κ → AF F)) (hm : m.IsAddHaarMeasure) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (h0 : Φ ≠ 0) :
    ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m ≠ 0 := by
  obtain ⟨e⟩ := hb
  subst e
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  intro h
  have h1 : MemLp Φ 2 m := GlobalTheory.WeilM.schA_memLp_two F κ m hm Φ hΦ
  have hint : Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) m := by
    have h2 : MemLp (fun x => starRingEnd ℂ (Φ x)) 2 m := h1.star
    haveI : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
    exact MemLp.integrable_mul (p := 2) (q := 2) h1 h2
  have hre : Integrable (fun x => Complex.normSq (Φ x)) m := by
    refine hint.re.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj]
  have hR : ∫ x, Complex.normSq (Φ x) ∂m = 0 := by
    have h3 : ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m = ((∫ x, Complex.normSq (Φ x) ∂m : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      exact Complex.mul_conj (Φ x)
    exact_mod_cast h3.symm.trans h
  have hae : Φ =ᵐ[m] 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (Φ x)) hre).1 hR
    filter_upwards [this] with x hx
    simpa using hx
  exact h0 ((Continuous.ae_eq_iff_eq m (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) continuous_const).1 hae)

theorem inl_mem_stab {B : Base F E} {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J}
    {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂) {k : UA σ X.J} (hk : k ∈ KInf σ X B.emb) : i (k, 1) ∈ K₂ := by
  have e1 : mat (i (k, 1)) = blkMat finSumFinEquiv (mat k) 1 := hD.emb k 1
  refine ((mem_KAt_inf hD.stab).2 ⟨fun u hu => ?_, fun w => ?_⟩).1
  · have h1 := hk.1 u hu
    have e0 : (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = blkMat finSumFinEquiv 1 1 := (blkMat_one _).symm
    rw [e1, e0]
    ext r s
    simp only [blkMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    generalize finSumFinEquiv.symm r = p
    generalize finSumFinEquiv.symm s = q
    rcases p with r | r <;> rcases q with s | s
    · simpa using congrFun (congrFun h1 r) s
    all_goals simp
  · rw [e1, hD.maj, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    show _ * _ = _ * _
    rw [blkMat_mul, blkMat_mul, (hk.2 w).eq, Matrix.mul_one, Matrix.one_mul]

theorem zetaOn_real {B : Base F E} {n d r s : ℕ} {X : Spc F E n} {W : Spc F E d} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hθ : ∀ w, X.θ w = 1 ∨ X.θ w = -1) {M : Model σ X W} (hM : M.IsGood B.ψ) {om : Rep σ X W}
    {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂)
    [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (hm : m.IsAddHaarMeasure) {f : SInf F (Fin n × Fin d)} (hf : ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f f)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _) (hvac : ∀ᶠ v in cofinite, φ v = M.vac v)
    (h0 : pure f φ ≠ 0) (μ : Measure (UAtSub σ X (evI F))) (hμ : μ.IsHaarMeasure) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z := by
  have hK : ∀ g : UAtSub σ X (evI F), g.1 ∈ KInf σ X B.emb := fun g => ⟨g.2, fun w => by
    rcases hθ w with h | h <;> rw [h]
    exacts [Commute.one_right _, Commute.neg_one_right _]⟩
  have hst := GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X
  have hcpt : IsCompact (UAtSub σ X (evI F) : Set (UA σ X.J)) := by
    have := GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf F E σ B n X r s hB hX _ hst
    convert this using 1
    ext g
    exact ⟨fun h => (mem_KAt_inf hst).2 (hK ⟨g, h⟩), fun h => ((mem_KAt_inf hst).1 h).1⟩
  haveI : CompactSpace (UAtSub σ X (evI F)) := isCompact_iff_compactSpace.1 hcpt
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {y | ∀ i, y i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hsch := GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd
  have hrest : Rest (evI F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) := ⟨fun y z hz => GlobalTheory.EvZeroInf.finPart_add φ y z hz, hsch⟩
  have hfix : ∀ g : UAtSub σ X (evI F), om (g.1, 1) (pure f φ) = pure f φ := fun g => hf _ (hK g) _ hrest
  have hc : ∀ g : UAtSub σ X (evI F), coef m om (pure f φ) g.1 = coef m om (pure f φ) 1 := fun g => by
    have h1 := hfix 1
    simp only [Bot.coef, hfix g]
    rw [show ((1 : UAtSub σ X (evI F)) : UA σ X.J) = 1 from rfl] at h1
    rw [h1]
  have hc0 : coef m om (pure f φ) 1 ≠ 0 := by
    rw [← hc 1]
    simp only [Bot.coef, hfix 1]
    exact integral_mul_conj_ne_zero m hm hsch h0
  refine ⟨(μ.real Set.univ : ℝ), ?_, fun s => ?_⟩
  · have h1 : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    have h2 : μ Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
  · have hh : ∀ g : UAtSub σ X (evI F),
        hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g.1, 1)) = 1 := fun g =>
      IsIwasawa.iwAbs_of_mem hD.iwa (inl_mem_stab hD (hK g))
    simp only [zetaOn, hc, hh, div_self hc0]
    simp

theorem real_zeta_small : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → G.p = 0 → G.q = 0 →
    ∀ (X₂ : Spc F E (a' + a')) (i : UA σ G.V'.J × UA σ G.V'.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B G.V' X₂ i K₂ →
    ∀ [MeasurableSpace (Fin a' × Fin (a + a') → AF F)] [BorelSpace (Fin a' × Fin (a + a') → AF F)] (m : Measure (Fin a' × Fin (a + a') → AF F)), m.IsAddHaarMeasure →
    ∃ f ∈ G.M'.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → pure f φ ≠ 0 →
      ∀ μ : Measure (UAtSub σ G.V' (evI F)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om' (pure f φ) i K₂ _ μ s = z := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT hp hq X₂ i K₂ hD _ _ m hm
  obtain ⟨f, hf, hf0, hfix⟩ := (triple_fixed hKP.base hT).2
  have hV := hT.geo.hV'
  refine ⟨f, hf, hf0, fun φ hφ hvac h0 μ hμ => zetaOn_real hT.base hV (fun w => Or.inr ?_) hT.geo.hM' hD m hm hfix φ hφ hvac
    h0 μ hμ⟩
  rw [hq] at hV
  exact GlobalTheory.DefiniteLevel.eq_neg_one_of_hasSig (hV.sig w) (hV.cartan w)

end GlobalTheory.DefiniteRealZeta

end
