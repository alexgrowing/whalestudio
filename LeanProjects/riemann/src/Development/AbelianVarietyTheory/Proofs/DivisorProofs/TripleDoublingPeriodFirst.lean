import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOpenCompactAtInfinity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqOfIntegralsEq

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

namespace GlobalTheory.ThK.BotReal

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem commute_of_definite {n r s : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hs : HasSig M r s) (hc : IsCartan M θ)
    (h : r = 0 ∨ s = 0) (Y : Matrix (Fin n) (Fin n) ℂ) : Commute Y θ := by
  obtain ⟨A, ⟨-, A', hA'⟩, hθ⟩ := i_frameex _ _ _ _ _ hs hc
  have e : θ = A * Jm r s * A' := by rw [← hθ, Matrix.mul_assoc, hA', Matrix.mul_one]
  rcases h with rfl | rfl
  · have : Jm 0 s = -1 := by
      ext (i | i) (j | j)
      · exact i.elim0
      · exact i.elim0
      · exact j.elim0
      simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
    rw [e, this, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hA']
    exact (Commute.one_right Y).neg_right
  · have : Jm r 0 = 1 := by
      ext (i | i) (j | j)
      · simp [Jm, Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0
    rw [e, this, Matrix.mul_one, hA']
    exact Commute.one_right Y

theorem integral_mul_conj_ne_zero {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    (μ : Measure (κ → AF F)) (hH : μ.IsAddHaarMeasure) {d : (κ → AF F) → ℂ} (hd : d ∈ schA F κ) (h0 : d ≠ 0) :
    ∫ x, d x * starRingEnd ℂ (d x) ∂μ ≠ 0 := by
  intro h
  have hb := BorelSpace.measurable_eq (α := κ → AF F)
  subst hb
  letI : MeasurableSpace (κ → AF F) := borel _
  have h1 : MemLp d 2 μ := GlobalTheory.WeilM.schA_memLp_two F κ μ hH d hd
  have hre : Integrable (fun x => Complex.normSq (d x)) μ := by
    refine (h1.integrable_norm_pow two_ne_zero).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.normSq_eq_norm_sq]
  have hR : ∫ x, Complex.normSq (d x) ∂μ = 0 := by
    have h3 : ∫ x, d x * starRingEnd ℂ (d x) ∂μ = ((∫ x, Complex.normSq (d x) ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      exact Complex.mul_conj (d x)
    exact_mod_cast h3.symm.trans h
  have hae : d =ᵐ[μ] 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (d x)) hre).1 hR
    filter_upwards [this] with x hx
    simpa using hx
  exact h0 ((Continuous.ae_eq_iff_eq μ (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hd) continuous_const).1 hae)

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_KInf {B : Base F E} {r s : ℕ} (hX : X.IsHerm σ B r s) (h : r = 0 ∨ s = 0) {g : UA σ X.J}
    (hg : g ∈ UAt σ X (evI F)) : g ∈ KInf σ X B.emb :=
  ⟨hg, fun w => commute_of_definite (hX.sig w) (hX.cartan w) h _⟩

theorem compactSpace_real {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (h : r = 0 ∨ s = 0) :
    CompactSpace (UAtSub σ X (evI F)) := by
  have hK := GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X
  have hc := GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf F E σ B n X r s hB hX _ hK
  have e : (KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F) : Set (UA σ X.J)) = UAtSub σ X (evI F) := by
    ext g
    exact ⟨fun hg => hg.2, fun hg => (mem_KAt_inf hK).2 (mem_KInf hX h hg)⟩
  rw [e] at hc
  exact isCompact_iff_compactSpace.1 hc

theorem emb_mem {B : Base F E} {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)}
    (hD : IsDbl B X X₂ i K₂) {g : UA σ X.J} (hg : g ∈ KInf σ X B.emb) : i (g, 1) ∈ K₂ := by
  refine ((mem_KAt_inf hD.stab).2 ⟨fun u hu => ?_, fun w => ?_⟩).1
  · have h1 := hg.1 u hu
    rw [hD.emb, GlobalTheory.StabHaar.mat_one]
    ext a b
    obtain ⟨a | a, rfl⟩ := (finSumFinEquiv (m := n) (n := n)).surjective a <;>
    obtain ⟨b | b, rfl⟩ := (finSumFinEquiv (m := n) (n := n)).surjective b
    · simpa [blkMat, Matrix.one_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right] using congrFun (congrFun h1 a) b
    all_goals simp [blkMat, Matrix.one_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  · rw [hD.emb, hD.maj, blkMat_map _ _ (map_zero _), GlobalTheory.StabHaar.mat_one, Commute, SemiconjBy, blkMat_mul, blkMat_mul,
      (hg.2 w).eq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]

theorem zetaOn_of_fixed {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (h : r = 0 ∨ s = 0)
    (M : Model σ X W) (hM : M.IsGood B.ψ) (om : Rep σ X W)
    {X₂ : Spc F E (n + n)} {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂)
    [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (hm : m.IsAddHaarMeasure) (f : SInf F (Fin n × Fin d)) (hf : ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f f)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _) (hcof : ∀ᶠ v in cofinite, φ v = M.vac v)
    (h0 : pure f φ ≠ 0) (μ : Measure (UAtSub σ X (evI F))) (hμ : μ.IsHaarMeasure) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z := by
  haveI := compactSpace_real hB hX h
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {y | ∀ i, y i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hcof.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hsch := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hrest : Rest (evI F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) := ⟨fun y z hz => GlobalTheory.EvZeroInf.finPart_add φ y z hz, hsch⟩
  have hfix : ∀ g ∈ UAt σ X (evI F), om (g, 1) (pure f φ) = pure f φ := fun g hg => hf g (mem_KInf hX h hg) _ hrest
  have hc : ∀ g ∈ UAt σ X (evI F), coef m om (pure f φ) g = ∫ x, pure f φ x * starRingEnd ℂ (pure f φ x) ∂m :=
    fun g hg => by rw [Bot.coef, hfix g hg]
  have hne := integral_mul_conj_ne_zero m hm hsch h0
  refine ⟨(μ.real Set.univ : ℝ), ?_, fun s => ?_⟩
  · have : μ.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos μ Set.univ_nonempty).ne', isCompact_univ.measure_lt_top.ne⟩
    exact_mod_cast this
  · have hh : ∀ g : UAtSub σ X (evI F),
        hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g.1, 1)) = 1 := fun g => by
      have := hD.iwa.hgtOf_mul 1 (emb_mem hD (mem_KInf hX h g.2))
      simpa using this
    have e : ∀ g : UAtSub σ X (evI F), coef m om (pure f φ) g.1 / coef m om (pure f φ) 1 = 1 := fun g => by
      rw [hc _ g.2, hc _ (UAtSub σ X (evI F)).one_mem, div_self hne]
    simp [zetaOn, hh, e]

theorem exists_eigen {P Q R S : ℕ} {x : ℚ} (h : HasForm P Q R S x) :
    ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, f ≠ 0 ∧ ∀ Y, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f := by
  obtain ⟨M, pr, hM, hMn⟩ := i_quot P Q R S _ 0 h
  obtain ⟨μ, -, v, hv, -⟩ := i_gen _ _ _ _ _ _ M pr hM hMn
  obtain ⟨f, -, h1, h2⟩ := i_harm _ _ _ _ _ _ M pr hM _ v hv
  exact ⟨f, h2.1, h1⟩

theorem isExp_fixed {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U) {v : V} (hv : L v = 0) :
    U v = v := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (U v - v)).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) = fun n => if n = 0 then l v else 0 := by
    funext n; rcases n with _ | n
    · simp
    · simp [pow_succ, hv]
  have a := hU v l
  rw [e] at a
  exact a.unique (by simpa using hasSum_ite_eq 0 (l v))

theorem tprod_ne_zero {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (f : ι → V) (hf : ∀ i, f i ≠ 0) :
    PiTensorProduct.tprod ℂ f ≠ 0 := by
  choose l hl using fun i => Module.Projective.exists_dual_ne_zero ℂ (hf i)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h
  simp only [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hl i) this

theorem exists_fixed {P Q R S : ℕ} (B : Base F E) (M : Model σ X W) (om : Rep σ X W)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (hΦ : Function.Injective Φ)
    (x : InfinitePlace F → ℚ) (hx : ∀ w, HasForm P Q R S (x w)) (c : InfinitePlace F → ℂ)
    (hxc : ∀ w, (x w : ℂ) + c w = 0) (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb)
    (hcm : IsCMExt F E σ) (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ)
    (hA : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)) (hAθ : ∀ w, X.θ w * A w = A w * Jm P Q)
    (hact : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) :
    ∃ f ∈ M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f f := by
  choose f hf0 hf using fun w => exists_eigen (hx w)
  refine ⟨Φ (PiTensorProduct.tprod ℂ f), hrange ▸ LinearMap.mem_range_self Φ _,
    fun h => tprod_ne_zero f hf0 (hΦ (h.trans (map_zero Φ).symm)), fun k hk => ?_⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := i_kline i_lineex F E σ (Fin n) P Q B.emb (incM F X.J) 1 A X.θ hcm hA hAθ k hk.1 hk.2
  have hloc := i_locfin _ _ _ (fun w => locFin_fock1 P Q R S (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  have h1 := (i_actslaws F _ (Φ (PiTensorProduct.tprod ℂ f)) (Φ (U (PiTensorProduct.tprod ℂ f))) 0).2.1 _ (map_zero _) (hSA _)
  rw [MonoidHom.comp_apply, hγ1, isExp_fixed hU] at h1
  · exact h1
  unfold sumPl
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [atPl, PiTensorProduct.map_tprod]
  refine MultilinearMap.map_coord_zero _ w ?_
  simp only [Function.update_self, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [hf w _ (hKC w), ← add_smul, ← add_mul, hxc, zero_mul, zero_smul]

theorem exists_fixed_big (hP : GlobalTheory.FunPr.Hypotheses₂) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') :
    ∃ f ∈ G.M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ k ∈ KInf σ G.V B.emb, Acts (evI F) (om (k, 1)) f f := by
  have hpar := i_parity F E σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, hw'⟩ := h
  have hpa : G.p + G.q < a - G.p := by have := hg.eBig; omega
  have hqa : G.p + G.q < a' - G.q := by have := hg.aBig; omega
  have hF : ∀ w, HasForm (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) (((B.mα w - B.mβ w : ℤ) : ℚ) / 2) := fun w => by
    obtain ⟨m, hm⟩ := hg.even
    obtain ⟨k0, hk0⟩ := hpar w
    have hlt := hg.kappa w
    generalize hR : a + a' - (G.p + G.q) = R
    generalize hS : G.p + G.q = S at *
    have hk : (0 : ℤ) < k0 - m + S := by omega
    have hk' : (0 : ℤ) < k0 + m - S := by omega
    have ec : cPair R S = (m : ℚ) - S := by
      unfold cPair
      have : (R : ℚ) + S = m + m := by exact_mod_cast (by omega : R + S = m + m)
      linarith
    have ek : (((B.mα w - B.mβ w : ℤ) : ℚ) / 2) = k0 := by rw [hk0]; push_cast; ring
    exact i_formex _ _ R S _ (k0 - m + S).toNat (k0 + m - S).toNat (by omega) (by omega) (by omega) (by omega)
      (by rw [ec, ek]; rw [show (((k0 - m + S : ℤ).toNat : ℕ) : ℚ) = ((k0 - m + S : ℤ) : ℚ) by
            exact_mod_cast Int.toNat_of_nonneg hk.le]; push_cast; ring)
      (by rw [ec, ek]; rw [show (((k0 + m - S : ℤ).toNat : ℕ) : ℚ) = ((k0 + m - S : ℤ) : ℚ) by
            exact_mod_cast Int.toNat_of_nonneg hk'.le]; push_cast; ring)
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hfst := i_liefirst (i_liesecond hP i_derex hfe hvl (i_liescalar hP i_derex hvl))
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hx : ∀ w, (((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ) + (((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) = 0 := fun w => by
    push_cast; ring
  exact exists_fixed B G.M om Φ hΦ.1 _ hF _ hx hr hb.cm A hA1 hAθ hW1 hadm

theorem zetaOn_real_const : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → G.p = 0 → G.q = 0 →
    ∀ (X₂ : Spc F E (a + a)) (i : UA σ G.V.J × UA σ G.V.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B G.V X₂ i K₂ →
    ∀ [MeasurableSpace (Fin a × Fin (a + a') → AF F)] [BorelSpace (Fin a × Fin (a + a') → AF F)] (m : Measure (Fin a × Fin (a + a') → AF F)), m.IsAddHaarMeasure →
    ∃ f ∈ G.M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → pure f φ ≠ 0 →
      ∀ μ : Measure (UAtSub σ G.V (evI F)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' h hp _ X₂ i K₂ hD _ _ m hm
  obtain ⟨f, hf, h0, hfix⟩ := exists_fixed_big hP.base B G X om om' h
  exact ⟨f, hf, h0, fun φ hSB hcof hne μ hμ =>
    zetaOn_of_fixed h.base h.geo.hV (Or.inr hp) G.M h.geo.hM om hD m hm f hfix φ hSB hcof hne μ hμ⟩

end GlobalTheory.ThK.BotReal

end
