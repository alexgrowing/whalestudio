import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
import Development.WeilBound.ThetaLifts.LatticeBasics.DenseG
import Development.WeilBound.ThetaLifts.LatticeBasics.DenseM
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsRealStructure

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace Dense

open GlobalTheory.CompanionTheory.CMAdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_evI (hF : IsTotallyReal F) (a : AF F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
    ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, Subsingleton.elim (evI F a).2 0, map_zero, add_zero,
    Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ _), Matrix.trace]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv IsTotallyReal.isReal) _ _ fun w => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply, Pi.mul_apply,
    Pi.single_eq_same, mul_one, Equiv.subtypeUnivEquiv_apply]
  exact congrArg Complex.re (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (a.1 w.1))

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem ext_trace (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) z).1 w) = piInf τ z + piInf τ (cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]; exact map_zero _
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, ← hx, ← hy]
    exact map_add _ _ _
  | tmul a x =>
    change _ = _ + piInf τ (a ⊗ₜ[F] σ x)
    rw [trace_tmul, piInf_tmul, piInf_tmul, ← mul_add, ← map_add, ← trace_cm h,
      ← piInf_tmul, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul, piInf_tmul, map_one, mul_one,
      Algebra.smul_def, mul_comm]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem trace_symp (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (cA σ) (-1) (incM F X.J) (incM F W.J) u v)) =
      ∑ w, -(2 * (hf (X.J.map (τ w).1) (W.J.map (τ w).1) (u.map (piInf (τ w))) (v.map (piInf (τ w)))).re) := by
  rw [trace_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (v.map (cA σ)).map (piInf (τ w)) = (v.map (piInf (τ w))).map star := by
    ext i j
    exact piInf_cA h _ _
  rw [symp, ext_trace h (τ w), piInf_cA h, neg_one_mul, map_neg, hTens_tr,
    AddMonoidHom.map_trace (piInf (τ w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_map, map_incM, map_incM, e, ← hf]
  simp
  ring

theorem eq_of_coord (M : Model σ X W) {u v : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v)
    (h1 : (fun i => evI F ((M.co.e u).1 i)) = fun i => evI F ((M.co.e v).1 i))
    (h2 : (fun i => evI F ((M.co.e u).2 i)) = fun i => evI F ((M.co.e v).2 i)) : u = v := by
  have a : ∀ {u}, At (evI F) u → ∀ c : AF F, evI F c = 0 → c • M.co.e u = 0 := fun hu c hc => by
    rw [← map_smul, hu c hc, map_zero]
  refine M.co.e.injective (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
  · rw [← lift_evI (z := (M.co.e u).1 i) fun c hc => congrFun (congrArg Prod.fst (a hu c hc)) i,
      ← lift_evI (z := (M.co.e v).1 i) fun c hc => congrFun (congrArg Prod.fst (a hv c hc)) i, congrFun h1 i]
  · rw [← lift_evI (z := (M.co.e u).2 i) fun c hc => congrFun (congrArg Prod.snd (a hu c hc)) i,
      ← lift_evI (z := (M.co.e v).2 i) fun c hc => congrFun (congrArg Prod.snd (a hv c hc)) i, congrFun h2 i]

theorem eq_of_piInf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evI F) u) (hv : At (evI F) v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub, at_entry hu i j c hc, at_entry hv i j c hc, sub_zero]
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

def tr (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
    (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])

theorem tr_apply {κ : Type} [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) :
    tr κ y b = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := linForm_apply b y

theorem exists_isGauss {B : Base F E} (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') :
    ∃ (Q Q' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ)
      (f : SInf F (Fin n × Fin d)), (∀ x, x ≠ 0 → 0 < Q x x) ∧
      (∀ x, f x = 1 * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ))) ∧ M.IsGauss B.ψ B.emb f := by
  have h := hB.cm
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h B.emb M.co.e fun w => cs (X.θ w) (W.θ w)
  have hom : ∀ p q, om (tr (Fin n × Fin d)) p q = ∑ w, -(2 * (hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      ((S p).map (piInf (B.emb w))) ((S q).map (piInf (B.emb w)))).re) := fun p q => by
    have es : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b =>
      map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    rw [← trace_symp h, M.co.form, es, map_sub, om, tr_apply, tr_apply]
    simp only [dotProduct, evI_sum, evI_mul, congrFun (sev _).1, congrFun (sev _).2]
  have hA : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← h.2.2.2, hX.herm]
  have hC : ∀ w, (Complex.I • W.J.map (B.emb w).1)ᴴ = Complex.I • W.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2, hW.skew]
    simp
  obtain ⟨Q, Q', f, pos, hf', hv⟩ := exists_vacuum (tr (F := F) (Fin n × Fin d))
    (fun x y => by simp only [tr_apply, mul_comm]) J
    (fun p q => by
      simp only [hom, sJ, hf_cs (hX.cartan _) (hW.cartan _), Complex.neg_re, ← Finset.sum_neg_distrib, mul_neg])
    (fun p q => by simp only [hom, sJ, hf_cs_cs (hX.cartan _) (hW.cartan _)])
    (fun p hp => by
      obtain ⟨w, hw⟩ : ∃ w, (S p).map (piInf (B.emb w)) ≠ 0 := by
        by_contra hn
        push Not at hn
        have : S p = 0 := eq_of_piInf h B.emb (sAt p) (fun c _ => smul_zero c) fun w => by rw [hn]; simp
        have e := sev p
        rw [this, map_zero] at e
        exact hp (Prod.ext (e.1.symm.trans (funext fun _ => evI_zero)) (e.2.symm.trans (funext fun _ => evI_zero)))
      simp only [hom, sJ]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ _, ?_⟩
      · by_cases hv : (S p).map (piInf (B.emb v)) = 0
        · simp [hv, hf]
        · linarith [hf_neg (hA v) (hC v) (hX.cartan v) (hW.cartan v) hv]
      · linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) hw])
  refine ⟨Q, Q', f, pos, hf', fun _ => 1, fun u u' hu hu' e g g' hg hg' => ?_⟩
  let p := (fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i))
  have e1 : S p = u := eq_of_coord M (sAt p) hu (sev p).1 (sev p).2
  have e2 : u' = S (J p) := eq_of_piInf h B.emb hu' (sAt _) fun w => by
    rw [e, sJ, e1]
    simp [cs]
  rw [actsD_unique M hB.std hu hg, actsD_unique M hB.std hu' hg']
  ext x
  rw [SchwartzMap.smul_apply, dOp_apply, dOp_apply, e2, (sev _).1, (sev _).2]
  exact hv p x

theorem pol_dense {B : Base F E} (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (T : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (hT : ∀ f ∈ M.Pol B.ψ B.emb, T f = 0) : T = 0 := by
  obtain ⟨Q, Q', f, pos, hf', hG⟩ := exists_isGauss M hB hX hW
  exact schwartz_functional_eq_zero_of_dense Q Q' 1 f one_ne_zero pos hf' _ (Submodule.mem_sInf.2 fun _ hN => hN.1 _ hG)
    (fock_mul_linear F E σ n d X W M B.ψ B.emb hB.std) T hT

end Dense

theorem polSch : PolSch := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Dense.pure_mem f ⟨h1, (h2.and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩

theorem schToPol_of (hW : WeilConv) : SchToPol := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp h0 hz Φ hΦ
  obtain ⟨hc, hcont⟩ := hW F E σ B n d X W M χX χW om r s r' s' hp (Or.inr h0)
  have add := fun Φ Ψ => PositivityTheory.ThKG.I_add (Φ := Φ) (Ψ := Ψ) hp.weil fun Φ h => (hc Φ h).1
  funext h
  have key : ∀ Φ ∈ Submodule.span ℂ {Φ | ∃ f φ, Dense.Good φ ∧ Φ = pure (F := F) (κ := Fin n × Fin d) f φ},
      Φ ∈ schA F _ ∧ M.I om Φ h = 0 := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨zero_mem _, congrFun (PositivityTheory.ThKG.I_zero M om) h⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by rw [add _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by rw [PositivityTheory.ThKG.I_smul, hx.2, mul_zero]⟩
    | mem x hx =>
      obtain ⟨f, φ, hφ, rfl⟩ := hx
      have hm : ∀ f, pure f φ ∈ schA F _ := fun f => Dense.pure_mem f hφ
      let T : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
        { toFun := fun f => M.I om (pure f φ) h
          map_add' := fun f g => by
            rw [← add _ _ (hm f) (hm g)]
            exact congrArg (M.I om · h) (funext fun _ => add_mul _ _ _)
          map_smul' := fun c f => by
            rw [RingHom.id_apply, smul_eq_mul, ← PositivityTheory.ThKG.I_smul]
            exact congrArg (M.I om · h) (funext fun _ => mul_assoc _ _ _)
          cont := hcont _ (Dense.pf_mem hφ) h }
      have := Dense.pol_dense M hp.base hp.herm hp.skew T fun g hg => congrFun (hz _ (Submodule.subset_span
        ⟨g, hg, φ, hφ.1, (hφ.2.and hp.good.std).mono fun v hv => hv.1.trans hv.2.symm, rfl⟩)) h
      exact ⟨hm f, DFunLike.congr_fun this f⟩
  exact (key Φ (Dense.schA_le hΦ)).2

end GlobalTheory.ThK.Dbl

end
