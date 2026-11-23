import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import GroundTheory.AutomorphicForms.HermitianExistenceSymbol
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisOfIsQuadraticExtension
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HasseGp

open GlobalTheory.QuadSymbol Matrix
open GroundTheory.Automorphic.Reduction (finEval infEval)
open GroundTheory.Global.AdicLiesOver
open AdeleBaseChange SemiLocal

variable {K : Type} [Field K] [NumberField K]

theorem det_fin (v : Pl) (g : G2) :
    ((IdeleGroup.finiteProj v (GeneralLinearGroup.det g) : (Qv v)ˣ) : Qv v) = ((finAt v g).val).det := by
  rw [IdeleGroup.coe_finiteProj]
  have h := RingHom.map_det (finEval v) (g.val)
  have h2 : (finEval v).mapMatrix g.val = (finAt v g).val := by
    ext a b
    rfl
  rw [h2] at h
  exact h

theorem det_real (g : G2) :
    ((GL2Classical.realPart g).val).det =
      RationalIdeles.realEquiv ((GeneralLinearGroup.det g : (𝔸[ℚ])ˣ) : 𝔸[ℚ]).1 := by
  have h1 := RingHom.map_det ((RationalIdeles.realEquiv : _ →+* ℝ).comp (RingHom.fst _ _)) (g.val)
  have h2 : ((RationalIdeles.realEquiv : _ →+* ℝ).comp (RingHom.fst _ _)).mapMatrix g.val = (GL2Classical.realPart g).val := by
    ext a b
    rfl
  exact (h1.trans (congrArg Matrix.det h2)).symm

theorem pri_eq (β : ℚˣ) : pri β = IdeleGroup.diagonal ℚ β := rfl

section form

variable (e : Module.Basis (Fin 2) ℚ K) (h0 : e 0 = 1) {δ : ℚ} (h1 : e 1 * e 1 = algebraMap ℚ K δ)
include h0 h1

theorem fin_form (v : Pl) (x : (Qv v)ˣ) (a b : Qv v)
    (h : (x : Qv v) = a ^ 2 - (δ : Qv v) * b ^ 2) :
    x ∈ (IdeleNorm.finiteLocalNorm K v).range := by
  letI : Algebra ℚ (Qv v) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  obtain ⟨z, hz⟩ := mem_normGroup_iff.1 ((mem_normGroup_iff_form e h0 h1 (A := Qv v) (x := x)).2
    ⟨a, b, by rw [eq_ratCast (algebraMap ℚ (Qv v)) δ]; exact h⟩)
  exact mem_range_finiteLocalNorm_of_eq_norm K v x z hz.symm

theorem inf_form (v : InfinitePlace ℚ) (x : (v.Completion)ˣ) (a b : v.Completion)
    (h : (x : v.Completion) = a ^ 2 - algebraMap ℚ v.Completion δ * b ^ 2) :
    x ∈ (IdeleNorm.infiniteLocalNorm K v).range := by
  obtain ⟨z, hz⟩ := mem_normGroup_iff.1 ((mem_normGroup_iff_form e h0 h1 (A := v.Completion) (x := x)).2 ⟨a, b, h⟩)
  exact mem_range_infiniteLocalNorm_of_eq_norm K v x z hz.symm

theorem inf_form_of_mem (v : InfinitePlace ℚ) (x : (v.Completion)ˣ)
    (h : x ∈ (IdeleNorm.infiniteLocalNorm K v).range) :
    ∃ a b : v.Completion, (x : v.Completion) = a ^ 2 - algebraMap ℚ v.Completion δ * b ^ 2 := by
  obtain ⟨y, rfl⟩ := h
  obtain ⟨z, hz⟩ := exists_norm_tensor_eq_infiniteLocalNorm K v y
  exact (mem_normGroup_iff_form e h0 h1 (A := v.Completion)).1 (mem_normGroup_iff.2 ⟨z, hz.symm⟩)

theorem isOpen_range (hδ : δ ≠ 0) : IsOpen ((ideleNorm ℚ K).range : Set (IdeleGroup ℚ)) := by
  refine Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (GlobalTheory.QNorm.norm_form_mem_nhds_one ℚ δ hδ) fun a ha => ?_)
  obtain ⟨x, y, hxy⟩ := ha
  refine IdeleNorm.mem_range_ideleNorm_of_forall a (fun v => ?_) (fun v => ?_)
  · refine fin_form e h0 h1 v _ (x.2 v) (y.2 v) ?_
    rw [IdeleGroup.coe_finiteProj]
    have := congrArg (finEval v) hxy
    rw [map_sub, map_mul, map_pow, map_pow] at this
    have e2 : finEval v (algebraMap ℚ _ δ) = (δ : Qv v) :=
      eq_ratCast ((finEval v).comp (algebraMap ℚ _)) δ
    rw [e2] at this
    exact this
  · refine inf_form e h0 h1 v _ (x.1 v) (y.1 v) ?_
    rw [IdeleGroup.coe_infiniteProj]
    have := congrArg (infEval v) hxy
    rw [map_sub, map_mul, map_pow, map_pow] at this
    have e2 : infEval v (algebraMap ℚ _ δ) = algebraMap ℚ v.Completion δ := by
      rw [eq_ratCast (algebraMap ℚ v.Completion) δ]
      exact eq_ratCast ((infEval v).comp (algebraMap ℚ _)) δ
    rw [e2] at this
    exact this

end form

theorem local_unique (v : Pl) (w : PlK K) [h : w.asIdeal.LiesOver v.asIdeal]
    (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) (x : (Qv v)ˣ) :
    x ∈ (IdeleNorm.finiteLocalNorm K v).range ↔
      ∃ t : (Kv K w)ˣ, Algebra.norm (Qv v) (t : Kv K w) = x := by
  classical
  let w0 : SemiLocal.PlacesOver K v := ⟨w, h⟩
  haveI : Subsingleton (SemiLocal.PlacesOver K v) :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y w0, ?_⟩
    rw [IdeleNorm.coe_finiteLocalNorm, Fintype.prod_subsingleton _ w0]
  · rintro ⟨t, ht⟩
    refine ⟨Pi.mulSingle w0 t, Units.ext ?_⟩
    rw [IdeleNorm.finiteLocalNorm_mulSingle, ← ht]
    rfl

theorem local_norm_surjective_at_split_place {F : Type} [Field F] [NumberField F] [Algebra F K] (h2 : Module.finrank F K = 2)
    (v : HeightOneSpectrum (𝓞 F)) (w₁ w₂ : SemiLocal.PlacesOver K v) (hne : w₁ ≠ w₂)
    (x : (v.adicCompletion F)ˣ) : x ∈ (IdeleNorm.finiteLocalNorm K v).range := by
  classical
  have hs : Module.finrank (v.adicCompletion F) (SemiLocal.CompletionsOver K v) = 2 := by
    rw [← (SemiLocal.tensorEquiv K v).toLinearEquiv.finrank_eq, Module.finrank_baseChange, h2]
  have hsum : ∑ w : SemiLocal.PlacesOver K v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion K) = 2 := by
    rw [← hs]
    exact (Module.finrank_pi_fintype (v.adicCompletion F)).symm
  have hpos : ∀ w : SemiLocal.PlacesOver K v, 0 < Module.finrank (v.adicCompletion F) (w.1.adicCompletion K) :=
    fun w => Module.finrank_pos
  have h1 : Module.finrank (v.adicCompletion F) (w₁.1.adicCompletion K) = 1 := by
    have hle : ∑ w ∈ ({w₁, w₂} : Finset _), Module.finrank (v.adicCompletion F) (w.1.adicCompletion K) ≤ 2 := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne] at hle
    have := hpos w₁
    have := hpos w₂
    omega
  refine ⟨Pi.mulSingle w₁ (Units.map (algebraMap (v.adicCompletion F) (w₁.1.adicCompletion K)).toMonoidHom x), Units.ext ?_⟩
  rw [IdeleNorm.finiteLocalNorm_mulSingle]
  show Algebra.norm (v.adicCompletion F) (algebraMap (v.adicCompletion F) (w₁.1.adicCompletion K) x) = x
  rw [Algebra.norm_algebraMap, h1, pow_one]

theorem neg_delta (e : Module.Basis (Fin 2) ℚ K) (h0 : e 0 = 1) {δ : ℚ}
    (h1 : e 1 * e 1 = algebraMap ℚ K δ) (hδ : δ ≠ 0) (hcx : IsTotallyComplex K) : δ < 0 := by
  by_contra hge
  have hpos : 0 < δ := lt_of_le_of_ne (not_lt.1 hge) (Ne.symm hδ)
  let w : InfinitePlace K := Classical.arbitrary _
  let τ : K →+* ℂ := w.embedding
  have hc : τ (e 1) * τ (e 1) = (δ : ℂ) := by
    rw [← map_mul, h1, eq_ratCast (τ.comp (algebraMap ℚ K)) δ |>.symm]
    rfl
  have hposC : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hpos
  have him : (τ (e 1)).im = 0 := by
    have hre := congrArg Complex.re hc
    have himm := congrArg Complex.im hc
    simp only [Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im] at hre himm
    by_contra hne
    have h3 : (τ (e 1)).re = 0 := by
      have : (τ (e 1)).re * (τ (e 1)).im + (τ (e 1)).im * (τ (e 1)).re = 2 * (τ (e 1)).re * (τ (e 1)).im := by ring
      rw [this] at himm
      have h4 : 2 * (τ (e 1)).re * (τ (e 1)).im = 0 := himm
      rcases mul_eq_zero.1 h4 with h5 | h5
      · rcases mul_eq_zero.1 h5 with h6 | h6
        · norm_num at h6
        · exact h6
      · exact absurd h5 hne
    rw [h3] at hre
    nlinarith [mul_self_nonneg (τ (e 1)).im]
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have hx : x = e.repr x 0 • (1 : K) + e.repr x 1 • e 1 := by
      conv_lhs => rw [← e.sum_repr x, Fin.sum_univ_two, h0]
    rw [hx, map_add, map_add]
    have hs : ∀ (q : ℚ) (y : K), τ (q • y) = (q : ℂ) * τ y := fun q y => by
      rw [Algebra.smul_def, map_mul]
      congr 1
      exact eq_ratCast (τ.comp (algebraMap ℚ K)) q
    rw [hs, hs, map_one, mul_one, map_mul, map_ratCast, map_ratCast]
    have : (starRingEnd ℂ) (τ (e 1)) = τ (e 1) := Complex.conj_eq_iff_im.2 him
    rw [this]
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hcx.isComplex w))
    (InfinitePlace.isReal_iff.2 hreal)

theorem inf_iff (e : Module.Basis (Fin 2) ℚ K) (h0 : e 0 = 1) {δ : ℚ}
    (h1 : e 1 * e 1 = algebraMap ℚ K δ) (hneg : δ < 0) (u : Jd) :
    (∀ v, IdeleGroup.infiniteProj v u ∈ (IdeleNorm.infiniteLocalNorm K v).range) ↔
      0 < RationalIdeles.realEquiv (u : 𝔸[ℚ]).1 := by
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal
    (RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ))
  have hf : ∀ x : InfiniteAdeleRing ℚ, RationalIdeles.realEquiv x = f (x default) := fun _ => rfl
  rw [hf]
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := inf_form_of_mem e h0 h1 default _ (h default)
    rw [IdeleGroup.coe_infiniteProj] at hab
    have hne : f ((u : 𝔸[ℚ]).1 default) ≠ 0 := by
      rw [map_ne_zero_iff f f.injective, ← IdeleGroup.coe_infiniteProj]
      exact Units.ne_zero _
    have hδ : f (algebraMap ℚ (default : InfinitePlace ℚ).Completion δ) = (δ : ℝ) := by
      rw [eq_ratCast (algebraMap ℚ (default : InfinitePlace ℚ).Completion) δ, map_ratCast]
    have hv : f ((u : 𝔸[ℚ]).1 default) = (f a) ^ 2 - (δ : ℝ) * (f b) ^ 2 := by
      rw [hab, map_sub, map_mul, map_pow, map_pow, hδ]
    have hδ0 : (δ : ℝ) < 0 := by exact_mod_cast hneg
    have hnn : 0 ≤ f ((u : 𝔸[ℚ]).1 default) := by
      rw [hv]
      nlinarith [sq_nonneg (f a), sq_nonneg (f b)]
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  · intro h v
    obtain rfl : v = default := Subsingleton.elim _ _
    refine inf_form e h0 h1 default _ (f.symm (Real.sqrt (f ((u : 𝔸[ℚ]).1 default)))) 0 ?_
    rw [IdeleGroup.coe_infiniteProj]
    apply f.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_zero, RingEquiv.apply_symm_apply, Real.sq_sqrt h.le]
    simp

theorem plus_iff (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl} (m : LM c v) (hm : m.ok)
    (g : GL (Fin 2) (Qv v)) (x : (Qv v)ˣ) (hx : (x : Qv v) = (g.val).det) :
    m.plus g ↔ x ∈ (IdeleNorm.finiteLocalNorm K v).range := by
  cases m with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    refine iff_of_true trivial (local_norm_surjective_at_split_place h2 v ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ ?_ x)
    intro h
    exact hm.1 (congrArg Subtype.val h)
  | @ns w h σ η Φ =>
    rw [local_unique v w hm.1 x, hx]
    rfl

theorem gpd : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.GPD K := by
  intro K _ _ h2 hcx c M hM
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  obtain ⟨δ, e, hsq, h0, h1⟩ := exists_basis_of_isQuadraticExtension ℚ K
  have hδ0 : δ ≠ 0 := fun h => hsq (h ▸ IsSquare.zero)
  have hneg := neg_delta e h0 h1 hδ0 hcx
  refine ⟨(ideleNorm ℚ K).range, isOpen_range e h0 h1 hδ0, ?_, fun β => ?_⟩
  · ext g
    show ((∀ v, (M v).plus (finAt v g)) ∧ 0 < ((GL2Classical.realPart g).val).det) ↔
      GeneralLinearGroup.det g ∈ (ideleNorm ℚ K).range
    rw [IdeleNorm.mem_range_ideleNorm_iff_forall K, inf_iff e h0 h1 hneg, det_real]
    refine and_congr_left' (forall_congr' fun v => ?_)
    exact plus_iff h2 (M v) (hM.1 v) _ _ (det_fin v g)
  · rw [pri_eq]
    exact (mem_range_norm_iff_diagonal_mem_range_ideleNorm_of_finrank_eq_two h2 β).symm

end GlobalTheory.CompanionTheory.HasseGp
