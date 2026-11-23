import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gen_coord (R : Type) [CommRing R] [Algebra F R] (α β : E →ₗ[F] F) (ξ : E) (h : ∀ e, e = α e • (1 : E) + β e • ξ) :
    ∃ a b : R ⊗[F] E →ₗ[R] R, ∀ z, z = a z ⊗ₜ[F] (1 : E) + b z ⊗ₜ[F] ξ := by
  let r := (TensorProduct.AlgebraTensorModule.rid F R R).toLinearMap
  refine ⟨r ∘ₗ α.baseChange _, r ∘ₗ β.baseChange _, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [r, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.rid_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, ← h]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul]
    conv_lhs => rw [hx, hy]
    abel

theorem gen_parts (R S : Type) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (z : (R × S) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F R S) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F R S) (AlgHom.id F E) z = 0) : z = 0 := by
  have : ∀ z : (R × S) ⊗[F] E, z =
      LinearMap.rTensor E (LinearMap.inl F R S) (Algebra.TensorProduct.map (AlgHom.fst F R S) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F R S) (Algebra.TensorProduct.map (AlgHom.snd F R S) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      conv_lhs => rw [hx, hy]
      abel
  rw [this z, h1, h2, map_zero, map_zero, add_zero]

end Gen

theorem embedding_xi_zero_ne_zero (D : D7) : D.host.xi0 ≠ 0 := by
  intro h
  have := xi_zero_im_pos D (D.eTau.symm 1)
  rw [h, map_zero] at this
  simp at this

theorem exists_coord (D : D7) : ∃ α β : D.host.E →ₗ[D.host.F] D.host.F,
    ∀ e, e = α e • (1 : D.host.E) + β e • D.host.xi0 := by
  have li : LinearIndependent D.host.F ![(1 : D.host.E), D.host.xi0] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    have h1 : star D.host.xi0 = D.host.xi0 :=
      (D.sp.cm.fixed _).2 ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
    rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg] at h1
    exact embedding_xi_zero_ne_zero D (by linear_combination (-1 / 2 : D.host.E) * h1)
  let b := basisOfLinearIndependentOfCardEqFinrank li (by rw [D.sp.cm.deg2]; simp)
  refine ⟨b.coord 0, b.coord 1, fun e => ?_⟩
  have := b.sum_repr e
  simp only [Fin.sum_univ_two, b, coe_basisOfLinearIndependentOfCardEqFinrank] at this
  exact this.symm

instance modTop (D : D7) : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

theorem exists_coordA (D : D7) : ∃ α β : AE D →ₗ[AF D.host.F] AF D.host.F, Continuous α ∧ Continuous β ∧
    ∀ z, z = α z ⊗ₜ[D.host.F] (1 : D.host.E) + β z ⊗ₜ[D.host.F] D.host.xi0 := by
  obtain ⟨α, β, h⟩ := exists_coord D
  obtain ⟨a, b, hab⟩ := gen_coord (AF D.host.F) α β _ h
  exact ⟨a, b, IsModuleTopology.continuous_of_linearMap _, IsModuleTopology.continuous_of_linearMap _, hab⟩

theorem isReal (D : D7) (v : InfinitePlace D.host.F) : v.IsReal :=
  haveI := D.sp.cm.totReal
  IsTotallyReal.isReal v

def reAt (D : D7) : Ainf D.host.F →+ (InfinitePlace D.host.F → ℝ) where
  toFun x v := InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal D v) (x v)
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

theorem continuous_reAt (D : D7) : Continuous (reAt D) :=
  continuous_pi fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (isReal D v)).continuous.comp (continuous_apply v)

theorem realAd_eq (D : D7) (s : InfinitePlace D.host.F → ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D s = pairA D.host.F
      (fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal D v)).symm (s v)) 0 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd
  congr 1
  refine (RingEquiv.symm_apply_eq _).2 ?_
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal D v)).apply_symm_apply (s v)).symm
  · exact absurd (isReal D v.1) (InfinitePlace.not_isReal_iff_isComplex.2 v.2)

theorem realAd_reAt (D : D7) (x : Ainf D.host.F) : GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D (reAt D x) = pairA D.host.F x 0 := by
  rw [realAd_eq]
  congr 1
  funext v
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal D v)).symm_apply_apply (x v)

theorem realAd_add (D : D7) (s t : InfinitePlace D.host.F → ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D (s + t) = GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D s + GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D t := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd
  refine Prod.ext ?_ (add_zero _).symm
  change _ = _ + _
  simp only [pairA]
  rw [← map_add, Prod.mk_add_mk, add_zero]
  rfl

theorem continuous_realAd (D : D7) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D) := by
  have : GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D = _ := funext (realAd_eq D)
  rw [this]
  exact Continuous.prodMk (continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal D v)).symm.continuous.comp (continuous_apply v))
    continuous_const

def realPtHom (D : D7) : (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ) →+ AE D :=
  AddMonoidHom.mk' (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D) fun p q => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt, Prod.fst_add, Prod.snd_add, realAd_add, TensorProduct.add_tmul]
    abel

theorem continuous_tmul (D : D7) (e : D.host.E) : Continuous fun a : AF D.host.F => (a ⊗ₜ[D.host.F] e : AE D) := by
  have : (fun a : AF D.host.F => (a ⊗ₜ[D.host.F] e : AE D)) = fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this]
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) _
  exact Continuous.smul (f := fun a : AF D.host.F => a)
    (g := fun _ : AF D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)) continuous_id continuous_const

theorem continuous_realPt (D : D7) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D) :=
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  ((continuous_tmul D 1).comp ((continuous_realAd D).comp continuous_fst)).add
    ((continuous_tmul D _).comp ((continuous_realAd D).comp continuous_snd))

theorem finPart_realPt (D : D7) (p) : finPart D (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D p) = 0 := by
  have : ∀ s e, finPart D (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realAd D s ⊗ₜ[D.host.F] e) = 0 := fun s e =>
    TensorProduct.zero_tmul _ e
  rw [GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt, RingHom.map_add, this, this, add_zero]

theorem parts_zero (D : D7) (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  gen_parts (Ainf D.host.F) (Af D.host.F) z h1 h2

theorem exists_co (D : D7) : ∃ co : AE D →+ (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ),
    Continuous co ∧ (∀ z, infPart D (z - GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z)) = 0) ∧
      ∀ z, finPart D z = 0 → GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z) = z := by
  obtain ⟨α, β, hα, hβ, h⟩ := exists_coordA D
  let r : AF D.host.F →+ (InfinitePlace D.host.F → ℝ) := (reAt D).comp (AddMonoidHom.fst _ _)
  have hr : Continuous r := (continuous_reAt D).comp continuous_fst
  let co := (r.comp α.toAddMonoidHom).prod (r.comp β.toAddMonoidHom)
  have k : ∀ z, infPart D (z - GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z)) = 0 := by
    intro z
    have e : GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.realPt D (co z) = pairA D.host.F (α z).1 0 ⊗ₜ[D.host.F] (1 : D.host.E) +
        pairA D.host.F (β z).1 0 ⊗ₜ[D.host.F] D.host.xi0 := by
      rw [← realAd_reAt, ← realAd_reAt]
      rfl
    rw [RingHom.map_sub, e, sub_eq_zero]
    conv_lhs => rw [h z]
    rw [RingHom.map_add, RingHom.map_add]
    rfl
  refine ⟨co, (hr.comp hα).prodMk (hr.comp hβ), k, fun z hz => ?_⟩
  exact (sub_eq_zero.1 (parts_zero D _ (k z) (by rw [RingHom.map_sub, hz, finPart_realPt, sub_zero]))).symm

def plF (D : D7) (ρ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E))

theorem emb_mk (D : D7) (φ : D.host.F →+* ℂ) : (InfinitePlace.mk φ).embedding = φ :=
  haveI := D.sp.cm.totReal
  InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)

theorem plF_bijective (D : D7) : Function.Bijective (plF D) := by
  constructor
  · intro ρ ρ' h
    have h1 : (tauE D ρ).comp (algebraMap D.host.F D.host.E) = (tauE D ρ').comp (algebraMap D.host.F D.host.E) := by
      rw [← emb_mk D (RingHom.comp _ _), ← emb_mk D ((tauE D ρ').comp _)]
      exact congrArg InfinitePlace.embedding h
    have h2 : tauE D ρ D.host.xi0 = tauE D ρ' D.host.xi0 := by
      unfold Host.xi0
      simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD]
    obtain ⟨α, β, hc⟩ := exists_coord D
    have h3 : tauE D ρ = tauE D ρ' := by
      refine RingHom.ext fun e => ?_
      rw [hc e, Algebra.smul_def, Algebra.smul_def]
      simp only [map_add, map_mul, map_one, h2]
      rw [show tauE D ρ (algebraMap _ _ (α e)) = tauE D ρ' (algebraMap _ _ (α e)) from DFunLike.congr_fun h1 _,
        show tauE D ρ (algebraMap _ _ (β e)) = tauE D ρ' (algebraMap _ _ (β e)) from DFunLike.congr_fun h1 _]
    exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h3))
  · intro v
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v
    have key : ∀ τ : D.host.E →+* ℂ, InfinitePlace.mk τ = w →
        τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) → ∃ ρ, plF D ρ = v := by
      intro τ h1 h2
      obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
      refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h2⟩, ?_⟩
      rw [← hw, ← h1]
      unfold plF tauE
      rw [Equiv.apply_symm_apply]
      rfl
    have hsq : w.embedding D.host.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
      have h1 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
        rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        simp
      have h2 : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
        apply D.host.φ₀.injective
        rw [map_pow, h0, h1, map_neg, map_natCast]
      rw [h1, ← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact key _ (InfinitePlace.mk_embedding w) h
    · refine key (ComplexEmbedding.conjugate w.embedding) (by rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]) ?_
      rw [ComplexEmbedding.conjugate_coe_eq, h]
      simp

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_inf_val (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E))
    (θ : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (x : Ainf F) :
    θ (x ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (x w) := by
  have key : (fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))) =
      fun a : Ainf F => InfinitePlace.Completion.extensionEmbedding w (a w) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h.2
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)) ?_
    funext y
    have e : (algebraMap F (Ainf F) y) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E y) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    show θ (algebraMap F (Ainf F) y ⊗ₜ[F] (1 : E)) =
      InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) y w)
    rw [e, h.1, InfiniteAdeleRing.algebraMap_apply]
    exact ((InfinitePlace.Completion.extensionEmbedding_coe w _).trans (DFunLike.congr_fun hw y)).symm
  exact congrFun key x

theorem gen_inf_exists (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E)) :
    ∃ θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  let _ : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : Ainf F →ₐ[F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x =>
        (InfinitePlace.Completion.extensionEmbedding_coe w _).trans (DFunLike.congr_fun hw x) }
  let g : E →ₐ[F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

end Gen

theorem exists_infFam (D : D7) : ∃ θ, IsInfFam (D := D) θ := by
  choose θ hθ using fun ρ => gen_inf_exists (tauE D ρ) (plF D ρ) (emb_mk D _)
  exact ⟨θ, hθ⟩

theorem sum_infFam (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (x : Ainf D.host.F) : ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  push_cast
  refine Fintype.sum_bijective _ (plF_bijective D) _ _ fun ρ => ?_
  have hv := isReal D (plF D ρ)
  rw [gen_inf_val (tauE D ρ) (plF D ρ) (emb_mk D _) _ (hθ ρ), InfinitePlace.mult_isReal ⟨_, hv⟩,
    ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Complex.ofReal_re]
  simp only [Nat.cast_one, one_mul]

end GlobalTheory.DualPairCompare

end
