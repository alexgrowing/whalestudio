import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_cmb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  have e : d.cmb c i j = ∑ k, c (i, j, k) • (Algebra.TensorProduct.basis (AF F) d.bs) k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  show (Algebra.TensorProduct.basis (AF F) d.bs).repr (d.cmb c i j) l = c (i, j, l)
  rw [e, Module.Basis.repr_sum_self]
theorem detIm_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) :
    ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
      ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  haveI : IsTotallyComplex E := hcm.2.1
  set τ : E →+* ℂ := (d.B.emb w).1 with hτ
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
    intro f
    have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
    have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    have e4 := RingHom.congr_fun e3 f
    rw [ComplexEmbedding.conjugate_coe_eq] at e4
    rw [e1]
    exact Complex.conj_eq_iff_im.mp e4
  have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
      τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
    intro e
    conv_lhs => rw [← d.bs.sum_repr e]
    simp [Fin.sum_univ_two, Algebra.smul_def, map_add, map_mul]
  obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    rw [InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (hne x)
  intro hD
  apply he
  have h1 := hexp 1
  have h2 := hexp e
  set p := τ (algebraMap F E (d.bs.repr 1 0)) with hp
  set q := τ (algebraMap F E (d.bs.repr 1 1)) with hq
  set p' := τ (algebraMap F E (d.bs.repr e 0)) with hp'
  set q' := τ (algebraMap F E (d.bs.repr e 1)) with hq'
  have ip : p.im = 0 := hreal _
  have iq : q.im = 0 := hreal _
  have ip' : p'.im = 0 := hreal _
  have iq' : q'.im = 0 := hreal _
  rw [map_one] at h1
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2im := congrArg Complex.im h2
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
    ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
  linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
    (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
def realLinearCoordinates (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) :
    (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
    ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
  map_add' r s := by
    funext w a j
    simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
  map_smul' c r := by
    funext w a j
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
    conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
theorem realLinearCoordinates_injective (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr0
  have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
    intro w
    let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
    have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
      ext a j
      have h := congrFun (congrFun (congrFun hr0 w) a) j
      have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
      rw [star_eq_zero] at h'
      rw [Matrix.mul_apply]
      exact h'
    have h2 : Z = 0 := by
      have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [e, h1, Matrix.mul_zero]
    intro i j
    exact congrFun (congrFun h2 i) j
  funext k
  obtain ⟨i, j, l⟩ := k
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have h := hz v.1 i j
    rw [Fin.sum_univ_two] at h
    have hi := real_indep (_root_.PositivityTheory.SiegelWeilFormula.KFock.detIm_ne_k d v.1) h
    have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
    rw [ev] at hi
    fin_cases l
    · exact hi.1
    · exact hi.2
  · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))
theorem archEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
      ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
        L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
    simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
    ring
  have hinj := _root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates_injective d R hr
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨(LinearEquiv.ofBijective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
  funext a j
  show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
      ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
    star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
  rw [Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  rfl
end PositivityTheory.SiegelWeilFormula.KFock
end
end
