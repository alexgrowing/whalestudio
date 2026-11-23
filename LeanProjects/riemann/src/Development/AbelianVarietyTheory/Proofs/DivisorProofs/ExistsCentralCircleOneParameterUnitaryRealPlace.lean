import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.CentralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def mk (x : mixedEmbedding.mixedSpace F) (y : Af F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, y)

theorem mk_add (x x' : mixedEmbedding.mixedSpace F) (y y' : Af F) : mk F x y + mk F x' y' = mk F (x + x') (y + y') :=
  Prod.ext (map_add _ x x').symm rfl

theorem mk_mul (x x' : mixedEmbedding.mixedSpace F) (y y' : Af F) : mk F x y * mk F x' y' = mk F (x * x') (y * y') :=
  Prod.ext (map_mul _ x x').symm rfl

theorem mk_sub (x x' : mixedEmbedding.mixedSpace F) (y y' : Af F) : mk F x y - mk F x' y' = mk F (x - x') (y - y') :=
  Prod.ext (map_sub _ x x').symm rfl

theorem mk_one : mk F 1 1 = 1 := Prod.ext (map_one _) rfl

theorem mk_zero : mk F 0 0 = 0 := Prod.ext (map_zero _) rfl

theorem mk_neg (x : mixedEmbedding.mixedSpace F) (y : Af F) : -mk F x y = mk F (-x) (-y) :=
  Prod.ext (map_neg _ x).symm rfl

theorem mul_mk_zero (a : AF F) (x : mixedEmbedding.mixedSpace F) :
    a * mk F x 0 = mk F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * x) 0 := by
  refine Prod.ext ?_ (mul_zero _)
  exact (by rw [map_mul, RingEquiv.symm_apply_apply] : (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * x) = a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x).symm

theorem mk_fst (x : mixedEmbedding.mixedSpace F) (y : Af F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (mk F x y).1 = x :=
  RingEquiv.apply_symm_apply _ x

theorem continuous_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_mk {f : ℝ → mixedEmbedding.mixedSpace F} (hf : Continuous f) (y : Af F) :
    Continuous fun t => mk F (f t) y :=
  (continuous_symm.comp hf).prodMk continuous_const

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (hw : w.IsReal) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = ((InfiniteAdeleRing.ringEquiv_mixedSpace F a.1).1 ⟨w, hw⟩ : ℂ) * τ.1 e := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 e = _
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  rfl

theorem exists_anti (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (τ : E →+* ℂ) :
    ∃ θ : E, σ θ = -θ ∧ (τ θ).re = 0 ∧ (τ θ).im ≠ 0 ∧ ∃ p : F, θ * θ = algebraMap F E p := by
  haveI := hσ.2.1
  have hnr : ∃ x, star (τ x) ≠ τ x := by
    by_contra h
    push_neg at h
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact h x
  obtain ⟨x, hx⟩ := hnr
  have hconj := hσ.2.2.2 τ
  set θ := x - σ x with hθ
  have hσθ : σ θ = -θ := by
    apply τ.injective
    rw [hconj, hθ, map_sub, map_neg, map_sub, hconj, star_sub, star_star]
    ring
  have hre : (τ θ).re = 0 := by rw [hθ, map_sub, hconj]; simp
  have him : (τ θ).im ≠ 0 := by
    rw [hθ, map_sub, hconj]
    intro h0
    apply hx
    apply Complex.ext <;> simp at h0 ⊢ <;> linarith
  have hθ0 : θ ≠ 0 := fun h => him (by rw [h, map_zero, Complex.zero_im])
  have hA := (algebraMap F E).injective
  have hind : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h2
    have h3 : algebraMap F E (2 * s) = 0 := by rw [map_mul, map_ofNat]; linear_combination hst + h2
    have hs : s = 0 := by
      have := hA (h3.trans (map_zero _).symm)
      simpa using this
    subst hs
    rw [map_zero, zero_add, mul_eq_zero] at hst
    refine ⟨rfl, ?_⟩
    rcases hst with h | h
    · exact hA (h.trans (map_zero _).symm)
    · exact absurd h hθ0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hσ.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hsum := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank] at hsum
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hsum
  set c0 := b.repr (θ * θ) 0
  set c1 := b.repr (θ * θ) 1
  have h2 := congrArg σ hsum
  rw [map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
  have h4 : algebraMap F E (2 * c1) * θ = 0 := by rw [map_mul, map_ofNat]; linear_combination hsum - h2
  rcases mul_eq_zero.1 h4 with h | h
  · have hc1 : 2 * c1 = 0 := hA (h.trans (map_zero _).symm)
    have : c1 = 0 := by simpa using hc1
    refine ⟨θ, hσθ, hre, him, c0, ?_⟩
    rw [← hsum, this, map_zero, zero_mul, add_zero]
  · exact absurd h hθ0

variable (F) in

def aF (i₀ : {w : InfinitePlace F // w.IsReal}) (t : ℝ) : AF F := mk F (Function.update 1 i₀ (Real.cos t), 1) 1

variable (F) in

def bF (i₀ : {w : InfinitePlace F // w.IsReal}) (c t : ℝ) : AF F := mk F (Function.update 0 i₀ (Real.sin t / c), 0) 0

theorem aF_add (i₀ : {w : InfinitePlace F // w.IsReal}) {c : ℝ} (hc : c ≠ 0) (P : AF F)
    (hP : (InfiniteAdeleRing.ringEquiv_mixedSpace F P.1).1 i₀ = -c ^ 2) (s t : ℝ) :
    aF F i₀ (s + t) = aF F i₀ s * aF F i₀ t + P * (bF F i₀ c s * bF F i₀ c t) := by
  simp only [aF, bF, mk_mul, mul_zero, mul_mk_zero, mk_add, mul_one, add_zero, mk_fst]
  congr 1
  refine Prod.ext (funext fun j => ?_) ?_
  · by_cases h : j = i₀
    · subst h
      simp only [Prod.fst_add, Prod.fst_mul, Pi.add_apply, Pi.mul_apply, Function.update_self, hP]
      field_simp
      rw [Real.cos_add]
      ring
    · simp [Function.update_of_ne h]
  · simp

theorem bF_add (i₀ : {w : InfinitePlace F // w.IsReal}) (c s t : ℝ) :
    bF F i₀ c (s + t) = aF F i₀ s * bF F i₀ c t + bF F i₀ c s * aF F i₀ t := by
  simp only [aF, bF, mk_mul, mk_add, mul_zero, zero_mul, add_zero]
  congr 1
  refine Prod.ext (funext fun j => ?_) ?_
  · by_cases h : j = i₀
    · subst h
      simp only [Prod.fst_add, Prod.fst_mul, Pi.add_apply, Pi.mul_apply, Function.update_self]
      rw [Real.sin_add]
      ring
    · simp [Function.update_of_ne h]
  · simp

theorem aF_zero (i₀ : {w : InfinitePlace F // w.IsReal}) : aF F i₀ 0 = 1 := by
  simp only [aF, Real.cos_zero]
  rw [show Function.update (1 : {w : InfinitePlace F // w.IsReal} → ℝ) i₀ 1 = 1 from Function.update_eq_self i₀ 1]
  exact mk_one (F := F)

theorem bF_zero (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) : bF F i₀ c 0 = 0 := by
  simp only [bF, Real.sin_zero, zero_div]
  rw [show Function.update (0 : {w : InfinitePlace F // w.IsReal} → ℝ) i₀ 0 = 0 from Function.update_eq_self i₀ 0]
  exact mk_zero

theorem aF_neg (i₀ : {w : InfinitePlace F // w.IsReal}) (t : ℝ) : aF F i₀ (-t) = aF F i₀ t := by
  simp [aF]

theorem bF_neg (i₀ : {w : InfinitePlace F // w.IsReal}) (c t : ℝ) : bF F i₀ c (-t) = -bF F i₀ c t := by
  simp only [bF, mk_neg, neg_zero, Real.sin_neg, neg_div]
  congr 1
  refine Prod.ext (funext fun j => ?_) (by simp)
  by_cases h : j = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem continuous_aF (i₀ : {w : InfinitePlace F // w.IsReal}) : Continuous (aF F i₀) :=
  continuous_mk ((continuous_const.update i₀ Real.continuous_cos).prodMk continuous_const) 1

theorem continuous_bF (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) : Continuous (bF F i₀ c) :=
  continuous_mk ((continuous_const.update i₀ (Real.continuous_sin.div_const c)).prodMk continuous_const) 0

theorem mul_sub_one_aF (i₀ : {w : InfinitePlace F // w.IsReal}) (t : ℝ) (u : AF F) (hu : evI F u = 0) :
    u * (aF F i₀ t - 1) = 0 := by
  have : aF F i₀ t - 1 = mk F ((Function.update (1 : {w : InfinitePlace F // w.IsReal} → ℝ) i₀ (Real.cos t), 1) - 1 : mixedEmbedding.mixedSpace F) 0 := by
    rw [aF, ← mk_one (F := F), mk_sub, sub_self]
  rw [this, mul_mk_zero, show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 from hu, zero_mul, mk_zero]

theorem mul_bF (i₀ : {w : InfinitePlace F // w.IsReal}) (c t : ℝ) (u : AF F) (hu : evI F u = 0) :
    u * bF F i₀ c t = 0 := by
  rw [bF, mul_mk_zero, show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 from hu, zero_mul, mk_zero]

variable (E) in

def Z (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) (θ : E) (t : ℝ) : AE F E :=
  aF F i₀ t ⊗ₜ[F] (1 : E) + bF F i₀ c t ⊗ₜ[F] θ

theorem Z_add (i₀ : {w : InfinitePlace F // w.IsReal}) {c : ℝ} (hc : c ≠ 0) {θ : E} {p : F}
    (hp : θ * θ = algebraMap F E p)
    (hP : (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) p).1).1 i₀ = -c ^ 2) (s t : ℝ) :
    Z E i₀ c θ (s + t) = Z E i₀ c θ s * Z E i₀ c θ t := by
  have key : ∀ x : AF F, x ⊗ₜ[F] (θ * θ) = (algebraMap F (AF F) p * x) ⊗ₜ[F] (1 : E) := by
    intro x
    rw [hp, Algebra.algebraMap_eq_smul_one (A := E) p, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def]
  simp only [Z, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, key]
  rw [aF_add i₀ hc _ hP s t, bF_add i₀ c s t, TensorProduct.add_tmul, TensorProduct.add_tmul]
  abel

theorem cA_Z {σ : E →ₐ[F] E} {θ : E} (hσθ : σ θ = -θ) (i₀ : {w : InfinitePlace F // w.IsReal}) (c t : ℝ) :
    cA σ (Z E i₀ c θ t) = Z E i₀ c θ (-t) := by
  simp only [Z, cA, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hσθ, TensorProduct.tmul_neg,
    aF_neg, bF_neg, TensorProduct.neg_tmul]

theorem Z_zero (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) (θ : E) : Z E i₀ c θ 0 = 1 := by
  rw [Z, aF_zero, bF_zero, TensorProduct.zero_tmul, add_zero, Algebra.TensorProduct.one_def]

theorem Z_at (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) (θ : E) (t : ℝ) : At (evI F) (Z E i₀ c θ t - 1) := by
  intro u hu
  rw [Z, Algebra.TensorProduct.one_def, add_sub_right_comm, ← TensorProduct.sub_tmul, smul_add,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_sub_one_aF i₀ t u hu,
    mul_bF i₀ c t u hu, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]

theorem piInf_Z {w : InfinitePlace F} (τ : EmbOver E w) (hw : w.IsReal) (i₀ : {w : InfinitePlace F // w.IsReal})
    (c : ℝ) (θ : E) (t : ℝ) :
    piInf τ (Z E i₀ c θ t) = (Function.update (1 : {w : InfinitePlace F // w.IsReal} → ℝ) i₀ (Real.cos t) ⟨w, hw⟩ : ℂ) +
      (Function.update (0 : {w : InfinitePlace F // w.IsReal} → ℝ) i₀ (Real.sin t / c) ⟨w, hw⟩ : ℂ) * τ.1 θ := by
  rw [Z, map_add, piInf_tmul τ hw, piInf_tmul τ hw, aF, bF, mk_fst, mk_fst, map_one, mul_one]

theorem continuous_Z (i₀ : {w : InfinitePlace F // w.IsReal}) (c : ℝ) (θ : E) : Continuous (Z E i₀ c θ) := by
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have e : Z E i₀ c θ = fun t => aF F i₀ t • ((1 : AF F) ⊗ₜ[F] (1 : E)) + bF F i₀ c t • ((1 : AF F) ⊗ₜ[F] θ) := by
    funext t
    rw [Z, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [e]
  have h1 : Continuous fun t => aF F i₀ t • ((1 : AF F) ⊗ₜ[F] (1 : E)) :=
    continuous_smul.comp ((continuous_aF i₀).prodMk continuous_const)
  have h2 : Continuous fun t => bF F i₀ c t • ((1 : AF F) ⊗ₜ[F] θ) :=
    continuous_smul.comp ((continuous_bF i₀ c).prodMk continuous_const)
  exact h1.add h2

theorem algebraMap_eq_diag {β : Type} [Fintype β] [DecidableEq β] (x : AE F E) :
    algebraMap (AE F E) (Matrix β β (AE F E)) x = Matrix.diagonal (fun _ => x) := by
  rw [Matrix.algebraMap_eq_diagonal]; rfl

theorem exists_central_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (AE F E)ˣ, ∃ γ ∈ RLines σ J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) = (z t : AE F E) • (1 : Matrix β β (AE F E))) ∧
      (∀ t : ℝ, At (evI F) ((z t : AE F E) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : AE F E) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J C w₀ hσ
  haveI := hσ.1
  have hw : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  obtain ⟨θ, hσθ, hre, him, p, hp⟩ := exists_anti σ hσ (τ w₀).1
  set c := ((τ w₀).1 θ).im with hcdef
  have hτθ : (τ w₀).1 θ = (c : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp [hcdef])
  set i₀ : {w : InfinitePlace F // w.IsReal} := ⟨w₀, hw w₀⟩ with hi₀
  have hP : (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) p).1).1 i₀ = -c ^ 2 := by
    have h3 : (algebraMap F (AF F) p) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E p) := by
      rw [Algebra.algebraMap_eq_smul_one (A := AF F), Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
    have e1 := (piInf_tmul (τ w₀) (hw w₀) (algebraMap F (AF F) p) (1 : E)).symm.trans
      ((congrArg (piInf (τ w₀)) h3).trans (piInf_tmul (τ w₀) (hw w₀) 1 (algebraMap F E p)))
    rw [← hp, map_mul, hτθ, map_one, mul_one] at e1
    have e2 : (((InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) p).1).1 i₀ : ℝ) : ℂ) =
        ((-c ^ 2 : ℝ) : ℂ) := by
      have hone : (InfiniteAdeleRing.ringEquiv_mixedSpace F (1 : AF F).1).1 ⟨w₀, hw w₀⟩ = 1 := by
        rw [show (1 : AF F).1 = (1 : InfiniteAdeleRing F) from rfl, map_one]; rfl
      rw [e1, hone]
      push_cast
      linear_combination (c : ℂ) ^ 2 * Complex.I_sq
    exact_mod_cast e2
  have hZadd := Z_add (E := E) i₀ him hp hP
  have hZ0 := Z_zero (E := E) i₀ c θ
  have hinv : ∀ t, Z E i₀ c θ t * Z E i₀ c θ (-t) = 1 := fun t => by rw [← hZadd, add_neg_cancel, hZ0]
  let zu : ℝ → (AE F E)ˣ := fun t => ⟨Z E i₀ c θ t, Z E i₀ c θ (-t), hinv t, by rw [← hZadd, neg_add_cancel, hZ0]⟩
  let zh : Multiplicative ℝ →* (AE F E)ˣ :=
    { toFun := fun t => zu (Multiplicative.toAdd t)
      map_one' := Units.ext hZ0
      map_mul' := fun s t => Units.ext (hZadd (Multiplicative.toAdd s) (Multiplicative.toAdd t)) }
  let g : Multiplicative ℝ →* GL β (AE F E) :=
    (Units.map (algebraMap (AE F E) (Matrix β β (AE F E))).toMonoidHom).comp zh
  have hg : ∀ t, ((g t : GL β (AE F E)) : Matrix β β (AE F E)) =
      Matrix.diagonal (fun _ => Z E i₀ c θ (Multiplicative.toAdd t)) := fun t => algebraMap_eq_diag _
  have hmem : ∀ t, g t ∈ UG (cA σ) J := by
    intro t
    change ((g t : GL β (AE F E)) : Matrix β β (AE F E))ᵀ * J * ((g t : GL β (AE F E)) : Matrix β β (AE F E)).map (cA σ) = J
    rw [hg, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _)]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, cA_Z hσθ]
    linear_combination J i j * hinv (Multiplicative.toAdd t)
  let γ : Multiplicative ℝ →* UG (cA σ) J := g.codRestrict _ hmem
  have hγ : ∀ t, (((γ t : UG (cA σ) J) : GL β (AE F E)) : Matrix β β (AE F E)) =
      Matrix.diagonal (fun _ => Z E i₀ c θ (Multiplicative.toAdd t)) := hg
  have hpi : ∀ (t : ℝ) (w : InfinitePlace F),
      piInf (τ w) (Z E i₀ c θ t) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
    intro t w
    rw [piInf_Z (τ w) (hw w)]
    by_cases h : w = w₀
    · subst h
      have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 him
      rw [if_pos rfl, Function.update_self, Function.update_self, hτθ, Complex.exp_mul_I,
        show ((Real.sin t / c : ℝ) : ℂ) * ((c : ℂ) * Complex.I) = (Real.sin t : ℂ) * Complex.I by
          push_cast; field_simp]
      push_cast
      ring
    · have h' : (⟨w, hw w⟩ : {w : InfinitePlace F // w.IsReal}) ≠ i₀ := fun e => h (congrArg Subtype.val e)
      rw [if_neg h, Function.update_of_ne h', Function.update_of_ne h']
      simp
  have hvc : Continuous fun t => ((g t : GL β (AE F E)) : Matrix β β (AE F E)) := by
    simp only [hg]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => (continuous_Z i₀ c θ).comp continuous_toAdd)
  have hgc : Continuous g := by
    refine Units.continuous_iff.2 ⟨hvc, ?_⟩
    refine (hvc.comp continuous_inv).congr fun t => ?_
    simp only [Function.comp_apply, map_inv]
  refine ⟨zu, γ, ⟨hgc.subtype_mk _, fun t => ?_⟩, fun t w => ?_, fun t => ?_, fun t => Z_at i₀ c θ t, hpi⟩
  · intro u hu
    rw [hγ]
    ext i j
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · exact Z_at i₀ c θ _ u hu
    · simp
  · rw [hγ, Matrix.diagonal_map (map_zero _), toAdd_ofAdd, hpi t w]
    show _ = C w * NormedSpace.exp (t • (if w = w₀ then Complex.I • (1 : Mat R S) else 0))
    by_cases h : w = w₀
    · rw [if_pos h, if_pos h]
      have e : (t • (Complex.I • (1 : Mat R S))) = Matrix.diagonal (fun _ => (t : ℂ) * Complex.I) := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [Complex.real_smul]
        · simp [Matrix.one_apply, Matrix.diagonal_apply, hij]
      rw [e, Matrix.exp_diagonal]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.exp_eq_exp_ℂ, mul_comm]
    · rw [if_neg h, if_neg h, smul_zero, NormedSpace.exp_zero, Matrix.mul_one]
      rw [show Matrix.diagonal (fun _ : β => (1 : ℂ)) = 1 from rfl, Matrix.one_mul]
  · show algebraMap (AE F E) (Matrix β β (AE F E)) (Z E i₀ c θ t) = _
    exact Algebra.algebraMap_eq_smul_one _

end GlobalTheory.CentralLine
