import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatAnnih

section Scalar

variable {F : Type} [Field F] [NumberField F]

theorem inf_rat (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) (y : Ainf F)
    (h : ∀ c : 𝓞 F, ∃ n : ℤ, L (y * algebraMap F _ (c : F)) = n) : ∃ d : F, y = algebraMap F _ d := by
  classical
  have hb : ∀ i, ∃ n : ℤ, L (y * algebraMap F _ (integralBasis F i)) = n := fun i => by
    rw [integralBasis_apply]; exact h _
  choose n hn using hb
  refine ⟨∑ i, (n i : F) * (integralBasis F).traceDual i, funext fun v => ?_⟩
  let φ : Ainf F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding v).comp (Pi.evalRingHom _ v)
  have hφ : Continuous φ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  have key : (fun w : Ainf F => φ w) = fun w => ∑ i, L (w * algebraMap F _ (integralBasis F i)) *
      φ (algebraMap F _ ((integralBasis F).traceDual i)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hφ
      (continuous_finset_sum _ fun i _ => (hL.comp (continuous_id.mul continuous_const)).mul continuous_const) ?_
    funext x
    simp only [Function.comp_apply, ← map_mul, hT]
    conv_lhs => rw [← (integralBasis F).traceDual.sum_repr x]
    simp only [map_sum, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      eq_ratCast]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← RingHom.comp_apply φ (algebraMap F (Ainf F)), map_ratCast]
  apply (InfinitePlace.Completion.extensionEmbedding v).injective
  change φ y = φ (algebraMap F (Ainf F) _)
  rw [congrFun key y]
  simp only [hn, map_sum, map_mul, map_intCast]

theorem fin_eq_zero {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1) (l : Af F)
    (h : ∀ c : F, ψ (pairA F 0 (l * algebraMap F _ c)) = 1) : l = 0 := by
  classical
  have hp : Continuous fun y : Af F => pairA F 0 (l * y) :=
    Continuous.prodMk continuous_const (continuous_const.mul continuous_id)
  have hall : ∀ z : Af F, ψ (pairA F 0 (l * z)) = 1 := by
    intro z
    obtain ⟨x, β, hβ, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 z
    have h1 : ψ (pairA F 0 (l * β)) = 1 :=
      GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 (l * y)) = 1})
        (isClosed_eq (hψ.comp hp) continuous_const) (fun a => h a) β hβ
    have e : pairA F 0 (l * (algebraMap F _ x + 1 • β)) =
        pairA F 0 (l * algebraMap F _ x) + pairA F 0 (l * β) := by
      rw [one_smul, mul_add]
      exact Prod.ext (add_zero _).symm rfl
    rw [e, ψ.map_add_eq_mul, h, h1, one_mul]
  have hext : ∀ a b : Af F, (∀ w, evalV F w a = evalV F w b) → a = b := fun a b hab =>
    Subtype.ext (funext hab)
  refine hext _ _ fun v => ?_
  by_contra hne
  rw [map_zero] at hne
  obtain ⟨y, hy⟩ := hv v
  have same : ∀ t, evalV F v (singleV F v t) = t := fun t => RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t
  have diff : ∀ t w, w ≠ v → evalV F w (singleV F v t) = 0 := fun t w hw => RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t hw
  refine hy ?_
  rw [psiV, ← hall (singleV F v ((evalV F v l)⁻¹ * y))]
  congr 2
  refine hext _ _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, same, same, mul_inv_cancel_left₀ hne]
  · rw [map_mul, diff _ _ hw, diff _ _ hw, mul_zero]

theorem adele_rat {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1)
    (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ))
    (hinf : ∀ x, psiInf F ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x))) (a : AF F)
    (h : ∀ c : F, ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  have hsub : ∀ (b : AF F) (x : F), (∀ c : F, ψ (b * algebraMap F _ c) = 1) →
      ∀ c : F, ψ ((b - algebraMap F _ x) * algebraMap F _ c) = 1 := fun b x hb c => by
    rw [sub_mul, ← map_mul, AddChar.map_sub_eq_div, hb, hψ.2.2.1, div_one]
  obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 (sndA F a)
  have h1 := hsub a x h
  have hβ' : sndA F (a - algebraMap F _ x) = β := by
    rw [map_sub, AlgHom.commutes, hx, one_smul, add_sub_cancel_left]
  obtain ⟨d, hd⟩ := inf_rat L hL hT (fstA F (a - algebraMap F _ x)) fun c => by
    have h2 : ψ (pairA F 0 (β * algebraMap F _ (c : F))) = 1 := by
      refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 c (fun r => ?_) β hβ
      have h3 := GlobalTheory.StdAdelicChar.ratChar_integer F (r * c)
      rw [GlobalTheory.StdRat.char_fin_rat ψ hψ, hinf, hT, map_neg, ← h3, GlobalTheory.StdAdelicChar.ratChar]
      congr 1
      push_cast
      ring
    have e : (a - algebraMap F _ x) * algebraMap F _ (c : F) =
        pairA F (fstA F (a - algebraMap F _ x) * algebraMap F _ (c : F)) 0 +
          pairA F 0 (β * algebraMap F _ (c : F)) := by
      rw [← hβ']
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    have h4 := h1 c
    rw [e, ψ.map_add_eq_mul, h2, mul_one] at h4
    have h5 := (hinf _).symm.trans h4
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h5
    refine ⟨-n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    push_cast
    linear_combination -hn
  have h6 := hsub _ d h1
  have h7 : fstA F (a - algebraMap F _ x - algebraMap F _ d) = 0 := by
    rw [map_sub, AlgHom.commutes, hd, sub_self]
  have h8 := fin_eq_zero hψ.1 hv (sndA F (a - algebraMap F _ x - algebraMap F _ d)) fun c => by
    rw [← h6 c]
    congr 1
    refine Prod.ext ?_ rfl
    change 0 = fstA F (a - algebraMap F _ x - algebraMap F _ d) * _
    rw [h7, zero_mul]
  refine ⟨x + d, ?_⟩
  rw [map_add, ← sub_eq_zero, ← sub_sub]
  exact Prod.ext h7 h8

end Scalar

theorem tensor_rat {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E)
    (h : ∀ e : E, ∃ d : F, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) = algebraMap F R d) :
    ∃ e : E, z = (1 : R) ⊗ₜ[F] e := by
  classical
  let b := Module.finBasis F E
  have key : ∀ z : R ⊗[F] E,
      z = ∑ i, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b i * z) ⊗ₜ[F] b.traceDual i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [mul_add, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | tmul a e =>
      conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul, Module.Basis.traceDual_repr_apply,
        Algebra.traceForm_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm, mul_comm e]
  choose d hd using h
  refine ⟨∑ i, d (b i) • b.traceDual i, ?_⟩
  rw [key z, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_mul_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E) (e : E) (c : F) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) * algebraMap F R c =
      Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (c • e) * z) := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc, algebraMap_smul, ← TensorProduct.tmul_smul]

theorem sum_single {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {m n : ℕ} (P : Matrix (Fin m) (Fin m) E)
    (Q : Matrix (Fin n) (Fin n) E) (hP : IsUnit P.det) (hQ : IsUnit Q.det) (a₀ : Fin m) (d₀ : Fin n) (e : E)
    (x : Fin n → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι ((P * Matrix.single a₀ d₀ e * Q⁻¹) b c) * ι (Q c d) * x d a =
      ι e * x d₀ a₀ := by
  have h1 : P⁻¹ * (P * Matrix.single a₀ d₀ e * Q⁻¹) * Q = Matrix.single a₀ d₀ e := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
  generalize P * Matrix.single a₀ d₀ e * Q⁻¹ = M at h1
  have h2 : ∀ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι (M b c) * ι (Q c d) * x d a =
      ∑ d, ι (Matrix.single a₀ d₀ e a d) * x d a := fun a => by
    rw [← h1]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm
  simp only [h2]
  rw [Finset.sum_eq_single a₀, Finset.sum_eq_single d₀, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne ha.symm, map_zero, zero_mul]
  · simp

theorem exists_symplO_eq {D : D7} (S T : HSp D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E) :
    ∃ γ ∈ ratL T S, symplO S T x γ = Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j) := by
  refine ⟨ratW T S fun c b => star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c), ⟨_, rfl⟩, ?_⟩
  have h := sum_single (incA D) S.gram T.gram (GlobalTheory.LatVac.gram_det_isUnit S) (GlobalTheory.LatVac.gram_det_isUnit T) j i
    (D.host.xi0⁻¹ * e) x
  have h2 : hO S T x (ratW T S fun c b =>
      star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c)) =
      incA D (D.host.xi0⁻¹ * e) * x i j := by
    rw [← h, hO]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    exact congrArg (fun t => incA D (S.gram⁻¹ a b) * t * incA D (T.gram c d) * x d a)
      ((GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (star_star _)))
  rw [symplO, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

theorem ratL_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  intro D ψ hψ S T x
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := hψ.2.1
    let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
      simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    have hrat := adele_rat hψ.1 (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) L
      (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
      (fun x => by
        show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
      (fun y => by
        rw [hψ.2.2 θ hθ]
        congr 1
        change _ = -(_ * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E)))
        push_cast
        ring)
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      tensor_rat (x i j) fun e => hrat _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplO_eq S T x i j (c • e)
        exact (congrArg ψ ((trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T γ γ'
    exact (congrArg ψ ha).trans (hψ.1.2.2.1 a)

end GlobalTheory.RatAnnih

end
