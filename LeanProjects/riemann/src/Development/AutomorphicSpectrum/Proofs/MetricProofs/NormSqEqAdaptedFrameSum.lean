import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
theorem embOf_of_comp (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext a
  simp [embOf_coe]

omit [IsCMField E] in
theorem embOf_injective : Function.Injective (embOf : (𝓞 E →+* ℂ) → (E →+* ℂ)) := by
  intro s s' h
  ext a
  rw [← embOf_coe s a, ← embOf_coe s' a, h]

theorem conj_eq_complexConj (x : E) : conj (maximalRealSubfield E) E x = IsCMField.complexConj E x := by
  set K := maximalRealSubfield E
  set t := IsCMField.complexConj E
  set y := conj K E x with hy
  have hyy : conj K E y = x := conj_conj x
  have fix : ∀ a : E, conj K E a = a → t a = a := by
    intro a ha
    obtain ⟨b, rfl⟩ := conj_eq_self_iff.1 ha
    exact (IsCMField.complexConj_eq_self_iff E _).2 b.2
  have ha : t (x + y) = x + y := fix _ (by rw [map_add, hyy, ← hy, add_comm])
  have hb : t (x * y) = x * y := fix _ (by rw [map_mul, hyy, ← hy, mul_comm])
  have hz : (t x - x) * (t x - y) = 0 := by
    have h0 : x * x - (x + y) * x + x * y = 0 := by ring
    have h1 := congrArg t h0
    rw [map_add, map_sub, map_mul, map_mul, ha, hb, map_zero] at h1
    linear_combination h1
  rcases mul_eq_zero.1 hz with h | h
  · have hx : t x = x := sub_eq_zero.1 h
    have : x ∈ K := (IsCMField.complexConj_eq_self_iff E x).1 hx
    have h2 : y = x := conj_eq_self_iff.2 ⟨⟨x, this⟩, rfl⟩
    rw [h2, hx]
  · exact (sub_eq_zero.1 h).symm

theorem embOf_conj (s : 𝓞 E →+* ℂ) (x : E) :
    embOf s (conjHom (maximalRealSubfield E) E x) = starRingEnd ℂ (embOf s x) := by
  rw [conjHom_apply, conj_eq_complexConj]
  exact IsCMField.complexEmbedding_complexConj E _ x

theorem emb_bij {Ψ : Type} {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Function.Bijective (fun p : Ψ × Bool =>
      if p.2 then (starRingEnd ℂ).comp (embOf (σ p.1)) else embOf (σ p.1)) := by
  have hres : ∀ s : 𝓞 E →+* ℂ, (embOf s).comp (algebraMap (𝓞 E) E) = s := by
    intro s; ext a; simp [embOf_coe]
  have hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp (embOf s) = embOf ((starRingEnd ℂ).comp s) := by
    intro s
    rw [← embOf_of_comp ((starRingEnd ℂ).comp (embOf s))]
    congr 1
    rw [RingHom.comp_assoc, hres]
  constructor
  · rintro ⟨τ, b⟩ ⟨τ', b'⟩ e
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_true, if_false, hconj] at e
    · rw [h.1 (embOf_injective e)]
    · exact absurd ⟨τ, embOf_injective e⟩ ((h.2 (σ τ')).1 ⟨τ', rfl⟩)
    · exact absurd ⟨τ', (embOf_injective e).symm⟩ ((h.2 (σ τ)).1 ⟨τ, rfl⟩)
    · have e2 := embOf_injective e
      have : σ τ = σ τ' := by
        ext a
        have := congrArg (fun f : 𝓞 E →+* ℂ => starRingEnd ℂ (f a)) e2
        simpa using this
      rw [h.1 this]
  · intro φ
    by_cases hs : ∃ τ, σ τ = φ.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      exact ⟨(τ, false), by simp [hτ, embOf_of_comp]⟩
    · have : ∃ τ, σ τ = (starRingEnd ℂ).comp (φ.comp (algebraMap (𝓞 E) E)) := by
        by_contra hn
        exact hs ((h.2 _).2 hn)
      obtain ⟨τ, hτ⟩ := this
      refine ⟨(τ, true), ?_⟩
      have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (φ.comp (algebraMap (𝓞 E) E))) =
          φ.comp (algebraMap (𝓞 E) E) := by
        ext a; simp
      simp only [if_true, hconj, hτ, e, embOf_of_comp]

theorem trace_eq {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (embOf (σ τ) x).re := by
  classical
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)
  rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp, ← (Equiv.ofBijective _ (emb_bij h)).sum_comp,
    Fintype.sum_prod_type] at h1
  have h2 := congrArg Complex.re h1
  rw [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [two_mul]

end Field

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem gr_apply (τ : Ψ) (u w : Fin (j + j') → E) :
    star (fun i => embOf (F.σ τ) (u i)) ⬝ᵥ (C.gr τ *ᵥ fun i => embOf (F.σ τ) (w i)) =
      embOf (F.σ τ) (C.h.toSesq u w) := by
  have hu : u = ∑ a, u a • Pi.basisFun E (Fin (j + j')) a := ((Pi.basisFun E _).sum_repr u).symm
  have hw : w = ∑ b, w b • Pi.basisFun E (Fin (j + j')) b := ((Pi.basisFun E _).sum_repr w).symm
  have hB : C.h.toSesq u w = ∑ a, ∑ b, conjHom (maximalRealSubfield E) E (u a) * (w b *
      gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) a b) := by
    conv_lhs => rw [hu, hw]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, GroundTheory.Automorphic.gram]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hB]
  simp only [dotProduct, mulVec, map_sum, map_mul, embOf_conj, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hg : C.gr τ a b = embOf (F.σ τ) (gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) a b) := rfl
  rw [hg]
  ring

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) where
  toFun := C.vec
  map_zero' := by ext τ i; simp [LatEmb.vec]
  map_add' x y := by ext τ i; simp [LatEmb.vec]

theorem vec_lam (k : Fin (2 * g)) : C.vec (C.lam k) = C.bas k := by
  ext τ i; exact (C.bas_eq k τ i).symm

theorem perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  have : ((C.perExt R).toAddMonoidHom.comp (vecHom C)).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [vec_lam]
    simp [LatEmb.perExt]
  exact congrArg (fun f : Λ →ₗ[ℤ] (Fin g → ℂ) => f x) this

theorem Fm_vec (x y : Λ) : C.Fm (C.vec x) (C.vec y) = (F.form x y : ℝ) := by
  have h1 : ((F.form x y : ℤ) : ℝ) = (((F.form x y : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h1, C.form_eq, trace_eq F.cm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, ← gr_apply]
  rfl

def FmB : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ C.Fm
    (fun a b c => by
      simp only [LatEmb.Fm, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re, ← Finset.sum_add_distrib]
      )
    (fun r a c => by
      simp only [LatEmb.Fm, Pi.smul_apply, mulVec_smul, dotProduct_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring)
    (fun a b c => by
      simp only [LatEmb.Fm, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re, ← Finset.sum_add_distrib])
    (fun r a c => by
      simp only [LatEmb.Fm, Pi.smul_apply, Pi.star_apply, star_smul, star_trivial, smul_dotProduct, mul_smul_comm,
        Complex.smul_re, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring)

def HB (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y y' => (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im)
    (fun a b c => by simp [add_dotProduct])
    (fun r a c => by
      simp)
    (fun a b c => by simp [mulVec_add, dotProduct_add, star_add])
    (fun r a c => by
      simp [mulVec_smul, dotProduct_smul])

end Lat

section Adapted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)
  {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ}

theorem form_ext (hR : R.form = F.form) (y y' : Ψ → Fin (j + j') → ℂ) :
    (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y' := by
  have h : HB C R = FmB C := by
    refine C.bas.ext fun k => C.bas.ext fun l => ?_
    show (C.perExt R (C.bas k) ⬝ᵥ R.Hm *ᵥ star (C.perExt R (C.bas l))).im = C.Fm (C.bas k) (C.bas l)
    rw [← vec_lam, ← vec_lam, perExt_vec, perExt_vec, R.im, Fm_vec, hR]
  exact LinearMap.congr_fun₂ h y y'

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply, fromBlocks_one]

variable {C R}

theorem cinv_mul (h : C.IsAdapted R A) (τ : Ψ) : C.cinv (A τ) τ * A τ = 1 := by
  unfold LatEmb.cinv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A τ)ᴴ, h.unit, sgI_mul_self]

theorem mul_cinv (h : C.IsAdapted R A) (τ : Ψ) : A τ * C.cinv (A τ) τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (cinv_mul h τ)

def tw (v : Sg j j' → ℂ) : Sg j j' → ℂ :=
  Sum.elim (-Complex.I • (v ∘ Sum.inl)) (Complex.I • (v ∘ Sum.inr))

open Classical in
theorem perExt_single_tw (h : C.IsAdapted R A) (τ : Ψ) (v : Sg j j' → ℂ) :
    C.perExt R (Pi.single τ (A τ *ᵥ tw v)) = Complex.I • C.perExt R (Pi.single τ (A τ *ᵥ v)) := by
  set l : (Fin (j + j') → ℂ) →+ (Fin g → ℂ) :=
    (C.perExt R).toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Ψ => Fin (j + j') → ℂ) τ) with hl
  have hl' : ∀ w, C.perExt R (Pi.single τ w) = l w := fun _ => rfl
  set p := A τ *ᵥ Sum.elim (v ∘ Sum.inl) (0 : Fin j' → ℂ) with hp
  set q := A τ *ᵥ Sum.elim (0 : Fin j → ℂ) (v ∘ Sum.inr) with hq
  have h1 : l p = Complex.I • l (Complex.I • p) := by
    have := h.ker τ (v ∘ Sum.inl)
    unfold LatEmb.pPart at this
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · norm_num at h0
    · exact sub_eq_zero.1 h0
  have h2 : l q = -(Complex.I • l (Complex.I • q)) := by
    have := h.kerBar τ (v ∘ Sum.inr)
    unfold LatEmb.pBar at this
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · norm_num at h0
    · exact eq_neg_of_add_eq_zero_left h0
  have hII : ∀ u : Fin g → ℂ, Complex.I • Complex.I • u = -u := by
    intro u; rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hv : A τ *ᵥ v = p + q := by
    rw [hp, hq, ← mulVec_add]
    congr 1
    ext (i | i) <;> simp
  have hw : A τ *ᵥ tw v = -(Complex.I • p) + Complex.I • q := by
    rw [hp, hq, ← mulVec_smul, ← mulVec_smul, ← mulVec_neg, ← mulVec_add]
    congr 1
    ext (i | i) <;> simp [tw]
  rw [hl', hl', hv, hw, map_add, map_add, map_neg, smul_add]
  have e1 : Complex.I • l p = -l (Complex.I • p) := by rw [h1, hII]
  have e2 : Complex.I • l q = l (Complex.I • q) := by
    rw [h2, smul_neg, hII, neg_neg]
  rw [e1, e2]

theorem perExt_tw (h : C.IsAdapted R A) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (fun τ => A τ *ᵥ tw (C.cinv (A τ) τ *ᵥ y τ)) = Complex.I • C.perExt R y := by
  classical
  have hs : ∀ u : Ψ → Fin (j + j') → ℂ, u = ∑ τ, Pi.single τ (u τ) := fun u => (Finset.univ_sum_single u).symm
  conv_lhs => rw [hs (fun τ => A τ *ᵥ tw (C.cinv (A τ) τ *ᵥ y τ))]
  conv_rhs => rw [hs y]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [perExt_single_tw h]
  have : A τ *ᵥ (C.cinv (A τ) τ *ᵥ y τ) = y τ := by
    rw [mulVec_mulVec, mul_cinv h, one_mulVec]
  rw [this]

theorem sgI_mulVec_tw (v : Sg j j' → ℂ) : sgI j j' *ᵥ tw v = -Complex.I • v := by
  ext (i | i) <;> simp [sgI, tw, fromBlocks_mulVec, mulVec_neg, neg_mulVec]

theorem term_eq (h : C.IsAdapted R A) (τ : Ψ) (v : Sg j j' → ℂ) :
    2 * (embOf (F.σ τ) C.xi * (star (A τ *ᵥ v) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ tw v)))).re =
      2 * C.c * (star v ⬝ᵥ v).re := by
  have key : star (A τ *ᵥ v) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ tw v)) = star v ⬝ᵥ (((A τ)ᴴ * C.gr τ * A τ) *ᵥ tw v) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hu : ((C.eps τ : ℝ) : ℂ) • ((A τ)ᴴ * C.gr τ * A τ) = sgI j j' := by
    rw [← h.unit τ, LatEmb.sgr]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  have hX : ((C.eps τ : ℝ) : ℂ) * (star v ⬝ᵥ (((A τ)ᴴ * C.gr τ * A τ) *ᵥ tw v)) =
      -Complex.I * (star v ⬝ᵥ v) := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← smul_mulVec, hu, sgI_mulVec_tw, dotProduct_smul, smul_eq_mul]
  have hz : embOf (F.σ τ) C.xi * (star (A τ *ᵥ v) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ tw v))) =
      ((C.c : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
    rw [key, C.xi_eq τ]
    push_cast
    have : Complex.I * ((C.c : ℂ) * ((C.eps τ : ℝ) : ℂ)) * (star v ⬝ᵥ (((A τ)ᴴ * C.gr τ * A τ) *ᵥ tw v)) =
        Complex.I * (C.c : ℂ) * (((C.eps τ : ℝ) : ℂ) * (star v ⬝ᵥ (((A τ)ᴴ * C.gr τ * A τ) *ᵥ tw v))) := by ring
    rw [this, hX]
    linear_combination (-(C.c : ℂ) * (star v ⬝ᵥ v)) * Complex.I_mul_I
  rw [hz, Complex.re_ofReal_mul]
  ring

theorem normSq_eq_adapted (hR : R.form = F.form) (h : C.IsAdapted R A) (x : Λ) :
    R.normSq x = 2 * C.c * ∑ τ, (star (C.cinv (A τ) τ *ᵥ C.vec x τ) ⬝ᵥ (C.cinv (A τ) τ *ᵥ C.vec x τ)).re := by
  have hz : C.perExt R (C.vec x) = R.P x := perExt_vec C R x
  have h1 : R.normSq x = ((Complex.I • R.P x) ⬝ᵥ R.Hm *ᵥ star (R.P x)).im := by
    rw [smul_dotProduct, smul_eq_mul]
    simp [RiemLat.normSq, RiemLat.ip]
  rw [h1, ← hz, ← perExt_tw h, form_ext C R hR, Finset.mul_sum]
  unfold LatEmb.Fm
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hy : C.vec x τ = A τ *ᵥ (C.cinv (A τ) τ *ᵥ C.vec x τ) := by
    rw [mulVec_mulVec, mul_cinv h, one_mulVec]
  rw [← term_eq h τ, ← hy]

end Adapted

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen

theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → ∀ x, R.normSq x = 2 * C.c * ∑ τ, (star (C.cinv (A τ) τ *ᵥ C.vec x τ) ⬝ᵥ (C.cinv (A τ) τ *ᵥ C.vec x τ)).re := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A hR h x
  exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.normSq_eq_adapted hR h x
