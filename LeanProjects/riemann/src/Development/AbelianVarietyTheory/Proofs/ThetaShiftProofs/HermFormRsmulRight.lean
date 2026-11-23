import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open scoped Classical

namespace GlobalTheory.ArchLen

theorem hermForm_eq_sum {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * (starRingEnd ℂ) (w j) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rfl

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp only [hermForm, add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem hermForm_rsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by
  rw [← hermForm_smul_left]; rfl

theorem hermForm_rsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = a * hermForm Hm z w := by
  simp only [hermForm_eq_sum, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem im_eq_on_span {g : ℕ} (Hm Hm' : Matrix (Fin g) (Fin g) ℂ)
    (A B A' B' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (S : Set (Fin g → ℂ))
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm' (A' z) (B' w)).im = (hermForm Hm (A z) (B w)).im) :
    ∀ z ∈ Submodule.span ℝ S, ∀ w ∈ Submodule.span ℝ S,
      (hermForm Hm' (A' z) (B' w)).im = (hermForm Hm (A z) (B w)).im := by
  intro z hz w hw
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact h x hx y hy
  | zero_left y _ => simp [hermForm]
  | zero_right x _ => simp [hermForm]
  | add_left x y z _ _ _ h1 h2 => simp only [map_add, hermForm_add_left, Complex.add_im, h1, h2]
  | add_right x y z _ _ _ h1 h2 => simp only [map_add, hermForm_add_right, Complex.add_im, h1, h2]
  | smul_left r x y _ _ h1 => simp only [map_smul, hermForm_rsmul_left, Complex.im_ofReal_mul, h1]
  | smul_right r x y _ _ h1 => simp only [map_smul, hermForm_rsmul_right, Complex.im_ofReal_mul, h1]

theorem hermForm_block {g : ℕ} {ι : Type} (ty : Fin g → ι) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hb : ∀ i j, ty i ≠ ty j → Hm i j = 0) (p : ι → Prop) [DecidablePred p] (z : Fin g → ℂ) :
    hermForm Hm (fun j => if p (ty j) then z j else 0) (fun j => if p (ty j) then z j else 0) =
      ∑ i, if p (ty i) then ∑ j, z i * Hm i j * (starRingEnd ℂ) (z j) else 0 := by
  rw [hermForm_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p (ty i)
  · simp only [hi, if_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : p (ty j)
    · simp only [hj, if_true]
    · have : ty i ≠ ty j := fun h => hj (h ▸ hi)
      simp [hb i j this]
  · simp [hi]

variable {E : Type} [Field E] [NumberField E]

theorem emb_ext {ρ ρ' : E →+* ℂ} (h : ∀ a : 𝓞 E, ρ (a : E) = ρ' (a : E)) : ρ = ρ' := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_
  ext a
  exact h a

theorem emb_of_norm_eq {ρ ρ' : E →+* ℂ} (h : ∀ a : 𝓞 E, ‖ρ (a : E)‖ = ‖ρ' (a : E)‖) :
    ρ = ρ' ∨ ComplexEmbedding.conjugate ρ = ρ' := by
  rw [← InfinitePlace.mk_eq_iff]
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  change ‖ρ _‖ = ‖ρ' _‖
  rw [map_div₀, map_div₀, norm_div, norm_div]
  exact congrArg₂ (· / ·) (h a) (h b)

noncomputable def sqAbs (ρ : E →+* ℂ) : 𝓞 E →* ℝ where
  toFun a := ‖ρ (a : E)‖ ^ 2
  map_one' := by simp
  map_mul' a b := by simp [mul_pow]

theorem coeff_eq (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (m m' : Ψ → ℝ) (h : ∀ a : 𝓞 E, ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m τ = ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m' τ) :
    m = m' := by
  have hinj : Function.Injective (fun τ : Ψ => sqAbs τ.1) := by
    intro τ τ' hh
    have h1 : ∀ a : 𝓞 E, ‖τ.1 (a : E)‖ = ‖τ'.1 (a : E)‖ := fun a => by
      have : ‖τ.1 (a : E)‖ ^ 2 = ‖τ'.1 (a : E)‖ ^ 2 := DFunLike.congr_fun hh a
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    rcases emb_of_norm_eq h1 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (h2 ▸ τ'.2) ((hΨ τ.1).1 τ.2)
  have hli := (linearIndependent_monoidHom (𝓞 E) ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext τ
  have := hli (m - m') (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    have := h a
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl fun τ _ => by
      change _ * ‖τ.1 (a : E)‖ ^ 2 = _
      ring) τ
  exact sub_eq_zero.1 this

theorem block_le {g : ℕ} (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (ty : Fin g → (E →+* ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hb : ∀ i j, ty i ≠ ty j → Hm i j = 0) (z : Fin g → ℂ) (m : Ψ → ℝ)
    (h : ∀ a : 𝓞 E, (hermForm Hm (fun j => ty j (a : E) * z j) (fun j => ty j (a : E) * z j)).re =
      ∑ τ : Ψ, ‖τ.1 (a : E)‖ ^ 2 * m τ) (ρ : E →+* ℂ) (τ' : Ψ)
    (hρ : τ'.1 = ρ ∨ ComplexEmbedding.conjugate τ'.1 = ρ) :
    (hermForm Hm (fun j => if ty j = ρ then z j else 0) (fun j => if ty j = ρ then z j else 0)).re ≤ m τ' := by
  have hnn : ∀ z : Fin g → ℂ, 0 ≤ (hermForm Hm z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz, hermForm]
    · exact (hpos z hz).le
  have cc2 : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := fun φ => by
    ext a; simp
  let π : (E →+* ℂ) → Ψ := fun φ => if hφ : φ ∈ Ψ then ⟨φ, hφ⟩ else
    ⟨ComplexEmbedding.conjugate φ, by by_contra h'; exact hφ ((hΨ φ).2 h')⟩
  have hπ : ∀ φ (a : E), ‖(π φ).1 a‖ = ‖φ a‖ := fun φ a => by
    by_cases hφ : φ ∈ Ψ
    · simp [π, hφ]
    · simp [π, hφ]
  have hπρ : π ρ = τ' := by
    rcases hρ with h1 | h1
    · subst h1; simp [π, τ'.2]
    · subst h1
      have := (hΨ τ'.1).1 τ'.2
      simp only [π, this, dif_neg, not_false_eq_true]
      exact Subtype.ext (cc2 _)
  set q : Fin g → ℂ := fun i => ∑ j, z i * Hm i j * (starRingEnd ℂ) (z j) with hq
  have key : m = fun τ => ∑ i, if π (ty i) = τ then (q i).re else 0 := by
    refine coeff_eq Ψ hΨ _ _ fun a => ?_
    rw [← h a, hermForm_eq_sum]
    have e1 : ∀ i, ∑ j, ty i (a : E) * z i * Hm i j * (starRingEnd ℂ) (ty j (a : E) * z j) =
        ((‖ty i (a : E)‖ ^ 2 : ℝ) : ℂ) * q i := fun i => by
      simp only [hq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : ty i = ty j
      · rw [← hij, map_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; ring
      · simp [hb i j hij]
    simp only [e1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hπ]
  have h1 := hermForm_block ty Hm hb (fun φ => φ = ρ) z
  have h2 := hermForm_block ty Hm hb (fun φ => π φ = τ' ∧ φ ≠ ρ) z
  have h3 := hnn (fun j => if π (ty j) = τ' ∧ ty j ≠ ρ then z j else 0)
  have h4 : m τ' = (∑ i, if ty i = ρ then q i else 0).re + (∑ i, if π (ty i) = τ' ∧ ty i ≠ ρ then q i else 0).re := by
    rw [key, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ty i = ρ
    · simp [hi, hπρ]
    · by_cases hi' : π (ty i) = τ' <;> simp [hi, hi']
  have h5 : (∑ i, if π (ty i) = τ' ∧ ty i ≠ ρ then q i else 0).re ≥ 0 := by
    rw [h2] at h3
    exact h3
  have h6 : hermForm Hm (fun j => if ty j = ρ then z j else 0) (fun j => if ty j = ρ then z j else 0) =
      ∑ i, if ty i = ρ then q i else 0 := by convert h1
  rw [h6, h4]; linarith

variable [IsCMField E]

theorem emb_cc (ρ : E →+* ℂ) (x : E) : ρ (cc x) = (starRingEnd ℂ) (ρ x) :=
  IsCMField.complexEmbedding_complexConj E ρ x

theorem herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul_right {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G x (a • y) = cc a * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermC_smul_left {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (x y : Fin r → ℂ) :
    hermC τ G (a • x) y = a * hermC τ G x y := by
  simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermC_smul_right {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (x y : Fin r → ℂ) :
    hermC τ G x (a • y) = (starRingEnd ℂ) a * hermC τ G x y := by
  simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem maj_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (a • v) = ‖a‖ ^ 2 * X.maj x τ v := by
  have e : ((‖a‖ ^ 2 : ℝ) : ℂ) = a * (starRingEnd ℂ) a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : X.posPart x τ (a • v) = ‖a‖ ^ 2 * X.posPart x τ v := by
    simp only [Data.posPart]
    rw [← Complex.re_ofReal_mul, e]
    congr 1
    simp only [hermC_smul_left, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : (hermC τ.1 X.Gm (a • v) (a • v)).re = ‖a‖ ^ 2 * (hermC τ.1 X.Gm v v).re := by
    rw [← Complex.re_ofReal_mul, e, hermC_smul_left, hermC_smul_right, mul_assoc]
  simp only [Data.maj, h1, h2]; ring

noncomputable def diagMul {g : ℕ} (d : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z := fun j => d j * z j
  map_add' z w := by funext j; simp [mul_add]
  map_smul' a z := by funext j; simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply]; ring

theorem block_of_adjoint {g : ℕ} (ty : Fin g → (E →+* ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ (a : 𝓞 E) (z w : Fin g → ℂ), (hermForm Hm (fun j => ty j (a : E) * z j) w).im =
      (hermForm Hm z (fun j => ty j (cc (a : E)) * w j)).im) (i j : Fin g) (hij : ty i ≠ ty j) : Hm i j = 0 := by
  by_contra hne
  refine hij (emb_ext fun a => ?_)
  have key : ∀ s : ℂ, (s * (ty i (a : E) * Hm i j)).im = (s * (ty j (a : E) * Hm i j)).im := fun s => by
    have := h a (Pi.single i s) (Pi.single j 1)
    simp only [hermForm_eq_sum, Pi.single_apply, mul_ite, ite_mul, mul_zero, zero_mul, apply_ite (starRingEnd ℂ),
      map_zero, map_one, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, emb_cc, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have : ty i (a : E) * Hm i j = ty j (a : E) * Hm i j := by
    apply Complex.ext
    · simpa using key Complex.I
    · simpa using key 1
  exact mul_right_cancel₀ hne this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := by
  intro τ τ' h
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_rt (hσ : GoodEmb c σ) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    relab c σ τ (H.rt : E) = H.rt0 := by
  have h2 : embF c τ (H.rt : E) = (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := Subtype.ext h
  change σ (embF c τ (H.rt : E)) = _
  rw [h2]; exact hσ

theorem period_flow (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x x' : (U.X k).dom)
    (s : (U.X k).Ψ → ℂ) (hσ : GoodEmb c σ) (hU : IsUnf U) (hξ : (U.X k).IsIso ξ')
    (hx : x'.1 = (U.X k).flow ξ' s x.1) (v : (Uw.F.Di (Uw.ik k)).La)
    (hv : herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0) : Uw.Pm k x' v = Uw.Pm k x v := by
  funext j
  rw [Uw.Pm_eq, Uw.Pm_eq, hx]
  have hf := (GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change E r (U.X k)).1 ξ' hξ.2.1 s x.1 x.2 (Uw.φ k v : Fin r → E)
  by_cases hm : relab c σ (Uw.e j).1 ∈ (U.X k).Ψ
  · have := (hf ⟨_, hm⟩ (Uw.e j).2).1
    simpa [hv] using this
  · have hm' : conjEmb (relab c σ (Uw.e j).1) ∈ (U.X k).Ψ := by
      by_contra h'
      exact hm (((U.X k).cmType _).2 h')
    have hcc : conjEmb (conjEmb (relab c σ (Uw.e j).1)) = relab c σ (Uw.e j).1 := by
      ext a; simp [conjEmb]
    have hne : ¬ (Uw.e j).1 (H.rt : E) = H.rt0 := fun h =>
      hm (((hU.2.1 k).2 _).2 (relab_rt hσ _ h))
    have hlt : ((Uw.e j).2 : ℕ) < (U.X k).p0 := by
      have h1 := (Uw.e j).2.2
      have h2 : Dw.mult (Uw.e j).1 = Dw.q := if_neg hne
      rw [(hU.2.1 k).1, ← h2]; exact h1
    have := (hf ⟨_, hm'⟩ (Uw.e j).2).2 hlt
    simpa [hv, hcc] using this

theorem riem_block (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom)
    (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (hH : IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm) (i j : Fin Uw.g)
    (hij : relab c σ (Uw.e i).1 ≠ relab c σ (Uw.e j).1) : Hm i j = 0 := by
  refine block_of_adjoint (fun j => relab c σ (Uw.e j).1) Hm (fun a z w => ?_) i j hij
  obtain ⟨hlin, -, -, hspan, -⟩ := Uw.period k x
  let a' : 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a
  have ha' : (a' : E) = cc (a : E) := rfl
  refine im_eq_on_span Hm Hm LinearMap.id (diagMul fun j => relab c σ (Uw.e j).1 (cc (a : E)))
    (diagMul fun j => relab c σ (Uw.e j).1 (a : E)) LinearMap.id (Set.range (Uw.Pm k x)) ?_ z
    (hspan ▸ Submodule.mem_top) w (hspan ▸ Submodule.mem_top)
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  have e1 : diagMul (fun j => relab c σ (Uw.e j).1 (a : E)) (Uw.Pm k x u) = Uw.Pm k x (a • u) := by
    funext j; exact (hlin a u j).symm
  have e2 : diagMul (fun j => relab c σ (Uw.e j).1 (cc (a : E))) (Uw.Pm k x v) = Uw.Pm k x (a' • v) := by
    funext j; exact (hlin a' v j).symm
  rw [e1, e2, LinearMap.id_apply, LinearMap.id_apply, hH.2.2, hH.2.2]
  have : (((Uw.F.Di (Uw.ik k)).EF (a • u) v : ℤ) : ℚ) = (((Uw.F.Di (Uw.ik k)).EF u (a' • v) : ℤ) : ℚ) := by
    rw [Uw.iso, Uw.iso, map_smul, map_smul]
    have s1 : ((a • Uw.φ k u : (U.X k).Λ) : Fin r → E) = (a : E) • (Uw.φ k u : Fin r → E) := rfl
    have s2 : ((a' • Uw.φ k v : (U.X k).Λ) : Fin r → E) = (a' : E) • (Uw.φ k v : Fin r → E) := rfl
    rw [s1, s2, herm_smul_left, herm_smul_right, ha']
    simp [cc]
  exact_mod_cast this

theorem lengths_along_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x x' : (U.X k).dom) (s : (U.X k).Ψ → ℂ) (Hm Hm' : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x'.1 = (U.X k).flow ξ' s x.1 → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x') Hm' → (∀ V : Submodule ℂ (Fin Uw.g → ℂ), (∀ z ∈ V, z ∈ Submodule.span ℝ {p | ∃ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 ∧ p = Uw.Pm k x v}) → ∀ z ∈ V, hermForm Hm' z z = hermForm Hm z z) ∧ ∀ t, (Uw.φ k t : Fin r → E) = ξ' → ∀ (τ : E →+* ℂ) (τ' : (U.X k).Ψ), (τ'.1 = relab c σ τ ∨ conjEmb τ'.1 = relab c σ τ) → (hermForm Hm' (fun j => if (Uw.e j).1 = τ then Uw.Pm k x t j else 0) (fun j => if (Uw.e j).1 = τ then Uw.Pm k x t j else 0)).re ≤ ((U.X k).tt ξ' x'.1 τ')⁻¹ := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x x' s Hm Hm' hσ hU hξ hx hH hH'
  have hper := period_flow U Uw k ξ' x x' s hσ hU hξ hx
  refine ⟨fun V hV z hz => ?_, fun t ht τ τ' hτ => ?_⟩
  · have him := im_eq_on_span Hm Hm' LinearMap.id LinearMap.id LinearMap.id LinearMap.id
      {p | ∃ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 ∧ p = Uw.Pm k x v} (by
        rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
        simp only [LinearMap.id_apply]
        rw [hH.2.2, ← hper u hu, ← hper v hv, hH'.2.2])
    simp only [LinearMap.id_apply] at him
    apply Complex.ext
    · have := him _ (hV _ (V.smul_mem Complex.I hz)) _ (hV _ hz)
      simpa [hermForm_smul_left] using this
    · exact him _ (hV _ hz) _ (hV _ hz)
  · rw [← hper t (by rw [ht]; exact hξ.2.1)]
    have hmaj := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x' Hm' hσ hU hH').1
    have hlin := (Uw.period k x').1
    have key := block_le (U.X k).Ψ (U.X k).cmType (fun j => relab c σ (Uw.e j).1) Hm' hH'.2.1
      (riem_block U Uw k x' Hm' hH') (Uw.Pm k x' t)
      (fun τ => (U.X k).c τ * (U.X k).maj x'.1 τ (Data.emb τ.1 ξ')) (fun a => by
        have e1 : (fun j => relab c σ (Uw.e j).1 (a : E) * Uw.Pm k x' t j) = Uw.Pm k x' (a • t) := by
          funext j; exact (hlin a t j).symm
        rw [e1, hmaj]
        refine Finset.sum_congr rfl fun τ _ => ?_
        have e2 : Data.emb τ.1 (Uw.φ k (a • t) : Fin r → E) = τ.1 (a : E) • Data.emb τ.1 ξ' := by
          rw [map_smul, ← ht]
          funext b
          exact map_mul τ.1 (a : E) _
        rw [e2, maj_smul]; ring) (relab c σ τ) τ' hτ
    simp only [(relab_inj c σ).eq_iff] at key
    rw [Data.tt, one_div, inv_inv]
    exact key

end GlobalTheory.ArchLen
