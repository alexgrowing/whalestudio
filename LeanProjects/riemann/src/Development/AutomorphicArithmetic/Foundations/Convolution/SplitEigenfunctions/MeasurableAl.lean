import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

variable {E : Type} [Field E] [NumberField E]

private theorem isClosed_vle {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsClosed {p : K × K | (Valued.v p.2 : Γ) ≤ Valued.v p.1} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  have hp' : (Valued.v p.1 : Γ) < Valued.v p.2 := not_le.1 hp
  have hne : (Valued.v p.2 : Γ) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  have hB : IsOpen {x : K | (Valued.v x : Γ) < Valued.v p.2} := by
    have := Valued.isOpen_ball K (Valued.v.restrict p.2)
    simpa only [Valuation.restrict_lt_iff] using this
  have hN : ({x : K | (Valued.v x : Γ) < Valued.v p.2} ×ˢ {y : K | (Valued.v y : Γ) = Valued.v p.2}) ∈ 𝓝 p :=
    prod_mem_nhds (hB.mem_nhds hp') (Valued.locally_const hne)
  filter_upwards [hN] with q hq
  have h1 : (Valued.v q.1 : Γ) < Valued.v p.2 := hq.1
  have h2 : (Valued.v q.2 : Γ) = Valued.v p.2 := hq.2
  show ¬ (Valued.v q.2 : Γ) ≤ Valued.v q.1
  rw [h2]
  exact not_le.2 h1

private def pI (h : G1 E) (v : InfinitePlace E) : v.Completion :=
  if ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ then (h 1 0).1 v else (h 1 1).1 v

private def pF (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E :=
  if Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) then (h 1 0).2 w else (h 1 1).2 w

private theorem det_eq (h : G1 E) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  have := h.2
  rwa [Matrix.det_fin_two] at this

private theorem det_I (h : G1 E) (v : InfinitePlace E) :
    (h 0 0).1 v * (h 1 1).1 v - (h 0 1).1 v * (h 1 0).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (det_eq h)

private theorem det_F (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    (h 0 0).2 w * (h 1 1).2 w - (h 0 1).2 w * (h 1 0).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (det_eq h)

private theorem pI_ne (h : G1 E) (v : InfinitePlace E) : pI h v ≠ 0 := by
  unfold pI
  split_ifs with hc
  · intro h0
    rw [h0, norm_zero] at hc
    have hd : (h 1 1).1 v = 0 := norm_le_zero_iff.1 hc
    have := det_I h v
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, norm_zero] at hc
    exact hc (norm_nonneg _)

private theorem pF_ne (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : pF h w ≠ 0 := by
  unfold pF
  split_ifs with hc
  · intro h0
    rw [h0, map_zero] at hc
    have hd : (h 1 1).2 w = 0 := (map_eq_zero _).1 (le_zero_iff.1 hc)
    have := det_F h w
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, map_zero] at hc
    exact hc zero_le'

private theorem pF_one (h : G1 E) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, Valued.v (pF h w) = 1 := by
  filter_upwards [(h 0 0).2.2, (h 0 1).2.2, (h 1 0).2.2, (h 1 1).2.2] with w ha hb hc hd
  have ha' : Valued.v ((h 0 0).2 w) ≤ 1 := ha
  have hb' : Valued.v ((h 0 1).2 w) ≤ 1 := hb
  have hc' : Valued.v ((h 1 0).2 w) ≤ 1 := hc
  have hd' : Valued.v ((h 1 1).2 w) ≤ 1 := hd
  have hmax : ¬ (Valued.v ((h 1 0).2 w) < 1 ∧ Valued.v ((h 1 1).2 w) < 1) := by
    rintro ⟨h1, h2⟩
    have e1 : Valued.v ((h 0 0).2 w * (h 1 1).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha') h2
    have e2 : Valued.v ((h 0 1).2 w * (h 1 0).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb') h1
    have := Valuation.map_sub_lt _ e1 e2
    rw [det_F h w, map_one] at this
    exact lt_irrefl _ this
  unfold pF
  split_ifs with hle
  · by_contra hne
    exact hmax ⟨lt_of_le_of_ne hc' hne, lt_of_le_of_lt hle (lt_of_le_of_ne hc' hne)⟩
  · by_contra hne
    exact hmax ⟨lt_of_lt_of_le (not_le.1 hle) hd', lt_of_le_of_ne hd' hne⟩

private def bF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨pF h, (pF_one h).mono fun w hw => (le_of_eq hw : Valued.v (pF h w) ≤ 1)⟩

private def cF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => (pF h w)⁻¹, (pF_one h).mono fun w hw =>
    (le_of_eq (by rw [map_inv₀, hw, inv_one]) : Valued.v (pF h w)⁻¹ ≤ 1)⟩

private def al (h : G1 E) : IdeleGroup E where
  val := (fun v => (pI h v)⁻¹, cF h)
  inv := (fun v => pI h v, bF h)
  val_inv := Prod.ext (funext fun v => inv_mul_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => inv_mul_cancel₀ (pF_ne h w))
  inv_val := Prod.ext (funext fun v => mul_inv_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => mul_inv_cancel₀ (pF_ne h w))

private def co (x : IdeleGroup E) :
    (∀ v : InfinitePlace E, v.Completion) × (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) :=
  (((x⁻¹ : IdeleGroup E) : A E).1, fun w => ((x⁻¹ : IdeleGroup E) : A E).2 w)

private theorem continuous_co : Continuous (co : IdeleGroup E → _) := by
  have h0 : Continuous fun x : IdeleGroup E => ((x⁻¹ : IdeleGroup E) : A E) :=
    Units.continuous_val.comp continuous_inv
  refine Continuous.prodMk (continuous_fst.comp h0) (continuous_pi fun w => ?_)
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp h0)

private theorem injective_co : Function.Injective (co : IdeleGroup E → _) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  apply inv_injective
  apply Units.ext
  exact Prod.ext h1 (Subtype.ext <| funext fun w => congrFun h2 w)

private theorem cont_e (i j : Fin 2) : Continuous fun h : G1 E => (h i j : A E) :=
  Continuous.matrix_elem continuous_subtype_val i j

private theorem cont_I (i j : Fin 2) (v : InfinitePlace E) : Continuous fun h : G1 E => (h i j).1 v :=
  (continuous_apply v).comp (continuous_fst.comp (cont_e i j))

private theorem cont_F (i j : Fin 2) (w : HeightOneSpectrum (𝓞 E)) : Continuous fun h : G1 E => (h i j).2 w :=
  (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp (cont_e i j))

private theorem measurable_al : Measurable (al : G1 E → IdeleGroup E) := by
  letI : ∀ v : InfinitePlace E, MeasurableSpace v.Completion := fun _ => borel _
  haveI : ∀ v : InfinitePlace E, BorelSpace v.Completion := fun _ => ⟨rfl⟩
  letI : ∀ w : HeightOneSpectrum (𝓞 E), MeasurableSpace (w.adicCompletion E) := fun _ => borel _
  haveI : ∀ w : HeightOneSpectrum (𝓞 E), BorelSpace (w.adicCompletion E) := fun _ => ⟨rfl⟩
  have hc := comap_eq_borel_of_continuous_injective (continuous_co (E := E)) (injective_co (E := E))
  have hm : Measurable ((co : IdeleGroup E → _) ∘ (al : G1 E → IdeleGroup E)) := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun v => ?_) (measurable_pi_iff.2 fun w => ?_)
    · have hS : MeasurableSet {h : G1 E | ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖} :=
        (isClosed_le (cont_I 1 1 v).norm (cont_I 1 0 v).norm).measurableSet
      exact Measurable.ite hS (cont_I 1 0 v).measurable (cont_I 1 1 v).measurable
    · have hS : MeasurableSet {h : G1 E | Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)} :=
        (isClosed_vle.preimage ((cont_F 1 0 w).prodMk (cont_F 1 1 w))).measurableSet
      exact Measurable.ite hS (cont_F 1 0 w).measurable (cont_F 1 1 w).measurable
  have h2 := measurable_comap_iff.2 hm
  rw [hc, ← BorelSpace.measurable_eq] at h2
  exact h2

private theorem e_nU (u : A E) (h : G1 E) (j : Fin 2) : (nU u * h) 1 j = h 1 j := by
  show ((nU u).1 * h.1) 1 j = h.1 1 j
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e_mD (t : (A E)ˣ) (h : G1 E) (j : Fin 2) :
    (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := by
  show ((mD t).1 * h.1) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h.1 1 j
  simp [mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem al_nU (u : A E) (h : G1 E) : al (nU u * h) = al h := by
  have hI : pI (nU u * h) = pI h := by
    funext v
    simp only [pI, e_nU]
  have hF : pF (nU u * h) = pF h := by
    funext w
    simp only [pF, e_nU]
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (nU u * h) v)⁻¹ = (pI h v)⁻¹
    rw [hI]
  · show (pF (nU u * h) w)⁻¹ = (pF h w)⁻¹
    rw [hF]

private theorem tI (t : (A E)ˣ) (v : InfinitePlace E) :
    ((t⁻¹ : (A E)ˣ) : A E).1 v * (t : A E).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (Units.inv_mul t)

private theorem tF (t : (A E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((t⁻¹ : (A E)ˣ) : A E).2 w * (t : A E).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (Units.inv_mul t)

private theorem pI_mD (t : (A E)ˣ) (h : G1 E) (v : InfinitePlace E) :
    pI (mD t * h) v = ((t⁻¹ : (A E)ˣ) : A E).1 v * pI h v := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).1 v ≠ 0 := left_ne_zero_of_mul_eq_one (tI t v)
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).1 v = ((t⁻¹ : (A E)ˣ) : A E).1 v * (h 1 j).1 v := fun j => by rw [e j]; rfl
  have key : ‖((mD t * h) 1 1).1 v‖ ≤ ‖((mD t * h) 1 0).1 v‖ ↔ ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ := by
    rw [e', e', norm_mul, norm_mul]
    exact mul_le_mul_iff_of_pos_left (norm_pos_iff.2 hs)
  unfold pI
  by_cases hc : ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem pF_mD (t : (A E)ˣ) (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    pF (mD t * h) w = ((t⁻¹ : (A E)ˣ) : A E).2 w * pF h w := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).2 w ≠ 0 := left_ne_zero_of_mul_eq_one (tF t w)
  have hs' : Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w) ≠ 0 := (Valuation.ne_zero_iff _).2 hs
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).2 w = ((t⁻¹ : (A E)ˣ) : A E).2 w * (h 1 j).2 w := fun j => by rw [e j]; rfl
  have key : Valued.v (((mD t * h) 1 1).2 w) ≤ Valued.v (((mD t * h) 1 0).2 w) ↔
      Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) := by
    rw [e', e', map_mul, map_mul]
    constructor
    · intro x
      have := mul_le_mul_right x (Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w))⁻¹
      simpa [inv_mul_cancel_left₀ hs'] using this
    · intro x
      exact mul_le_mul_right x _
  unfold pF
  by_cases hc : Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem al_mD (t : (A E)ˣ) (h : G1 E) : al (mD t * h) = t * al h := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (mD t * h) v)⁻¹ = (t : A E).1 v * (pI h v)⁻¹
    rw [pI_mD, mul_inv, inv_eq_of_mul_eq_one_right (tI t v)]
  · show (pF (mD t * h) w)⁻¹ = (t : A E).2 w * (pF h w)⁻¹
    rw [pF_mD, mul_inv, inv_eq_of_mul_eq_one_right (tF t w)]

end UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.torCo :
    TorCo := by
  intro E _ _
  exact ⟨al, measurable_al, al_nU, al_mD⟩
