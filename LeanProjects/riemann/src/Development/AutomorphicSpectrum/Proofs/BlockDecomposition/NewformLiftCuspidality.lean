import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.CompactAbelianCharacters
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.NewformLiftCuspidality

open Ad3 Ad3.R

def cf (f : 𝔸[ℚ] → ℂ) (α : ℚ) : ℂ :=
  ∫ x in fundamentalSet ℚ, f x * (adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] α * x)) : ℂ) ∂adeleMeasure ℚ

theorem continuous_unipotentGL2 : Continuous (uni2 : 𝔸[ℚ] → G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop

theorem rationalEmbedding_unipotent (q : ℚ) : dia2 (uni2 q) = uni2 (algebraMap ℚ 𝔸[ℚ] q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AdelicGLn.diagonal_apply, uni2]

theorem rationalEmbedding_diagonal (α : ℚˣ) : dia2 (dg2 α 1) = dg2 (pri α) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AdelicGLn.diagonal_apply, dg2, pri]

theorem unipotent_add (x y : 𝔸[ℚ]) : (uni2 (x + y) : G2) = uni2 x * uni2 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> exact add_comm _ _

theorem periodic_of_LInv {X : Type} {φ : G2 → X} (hL : LInv φ) (g : G2) (q : ℚ) (x : 𝔸[ℚ]) :
    φ (uni2 (algebraMap ℚ 𝔸[ℚ] q + x) * g) = φ (uni2 x * g) := by
  rw [unipotent_add, ← rationalEmbedding_unipotent, mul_assoc, hL]

theorem unipotent_mul_torus_commute (a : Jd) (x : 𝔸[ℚ]) :
    (uni2 x * dg2 a 1 : G2) = dg2 a 1 * uni2 (((a⁻¹ : Jd) : 𝔸[ℚ]) * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_mul_diagonal_alt (a b : Jd) : (dg2 (a * b) 1 : G2) = dg2 a 1 * dg2 b 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem fd_preimage (T : 𝔸[ℚ] ≃ₜ 𝔸[ℚ]) (σ : ℚ ≃ ℚ)
    (hT : ∀ (q : ℚ) x, T (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ q) + T x) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (T ⁻¹' fundamentalSet ℚ) (adeleMeasure ℚ) := by
  refine IsAddFundamentalDomain.mk'
    ((measurableSet_fundamentalSet ℚ).preimage T.continuous.measurable).nullMeasurableSet fun x => ?_
  obtain ⟨k, hk, hu⟩ := existsUnique_sub_mem_fundamentalSet ℚ (T x)
  refine ⟨⟨algebraMap ℚ 𝔸[ℚ] (σ.symm (-k)), _, rfl⟩, ?_, ?_⟩
  · change T (algebraMap ℚ 𝔸[ℚ] (σ.symm (-k)) + x) ∈ fundamentalSet ℚ
    rw [hT, σ.apply_symm_apply, map_neg, neg_add_eq_sub]
    exact hk
  · rintro ⟨_, ξ, rfl⟩ h
    have h' : T (algebraMap ℚ 𝔸[ℚ] ξ + x) ∈ fundamentalSet ℚ := h
    rw [hT] at h'
    have e : -σ ξ = k := hu _ (by
      show T x - algebraMap ℚ 𝔸[ℚ] (-σ ξ) ∈ fundamentalSet ℚ
      rw [map_neg, sub_neg_eq_add, add_comm]; exact h')
    refine Subtype.ext ?_
    change algebraMap ℚ 𝔸[ℚ] ξ = algebraMap ℚ 𝔸[ℚ] (σ.symm (-k))
    rw [← e, neg_neg, σ.symm_apply_apply]

theorem hT_symm (T : 𝔸[ℚ] ≃ₜ 𝔸[ℚ]) (σ : ℚ ≃ ℚ)
    (hT : ∀ (q : ℚ) x, T (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ q) + T x) (q : ℚ) (x : 𝔸[ℚ]) :
    T.symm (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ.symm q) + T.symm x := by
  apply T.injective
  rw [hT, T.apply_symm_apply, T.apply_symm_apply, σ.apply_symm_apply]

theorem setIntegral_comp (T : 𝔸[ℚ] ≃ₜ 𝔸[ℚ]) (σ : ℚ ≃ ℚ)
    (hT : ∀ (q : ℚ) x, T (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (σ q) + T x)
    (hm : MeasurePreserving T (adeleMeasure ℚ) (adeleMeasure ℚ)) (h : 𝔸[ℚ] → ℂ)
    (hh : ∀ (q : ℚ) x, h (algebraMap ℚ 𝔸[ℚ] q + x) = h x) :
    ∫ x in fundamentalSet ℚ, h (T x) ∂adeleMeasure ℚ = ∫ x in fundamentalSet ℚ, h x ∂adeleMeasure ℚ := by
  have fd := fd_preimage T.symm σ.symm (hT_symm T σ hT)
  have e := hm.setIntegral_preimage_emb T.measurableEmbedding h (T.symm ⁻¹' fundamentalSet ℚ)
  have e2 : T ⁻¹' (T.symm ⁻¹' fundamentalSet ℚ) = fundamentalSet ℚ := by
    ext x; simp
  rw [e2] at e
  rw [e]
  refine fd.setIntegral_eq (isAddFundamentalDomain_fundamentalSet ℚ) ?_
  rintro ⟨_, q, rfl⟩ x
  exact hh q x

def scaleH (α : ℚˣ) : 𝔸[ℚ] ≃ₜ 𝔸[ℚ] := Homeomorph.smul (pri α)

theorem scaleH_apply (α : ℚˣ) (x : 𝔸[ℚ]) : scaleH α x = algebraMap ℚ 𝔸[ℚ] α * x := rfl

theorem scaleH_add (α : ℚˣ) (q : ℚ) (x : 𝔸[ℚ]) :
    scaleH α (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (Units.mulLeft α q) + scaleH α x := by
  simp only [scaleH_apply, mul_add, Units.mulLeft_apply, map_mul]

theorem measurePreserving_scaleH (α : ℚˣ) :
    MeasurePreserving (scaleH α) (adeleMeasure ℚ) (adeleMeasure ℚ) := by
  refine ⟨(scaleH α).continuous.measurable, ?_⟩
  have hmap : (adeleMeasure ℚ).map (scaleH α) = _ := map_smul_adeleMeasure (K := ℚ) (pri α)
  have hfd := fd_preimage (scaleH α) (Units.mulLeft α) (scaleH_add α)
  have h1 := hfd.measure_eq (isAddFundamentalDomain_fundamentalSet ℚ)
  rw [adeleMeasure_fundamentalSet] at h1
  have hD := measurableSet_fundamentalSet ℚ
  have h2 := congrArg (fun ν : Measure 𝔸[ℚ] => ν (fundamentalSet ℚ)) hmap
  simp only [Measure.smul_apply, adeleMeasure_fundamentalSet, smul_eq_mul, mul_one] at h2
  rw [Measure.map_apply (scaleH α).continuous.measurable hD, h1] at h2
  rw [hmap, ← h2, one_smul]

theorem coef (φ : G2 → ℂ) (hL : LInv φ) (α : ℚˣ) (g : G2) :
    Wh φ (dg2 (pri α) 1 * g) = cf (fun x => φ (uni2 x * g)) α := by
  set h : 𝔸[ℚ] → ℂ := fun y => φ (uni2 y * g) * (adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] α * y)) : ℂ) with hh
  have hper : ∀ (q : ℚ) x, h (algebraMap ℚ 𝔸[ℚ] q + x) = h x := by
    intro q x
    simp only [hh, periodic_of_LInv hL g q x]
    congr 2
    rw [mul_add, ← map_mul, neg_add, AddChar.map_add_eq_mul, ← map_neg, adelicChar_algebraMap, one_mul]
  have e := setIntegral_comp (scaleH α⁻¹) (Units.mulLeft α⁻¹) (scaleH_add α⁻¹) (measurePreserving_scaleH α⁻¹) h hper
  unfold cf Wh
  rw [← e]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hh, scaleH_apply]
  have e1 : algebraMap ℚ 𝔸[ℚ] ((α : ℚ)) * (algebraMap ℚ 𝔸[ℚ] ((α⁻¹ : ℚˣ) : ℚ) * x) = x := by
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [e1, ← mul_assoc, unipotent_mul_torus_commute, mul_assoc, ← rationalEmbedding_diagonal, hL]
  rfl

def Cq : Type := Multiplicative (AdeleQuotient ℚ)

instance : CommGroup Cq := inferInstanceAs (CommGroup (Multiplicative (AdeleQuotient ℚ)))
instance : TopologicalSpace Cq := inferInstanceAs (TopologicalSpace (Multiplicative (AdeleQuotient ℚ)))
instance : IsTopologicalGroup Cq := inferInstanceAs (IsTopologicalGroup (Multiplicative (AdeleQuotient ℚ)))
instance : CompactSpace Cq := inferInstanceAs (CompactSpace (AdeleQuotient ℚ))
instance : T2Space Cq := inferInstanceAs (T2Space (AdeleQuotient ℚ))
instance : MeasurableSpace Cq := borel Cq
instance : BorelSpace Cq := ⟨rfl⟩

def pc (x : 𝔸[ℚ]) : Cq := Multiplicative.ofAdd (QuotientAddGroup.mk x : AdeleQuotient ℚ)

theorem isQuotientMap_pc : IsQuotientMap pc :=
  QuotientAddGroup.isQuotientMap_mk (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)

theorem continuous_pc : Continuous pc := isQuotientMap_pc.continuous

theorem pc_surjective : Function.Surjective pc := isQuotientMap_pc.surjective

theorem pc_add (x y : 𝔸[ℚ]) : pc (x + y) = pc x * pc y := rfl

theorem pc_zero : pc 0 = 1 := rfl

theorem exists_of_pc_eq {x y : 𝔸[ℚ]} (h : pc x = pc y) : ∃ q : ℚ, y = algebraMap ℚ 𝔸[ℚ] q + x := by
  obtain ⟨q, hq⟩ := QuotientAddGroup.eq.1 (Multiplicative.ofAdd.injective h)
  refine ⟨q, ?_⟩
  have hq' : algebraMap ℚ 𝔸[ℚ] q = -x + y := hq
  rw [hq']; abel

theorem pc_algebraMap_add (q : ℚ) (x : 𝔸[ℚ]) : pc (algebraMap ℚ 𝔸[ℚ] q + x) = pc x := by
  rw [pc_add]
  have : pc (algebraMap ℚ 𝔸[ℚ] q) = 1 :=
    congrArg Multiplicative.ofAdd ((QuotientAddGroup.eq_zero_iff _).2 ⟨q, rfl⟩)
  rw [this, one_mul]

def desc {X : Type} (f : 𝔸[ℚ] → X) (c : Cq) : X := f (Function.surjInv pc_surjective c)

theorem desc_pc {X : Type} {f : 𝔸[ℚ] → X} (hp : ∀ (q : ℚ) x, f (algebraMap ℚ 𝔸[ℚ] q + x) = f x) (x : 𝔸[ℚ]) :
    desc f (pc x) = f x := by
  obtain ⟨q, hq⟩ := exists_of_pc_eq (Function.surjInv_eq pc_surjective (pc x)).symm
  rw [desc, show Function.surjInv pc_surjective (pc x) = algebraMap ℚ 𝔸[ℚ] q + x from hq, hp]

theorem continuous_desc {X : Type} [TopologicalSpace X] {f : 𝔸[ℚ] → X} (hf : Continuous f)
    (hp : ∀ (q : ℚ) x, f (algebraMap ℚ 𝔸[ℚ] q + x) = f x) : Continuous (desc f) := by
  rw [isQuotientMap_pc.continuous_iff]
  have : desc f ∘ pc = f := funext (desc_pc hp)
  rwa [this]

def nu : Measure Cq := ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)).map pc

instance : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
  ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]⟩

instance : IsProbabilityMeasure nu :=
  Measure.isProbabilityMeasure_map continuous_pc.aemeasurable

theorem addRight_add (a : 𝔸[ℚ]) (q : ℚ) (x : 𝔸[ℚ]) :
    Homeomorph.addRight a (algebraMap ℚ 𝔸[ℚ] q + x) = algebraMap ℚ 𝔸[ℚ] (Equiv.refl ℚ q) + Homeomorph.addRight a x := by
  simp [add_assoc]

instance : nu.IsMulLeftInvariant := by
  refine ⟨fun c => ?_⟩
  obtain ⟨a, rfl⟩ := pc_surjective c
  set T := Homeomorph.addRight a with hTdef
  have hTm : MeasurePreserving T (adeleMeasure ℚ) (adeleMeasure ℚ) := measurePreserving_add_right _ a
  have hD := measurableSet_fundamentalSet ℚ
  ext E hE
  have hEm : MeasurableSet (pc ⁻¹' E) := continuous_pc.measurable hE
  have hmul : Measurable (fun x : Cq => pc a * x) := (by fun_prop : Continuous fun x : Cq => pc a * x).measurable
  rw [Measure.map_apply hmul hE, nu, Measure.map_apply continuous_pc.measurable hE,
    Measure.map_apply continuous_pc.measurable (hmul hE),
    Measure.restrict_apply hEm, Measure.restrict_apply (continuous_pc.measurable (hmul hE))]
  have fd := fd_preimage T.symm (Equiv.refl ℚ).symm (hT_symm T (Equiv.refl ℚ) (addRight_add a))
  have h1 := fd.measure_set_eq (isAddFundamentalDomain_fundamentalSet ℚ) hEm (by
    rintro ⟨_, q, rfl⟩
    ext x
    change pc (algebraMap ℚ 𝔸[ℚ] q + x) ∈ E ↔ pc x ∈ E
    rw [pc_algebraMap_add])
  rw [← h1]
  have h2 : (pc ⁻¹' ((fun x => pc a * x) ⁻¹' E)) ∩ fundamentalSet ℚ =
      T ⁻¹' (pc ⁻¹' E ∩ T.symm ⁻¹' fundamentalSet ℚ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Homeomorph.symm_apply_apply]
    rw [hTdef, Homeomorph.coe_addRight, pc_add, mul_comm]
  rw [h2]
  exact hTm.measure_preimage (hEm.inter ((hD.preimage T.symm.continuous.measurable))).nullMeasurableSet

instance : nu.IsHaarMeasure := by
  haveI : nu.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by simp)
  exact {}

theorem integral_nu (G : Cq → ℂ) (hG : Continuous G) :
    ∫ c, G c ∂nu = ∫ x in fundamentalSet ℚ, G (pc x) ∂adeleMeasure ℚ :=
  integral_map continuous_pc.aemeasurable hG.aestronglyMeasurable

theorem char_periodic (α : ℚ) (q : ℚ) (x : 𝔸[ℚ]) :
    adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * (algebraMap ℚ 𝔸[ℚ] q + x)) = adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x) := by
  rw [mul_add, ← map_mul, AddChar.map_add_eq_mul, adelicChar_algebraMap, one_mul]

def ech (α : ℚ) : Cq →ₜ* Circle where
  toFun := desc fun x => adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x)
  map_one' := by
    rw [← pc_zero, desc_pc (f := fun x => adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x)) (char_periodic α)]
    simp
  map_mul' := by
    intro c d
    obtain ⟨x, rfl⟩ := pc_surjective c
    obtain ⟨y, rfl⟩ := pc_surjective d
    have hd := desc_pc (f := fun x => adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x)) (char_periodic α)
    rw [← pc_add, hd, hd, hd, mul_add, AddChar.map_add_eq_mul]
  continuous_toFun := continuous_desc (continuous_adelicChar_mul α) (char_periodic α)

theorem ech_pc (α : ℚ) (x : 𝔸[ℚ]) : ech α (pc x) = adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x) :=
  desc_pc (f := fun x => adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x)) (char_periodic α) x

theorem ech_bijective : Function.Bijective ech := by
  constructor
  · intro α β h
    refine eq_of_forall_adelicChar_mul_eq fun x => ?_
    rw [← ech_pc, ← ech_pc, h]
  · intro χ
    let χ' : AddChar (AdeleQuotient ℚ) Circle :=
      { toFun := fun c => χ (Multiplicative.ofAdd c)
        map_zero_eq_one' := map_one χ
        map_add_eq_mul' := fun a b => map_mul χ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) }
    have hχ' : Continuous χ' := χ.continuous_toFun
    obtain ⟨ξ, hξ, -⟩ := existsUnique_adeleQuotient_char_eq χ' hχ'
    refine ⟨ξ, ContinuousMonoidHom.ext fun c => ?_⟩
    obtain ⟨x, rfl⟩ := pc_surjective c
    rw [ech_pc, ← hξ x]
    rfl

open GroundTheory.Automorphic.CompactAbelianFourier in
theorem parseval (f f' : 𝔸[ℚ] → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hp : ∀ (q : ℚ) x, f (algebraMap ℚ 𝔸[ℚ] q + x) = f x)
    (hp' : ∀ (q : ℚ) x, f' (algebraMap ℚ 𝔸[ℚ] q + x) = f' x) :
    HasSum (fun α : ℚ => cf f α * conj (cf f' α)) (∫ x in fundamentalSet ℚ, f x * conj (f' x) ∂adeleMeasure ℚ) := by
  let F : C(Cq, ℂ) := ⟨desc f, continuous_desc hf hp⟩
  let F' : C(Cq, ℂ) := ⟨desc f', continuous_desc hf' hp'⟩
  have hF : ∀ x, F (pc x) = f x := desc_pc hp
  have hF' : ∀ x, F' (pc x) = f' x := desc_pc hp'
  have hco : ∀ (G : C(Cq, ℂ)) (g : 𝔸[ℚ] → ℂ), (∀ x, G (pc x) = g x) → ∀ α,
      inner ℂ (charL2 nu (ech α)) (ContinuousMap.toLp 2 nu ℂ G) = cf g α := by
    intro G g hG α
    rw [inner_charL2_toLp]
    refine (integral_nu _ ((Complex.continuous_conj.comp (charCM (ech α)).continuous).mul G.continuous)).trans ?_
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show conj ((ech α (pc x) : Circle) : ℂ) * G (pc x) = _
    rw [ech_pc, hG]
    show conj ((adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] α * x) : Circle) : ℂ) * g x =
      g x * ((adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] α * x)) : Circle) : ℂ)
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, mul_comm]
  have h := (charBasis nu).hasSum_inner_mul_inner (ContinuousMap.toLp 2 nu ℂ F') (ContinuousMap.toLp 2 nu ℂ F)
  rw [coe_charBasis] at h
  have h2 := ((Equiv.ofBijective ech ech_bijective).hasSum_iff).2 h
  have e1 : inner ℂ (ContinuousMap.toLp 2 nu ℂ F') (ContinuousMap.toLp 2 nu ℂ F) =
      ∫ x in fundamentalSet ℚ, f x * conj (f' x) ∂adeleMeasure ℚ := by
    rw [ContinuousMap.inner_toLp]
    refine (integral_nu _ (F.continuous.mul (Complex.continuous_conj.comp F'.continuous))).trans ?_
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show F (pc x) * conj (F' (pc x)) = _
    rw [hF, hF']
  rw [e1] at h2
  have e3 : ∀ α, ((fun i : Cq →ₜ* Circle => inner ℂ (ContinuousMap.toLp 2 nu ℂ F') (charL2 nu i) *
      inner ℂ (charL2 nu i) (ContinuousMap.toLp 2 nu ℂ F)) ∘ ⇑(Equiv.ofBijective ech ech_bijective)) α =
      cf f α * conj (cf f' α) := by
    intro α
    simp only [Function.comp, Equiv.ofBijective_apply]
    rw [← inner_conj_symm, hco F f hF, hco F' f' hF', mul_comm]
  rwa [funext e3] at h2

theorem sq_sum_le (f : 𝔸[ℚ] → ℂ) (hf : Continuous f) (hp : ∀ (q : ℚ) x, f (algebraMap ℚ 𝔸[ℚ] q + x) = f x)
    (A : ℝ) (hA : ∀ x, ‖f x‖ ≤ A) :
    ∃ S : ℝ, HasSum (fun α : ℚ => ‖cf f α‖ ^ 2) S ∧ S ≤ A ^ 2 := by
  have h := parseval f f hf hf hp hp
  have e1 : ∀ α, cf f α * conj (cf f α) = ((‖cf f α‖ ^ 2 : ℝ) : ℂ) := fun α => by
    rw [Complex.mul_conj']; push_cast; rfl
  have e2 : ∀ x, f x * conj (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.mul_conj']; push_cast; rfl
  simp only [e1, e2] at h
  rw [integral_complex_ofReal] at h
  refine ⟨_, Complex.hasSum_ofReal.1 h, ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hb := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure ℚ) (s := fundamentalSet ℚ)
    (f := fun x => ‖f x‖ ^ 2) (C := A ^ 2) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top)
    (fun x _ => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hA x) 2)
  rw [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one] at hb
  exact (le_abs_self _).trans hb

theorem sum_bound (f f' : 𝔸[ℚ] → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hp : ∀ (q : ℚ) x, f (algebraMap ℚ 𝔸[ℚ] q + x) = f x)
    (hp' : ∀ (q : ℚ) x, f' (algebraMap ℚ 𝔸[ℚ] q + x) = f' x) (A B : ℝ) (hA0 : 0 < A) (hB0 : 0 < B)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖f' x‖ ≤ B) :
    ∑' α : ℚˣ, ‖cf f α * conj (cf f' α)‖ₑ ≤ ENNReal.ofReal (A * B) := by
  obtain ⟨S, hS, hSA⟩ := sq_sum_le f hf hp A hA
  obtain ⟨S', hS', hSB⟩ := sq_sum_le f' hf' hp' B hB
  set w : ℚ → ℝ := fun α => B / (2 * A) * ‖cf f α‖ ^ 2 + A / (2 * B) * ‖cf f' α‖ ^ 2 with hw
  have hsum : HasSum w (B / (2 * A) * S + A / (2 * B) * S') := (hS.mul_left _).add (hS'.mul_left _)
  have hw0 : ∀ α, 0 ≤ w α := fun α => by positivity
  have hle : ∀ α, ‖cf f α * conj (cf f' α)‖ ≤ w α := fun α => by
    rw [norm_mul, RCLike.norm_conj]
    set u := ‖cf f α‖
    set v := ‖cf f' α‖
    have : 0 ≤ (B * u - A * v) ^ 2 / (2 * A * B) := by positivity
    have e : (B * u - A * v) ^ 2 / (2 * A * B) = B / (2 * A) * u ^ 2 + A / (2 * B) * v ^ 2 - u * v := by
      field_simp
      ring
    simp only [hw]
    linarith
  calc ∑' α : ℚˣ, ‖cf f α * conj (cf f' α)‖ₑ ≤ ∑' α : ℚ, ‖cf f α * conj (cf f' α)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun α : ℚˣ => (α : ℚ)) Units.val_injective
          (fun α : ℚ => ‖cf f α * conj (cf f' α)‖ₑ)
    _ ≤ ∑' α : ℚ, ENNReal.ofReal (w α) := ENNReal.tsum_le_tsum fun α => by
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hle α)
    _ = ENNReal.ofReal (∑' α, w α) := (ENNReal.ofReal_tsum_of_nonneg hw0 hsum.summable).symm
    _ ≤ ENNReal.ofReal (A * B) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsum.tsum_eq]
        have h1 : B / (2 * A) * S ≤ B / (2 * A) * A ^ 2 := by gcongr
        have h2 : A / (2 * B) * S' ≤ A / (2 * B) * B ^ 2 := by gcongr
        have e1 : B / (2 * A) * A ^ 2 + A / (2 * B) * B ^ 2 = A * B := by field_simp; ring
        linarith

theorem f6 : Ad3.R.F6 := by
  intro φ φ' hφ hφ' hL hL' hD hB hc hW hW'
  obtain ⟨B, hB⟩ := hB
  have hcont : ∀ {ρ : G2 → ℂ}, Continuous ρ → ∀ g : G2, Continuous fun x : 𝔸[ℚ] => ρ (uni2 x * g) :=
    fun h g => h.comp (continuous_unipotentGL2.mul continuous_const)
  have hterm : ∀ (a : Jd) (κ : KA) (α : ℚˣ), Wh φ (dg2 (pri α * a) 1 * κ.1) * conj (Wh φ' (dg2 (pri α * a) 1 * κ.1)) =
      cf (fun x => φ (uni2 x * (dg2 a 1 * κ.1))) α * conj (cf (fun x => φ' (uni2 x * (dg2 a 1 * κ.1))) α) := by
    intro a κ α
    rw [diagonal_mul_diagonal_alt, mul_assoc, coef φ hL, coef φ' hL']
  refine ⟨hW.mul (Complex.continuous_conj.comp hW'), ?_, ?_⟩
  · intro a κ
    set g : G2 := dg2 a 1 * κ.1 with hg
    have h := parseval (fun x => φ (uni2 x * g)) (fun x => φ' (uni2 x * g)) (hcont hφ g) (hcont hφ' g)
      (periodic_of_LInv hL g) (periodic_of_LInv hL' g)
    have h0 : cf (fun x => φ (uni2 x * g)) 0 = 0 := by
      simp only [cf, map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
      exact hc g
    have h1 : HasSum (fun α : ℚˣ => cf (fun x => φ (uni2 x * g)) α * conj (cf (fun x => φ' (uni2 x * g)) α))
        (∫ x in fundamentalSet ℚ, φ (uni2 x * g) * conj (φ' (uni2 x * g)) ∂adeleMeasure ℚ) := by
      refine (Function.Injective.hasSum_iff (g := fun α : ℚˣ => (α : ℚ)) Units.val_injective ?_).2 h
      intro q hq
      have : q = 0 := by
        by_contra h2
        exact hq ⟨Units.mk0 q h2, rfl⟩
      subst this
      simp [h0]
    simp only [hterm, ← mul_assoc] at h1 ⊢
    simpa only [hg, ← mul_assoc] using h1
  · intro M
    obtain ⟨C, hC⟩ := hD M
    refine ⟨max C 1 * max B 1, fun a κ => ?_⟩
    set g : G2 := dg2 a 1 * κ.1 with hg
    simp only [hterm]
    have hm : 0 < min 1 (md a)⁻¹ := lt_min one_pos (inv_pos.2 (IdeleGroup.ideleModule ℚ a).2)
    have := sum_bound (fun x => φ (uni2 x * g)) (fun x => φ' (uni2 x * g)) (hcont hφ g) (hcont hφ' g)
      (periodic_of_LInv hL g) (periodic_of_LInv hL' g) (max C 1 * min 1 (md a)⁻¹ ^ M) (max B 1)
      (by positivity) (by positivity)
      (fun x => by
        have := hC x a κ
        simp only [hg, ← mul_assoc]
        refine this.trans ?_
        gcongr
        exact le_max_left _ _)
      (fun x => (hB _).trans (le_max_left _ _))
    refine this.trans (le_of_eq ?_)
    congr 1
    ring

end GlobalTheory.CompanionTheory.NewformLiftCuspidality
end
