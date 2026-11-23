import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ChangeVar
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTest
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotAny
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotFin
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProper

open MeasureTheory PositivityTheory.Rg.Tf.Geo
open scoped ENNReal Pointwise
namespace UpperTheory.ConvolutionTheory.L1

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private lemma cont_prod (m : ℕ) : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  induction m with
  | zero => simpa using continuous_const
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (continuous_apply 0).mul (ih.comp (continuous_pi fun i => continuous_apply i.succ))

private lemma cont_fib (m : ℕ) : Continuous fun p : (Fin m → G) × G => fib p.1 p.2 := by
  unfold fib
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact ((cont_prod m).comp continuous_fst).inv.mul continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_fst

private lemma prod_fib {m : ℕ} (y : Fin m → G) (x : G) : (List.ofFn (fib y x)).prod = x := by
  unfold fib
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one, mul_inv_cancel_left]

private lemma closed_centr [T2Space G] (γ : G) : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G) := by
  have : ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {g | g * γ = γ * g} := by
    ext g; simp [Subgroup.mem_centralizer_singleton_iff]
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

private lemma inv_inv_meas [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Z : Subgroup G) (hc : IsClosed (Z : Set G)) (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (ν : Measure Z) [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  haveI : LocallyCompactSpace Z := hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Z := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : TopologicalSpace.MetrizableSpace Z := TopologicalSpace.metrizableSpace_of_t3_secondCountable Z
  haveI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular ν

private lemma supp_bound {m : ℕ} (γ : G) (Z : Subgroup G) (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (δ : Fin (m + 1) → G) (hδ : ∀ i, δ i ∈ Z) (K : Set (Fin (m + 1) → G)) (hK : IsCompact K)
    (hprod : ∀ x : Fin (m + 1) → G, (fun i => (x i)⁻¹ * δ i * x (i + 1)) ∈ K →
      (x 0)⁻¹ * γ * x 0 ∈ (fun g : Fin (m + 1) → G => (List.ofFn g).prod) '' K)
    (hprop : ∀ D : Set G, IsCompact D → ∃ C : Set G, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t ∈ Z, ∃ y ∈ C, x = t * y) :
    ∃ C : Set (Fin (m + 1) → G), IsCompact C ∧ ∀ x : Fin (m + 1) → G, (fun i => (x i)⁻¹ * δ i * x (i + 1)) ∈ K →
      ∃ t : Z, ∃ y ∈ C, x = (fun _ => (t : G)) * y := by
  obtain ⟨C₀, hC₀, hC⟩ := hprop _ (hK.image (cont_prod (m + 1)))
  let K' : Set G := ⋃ i, (fun g : Fin (m + 1) → G => g i) '' K
  have hK' : IsCompact K' := isCompact_iUnion fun i => hK.image (continuous_apply i)
  let Dl : Set G := Set.range fun i => (δ i)⁻¹
  have hDl : IsCompact Dl := (Set.finite_range _).isCompact
  let A : ℕ → Set G := fun k => Nat.rec C₀ (fun _ S => Dl * S * K') k
  have hA : ∀ k, IsCompact (A k) := by
    intro k
    induction k with
    | zero => exact hC₀
    | succ k ih => exact (hDl.mul ih).mul hK'
  refine ⟨Set.pi Set.univ fun i : Fin (m + 1) => A i, isCompact_univ_pi fun i => hA i, ?_⟩
  intro x hx
  obtain ⟨t, ht, y₀, hy₀, hx₀⟩ := hC (x 0) (hprod x hx)
  refine ⟨⟨t, ht⟩, fun i => t⁻¹ * x i, ?_, ?_⟩
  · have key : ∀ k (hk : k < m + 1), t⁻¹ * x ⟨k, hk⟩ ∈ A k := by
      intro k
      induction k with
      | zero =>
        intro hk
        have : (⟨0, hk⟩ : Fin (m + 1)) = 0 := rfl
        rw [this, hx₀, inv_mul_cancel_left]
        exact hy₀
      | succ k ih =>
        intro hk
        have hk' : k < m + 1 := by omega
        have hs : (⟨k, hk'⟩ : Fin (m + 1)) + 1 = ⟨k + 1, hk⟩ := by
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt hk]
        have hc := hcomm t ht (δ ⟨k, hk'⟩) (hδ _)
        have e : t⁻¹ * x ⟨k + 1, hk⟩ = (δ ⟨k, hk'⟩)⁻¹ * (t⁻¹ * x ⟨k, hk'⟩) *
            ((x ⟨k, hk'⟩)⁻¹ * δ ⟨k, hk'⟩ * x (⟨k, hk'⟩ + 1)) := by
          rw [hs]
          have h2 : (δ ⟨k, hk'⟩)⁻¹ * t⁻¹ * δ ⟨k, hk'⟩ = t⁻¹ := by
            have h3 : t⁻¹ * δ ⟨k, hk'⟩ = δ ⟨k, hk'⟩ * t⁻¹ := by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_inv_cancel_right]
            rw [mul_assoc, h3, inv_mul_cancel_left]
          calc _ = ((δ ⟨k, hk'⟩)⁻¹ * t⁻¹ * δ ⟨k, hk'⟩) * x ⟨k + 1, hk⟩ := by rw [h2]
            _ = _ := by group
        rw [e]
        exact Set.mul_mem_mul (Set.mul_mem_mul ⟨⟨k, hk'⟩, rfl⟩ (ih hk'))
          (Set.mem_iUnion.2 ⟨⟨k, hk'⟩, _, hx, rfl⟩)
    intro i _
    exact key i i.2
  · funext i
    simp
end

theorem geoAbs : GeoAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ m γ hcl hcomm ν _ δ hδ hprod Φ hΦ hΦc
  have hZc := closed_centr γ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ} : Subgroup G) :=
    hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer {γ} : Subgroup G) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI := inv_inv_meas _ hZc hcomm ν
  have CV := changeVar G μ m δ
  obtain ⟨pc, -, pne, -, -, -⟩ := pushTest G μ m Φ hΦ hΦc
  have CP := closedProper G γ hcl
  let dg : (Subgroup.centralizer {γ} : Subgroup G) →* (Fin (m + 1) → G) :=
    { toFun := fun t _ => (t : G), map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hdg : Continuous dg := continuous_pi fun _ => continuous_subtype_val
  let F : (Fin (m + 1) → G) → ℂ := fun x => Φ fun i => (x i)⁻¹ * δ i * x (i + 1)
  have hFc : Continuous F := hΦ.comp (continuous_pi fun i =>
    ((continuous_apply i).inv.mul continuous_const).mul (continuous_apply (i + 1)))
  have hFinv : ∀ t x, F (dg t * x) = F x := by
    intro t x
    show (Φ fun i => ((t : G) * x i)⁻¹ * δ i * ((t : G) * x (i + 1))) = Φ fun i => (x i)⁻¹ * δ i * x (i + 1)
    congr 1
    funext i
    have hc := hcomm t t.2 (δ i) (hδ i)
    have h2 : (t : G)⁻¹ * δ i * t = δ i := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    calc ((t : G) * x i)⁻¹ * δ i * ((t : G) * x (i + 1)) = (x i)⁻¹ * ((t : G)⁻¹ * δ i * t) * x (i + 1) := by group
      _ = _ := by rw [h2]
  let f : G → ℂ := fun x => push μ m Φ (x⁻¹ * γ * x)
  have hfc : Continuous f := pc.comp ((continuous_inv.mul continuous_const).mul continuous_id)
  have hfinv : ∀ (t : (Subgroup.centralizer {γ} : Subgroup G)) x, f ((Subgroup.centralizer {γ} : Subgroup G).subtype t * x) = f x := by
    intro t x
    show push μ m Φ (((t : G) * x)⁻¹ * γ * ((t : G) * x)) = push μ m Φ (x⁻¹ * γ * x)
    have hc : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have h2 : (t : G)⁻¹ * γ * t = γ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    congr 1
    calc ((t : G) * x)⁻¹ * γ * ((t : G) * x) = x⁻¹ * ((t : G)⁻¹ * γ * t) * x := by group
      _ = _ := by rw [h2]
  have hw : ∀ x : Fin (m + 1) → G, (List.ofFn fun i => (x i)⁻¹ * δ i * x (i + 1)).prod = (x 0)⁻¹ * γ * x 0 := by
    intro x
    rw [CV.2 x, prod_fib, hprod]
  obtain ⟨C, hC, hCx⟩ := supp_bound γ _ hcomm δ hδ (tsupport Φ) hΦc
    (fun x hx => ⟨_, hx, hw x⟩) CP
  obtain ⟨C', hC', hCx'⟩ := CP _ (hΦc.image (cont_prod (m + 1)))
  have fin1 : ∀ ρ, IsNormAlong id dg ν ρ → ∫⁻ x, ‖F x‖ₑ * ρ x ∂(Measure.pi fun _ => μ) < ⊤ := fun ρ hρ =>
    quotFin (Fin (m + 1) → G) _ (Measure.pi fun _ => μ) ν dg hdg F ρ hFc hFinv
      ⟨C, hC, fun x hx => by
        obtain ⟨t, y, hy, e⟩ := hCx x (subset_tsupport _ (Function.mem_support.2 hx))
        exact ⟨t, y, hy, e⟩⟩ hρ
  have fin2 : ∀ ρ, IsNormAlong id (Subgroup.centralizer {γ} : Subgroup G).subtype ν ρ → ∫⁻ x, ‖f x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ =>
    quotFin G _ μ ν (Subgroup.centralizer {γ} : Subgroup G).subtype continuous_subtype_val f ρ hfc hfinv
      ⟨C', hC', fun x hx => by
        obtain ⟨g, hg, e⟩ := pne _ hx
        obtain ⟨t, ht, y, hy, e'⟩ := hCx' x ⟨g, subset_tsupport _ (Function.mem_support.2 hg), e⟩
        exact ⟨⟨t, ht⟩, y, hy, e'⟩⟩ hρ
  refine ⟨fin1, ?_⟩
  by_cases hex : ∃ ρ', IsNormAlong id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => (t : G)) ν ρ'
  · obtain ⟨ρ', hρ'⟩ := hex
    have hρ : IsNormAlong id dg ν (fun x => ρ' (x 0)) :=
      ⟨hρ'.1.comp (measurable_pi_apply 0), fun x => hρ'.2 (x 0)⟩
    have L : quotInt (Measure.pi fun _ => μ) id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => fun _ : Fin (m + 1) => (t : G)) ν F =
        ∫ x, F x * ((ρ' (x 0)).toReal : ℂ) ∂(Measure.pi fun _ => μ) :=
      quotAny (Fin (m + 1) → G) _ (Measure.pi fun _ => μ) ν dg hdg.measurable F _ hFc.measurable hFinv hρ (fin1 _ hρ)
    have R : quotInt μ id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => (t : G)) ν f =
        ∫ x, f x * ((ρ' x).toReal : ℂ) ∂μ :=
      quotAny G _ μ ν (Subgroup.centralizer {γ} : Subgroup G).subtype continuous_subtype_val.measurable f _ hfc.measurable hfinv hρ' (fin2 _ hρ')
    refine L.trans (Eq.trans ?_ R.symm)
    let H : G × (Fin m → G) → ℂ := fun p => Φ (fib p.2 (p.1⁻¹ * γ * p.1)) * ((ρ' p.1).toReal : ℂ)
    have hHm : Measurable H := by
      have h1 : Continuous fun p : G × (Fin m → G) => Φ (fib p.2 (p.1⁻¹ * γ * p.1)) :=
        hΦ.comp ((cont_fib m).comp (continuous_snd.prodMk
          ((continuous_fst.inv.mul continuous_const).mul continuous_fst)))
      exact h1.measurable.mul (Complex.measurable_ofReal.comp (hρ'.1.comp measurable_fst).ennreal_toReal)
    let φ : (Fin (m + 1) → G) → G × (Fin m → G) :=
      fun x => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ)
    have hcomp : ∀ x, H (φ x) = F x * ((ρ' (x 0)).toReal : ℂ) := by
      intro x
      show Φ _ * _ = Φ _ * _
      rw [CV.2 x, hprod]
    have hint : Integrable (fun x => F x * ((ρ' (x 0)).toReal : ℂ)) (Measure.pi fun _ => μ) := by
      refine ⟨(hFc.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable, ?_⟩
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (fin1 _ hρ)
      rw [enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    have hHint : Integrable H (μ.prod (Measure.pi fun _ => μ)) := by
      refine (CV.1.integrable_comp hHm.aestronglyMeasurable).1 ?_
      exact hint.congr (Filter.Eventually.of_forall fun x => (hcomp x).symm)
    calc ∫ x, F x * ((ρ' (x 0)).toReal : ℂ) ∂(Measure.pi fun _ => μ)
        = ∫ x, H (φ x) ∂(Measure.pi fun _ => μ) := by simp only [hcomp]
      _ = ∫ p, H p ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← CV.1.map_eq]
        exact (integral_map CV.1.aemeasurable hHm.aestronglyMeasurable).symm
      _ = ∫ a, ∫ v, H (a, v) ∂(Measure.pi fun _ => μ) ∂μ := integral_prod H hHint
      _ = ∫ a, f a * ((ρ' a).toReal : ℂ) ∂μ := by
        congr 1
        funext a
        show ∫ v, Φ (fib v (a⁻¹ * γ * a)) * ((ρ' a).toReal : ℂ) ∂(Measure.pi fun _ => μ) =
          (∫ v, Φ (fib v (a⁻¹ * γ * a)) ∂(Measure.pi fun _ => μ)) * ((ρ' a).toReal : ℂ)
        rw [integral_mul_const]
  · have no : ¬∃ ρ, IsNormAlong id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => fun _ : Fin (m + 1) => (t : G)) ν ρ := by
      rintro ⟨ρ, hρ⟩
      refine hex ⟨fun g => ρ fun _ => g, hρ.1.comp (measurable_pi_lambda _ fun _ => measurable_id), fun x => ?_⟩
      exact hρ.2 fun _ => x
    unfold quotInt
    rw [dif_neg no, dif_neg hex]

end UpperTheory.ConvolutionTheory.L1
