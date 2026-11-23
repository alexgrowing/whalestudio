import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GeoAbs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTest
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotAny
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotFin

open MeasureTheory PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1

private theorem prod_ofFn_single {G : Type*} [Monoid G] : ∀ (n : ℕ) (f : Fin n → G) (k : Fin n),
    (∀ i, i ≠ k → f i = 1) → (List.ofFn f).prod = f k
  | 0, _, k, _ => k.elim0
  | n + 1, f, k, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (fun h => ?_) (fun k h => ?_) k h
    · rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero i)
    · rw [h 0 (Fin.succ_ne_zero k).symm, one_mul,
        prod_ofFn_single n (fun i => f i.succ) k fun i hi => h _ fun h' => hi (Fin.succ_injective _ h')]

private theorem transport (X Y T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [MeasurableSpace T]
    [MeasurableInv T] [Group Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [SFinite ν] [ν.IsInvInvariant] (i : T →* X) (hi : Measurable i)
    (e : X ≃ₜ Y) (he : ∀ a b, e (a * b) = e a * e b) (j : T → Y) (hj : ∀ t, j t = e (i t)) (Φ : Y → ℂ)
    (hΦ : Measurable fun x => Φ (e x)) (hinv : ∀ t x, Φ (e (i t * x)) = Φ (e x))
    (hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ (e x)‖ₑ * ρ x ∂μ < ⊤) (c : ℝ) (hc : 0 ≤ c) :
    quotInt (ENNReal.ofReal c • μ.map e) id j ν Φ = c * quotInt μ id i ν fun x => Φ (e x) := by
  by_cases h : ∃ ρ, IsNormAlong id j ν ρ
  · have hρ := h.choose_spec
    have h' : IsNormAlong id i ν fun x => h.choose (e x) := by
      refine ⟨hρ.1.comp e.continuous.measurable, fun x => ?_⟩
      have := hρ.2 (e x)
      simpa only [id, he, hj] using this
    rw [quotAny X T μ ν i hi _ _ hΦ hinv h' (hfin _ h'), quotInt, dif_pos h, integral_smul_measure,
      e.measurableEmbedding.integral_map, ENNReal.toReal_ofReal hc]
    simp
  · have h' : ¬ ∃ ρ, IsNormAlong id i ν ρ := by
      rintro ⟨ρ, hρ⟩
      refine h ⟨fun y => ρ (e.symm y), hρ.1.comp e.symm.continuous.measurable, fun y => ?_⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      have := hρ.2 x
      simpa only [id, hj, ← he, e.symm_apply_apply] using this
    rw [quotInt, dif_neg h, quotInt, dif_neg h', mul_zero]

private theorem invInv {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (h : ∀ a b : T, a * b = b * a) (ν : Measure T)
    [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := h }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular ν

theorem matchSplit :
    UpperTheory.ConvolutionTheory.L1.MatchSplit := by
  intro R S _ _ _ _ _ _ _ _ _ ι s m D n _ _ _ _ μS μR hS hR hreg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) := Units.isEmbedding_embedProduct.secondCountableTopology
  let e : (Fin (m + 1) → GL (Fin n) R) ≃ₜ GL (Fin n) S :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext (h1 g)
      right_inv := h2
      continuous_toFun := h4
      continuous_invFun := continuous_pi h5 }
  let e' : (Fin (m + 1) → GL (Fin n) R) ≃* GL (Fin n) S := { e.toEquiv with map_mul' := h3 }
  haveI : LocallyCompactSpace (GL (Fin n) S) := e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) S) := e.symm.isEmbedding.secondCountableTopology
  haveI hH : (Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (Measure.pi fun _ : Fin (m + 1) => μR) e' h4 (continuous_pi h5)
  set c := Measure.haarScalarFactor μS (Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR)) with hc
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hμ : μS = ENNReal.ofReal (c : ℝ) • Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨c, hcpos, hμ, fun φ hφ hφc => ?_⟩
  have hΦ : Continuous fun g => φ (D.glue n g) := hφ.comp h4
  have hΦc : HasCompactSupport fun g => φ (D.glue n g) := hφc.comp_homeomorph e
  obtain ⟨p1, p2, -⟩ := pushTest _ μR m _ hΦ hΦc
  refine ⟨p1, p2, fun γ hγ ν hν => ⟨fun δ hδ => ?_, fun hn => (hn ?_).elim⟩⟩
  · obtain ⟨r1, r2⟩ := hreg γ hγ
    obtain ⟨d1, d2, -⟩ := (h8 δ γ).1 hδ
    obtain ⟨g1, g2⟩ := geoAbs _ μR m γ r1 r2 ν (fun i => D.comp n i δ) d1 d2 _ hΦ hΦc
    have hcl : IsClosed (Subgroup.centralizer {γ} : Set (GL (Fin n) R)) := by
      have : (Subgroup.centralizer {γ} : Set (GL (Fin n) R)) = {x | γ * x = x * γ} := by
        ext x
        simp [Subgroup.mem_centralizer_iff]
      rw [this]
      exact isClosed_eq (by fun_prop) (by fun_prop)
    haveI : LocallyCompactSpace (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) := hcl.locallyCompactSpace
    haveI : SecondCountableTopology (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) :=
      TopologicalSpace.Subtype.secondCountableTopology _
    haveI : ν.IsInvInvariant := invInv (fun a b => Subtype.ext (r2 _ a.2 _ b.2)) ν
    let i : (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) →* (Fin (m + 1) → GL (Fin n) R) :=
      MonoidHom.pi fun _ => Subgroup.subtype _
    have hi : Continuous i := continuous_pi fun _ => continuous_subtype_val
    have key : ∀ x, (e x)⁻¹ * δ * mapGL n s (e x) = D.glue n fun k => (x k)⁻¹ * D.comp n k δ * x (k + 1) := by
      intro x
      rw [← h2 ((e x)⁻¹ * δ * mapGL n s (e x))]
      congr 1
      funext k
      rw [map_mul, map_mul, map_inv, h7]
      exact congrArg₂ (· * ·) (congrArg (fun y => y⁻¹ * _) (h1 x k)) (h1 x (k + 1))
    have := transport _ (GL (Fin n) S) _ (Measure.pi fun _ : Fin (m + 1) => μR) ν i hi.measurable e h3
      (fun t => mapGL n ι (t : GL (Fin n) R)) (fun t => by
        rw [← h2 (mapGL n ι (t : GL (Fin n) R))]
        exact congrArg (D.glue n) (funext fun k => h6 _ k))
      (fun x => φ (x⁻¹ * δ * mapGL n s x)) (by
        simp only [key]
        exact (hΦ.comp (by fun_prop)).measurable) (fun t x => by
        simp only [key]
        congr 2
        funext k
        have := (Subgroup.mem_centralizer_iff.1 t.2)
        have h := r2 _ t.2 _ (d1 k)
        show ((t : GL (Fin n) R) * x k)⁻¹ * _ * ((t : GL (Fin n) R) * x (k + 1)) = _
        rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc (D.comp n k δ), ← h, mul_assoc, inv_mul_cancel_left,
          mul_assoc]) (by
        simp only [key]
        exact g1) c c.2
    simp only [key] at this
    rw [twOrb, orb, hμ]
    exact this.trans (congrArg _ g2)
  · have hs : ∀ j : Fin (m + 1),
        (List.ofFn fun i => D.comp n (j + i) (D.glue n (Pi.mulSingle 0 γ))).prod = γ := by
      intro j
      rw [prod_ofFn_single _ _ (-j) fun i hi => by
        rw [h1, Pi.mulSingle_eq_of_ne fun h => hi (eq_neg_of_add_eq_zero_right h)]]
      rw [h1, add_neg_cancel, Pi.mulSingle_eq_same]
    refine ⟨D.glue n (Pi.mulSingle 0 γ), (h8 _ _).2 ⟨fun k => ?_, by simpa only [zero_add] using hs 0, hs⟩⟩
    rw [h1]
    by_cases hk : k = 0
    · subst hk
      rw [Pi.mulSingle_eq_same]
      simp [Subgroup.mem_centralizer_iff]
    · rw [Pi.mulSingle_eq_of_ne hk]
      exact one_mem _

end UpperTheory.ConvolutionTheory.L1
