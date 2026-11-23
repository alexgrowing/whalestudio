import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.WeilIndicatorMeasures.MeasurableUnitMulIndicator
import Formalism.PeriodIntegrals.QuotInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.QuotMeasExists

variable {m : ℕ}

def Gt (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Type := {x : PI.MtM m // Matrix.of x ∈ G}

section Grp

variable (G : Set (Matrix (Fin m) (Fin m) ℂ)) [hG : Fact (PI.IsMatGroup G)]

theorem inv_mul_of {a : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ G) : a⁻¹ * a = 1 := by
  exact Matrix.nonsing_inv_mul a (Matrix.isUnit_det_of_right_inverse (hG.out.2.2.2 a ha).2)

instance : TopologicalSpace (Gt G) := inferInstanceAs (TopologicalSpace {x : PI.MtM m // Matrix.of x ∈ G})
instance : MeasurableSpace (Gt G) := inferInstanceAs (MeasurableSpace {x : PI.MtM m // Matrix.of x ∈ G})
instance : BorelSpace (Gt G) := inferInstanceAs (BorelSpace {x : PI.MtM m // Matrix.of x ∈ G})
instance : T2Space (Gt G) := inferInstanceAs (T2Space {x : PI.MtM m // Matrix.of x ∈ G})
instance : SecondCountableTopology (Gt G) :=
  inferInstanceAs (SecondCountableTopology {x : PI.MtM m // Matrix.of x ∈ G})

def mat (a : Gt G) : Matrix (Fin m) (Fin m) ℂ := Matrix.of a.1

theorem mat_mem (a : Gt G) : mat G a ∈ G := by
  exact a.2

def mk (M : Matrix (Fin m) (Fin m) ℂ) (h : M ∈ G) : Gt G := ⟨Matrix.of.symm M, by simpa using h⟩

@[simp] theorem mat_mk (M : Matrix (Fin m) (Fin m) ℂ) (h : M ∈ G) : mat G (mk G M h) = M := by
  rfl

theorem ext_mat {a b : Gt G} (h : mat G a = mat G b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

instance : Mul (Gt G) := ⟨fun a b => mk G (mat G a * mat G b) (hG.out.2.2.1 _ (mat_mem G a) _ (mat_mem G b))⟩
instance : One (Gt G) := ⟨mk G 1 hG.out.2.1⟩
instance : Inv (Gt G) := ⟨fun a => mk G (mat G a)⁻¹ (hG.out.2.2.2 _ (mat_mem G a)).1⟩

@[simp] theorem mat_mul (a b : Gt G) : mat G (a * b) = mat G a * mat G b := by
  rfl
@[simp] theorem mat_one : mat G (1 : Gt G) = 1 := by
  rfl
@[simp] theorem mat_inv (a : Gt G) : mat G a⁻¹ = (mat G a)⁻¹ := by
  rfl

instance : Group (Gt G) :=
  Group.ofLeftAxioms (fun a b c => ext_mat G (by simp [Matrix.mul_assoc]))
    (fun a => ext_mat G (by simp)) (fun a => ext_mat G (by simp [inv_mul_of G (mat_mem G a)]))

theorem continuous_mat : Continuous (mat G) := by
  exact continuous_subtype_val

theorem isClosed_set : IsClosed {x : PI.MtM m | Matrix.of x ∈ G} := by
  show IsClosed (Matrix.of ⁻¹' G)
  exact hG.out.1.preimage (by exact continuous_id)

theorem isClosedEmbedding_val : IsClosedEmbedding (Subtype.val : Gt G → PI.MtM m) := by
  exact (isClosed_set G).isClosedEmbedding_subtypeVal

instance : LocallyCompactSpace (Gt G) := (isClosedEmbedding_val G).locallyCompactSpace

theorem continuous_mk {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin m) (Fin m) ℂ}
    (hf : Continuous fun x => (Matrix.of.symm (f x) : PI.MtM m)) (h : ∀ x, f x ∈ G) :
    Continuous fun x => mk G (f x) (h x) := by
  exact hf.subtype_mk _

theorem det_ne (a : Gt G) : (mat G a).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_left_inverse (inv_mul_of G (mat_mem G a))

instance : IsTopologicalGroup (Gt G) where
  continuous_mul := by
    refine continuous_mk G (f := fun p : Gt G × Gt G => mat G p.1 * mat G p.2) ?_ _
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
    exact continuous_finsetSum _ fun l _ =>
      (((continuous_apply l).comp ((continuous_apply i).comp ((continuous_mat G).comp continuous_fst)))).mul
        ((continuous_apply j).comp ((continuous_apply l).comp ((continuous_mat G).comp continuous_snd)))
  continuous_inv := by
    refine continuous_mk G (f := fun a : Gt G => (mat G a)⁻¹) ?_ _
    have e : (fun a : Gt G => (Matrix.of.symm ((mat G a)⁻¹) : PI.MtM m)) =
        fun a => Matrix.of.symm (((mat G a).det)⁻¹ • (mat G a).adjugate) := by
      funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    have hd : Continuous fun a : Gt G => ((mat G a).det)⁻¹ :=
      ((continuous_mat G).matrix_det).inv₀ (det_ne G)
    have ha : Continuous fun a : Gt G => (mat G a).adjugate := (continuous_mat G).matrix_adjugate
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_symm_apply, Matrix.smul_apply, smul_eq_mul]
    exact hd.mul ((continuous_apply j).comp ((continuous_apply i).comp ha))

end Grp

section Sub

variable (G S : Set (Matrix (Fin m) (Fin m) ℂ)) [hG : Fact (PI.IsMatGroup G)]

def Hs (hS : PI.IsMatGroup S) (hSG : S ⊆ G) : Subgroup (Gt G) where
  carrier := {a | mat G a ∈ S}
  mul_mem' := fun {a b} ha hb => by
    show mat G (a * b) ∈ S
    rw [mat_mul]; exact hS.2.2.1 _ ha _ hb
  one_mem' := by show mat G 1 ∈ S; rw [mat_one]; exact hS.2.1
  inv_mem' := fun {a} ha => by
    show mat G a⁻¹ ∈ S
    rw [mat_inv]; exact (hS.2.2.2 _ ha).1

theorem isClosed_Hs (hS : PI.IsMatGroup S) (hSG : S ⊆ G) : IsClosed (Hs G S hS hSG : Set (Gt G)) := by
  exact hS.1.preimage (continuous_mat G)

end Sub

section Main

variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)}

theorem continuous_mulQ :
    Continuous fun p : PI.MtM m × PI.MtM m => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : PI.MtM m) := by
  exact (continuous_fst (X := PI.MtM m) (Y := PI.MtM m)).matrix_mul (continuous_snd (X := PI.MtM m) (Y := PI.MtM m))

theorem continuous_lmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (PI.lmulQ (m := m) a) := by
  unfold PI.lmulQ
  exact continuous_const.matrix_mul continuous_id

theorem quotM_existsSF (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G)
    {μG μS : Measure (PI.MtM m)} (hμG : PI.IsHaarOnM G μG) (hμS : PI.IsHaarOnM S μS) :
    ∃ ν : Measure (PI.MtM m), SFinite ν ∧ PI.IsQuotM μG μS ν := by
  classical
  have : Fact (PI.IsMatGroup G) := ⟨hG⟩
  obtain ⟨hGsf, -, hGcon, hGinv⟩ := hμG
  obtain ⟨hSsf, hSne, hScon, hSinv⟩ := hμS
  have := hGsf
  have := hSsf
  set H := Hs G S hS hSG with hH
  have hHc : IsClosed (H : Set (Gt G)) := isClosed_Hs G S hS hSG
  have : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  let e : H → PI.MtM m := fun h => h.1.1
  have hce : IsClosedEmbedding e := (isClosedEmbedding_val G).comp hHc.isClosedEmbedding_subtypeVal
  have he : MeasurableEmbedding e := hce.measurableEmbedding
  have hrange : Set.range e = {x | Matrix.of x ∈ S} := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hx
      exact ⟨⟨⟨x, hSG hx⟩, hx⟩, rfl⟩
  have hae : ∀ᵐ x ∂μS, x ∈ Set.range e := by
    rw [hrange, ae_iff]
    simpa using hScon
  set κ : Measure H := μS.comap e with hκ
  have hκmap : κ.map e = μS := by rw [hκ, he.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have : SigmaFinite κ := SigmaFinite.of_map κ he.measurable.aemeasurable (by rw [hκmap]; exact hSsf)
  have hκinv : ∀ g : H, κ.map (g * ·) = κ := by
    intro g
    have hcomm : e ∘ (g * ·) = PI.lmulQ (mat G g.1) ∘ e := by
      funext h
      rfl
    rw [← he.comap_map (κ.map (g * ·)), Measure.map_map he.measurable (measurable_const_mul g), hcomm,
      ← Measure.map_map (continuous_lmulQ _).measurable he.measurable, hκmap, hSinv _ g.2, hκ]
  have : κ.IsMulLeftInvariant := ⟨fun g => hκinv g⟩
  set lam : Measure H := Measure.haar with hlam
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hK0 : lam K ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hK1).ne'
  have hKt : lam K ≠ ⊤ := hKc.measure_lt_top.ne
  have hκeq : κ = (κ K / lam K) • lam := measure_eq_div_smul κ lam hK0 hKt
  set c : ℝ≥0∞ := κ K / lam K with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hSne
    rw [← hκmap, hκeq, h0, zero_smul, Measure.map_zero]
  have hct : c ≠ ⊤ := by
    intro ht
    have hnull : ∀ n, lam (spanningSets κ n) = 0 := fun n => by
      have h1 := measure_spanningSets_lt_top κ n
      generalize spanningSets κ n = A at h1 ⊢
      rw [hκeq, ht, Measure.smul_apply, smul_eq_mul] at h1
      by_contra hne
      rw [ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have h2 : lam Set.univ = 0 := by
      rw [← iUnion_spanningSets κ]
      exact measure_iUnion_null hnull
    exact hK0 (measure_mono_null (Set.subset_univ K) h2)
  obtain ⟨β, hβm, hβ1⟩ := Formalism.L2.SG.Pf.Weil.QuotInt.exists_fib_eq_one hHc lam
  let φ : PI.MtM m → ℝ≥0∞ := fun y => if hy : Matrix.of y ∈ G then β (mk G (Matrix.of y) hy)⁻¹ else 0
  have hGm : MeasurableSet {y : PI.MtM m | Matrix.of y ∈ G} := (isClosed_set G).measurableSet
  have hφm : Measurable φ := by
    refine measurable_of_restrict_of_restrict_compl hGm ?_ ?_
    · have e1 : Set.domRestrict {y | Matrix.of y ∈ G} φ = fun y => β (mk G (Matrix.of y.1) y.2)⁻¹ := by
        funext y
        exact dif_pos y.2
      rw [e1]
      refine hβm.comp (measurable_inv.comp ?_)
      exact (continuous_mk G (f := fun y : {y : PI.MtM m | Matrix.of y ∈ G} => Matrix.of y.1)
        continuous_subtype_val fun y => y.2).measurable
    · have e2 : Set.domRestrict {y | Matrix.of y ∈ G}ᶜ φ = fun _ => 0 := by
        funext y
        exact dif_neg y.2
      rw [e2]
      exact measurable_const
  refine ⟨μG.withDensity (fun y => c⁻¹ * φ y), inferInstance, fun f hf => ?_⟩
  have hF2 : Measurable fun p : PI.MtM m × PI.MtM m => f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) :=
    hf.comp (continuous_mulQ.comp continuous_swap).measurable
  have hin : Measurable fun x : PI.MtM m => ∫⁻ s : PI.MtM m, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS :=
    Measurable.lintegral_prod_right' hF2
  have hfib : ∀ x : PI.MtM m, Measurable fun s : PI.MtM m => f (fun i j => (Matrix.of s * Matrix.of x) i j) :=
    fun x => hf.comp (continuous_mulQ.comp (continuous_id.prodMk continuous_const)).measurable
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ G := by
    rw [ae_iff]
    simpa using hGcon

  have hsub : ∀ h : H, ∫⁻ x, c⁻¹ * φ x * f (fun i j => (Matrix.of (e h) * Matrix.of x) i j) ∂μG =
      ∫⁻ y, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂μG := by
    intro h
    have ha : mat G h.1 ∈ G := hSG h.2
    have hmap := hGinv _ ha
    have hFm : Measurable fun y => c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y :=
      (measurable_const.mul (hφm.comp (continuous_lmulQ _).measurable)).mul hf
    calc ∫⁻ x, c⁻¹ * φ x * f (fun i j => (Matrix.of (e h) * Matrix.of x) i j) ∂μG
        = ∫⁻ x, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) (PI.lmulQ (mat G h.1) x)) *
            f (PI.lmulQ (mat G h.1) x) ∂μG := by
          refine lintegral_congr fun x => ?_
          have hx : PI.lmulQ (mat G (h⁻¹ : H).1) (PI.lmulQ (mat G h.1) x) = x := by
            show (mat G (h⁻¹ : H).1 * (mat G h.1 * Matrix.of x) : Matrix (Fin m) (Fin m) ℂ) = x
            rw [← Matrix.mul_assoc, Subgroup.coe_inv, mat_inv, inv_mul_of G ha, Matrix.one_mul]
            rfl
          rw [hx]
          rfl
      _ = ∫⁻ y, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂(μG.map (PI.lmulQ (mat G h.1))) :=
          (lintegral_map hFm (continuous_lmulQ _).measurable).symm
      _ = ∫⁻ y, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂μG := by rw [hmap]

  have hone : ∀ y, ∀ hy : Matrix.of y ∈ G, ∫⁻ h, φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) ∂κ = c := by
    intro y hy
    have hval : ∀ h : H, φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) = β ((mk G (Matrix.of y) hy)⁻¹ * h.1) := by
      intro h
      have hm : Matrix.of (PI.lmulQ (mat G (h⁻¹ : H).1) y) ∈ G :=
        hG.2.2.1 _ (mat_mem G _) _ hy
      have hk : mk G (Matrix.of (PI.lmulQ (mat G (h⁻¹ : H).1) y)) hm = (h⁻¹ : H).1 * mk G (Matrix.of y) hy :=
        ext_mat G (by rw [mat_mk, mat_mul, mat_mk]; rfl)
      show (if hy' : Matrix.of (PI.lmulQ (mat G (h⁻¹ : H).1) y) ∈ G then
        β (mk G (Matrix.of (PI.lmulQ (mat G (h⁻¹ : H).1) y)) hy')⁻¹ else 0) = _
      rw [dif_pos hm, hk, mul_inv_rev, Subgroup.coe_inv, inv_inv]
    simp_rw [hval]
    rw [hκeq, lintegral_smul_measure]
    have := hβ1 (mk G (Matrix.of y) hy)⁻¹
    unfold Formalism.L2.SG.Pf.Weil.QuotInt.fib at this
    rw [this, smul_eq_mul, mul_one]
  symm
  have hden : Measurable fun y => c⁻¹ * φ y := measurable_const.mul hφm
  refine (lintegral_withDensity_eq_lintegral_mul μG hden hin).trans ?_
  simp only [Pi.mul_apply]
  calc ∫⁻ x, c⁻¹ * φ x * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂μG
      = ∫⁻ x, ∫⁻ s, c⁻¹ * φ x * f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂μG :=
        lintegral_congr fun x => (lintegral_const_mul _ (hfib x)).symm
    _ = ∫⁻ s, ∫⁻ x, c⁻¹ * φ x * f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μG ∂μS := by
        refine lintegral_lintegral_swap ?_
        exact ((measurable_const.mul (hφm.comp measurable_fst)).mul hF2).aemeasurable
    _ = ∫⁻ h, ∫⁻ x, c⁻¹ * φ x * f (fun i j => (Matrix.of (e h) * Matrix.of x) i j) ∂μG ∂κ := by
        rw [← hκmap, he.lintegral_map]
    _ = ∫⁻ h, ∫⁻ y, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂μG ∂κ := lintegral_congr hsub
    _ = ∫⁻ y, ∫⁻ h, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂κ ∂μG := by
        refine lintegral_lintegral_swap ?_
        have hc2 : Continuous fun p : H × PI.MtM m => PI.lmulQ (mat G (p.1⁻¹ : H).1) p.2 := by
          have h1 : Continuous fun p : H × PI.MtM m => (mat G (p.1⁻¹ : H).1) :=
            (continuous_mat G).comp (continuous_subtype_val.comp (continuous_inv.comp continuous_fst))
          refine continuous_pi fun i => continuous_pi fun j => ?_
          simp only [PI.lmulQ, Matrix.mul_apply, Matrix.of_apply]
          exact continuous_finsetSum _ fun l _ =>
            ((continuous_apply l).comp ((continuous_apply i).comp h1)).mul
              ((continuous_apply j).comp ((continuous_apply l).comp continuous_snd))
        exact ((measurable_const.mul (hφm.comp hc2.measurable)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr_ae ?_
        filter_upwards [hGae] with y hy
        have hmeas : Measurable fun h : H => φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) := by
          refine hφm.comp (Continuous.measurable ?_)
          have h1 : Continuous fun h : H => (mat G (h⁻¹ : H).1) :=
            (continuous_mat G).comp (continuous_subtype_val.comp continuous_inv)
          refine continuous_pi fun i => continuous_pi fun j => ?_
          simp only [PI.lmulQ, Matrix.mul_apply, Matrix.of_apply]
          exact continuous_finsetSum _ fun l _ =>
            ((continuous_apply l).comp ((continuous_apply i).comp h1)).mul continuous_const
        calc ∫⁻ h, c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) * f y ∂κ
            = (c⁻¹ * ∫⁻ h, φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) ∂κ) * f y := by
              have hmeas2 : Measurable fun h : H => c⁻¹ * φ (PI.lmulQ (mat G (h⁻¹ : H).1) y) :=
                measurable_const.mul hmeas
              rw [lintegral_mul_const (f y) hmeas2, lintegral_const_mul _ hmeas]
          _ = f y := by rw [hone y hy, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end Main

theorem quotM_exists {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G)
    (hS : PI.IsMatGroup S) (hSG : S ⊆ G)
    {μG μS : Measure (PI.MtM m)} (hμG : PI.IsHaarOnM G μG) (hμS : PI.IsHaarOnM S μS) :
    ∃ ν : Measure (PI.MtM m), PI.IsQuotM μG μS ν := by
  obtain ⟨ν, -, hν⟩ := quotM_existsSF hG hS hSG hμG hμS
  exact ⟨ν, hν⟩

theorem quotMeasExists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    ∀ μG μS : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS → ∃ ν, Formalism.MainNotions.S.IsQuotMeas μG μS ν := by
  intro k r z hz hT μG μS hG hS
  obtain ⟨h1, h2, h3, -, -⟩ := quotient_measure_unitary_group k r z hz hT
  obtain ⟨ν, -, hν⟩ := quotM_existsSF h1 h2 h3 hG hS
  exact ⟨ν, hν⟩

theorem quotMeasExistsSF : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    ∀ μG μS : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS → ∃ ν, SFinite ν ∧ Formalism.MainNotions.S.IsQuotMeas μG μS ν := by
  intro k r z hz hT μG μS hG hS
  obtain ⟨h1, h2, h3, -, -⟩ := quotient_measure_unitary_group k r z hz hT
  exact quotM_existsSF h1 h2 h3 hG hS

end Formalism.L2.SG.Pf.QuotMeasExists
