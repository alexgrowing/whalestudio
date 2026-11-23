import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalarStatement
open Formalism.MainNotions.S Matrix MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

namespace SchurOrth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}

theorem exists_coefMap (π : G → (H →L[ℂ] H)) (w : H)
    (h : ∀ v : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) :
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g v⟫_ℂ := by
  let L : H →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun v => (h v).toLp _
      map_add' := fun a b => by
        rw [← MemLp.toLp_add]
        congr 1
        ext g
        simp [inner_add_right]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        ext g
        simp [inner_smul_right] }
  have hL : ∀ v, (L v : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g v⟫_ℂ := fun v => (h v).coeFn_toLp
  have hc : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u x y hu hy => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
    have hall : ∀ᵐ g ∂μ, ∀ i, (L (u i) : G → ℂ) g = ⟪w, π g (u i)⟫_ℂ :=
      ae_all_iff.2 fun i => hL (u i)
    refine Lp.ext ?_
    filter_upwards [hae, hall, hL x] with g h1 h2 h3
    rw [h3]
    have h4 : Filter.Tendsto (fun i => ⟪w, π g (u (ns i))⟫_ℂ) Filter.atTop (nhds ⟪w, π g x⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds
        (((π g).continuous.tendsto x).comp (hu.comp hns.tendsto_atTop))
    refine tendsto_nhds_unique h1 ?_
    simpa only [Function.comp_apply, h2] using h4
  exact ⟨⟨L, hc⟩, hL⟩

omit [CompleteSpace H] [MeasurableSpace G] in
theorem inner_rep (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (a b : H) :
    ⟪a, π g b⟫_ℂ = ⟪π g⁻¹ a, b⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := ⟨(π g : H →ₗ[ℂ] H), hπ g⟩
  have h1 := e.inner_map_map (π g⁻¹ a) b
  have h2 : π g (π g⁻¹ a) = a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [← h1]
  change _ = ⟪π g (π g⁻¹ a), π g b⟫_ℂ
  rw [h2]

theorem schur_orthogonality [Nontrivial H] [TopologicalSpace G] [MeasurableMul G] [MeasurableInv G]
    [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (hc : ∀ v, Continuous fun g => π g v)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (h : ∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  choose T hT using fun w => exists_coefMap (μ := μ) π w (fun v => h v w)
  let I : H → H → H → H → ℂ := fun v w v' w' => ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ
  have hae : ∀ v w v' w', (fun g => ⟪(T w' v' : G → ℂ) g, (T w v : G → ℂ) g⟫_ℂ) =ᵐ[μ]
      fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ := by
    intro v w v' w'
    filter_upwards [hT w v, hT w' v'] with g h1 h2
    rw [h1, h2, RCLike.inner_apply]
    rfl
  have hint : ∀ v w v' w', Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ :=
    fun v w v' w' => (L2.integrable_inner (𝕜 := ℂ) (T w' v') (T w v)).congr (hae v w v' w')
  have hI : ∀ v w v' w',
      ⟪v', ((ContinuousLinearMap.adjoint (T w')).comp (T w)) v⟫_ℂ = I v w v' w' := by
    intro v w v' w'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
    exact integral_congr_ae (hae v w v' w')
  have hsc : ∀ w w', ∃ c : ℂ, ∀ v v', I v w v' w' = c * ⟪v', v⟫_ℂ := by
    intro w w'
    obtain ⟨c, hc⟩ := GlobalTheory.T.hilbert_schur_unitary_irreducible_scalar H G π hπ hirr
      ((ContinuousLinearMap.adjoint (T w')).comp (T w)) (by
        intro g
        ext v
        refine ext_inner_left ℂ fun v' => ?_
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, inner_rep π hπ, hI, hI]
        simp only [I]
        rw [← integral_mul_right_eq_self _ g]
        congr 1
        ext x
        rw [← ContinuousLinearMap.mul_apply (π (x * g)) (π g⁻¹), ← map_mul, mul_inv_cancel_right,
          map_mul, ContinuousLinearMap.mul_apply])
    refine ⟨c, fun v v' => ?_⟩
    rw [← hI, hc]
    simp [inner_smul_right]
  choose c hcI using hsc
  have hsym : ∀ v w v' w', I v w v' w' = I w' v' w v := by
    intro v w v' w'
    simp only [I]
    rw [← integral_inv_eq_self]
    congr 1
    ext x
    rw [inner_rep π hπ x⁻¹, inner_rep π hπ x⁻¹, inv_inv, mul_comm]
    simp [inner_conj_symm]
  obtain ⟨u, hu⟩ : ∃ u : H, ‖u‖ = 1 := exists_norm_eq H zero_le_one
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have hpt : ∀ g, ⟪u, π g u⟫_ℂ * star ⟪u, π g u⟫_ℂ = ((‖⟪u, π g u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ := by
    refine integral_pos_of_integrable_nonneg_nonzero (x := 1) ?_ ?_ (fun g => by positivity) ?_
    · exact ((continuous_const.inner (hc u)).norm).pow 2
    · exact (h u u).integrable_norm_pow (by norm_num)
    · simp [hu]
  have hcu : c u u = ((∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    have := hcI u u u u
    rw [huu, mul_one] at this
    rw [← this, ← integral_complex_ofReal]
    simp only [I, hpt]
  refine ⟨(∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ)⁻¹, inv_pos.2 hpos, fun v w v' w' => ⟨hint v w v' w', ?_⟩⟩
  have h1 : c w w' = c u u * ⟪w, w'⟫_ℂ := by
    rw [← hcI, ← hsym, hcI, huu, mul_one]
  change I v w v' w' = _
  rw [hcI, h1, hcu, Complex.ofReal_inv, div_inv_eq_mul]
  ring

end SchurOrth

theorem schur_orthogonality_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSqIntOn ε σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  intro n ε H _ _ _ _ σ hU hirr hsq
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hU
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  let π : Formalism.REAL.UJ ε →* (H →L[ℂ] H) :=
    { toFun := fun g => σ (umat g)
      map_one' := h1
      map_mul' := fun a b => hmul _ (hmem a) _ (hmem b) }
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsInvInvariant :=
    ⟨Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular n ε⟩
  exact SchurOrth.schur_orthogonality (μ := Formalism.REAL.muG ε) π (fun g v => hiso _ (hmem g) v)
    (fun v => (hcont v).comp_continuous (Formalism.REAL.continuous_coeMatrix ε) hmem)
    (fun S hS hst => hirr S hS fun g hg v hv => hst (Formalism.REAL.indefiniteUnitaryMk ε g hg) v hv) hsq

end GlobalTheory
