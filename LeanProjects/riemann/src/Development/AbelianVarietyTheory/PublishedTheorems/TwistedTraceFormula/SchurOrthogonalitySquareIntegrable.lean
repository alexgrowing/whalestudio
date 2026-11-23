import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

namespace Published

def SchurOrthogonalitySquareIntegrable : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)),
    (∀ g v, ‖π g v‖ = ‖v‖) →
    (∀ v, Continuous fun g => π g v) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∃ v₀ w₀ : H, v₀ ≠ 0 ∧ w₀ ≠ 0 ∧ MemLp (fun g => ⟪w₀, π g v₀⟫_ℂ) 2 μ) →
    (∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) ∧
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

end Published

namespace SqIntRep

theorem isInvInvariant_of_unimodular {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.Regular] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}

def coefGraph (μ : Measure G) (π : G → (H →L[ℂ] H)) (w : H) :
    Submodule ℂ (WithLp 2 (H × Lp ℂ 2 μ)) where
  carrier := {p | (p.snd : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g p.fst⟫_ℂ}
  zero_mem' := by
    change ((0 : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g 0⟫_ℂ
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with g hg
    rw [hg, map_zero, inner_zero_right, Pi.zero_apply]
  add_mem' := by
    intro a b ha hb
    change ((a.snd + b.snd : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g (a.fst + b.fst)⟫_ℂ
    filter_upwards [Lp.coeFn_add a.snd b.snd, ha, hb] with g h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, map_add, inner_add_right]
  smul_mem' := by
    intro c a ha
    change ((c • a.snd : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g (c • a.fst)⟫_ℂ
    filter_upwards [Lp.coeFn_smul c a.snd, ha] with g h1 h2
    rw [h1, Pi.smul_apply, h2, map_smul, inner_smul_right, smul_eq_mul]

omit [Group G] in
theorem mem_coefGraph {π : G → (H →L[ℂ] H)} {w : H} {p : WithLp 2 (H × Lp ℂ 2 μ)} :
    p ∈ coefGraph μ π w ↔ (p.snd : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g p.fst⟫_ℂ := Iff.rfl

omit [Group G] in
theorem isClosed_coefGraph (π : G → (H →L[ℂ] H)) (w : H) :
    IsClosed (coefGraph μ π w : Set (WithLp 2 (H × Lp ℂ 2 μ))) := by
  refine isSeqClosed_iff_isClosed.1 fun u p hu hp => ?_
  have h1 : Filter.Tendsto (fun i => (u i).fst) Filter.atTop (nhds p.fst) :=
    ((WithLp.continuous_fst 2 H (Lp ℂ 2 μ)).tendsto p).comp hp
  have h2 : Filter.Tendsto (fun i => (u i).snd) Filter.atTop (nhds p.snd) :=
    ((WithLp.continuous_snd 2 H (Lp ℂ 2 μ)).tendsto p).comp hp
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ i, ((u i).snd : G → ℂ) g = ⟪w, π g (u i).fst⟫_ℂ :=
    ae_all_iff.2 fun i => hu i
  refine mem_coefGraph.2 ?_
  filter_upwards [hae, hall] with g h3 h4
  have h5 : Filter.Tendsto (fun i => ⟪w, π g (u (ns i)).fst⟫_ℂ) Filter.atTop
      (nhds ⟪w, π g p.fst⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds
      (((π g).continuous.tendsto _).comp (h1.comp hns.tendsto_atTop))
  refine tendsto_nhds_unique h3 ?_
  simpa only [h4] using h5

theorem memLp_coef_right [CompleteSpace H] [MeasurableMul G] [μ.IsMulRightInvariant]
    (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    {w v₀ : H} (hv₀ : v₀ ≠ 0) (h : MemLp (fun g => ⟪w, π g v₀⟫_ℂ) 2 μ) (v : H) :
    MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ := by
  set Γ := coefGraph μ π w with hΓ
  haveI : CompleteSpace Γ := (isClosed_coefGraph (μ := μ) π w).completeSpace_coe
  let ρ : G → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ) := fun g =>
    Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * g) (measurePreserving_mul_right μ g)
  have hρ : ∀ g (a : H) (f : Lp ℂ 2 μ), WithLp.toLp 2 (a, f) ∈ Γ →
      WithLp.toLp 2 (π g a, ρ g f) ∈ Γ := by
    intro g a f hf
    have h1 : (f : G → ℂ) =ᵐ[μ] fun x => ⟪w, π x a⟫_ℂ := hf
    have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae_eq_comp h1
    have h3 := Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right μ g)
    change ((ρ g f : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun x => ⟪w, π x (π g a)⟫_ℂ
    refine (h3.trans h2).trans (Filter.Eventually.of_forall fun x => ?_)
    simp [map_mul]
  have huniq : ∀ (a : H) (f f' : Lp ℂ 2 μ), WithLp.toLp 2 (a, f) ∈ Γ → WithLp.toLp 2 (a, f') ∈ Γ →
      f = f' := by
    intro a f f' hf hf'
    have h1 : (f : G → ℂ) =ᵐ[μ] fun x => ⟪w, π x a⟫_ℂ := hf
    have h2 : (f' : G → ℂ) =ᵐ[μ] fun x => ⟪w, π x a⟫_ℂ := hf'
    exact Lp.ext (h1.trans h2.symm)
  have hinv : ∀ g (a : H), π g (π g⁻¹ a) = a := fun g a => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  let ι : H →L[ℂ] WithLp 2 (H × Lp ℂ 2 μ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp ℂ 2 μ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ H (Lp ℂ 2 μ))
  have hι : ∀ a, ι a = WithLp.toLp 2 (a, 0) := fun a => rfl
  let A : H →L[ℂ] H := (WithLp.fstL 2 ℂ H (Lp ℂ 2 μ)).comp (Γ.starProjection.comp ι)
  have hA : ∀ a, A a = (Γ.starProjection (ι a)).fst := fun a => rfl
  have hcomm : ∀ g, π g * A = A * π g := by
    intro g
    ext a
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hA, hA]
    set p := Γ.starProjection (ι a) with hp
    have hpm : WithLp.toLp 2 (p.fst, p.snd) ∈ Γ := Γ.starProjection_apply_mem _
    have key : Γ.starProjection (ι (π g a)) = WithLp.toLp 2 (π g p.fst, ρ g p.snd) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hρ g _ _ hpm) fun q hq => ?_
      have hq' : WithLp.toLp 2 (q.fst, q.snd) ∈ Γ := hq
      have h1 := hρ g⁻¹ _ _ hq'
      have h2 := hρ g _ _ h1
      rw [hinv] at h2
      have h3 : ρ g (ρ g⁻¹ q.snd) = q.snd := huniq _ _ _ h2 hq'
      have h4 := Submodule.starProjection_inner_eq_zero (K := Γ) (ι a) _ h1
      rw [← hp, WithLp.prod_inner_apply] at h4
      rw [WithLp.prod_inner_apply]
      change ⟪a - p.fst, π g⁻¹ q.fst⟫_ℂ + ⟪0 - p.snd, ρ g⁻¹ q.snd⟫_ℂ = 0 at h4
      change ⟪π g a - π g p.fst, q.fst⟫_ℂ + ⟪0 - ρ g p.snd, q.snd⟫_ℂ = 0
      rw [SchurOrth.inner_rep π hπ, inv_inv, map_sub, ← (ρ g).inner_map_map, h3, map_sub,
        map_zero] at h4
      exact h4
    rw [key]
    rfl
  obtain ⟨c, hc⟩ := hilbert_schur H G π hπ hirr A hcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    set p := Γ.starProjection (ι v₀) with hp
    have hp1 : p.fst = 0 := by rw [← hA, hc]; simp
    have hm : WithLp.toLp 2 (v₀, h.toLp _) ∈ Γ := h.coeFn_toLp
    have hpm : WithLp.toLp 2 (p.fst, p.snd) ∈ Γ := Γ.starProjection_apply_mem _
    rw [hp1] at hpm
    have hp2 : p.snd = 0 := huniq 0 _ _ hpm Γ.zero_mem
    have h4 := Submodule.starProjection_inner_eq_zero (K := Γ) (ι v₀) _ hm
    rw [← hp, WithLp.prod_inner_apply] at h4
    change ⟪v₀ - p.fst, v₀⟫_ℂ + ⟪0 - p.snd, h.toLp _⟫_ℂ = 0 at h4
    rw [hp1, hp2] at h4
    simp at h4
    exact hv₀ h4
  have hv : (Γ.starProjection (ι (c⁻¹ • v))).fst = v := by
    rw [← hA, hc]; simp [smul_smul, hc0]
  have hm := mem_coefGraph.1 (Γ.starProjection_apply_mem (ι (c⁻¹ • v)))
  rw [hv] at hm
  exact (Lp.memLp _).ae_eq hm

theorem memLp_coef [CompleteSpace H] [MeasurableMul G] [MeasurableInv G] [μ.IsMulRightInvariant]
    [μ.IsInvInvariant] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    {v₀ w₀ : H} (hv₀ : v₀ ≠ 0) (hw₀ : w₀ ≠ 0) (h : MemLp (fun g => ⟪w₀, π g v₀⟫_ℂ) 2 μ) (v w : H) :
    MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ := by
  have h1 := memLp_coef_right π hπ hirr hv₀ h w
  have h2 : MemLp (fun g => ⟪w, π g w₀⟫_ℂ) 2 μ := by
    have h3 := (h1.comp_measurePreserving (Measure.measurePreserving_inv μ)).star
    refine h3.ae_eq (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.star_apply, Function.comp_apply]
    rw [SchurOrth.inner_rep π hπ, inv_inv]
    exact inner_conj_symm _ _
  exact memLp_coef_right π hπ hirr hw₀ h2 v

example [MeasurableSpace Circle] [BorelSpace Circle] : ∃ π : Circle →* (ℂ →L[ℂ] ℂ),
    (∀ g, π g 1 = g) ∧ (∀ g v, ‖π g v‖ = ‖v‖) ∧ (∀ v, Continuous fun g => π g v) ∧
    (∀ S : Submodule ℂ ℂ, IsClosed (S : Set ℂ) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) ∧
    ∃ v₀ w₀ : ℂ, v₀ ≠ 0 ∧ w₀ ≠ 0 ∧
      MemLp (fun g => ⟪w₀, π g v₀⟫_ℂ) 2 (Measure.haar : Measure Circle) := by
  let π : Circle →* (ℂ →L[ℂ] ℂ) :=
    { toFun := fun g => (g : ℂ) • (1 : ℂ →L[ℂ] ℂ)
      map_one' := by simp
      map_mul' := fun a b => by simp [smul_smul, mul_comm] }
  have hπ : ∀ g v, π g v = (g : ℂ) * v := fun g v => rfl
  have hc : ∀ v, Continuous fun g => π g v := fun v => by
    simp only [hπ]
    exact continuous_subtype_val.mul continuous_const
  refine ⟨π, fun g => by simp [hπ], fun g v => by rw [hπ, norm_mul, Circle.norm_coe, one_mul], hc,
    fun S _ _ => Ideal.eq_bot_or_top S, 1, 1, one_ne_zero, one_ne_zero, ?_⟩
  refine MemLp.of_bound (continuous_const.inner (hc 1)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun g => ?_)
  rw [hπ, mul_one, RCLike.inner_apply, map_one, mul_one, Circle.norm_coe]

end SqIntRep

theorem Published.schurOrthogonalitySquareIntegrable' : Published.SchurOrthogonalitySquareIntegrable := by
  intro G _ _ _ _ _ _ _ μ _ _ _ H _ _ _ π hπ hc hirr ⟨v₀, w₀, hv₀, hw₀, h⟩
  haveI := SqIntRep.isInvInvariant_of_unimodular μ
  haveI : Nontrivial H := nontrivial_of_ne v₀ 0 hv₀
  have hall := SqIntRep.memLp_coef π hπ hirr hv₀ hw₀ h
  exact ⟨hall, SchurOrth.schur_orthogonality π hπ hc hirr hall⟩

end GlobalTheory
