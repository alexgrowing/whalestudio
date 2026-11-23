import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.SumUliftFinsetFinTwoExpand
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.TransferenceGivesSecondBound
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

variable (D : D7)

instance totCx : IsTotallyComplex D.host.E :=
  (D.host.isCMField_hostE).to_isTotallyComplex

theorem conjugate_emb (g : D.R.GG) :
    ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  rw [show ((D.host.conj : D.host.E →+* D.host.E) z) = D.host.conj z from rfl, Formalism.MainNotions.WeightFamilies.emb_conj]
  rfl

theorem mk_tauEmb_injective : Function.Injective fun τ : D.what₂.Tau => InfinitePlace.mk (DV.tauEmb D τ) := by
  intro τ τ' h
  simp only at h
  rcases mk_eq_iff.1 h with h1 | h1
  · have h2 := (factEmb D.R D.host).1.1 h1
    exact D.eTau.injective (Subtype.ext h2)
  · exfalso
    unfold DV.tauEmb at h1
    rw [conjugate_emb] at h1
    have h2 := (factEmb D.R D.host).1.1 h1
    have hm := (D.eTau τ).2
    rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem] at hm
    exact hm (h2 ▸ (D.eTau τ').2)

theorem card_places : Fintype.card (InfinitePlace D.host.E) = Fintype.card D.what₂.Tau := by
  have h1 := DualLatticeEmbeddings.nPl_mul_two (K := D.host.E)
  rw [D.host.finrank_cmField] at h1
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.what₂.card_Tau, h2]
  omega

def ePl : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨mk_tauEmb_injective D, (card_places D).symm⟩)

theorem ePl_embedding (τ : D.what₂.Tau) :
    (ePl D τ).embedding = DV.tauEmb D τ ∨ (ePl D τ).embedding = ComplexEmbedding.conjugate (DV.tauEmb D τ) :=
  embedding_mk_eq _

theorem re_ePl (τ : D.what₂.Tau) (z : D.host.E) :
    ((ePl D τ).embedding z).re = (DV.tauEmb D τ z).re := by
  rcases ePl_embedding D τ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem trF_eq (z : D.host.E) : Formalism.MainNotions.WeightFamilies.trF D z = ∑ v : InfinitePlace D.host.E, (v.embedding z).re := by
  unfold Formalism.MainNotions.WeightFamilies.trF
  rw [← (ePl D).sum_comp]
  exact Finset.sum_congr rfl fun τ _ => (re_ePl D τ z).symm

theorem finrank_E_eq : finrank ℚ D.host.E = 2 * D.R.f := by
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.host.finrank_cmField, h2]
  ring

@[instance_reducible] def starE : StarRing D.host.E := starRingOfComm

attribute [local instance] starE

variable {D}

theorem exists_im_ne (v : InfinitePlace D.host.E) : ∃ z, (v.embedding z).im ≠ 0 := by
  have hc : v.IsComplex := IsTotallyComplex.isComplex v
  rw [isComplex_iff] at hc
  by_contra h
  simp only [not_exists, not_not] at h
  apply hc
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h z)

theorem frames {n : ℕ} (χ : Matrix (Fin n) (Fin n) D.host.E) (hH : Formalism.MainNotions.WeightFamilies.IsHerm D χ)
    (hP : Formalism.MainNotions.WeightFamilies.PosDefE D χ) :
    ∃ Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ,
      (∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) ∧ ∀ v, IsUnit (Xf v).det := by
  have h : ∀ v : InfinitePlace D.host.E, ∃ X : Matrix (Fin n) (Fin n) ℂ,
      X * Xᴴ = χ.map v.embedding ∧ IsUnit X.det := by
    intro v
    obtain ⟨z, hz⟩ := exists_im_ne v
    obtain ⟨h1, h2⟩ := TraceQuadraticBound.psd_map (fun z => D.host.conj z) v.embedding
      (Formalism.MainNotions.WeightFamilies.emb_conj D v.embedding) (TraceQuadraticBound.denseRange_emb v.embedding z hz) χ hH
      (fun l hl => hP l hl v.embedding)
    exact TraceQuadraticBound.frame_exists h1 h2
  choose Xf h1 h2 using h
  exact ⟨Xf, h1, h2⟩

theorem star_mulVec_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star (M *ᵥ w) = M.map star *ᵥ star w := by
  funext i
  simp only [Pi.star_apply, mulVec, dotProduct, star_sum, map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul']

theorem tau_frame {n : ℕ} (χ : Matrix (Fin n) (Fin n) D.host.E)
    (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (hXf : ∀ v, IsUnit (Xf v).det) (τ : D.what₂.Tau) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y * Yᴴ = χ.map (DV.tauEmb D τ) ∧ IsUnit Y.det ∧
      ∀ y : Fin n → D.host.E, ∃ w : Fin n → ℂ, Formalism.MainNotions.WeightFamilies.embV D τ y = Y *ᵥ w ∧
        ∑ i, ‖w i‖ ^ 2 = ∑ i, ‖DualLatticeEmbeddings.fc Xf (ePl D τ) y i‖ ^ 2 := by
  set v := ePl D τ
  have hX1 : ∀ y : Fin n → D.host.E, Xf v *ᵥ DualLatticeEmbeddings.fc Xf v y = fun i => v.embedding (y i) := by
    intro y
    rw [DualLatticeEmbeddings.fc, mulVec_mulVec, Matrix.mul_nonsing_inv _ (hXf v), one_mulVec]
  rcases ePl_embedding D τ with h | h
  · refine ⟨Xf v, by rw [hfr v, h], hXf v, fun y => ⟨DualLatticeEmbeddings.fc Xf v y, ?_, rfl⟩⟩
    rw [hX1 y, h]; rfl
  · have hτ : ∀ z, DV.tauEmb D τ z = star (v.embedding z) := by
      intro z; rw [h, ComplexEmbedding.conjugate_coe_eq]; simp
    refine ⟨(Xf v).map star, ?_, ?_, fun y => ⟨star (DualLatticeEmbeddings.fc Xf v y), ?_, ?_⟩⟩
    · ext i k
      have := congrArg (fun M => star (M i k)) (hfr v)
      simp only [mul_apply, conjTranspose_apply, map_apply, star_sum, star_mul', star_star] at this ⊢
      rw [hτ, ← this]
    · rw [show ((Xf v).map star).det = starRingEnd ℂ (Xf v).det from (RingHom.map_det (starRingEnd ℂ) (Xf v)).symm]
      exact (hXf v).map _
    · rw [← star_mulVec_map, hX1 y]
      funext i
      simp [Formalism.MainNotions.WeightFamilies.embV, hτ]
    · simp only [Pi.star_apply, norm_star]

end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}

theorem Qv_le (χ : Matrix (Fin n) (Fin n) D.host.E) (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (hXf : ∀ v, IsUnit (Xf v).det)
    (b : Formalism.MainNotions.WeightFamilies.BForm D n) (hb : ∀ τ, (b τ).PosSemidef) (y : Fin n → D.host.E) :
    Formalism.MainNotions.WeightFamilies.Qv D b y ≤
      Formalism.MainNotions.WeightFamilies.pairB D χ b * ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun D.host.E (Fin n)) Xf y‖ ^ 2 := by
  choose Y hY _ hw using tau_frame χ Xf hfr hXf
  set N : D.what₂.Tau → ℝ := fun τ => ∑ i, ‖DualLatticeEmbeddings.fc Xf (ePl D τ) y i‖ ^ 2 with hN
  have hp : ∀ τ, 0 ≤ (Matrix.trace (b τ * χ.map (DV.tauEmb D τ))).re := by
    intro τ; rw [← hY τ]; exact TraceQuadraticBound.trace_nonneg (hb τ) (Y τ)
  have hN0 : ∀ τ, 0 ≤ N τ := fun τ => Finset.sum_nonneg fun i _ => by positivity
  have hq : ∀ τ, (star (Formalism.MainNotions.WeightFamilies.embV D τ y) ⬝ᵥ (b τ) *ᵥ (Formalism.MainNotions.WeightFamilies.embV D τ y)).re ≤
      (Matrix.trace (b τ * χ.map (DV.tauEmb D τ))).re * N τ := by
    intro τ
    obtain ⟨w, hw1, hw2⟩ := hw τ y
    simp only [hN]
    rw [hw1, ← hw2, ← hY τ]
    exact TraceQuadraticBound.quad_le_trace (hb τ) (Y τ) w
  have hnorm : ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun D.host.E (Fin n)) Xf y‖ ^ 2 = ∑ τ, N τ := by
    rw [DualLatticeEmbeddings.norm_sq_realize, ← (ePl D).sum_comp]
  rw [hnorm]
  unfold Formalism.MainNotions.WeightFamilies.Qv Formalism.MainNotions.WeightFamilies.pairB
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => (hq τ).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun τ _ => hN0 τ) (Finset.mem_univ τ)) (hp τ)

theorem pairB_pos (χ : Matrix (Fin n) (Fin n) D.host.E) (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (hXf : ∀ v, IsUnit (Xf v).det)
    (b : Formalism.MainNotions.WeightFamilies.BForm D n) (hb : ∀ τ, (b τ).PosSemidef) (hb0 : b ≠ 0) :
    0 < Formalism.MainNotions.WeightFamilies.pairB D χ b := by
  choose Y hY hYu _ using tau_frame χ Xf hfr hXf
  obtain ⟨τ0, hτ0⟩ := Function.ne_iff.1 hb0
  have hp : ∀ τ, 0 ≤ (Matrix.trace (b τ * χ.map (DV.tauEmb D τ))).re := by
    intro τ; rw [← hY τ]; exact TraceQuadraticBound.trace_nonneg (hb τ) (Y τ)
  have hp0 : 0 < (Matrix.trace (b τ0 * χ.map (DV.tauEmb D τ0))).re := by
    rw [← hY τ0]; exact TraceQuadraticBound.trace_pos (hb τ0) hτ0 (Y τ0) (hYu τ0)
  unfold Formalism.MainNotions.WeightFamilies.pairB
  exact lt_of_lt_of_le hp0 (Finset.single_le_sum (fun τ _ => hp τ) (Finset.mem_univ τ0))

theorem norm_sq_yv_D (χ : Matrix (Fin n) (Fin n) D.host.E) (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (ξ : Fin n → D.host.E) :
    ‖DualLatticeEmbeddings.yv Xf ξ‖ ^ 2 = 4 * Formalism.MainNotions.WeightFamilies.trF D (Formalism.MainNotions.WeightFamilies.hform D χ ξ ξ) := by
  rw [DualLatticeEmbeddings.norm_sq_yv (fun z => D.host.conj z) (fun v z => Formalism.MainNotions.WeightFamilies.emb_conj D v.embedding z) χ Xf hfr,
    trF_eq]
  rfl

theorem yv_zero (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ) : DualLatticeEmbeddings.yv Xf 0 = 0 := by
  unfold DualLatticeEmbeddings.yv DualLatticeEmbeddings.mkE
  ext p
  simp [Matrix.mulVec, dotProduct]

end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}

theorem dual_norm (χ : Matrix (Fin n) (Fin n) D.host.E) (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (hXf : ∀ v, IsUnit (Xf v).det)
    (Xc : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hX : Submodule.span D.host.E (Xc : Set (Fin n → D.host.E)) = ⊤) (c1 : ℝ)
    (hnk : ∀ xi ∈ Formalism.MainNotions.WeightFamilies.dualZ D Xc, xi ≠ 0 → c1 < Formalism.MainNotions.WeightFamilies.trF D (Formalism.MainNotions.WeightFamilies.hform D χ xi xi))
    (y : DualLatticeEmbeddings.Amb D.host.E n) (hy : y ∈ Formalism.HadamardInequality.zdual (DualLatticeEmbeddings.Mz Xf Xc)) (hy0 : y ≠ 0) :
    4 * c1 < ‖y‖ ^ 2 := by
  obtain ⟨ξ, rfl, hξ⟩ := DualLatticeEmbeddings.zdual_eq_yv Xf hXf Xc hX y hy
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; exact hy0 (yv_zero Xf)
  rw [norm_sq_yv_D χ Xf hfr]
  have := hnk ξ (fun x hx => hξ x hx) hξ0
  linarith

theorem trF_pos (χ : Matrix (Fin n) (Fin n) D.host.E) (hP : Formalism.MainNotions.WeightFamilies.PosDefE D χ)
    (ξ : Fin n → D.host.E) (hξ : ξ ≠ 0) : 0 < Formalism.MainNotions.WeightFamilies.trF D (Formalism.MainNotions.WeightFamilies.hform D χ ξ ξ) := by
  have hne : Nonempty D.what₂.Tau := by
    have h2 : D.R.f = 2 * D.R.ord := rfl
    have h3 := D.R.ord_pos
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau, h2]
    omega
  obtain ⟨τ0⟩ := hne
  unfold Formalism.MainNotions.WeightFamilies.trF
  exact Finset.sum_pos (fun τ _ => hP ξ hξ _) ⟨τ0, Finset.mem_univ _⟩

theorem span_E_top (χ : Matrix (Fin n) (Fin n) D.host.E) (hP : Formalism.MainNotions.WeightFamilies.PosDefE D χ)
    (Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) (hXf : ∀ v, IsUnit (Xf v).det)
    {m : ℕ} (x : Fin m → (Fin n → D.host.E))
    (hli : LinearIndependent ℝ fun j => Formalism.HermitianLatticesTheory.realize (Pi.basisFun D.host.E (Fin n)) Xf (x j))
    (hm : m = finrank ℝ (DualLatticeEmbeddings.Amb D.host.E n)) :
    Submodule.span D.host.E (Set.range x) = ⊤ := by
  classical
  by_contra hU
  obtain ⟨f, hf0, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hU) inferInstance
  set ξ : Fin n → D.host.E := fun i => f (Pi.single i 1) with hξdef
  have hf : ∀ u, f u = ∑ i, ξ i * u i := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (u i) = u i • (Pi.single i (1 : D.host.E) : Fin n → D.host.E) by
      rw [← Pi.single_smul']; simp, map_smul, smul_eq_mul, mul_comm]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun u => ?_
    rw [hf u, h0]
    simp
  have horth : ∀ j, inner ℝ (Formalism.HermitianLatticesTheory.realize (Pi.basisFun D.host.E (Fin n)) Xf (x j)) (DualLatticeEmbeddings.yv Xf ξ) = 0 := by
    intro j
    rw [DualLatticeEmbeddings.inner_yv Xf hXf, ← hf]
    have : f (x j) = 0 := by
      have hmem : f (x j) ∈ (Submodule.span D.host.E (Set.range x)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩)
      rw [hfU] at hmem
      exact (Submodule.mem_bot _).1 hmem
    rw [this, map_zero]
    simp
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hm])
  have hz : ∀ z ∈ Submodule.span ℝ (Set.range fun j => Formalism.HermitianLatticesTheory.realize (Pi.basisFun D.host.E (Fin n)) Xf (x j)),
      inner ℝ z (DualLatticeEmbeddings.yv Xf ξ) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact horth j
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul r a _ ha => rw [real_inner_smul_left, ha, mul_zero]
  have h0 := hz (DualLatticeEmbeddings.yv Xf ξ) (by rw [hspan]; trivial)
  rw [real_inner_self_eq_norm_sq, norm_sq_yv_D χ Xf hfr] at h0
  have := trF_pos χ hP ξ hξ0
  linarith

end Formalism.L2.Geo.Rec.StarEmbeddingNorm
