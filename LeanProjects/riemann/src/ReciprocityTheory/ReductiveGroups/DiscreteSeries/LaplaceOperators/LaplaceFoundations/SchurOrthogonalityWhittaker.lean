import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.MeasurableEmbeddingLeftMulOfIsUnit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.LowestKTypeIntertwinerExists

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem clm_continuousOn {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (σ : X → (V →L[ℂ] V)) (s : Set X)
    (h : ∀ v, ContinuousOn (fun g => σ g v) s) : ContinuousOn σ s := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_clm_apply.2 fun v => continuousOn_iff_continuous_domRestrict.1 (h v)

theorem isClosed_UW : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have e : {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} =
      {x | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} ∩
        ((⋂ a : Fin r, ({x | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {x | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩
          {x | Matrix.of x *ᵥ z0 k r = z0 k r}) := by
    ext x
    simp only [UWset, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc)
    continuous_const) (IsClosed.inter (isClosed_iInter fun a => IsClosed.inter ?_ ?_) ?_)
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const

theorem blk_cont : Continuous (fun x : Mt k r => StandardBasisEmbedding.blk (k := k) (r := r) (Matrix.of x)) := by
  refine continuous_pi fun q => continuous_pi fun q' => ?_
  exact (continuous_apply _).comp (continuous_apply _)

theorem uw_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UWset k r (z0 k r)) :
    g⁻¹ = Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) ∧ IsUnit g := by
  have hu := StandardBasisEmbedding.blk_unitary hg
  have h1 : g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) = 1 := by
    have e := StandardBasisEmbedding.eq_blockW hg
    rw [show g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) =
        Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk g) * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) from by rw [← e]]
    rw [← StandardBasisEmbedding.blockW_mul, Unitary.mul_star_self_of_mem hu, StandardBasisEmbedding.blockW_one]
  exact ⟨Matrix.inv_eq_right_inv h1, ⟨⟨g, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩⟩

theorem schur_orthogonality_whittaker {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {u : Fin k → ℝ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)) {ξ : Vp}
    {μW : Measure (Mt k r)} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P)
    (hπ : Formalism.MainNotions.S.IsHCTypeU k u (fun h => π (Formalism.MainNotions.S.blockW k r h))) (hξn : ‖ξ‖ = 1)
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => π (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ)
    (hΛ : ∀ a : Fin k, Λ ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a)
    (hμW : Formalism.MainNotions.S.IsHaarOn (UWset k r (z0 k r)) μW) (hμ1 : μW Set.univ = 1) (Y : T.V) :
    ∫ x, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * ⟪T.w, Y⟫_ℂ := by
  classical
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true := fun a ha => cay_eps hP hW a ha
  have hΛ' : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q := fun q => hΛ q
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : Nontrivial Vp := hπ.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  obtain ⟨U, α, hint, hα⟩ := lowestKType_intertwiner_exists T hε hΛ' π' hπ hξ
  have hUR := hπ.2.2.1
  have hπadj : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ a b : Vp, ⟪a, π' h b⟫_ℂ = ⟪π' (star h) a, b⟫_ℂ := by
    intro h hh a b
    have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
    have hinv : π' (star h) (π' h b) = b := by
      have := hUR.1.2 _ (unit_uj hs) _ (unit_uj hh)
      rw [Unitary.star_mul_self_of_mem hh, hUR.1.1] at this
      have := congrArg (fun A : Vp →L[ℂ] Vp => A b) this
      simpa using this.symm
    let Lm : Vp →ₗᵢ[ℂ] Vp := { toLinearMap := (π' (star h) : Vp →ₗ[ℂ] Vp), norm_map' := hUR.2.1 _ (unit_uj hs) }
    have := Lm.inner_map_map a (π' h b)
    change ⟪π' (star h) a, π' (star h) (π' h b)⟫_ℂ = _ at this
    rw [hinv] at this
    exact this.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    have : U ξ = 0 := Subtype.ext hα
    rw [LinearIsometryEquiv.map_eq_zero_iff] at this
    rw [this, norm_zero] at hξn
    exact zero_ne_one hξn
  set η : Vp := α⁻¹ • ξ with hηdef
  have hη : (U η : T.V) = T.w := by
    rw [hηdef, map_smul, Submodule.coe_smul, hα, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  set Y' : Vp := U.symm ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y) with hY'
  have hproj : ∀ s : spanW (k := k) (r := r) T,
      ⟪(s : T.V), Y⟫_ℂ = ⟪s, (spanW (k := k) (r := r) T).orthogonalProjectionOnto Y⟫_ℂ := by
    intro s
    have h0 : ⟪(s : T.V), Y - ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y : T.V)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal s.2 ((spanW (k := k) (r := r) T).sub_starProjection_mem_orthogonal Y)
    rw [inner_sub_right, sub_eq_zero] at h0
    rw [h0]
    rfl
  have hUY : ∀ a : Vp, ⟪(U a : T.V), Y⟫_ℂ = ⟪a, Y'⟫_ℂ := by
    intro a
    rw [hproj, ← U.inner_map_map a Y', hY', U.apply_symm_apply]
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have hpt : ∀ᵐ x ∂μW, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ =
      ⟪η, π (Matrix.of x) Y'⟫_ℂ * ⟪π (Matrix.of x) ξ, ξ⟫_ℂ := hae.mono fun x hx => by
    have hu : StandardBasisEmbedding.blk (Matrix.of x) ∈ Matrix.unitaryGroup (Fin k) ℂ := StandardBasisEmbedding.blk_unitary hx
    have hx' : Matrix.of x = Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk (Matrix.of x)) := StandardBasisEmbedding.eq_blockW hx
    have h1 : π (Matrix.of x)⁻¹ = π' (star (StandardBasisEmbedding.blk (Matrix.of x))) := by rw [(uw_inv hx).1]
    have h2 : HW.torepSig T (P * Matrix.of x * P⁻¹) = rhoK (k := k) (r := r) T (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [rhoK, ← cay_kE hP hW, ← hx']
    have h3 : π (Matrix.of x) = π' (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [hπ']; exact congrArg π hx'
    rw [h1, h2, h3]
    rw [rhoK_adj T hε hu, ← hη, hint _ (Unitary.star_mem hu), hUY, ← hπadj _ hu]
    rw [hπadj _ (Unitary.star_mem hu), star_star, mul_comm]
  rw [integral_congr_ae hpt]
  have hmul : ∀ g ∈ UWset k r (z0 k r), ∀ h ∈ UWset k r (z0 k r), π (g * h) = π g * π h := by
    intro g hg h hh
    have e1 := StandardBasisEmbedding.eq_blockW hg
    have e2 := StandardBasisEmbedding.eq_blockW hh
    rw [e1, e2, ← StandardBasisEmbedding.blockW_mul]
    exact hUR.1.2 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) _ (unit_uj (StandardBasisEmbedding.blk_unitary hh))
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hirr : ∀ S : Submodule ℂ Vp, (∀ g ∈ UWset k r (z0 k r), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    exact hπ.2.2.2.2.2.1 S le_top (fun g hg v hv => hS _ (StandardBasisEmbedding.mem_UW hg.1) v hv)
  have hmeas : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π' (StandardBasisEmbedding.blk (Matrix.of x))) {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
      (clm_continuousOn π' _ hUR.2.2).comp blk_cont.continuousOn (fun x hx => unit_uj (StandardBasisEmbedding.blk_unitary hx))
    have h1 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h1
    exact h1.congr (hae.mono fun x hx => (congrArg π (StandardBasisEmbedding.eq_blockW hx)).symm)
  rw [schur_orthogonality_unitary_rep (UWset k r (z0 k r)) μW hμW.2.2.1 (fun g hg => (uw_inv hg).2) (fun g hg => hμW.2.2.2 g hg)
    π hmul hunit hirr hmeas Y' ξ ξ η]
  have e1 : ⟪η, ξ⟫_ℂ = (starRingEnd ℂ) α⁻¹ := by
    rw [hηdef, inner_smul_left, inner_self_eq_norm_sq_to_K, hξn]; simp
  have e2 : ⟪ξ, Y'⟫_ℂ = (starRingEnd ℂ) α * ⟪T.w, Y⟫_ℂ := by
    rw [← hUY, hα, inner_smul_left]
  rw [e1, e2, map_inv₀]
  have hc0 : (starRingEnd ℂ) α ≠ 0 := by simpa using hα0
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
