import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PointArithIntersection

open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree

variable {T : Type} [Fintype T]

theorem logNorm_smul {A : HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by
  obtain ⟨a, ha, hhom, -⟩ := hs
  have hz : (fun p : Σ _ : Unit, T => c * z p) = scaleBlock () c z := by
    funext p
    simp [scaleBlock]
  have hh : A.h (fun p => c * z p) = ‖c‖ ^ A.a () * A.h z := by
    simpa using A.smul (fun _ => c) z (fun _ => hc)
  unfold logNorm
  rw [hh, hz, eval_scaleBlock () c z s a hhom, ha (), zpow_natCast, norm_mul, norm_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]

variable {K' : Type} [Field K'] [NumberField K']

theorem eq_of_ptOf_eq_smul {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by
  have ht : t = 1 := by
    have := congrFun h ⟨(), c ()⟩
    simp only [ptOf_chart hc, mul_one] at this
    exact this.symm
  subst ht
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
  rintro _ ⟨p, rfl⟩
  have := congrFun h p
  simp only [one_mul] at this
  exact this

theorem sum_reps_eq {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by
  have hex : ∀ t ∈ R, ∃ φ : blockFnField y →ₐ[ℚ] ℂ,
      ptOf y c φ = (fun p => (t ⟨p.1, c p.1⟩)⁻¹ * t p) ∧ ∀ k, t ⟨k, c k⟩ ≠ 0 :=
    fun t ht => exists_ptOf hP hc (hR t ht)
  refine Finset.sum_bij (fun t ht => (hex t ht).choose) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t ht t' ht' he
    have h1 := (hex t ht).choose_spec
    have h2 := (hex t' ht').choose_spec
    rw [he] at h1
    obtain ⟨u, -, hu⟩ := hU t (hR t ht)
    have e1 : t = u := hu t ⟨ht, ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩⟩
    have e2 : t' = u := by
      refine hu t' ⟨ht', fun k => t ⟨k, c k⟩ * (t' ⟨k, c k⟩)⁻¹,
        fun k => mul_ne_zero (h1.2 k) (inv_ne_zero (h2.2 k)), funext fun p => ?_⟩
      have := congrFun (h1.1.symm.trans h2.1) p
      have h0 := h1.2 p.1
      have h0' := h2.2 p.1
      simp only at this ⊢
      rw [show t p = t ⟨p.1, c p.1⟩ * ((t ⟨p.1, c p.1⟩)⁻¹ * t p) by field_simp, this]
      ring
    rw [e1, e2]
  · intro φ _
    obtain ⟨u, ⟨hu, ⟨d, hd, hdu⟩⟩, -⟩ := hU _ (ptOf_mem hc φ)
    refine ⟨u, hu, eq_of_ptOf_eq_smul hc ((u ⟨(), c ()⟩)⁻¹ * (d ())⁻¹) ?_⟩
    rw [(hex u hu).choose_spec.1, hdu]
    funext p
    have h0 := hd ()
    ring_nf
    field_simp
  · intro t ht
    rw [(hex t ht).choose_spec.1]
    exact (hF _ (inv_ne_zero ((hex t ht).choose_spec.2 ())) t).symm

theorem sum_ringHom_restrict (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by
  classical
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K' ℂ)
    (fun σ : K' →+* ℂ => H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')))
    (fun σ : K' →ₐ[ℚ] ℂ => H (σ.comp (IsScalarTower.toAlgHom ℚ κ K'))) (fun _ => rfl)]
  let res : (K' →ₐ[ℚ] ℂ) → (κ →ₐ[ℚ] ℂ) := fun σ => σ.comp (IsScalarTower.toAlgHom ℚ κ K')
  rw [← Fintype.sum_fiberwise res, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hconst : ∀ i : {σ // res σ = f}, H (res i) = H f := fun i => by rw [i.2]
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  have e : {σ // res σ = f} ≃ @AlgHom κ K' ℂ _ _ _ _ f.toRingHom.toAlgebra :=
    ((algHomEquivSigma (A := ℚ) (B := κ) (C := K') (D := ℂ)).subtypeEquiv
      (p := fun σ => res σ = f) (q := fun x => x.1 = f) fun σ => Iff.rfl).trans (Equiv.sigmaSubtype f)
  let _ := f.toRingHom.toAlgebra
  rw [Fintype.card_eq_nat_card, Nat.card_congr e,
    AlgHom.natCard_of_splits κ K' ℂ fun _ => IsAlgClosed.splits _]

end PointArithIntersection

open PointArithIntersection IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in

theorem PointArInt.proof : PointArInt.Statement := by
  intro T _ K' _ _ y A s hP hs
  classical
  obtain ⟨c0, hc0⟩ := hP.2.1.2.2 ()
  let c : Unit → T := fun _ => c0
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h => hc0 (X_mem_of_eq_zero h)
  obtain ⟨R, hR, hU, hsum⟩ := Inter.regularityPointsSum_holds.proof Unit (fun _ => T) (mCoordIdeal y) hP
  have harInt : arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) =
      ∑ t ∈ R, logNorm A s t := by
    unfold arInt
    have e0 : (fun (j : Fin 0) (z : (Σ _ : Unit, T) → ℂ) =>
        Real.log (((Fin.elim0 j : HermLine (fun _ : Unit => T))).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ _ : Unit, T) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [e0]
    apply hsum
    rintro z z' - ⟨d, hd, rfl⟩
    exact logNorm_smul hs (d ()) (hd ()) z'
  set κ := blockFnField y
  have hσ : ∀ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p)) =
      logNorm A s (ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K'))) := by
    intro σ
    have hy0 : σ (y ⟨(), c0⟩) ≠ 0 := (map_ne_zero σ).mpr (hc ())
    have e : (fun p => σ (y p)) = fun p => σ (y ⟨(), c0⟩) *
        ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p := by
      funext p
      have : ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p =
          σ (y p / y ⟨(), c0⟩) := rfl
      rw [this, map_div₀]
      field_simp
    rw [e, logNorm_smul hs _ hy0]
  rw [harInt, sum_reps_eq hP hc R hR hU (logNorm A s) (fun t ht z => logNorm_smul hs t ht z),
    Finset.sum_congr rfl (fun σ _ => hσ σ),
    sum_ringHom_restrict κ (fun φ => logNorm A s (ptOf y c φ)), degC_eq hP,
    AlgHom.natCard_of_splits ℚ κ ℂ fun _ => IsAlgClosed.splits _, ← Module.finrank_mul_finrank ℚ κ K']
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
