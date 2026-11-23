import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualModelTranscendence

variable {L : Type} [Field L]

def scaleHom (a : L) :
    MvPolynomial Unit (MvPolynomial Unit L) →+* MvPolynomial Unit (MvPolynomial Unit L) :=
  eval₂Hom ((C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)).comp
      (aeval fun _ : Unit => C a * X ()).toRingHom) fun _ => C (C a⁻¹) * X ()

theorem scaleHom_CC (a c : L) : scaleHom a (C (C c)) = C (C c) := by simp [scaleHom]

theorem scaleHom_S (a : L) : scaleHom a (C (X ())) = C (C a) * C (X ()) := by simp [scaleHom]

theorem scaleHom_alt (a : L) : scaleHom a (X ()) = C (C a⁻¹) * X () := by simp [scaleHom]

theorem scaleHom_comp {a : L} (ha : a ≠ 0) : (scaleHom a⁻¹).comp (scaleHom a) = RingHom.id _ := by
  have hC : ((scaleHom a⁻¹).comp (scaleHom a)).comp C =
      (C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, scaleHom_CC]
    · cases v
      simp only [RingHom.comp_apply, scaleHom_S, map_mul, scaleHom_CC]
      rw [← mul_assoc, ← map_mul, ← map_mul, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  refine MvPolynomial.ringHom_ext (fun p => ?_) (fun u => ?_)
  · exact RingHom.congr_fun hC p
  · cases u
    simp only [RingHom.comp_apply, scaleHom_alt, map_mul, scaleHom_CC, RingHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, inv_inv, inv_mul_cancel₀ ha, map_one, map_one, one_mul]

theorem scaleHom_injective {a : L} (ha : a ≠ 0) : Function.Injective (scaleHom a) :=
  Function.LeftInverse.injective (g := scaleHom a⁻¹) fun p => RingHom.congr_fun (scaleHom_comp ha) p

def scale {a : L} (ha : a ≠ 0) :
    FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) →+*
      FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) :=
  IsFractionRing.lift (A := MvPolynomial Unit (MvPolynomial Unit L))
    (g := (algebraMap _ (FractionRing (MvPolynomial Unit (MvPolynomial Unit L)))).comp (scaleHom a))
    ((IsFractionRing.injective _ _).comp (scaleHom_injective ha))

theorem scale_algebraMap {a : L} (ha : a ≠ 0) (p : MvPolynomial Unit (MvPolynomial Unit L)) :
    scale ha (algebraMap _ _ p) = algebraMap _ _ (scaleHom a p) :=
  IsFractionRing.lift_algebraMap _ p

theorem transcendental_of_scale {R Ω : Type} [CommRing R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {z : Ω} (hz : z ≠ 0)
    (h : ∀ n : ℕ, ∃ σ : Ω →+* Ω, (∀ y ∈ A, σ y = y) ∧ σ z = ((n : Ω) + 1) * z) : Transcendental A z := by
  rintro ⟨p, hp0, hp⟩
  rw [Polynomial.aeval_def] at hp
  have hroot : ∀ n : ℕ, Polynomial.eval₂ (algebraMap A Ω) (((n : Ω) + 1) * z) p = 0 := by
    intro n
    obtain ⟨σ, hfix, hσz⟩ := h n
    have hcomp : σ.comp (algebraMap A Ω) = algebraMap A Ω := RingHom.ext fun y => hfix y y.2
    have h' := Polynomial.hom_eval₂ p (algebraMap A Ω) σ z
    rw [hp, map_zero, hcomp, hσz] at h'
    exact h'.symm
  have hq : p.map (algebraMap A Ω) ≠ 0 := (Polynomial.map_ne_zero_iff fun x y h => Subtype.ext h).mpr hp0
  refine hq (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : Ω) + 1) * z) (fun n m hnm => ?_) fun n => ?_
  · exact Nat.cast_injective (add_right_cancel (mul_right_cancel₀ hz hnm))
  · change Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hroot n

variable {K : Type} [Field K] {i : ℕ}

theorem scale_emb {a : ProjField K i} (ha : a ≠ 0) (x : ProjField K i) :
    scale ha (dualStdModelEmb K i x) = dualStdModelEmb K i x := by
  simp only [dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_CC]

theorem scale_S {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelS K i) = dualStdModelEmb K i a * dualStdModelS K i := by
  simp only [dualStdModelS, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_S, map_mul]

theorem scale_alt {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelT K i) = dualStdModelEmb K i a⁻¹ * dualStdModelT K i := by
  simp only [dualStdModelT, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_alt, map_mul]

variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))

theorem scale_inl {a : ProjField K i} (ha : a ≠ 0) (t : T) :
    scale ha (dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelEmb K i a * dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S]
  ring

theorem scale_inr {a : ProjField K i} (ha : a ≠ 0) (j : PBlk i ()) :
    scale ha (dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  have h : dualStdModelEmb K i a * dualStdModelEmb K i a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S, scale_alt]
  linear_combination
    (dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i) * h

end StandardDualModelTranscendence

open DualArithmeticVariety StandardDualModelTranscendence in

theorem DualStdModelTransc.proof : DualStdModelTransc.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hy : dualLatticeCoord b ⟨(), c⟩ ≠ 0 := by
    rw [dualLatticeCoord_eq]
    exact evalForm_ne_zero fun h => b.ne_zero c (Subtype.ext h)
  have hS : dualStdModelS K i ≠ 0 := by
    intro h
    have h' := IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
      (dualStdModelField K i) (h.trans (map_zero _).symm)
    simp at h'
  refine transcendental_of_scale _ (mul_ne_zero ((map_ne_zero _).mpr hy) hS) fun n => ?_
  have ha : ((n : ProjField K i) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hΦfix : ∀ x : Φ₀, scale ha (algebraMap Φ₀ _ x) = algebraMap Φ₀ _ x := by
    intro x
    have hx : algebraMap Φ₀ (dualStdModelField K i) x ∈
        Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) :=
      hΦ ▸ RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
    refine RingHom.eqOn_field_closure (g := RingHom.id _) ?_ hx
    rintro _ ⟨⟨u, j⟩, rfl⟩
    cases u
    exact scale_inr b ha j
  let σ : dualStdModelField K i →ₐ[Φ₀] dualStdModelField K i := { scale ha with commutes' := hΦfix }
  refine ⟨scale ha, fun y hyA => AlgHom.adjoin_le_equalizer σ (AlgHom.id Φ₀ _) ?_ hyA, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change scale ha _ = _
    rw [map_div₀, scale_inl b ha, scale_inl b ha, mul_div_mul_left _ _ ((map_ne_zero _).mpr ha)]
    rfl
  · rw [scale_inl b ha]
    simp

end

end GroundTheory.Heights₂.Heights
