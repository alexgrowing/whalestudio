import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.IsOpenCball1
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.PieceMem

noncomputable section

open Matrix Topology

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniq_eZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w : Fin n → k) (hw : e *ᵥ w = w) (hw0 : w ≠ 0) (u1 u2 : Matrix (Fin n) (Fin n) k) (h1 : u1 ∈ Z)
    (h2 : u2 ∈ Z) (h1e : u1 * e = u1) (h2e : u2 * e = u2) (h12 : u1 *ᵥ w = u2 *ᵥ w) : u1 = u2 := by
  by_contra hne
  have hu : u1 - u2 ∈ Z := Z.sub_mem h1 h2
  have hue : (u1 - u2) * e = u1 - u2 := by rw [sub_mul, h1e, h2e]
  obtain ⟨u', -, -, hu'⟩ := hprim _ hu hue (sub_ne_zero.mpr hne)
  apply hw0
  have hz : (u1 - u2) *ᵥ w = 0 := by rw [sub_mulVec, h12, sub_self]
  rw [← hw, ← hu', ← mulVec_mulVec, hz, mulVec_zero]

theorem exists_psi (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w : Fin n → k) (hw : e *ᵥ w = w) (hw0 : w ≠ 0) :
    ∃ ψ : (Fin n → k) →ₗ[k] Matrix (Fin n) (Fin n) k,
      ∀ v, ψ v ∈ Z ∧ ψ v * e = ψ v ∧ ψ v *ᵥ w = e *ᵥ v := by
  have hex : ∀ v : Fin n → k, ∃ u ∈ Z, u * e = u ∧ u *ᵥ w = e *ᵥ v := fun v =>
    one_dim Z hZ h0 e he hee hprim w (e *ᵥ v) hw hw0 (by rw [mulVec_mulVec, hee])
  choose φ hφZ hφe hφw using hex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, fun v => ⟨hφZ v, hφe v, hφw v⟩⟩
  · intro v1 v2
    apply uniq_eZ Z e hprim w hw hw0 _ _ (hφZ _) (Z.add_mem (hφZ v1) (hφZ v2))
      (hφe _) (by rw [add_mul, hφe, hφe])
    rw [hφw, add_mulVec, hφw, hφw, mulVec_add]
  · intro c v
    apply uniq_eZ Z e hprim w hw hw0 _ _ (hφZ _) (Z.smul_mem (hφZ v) c)
      (hφe _) (by rw [smul_mul_assoc, hφe])
    rw [hφw, smul_mulVec, hφw, mulVec_smul]

theorem orbit_nhds (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (γ : (ValueGroupWithZero k)ˣ) (w : Wt e) (hw0' : w.1 ≠ 0) :
    {w' | ∃ g ∈ Ks Z e γ, g • w = w'} ∈ 𝓝 w := by
  obtain ⟨ψ, hψ⟩ := exists_psi Z hZ h0 e he hee hprim w.1 w.2 hw0'
  have hψc : Continuous ψ := by
    have hrep : ∀ v : Fin n → k, ψ v = ∑ i, v i • ψ (fun j => if i = j then 1 else 0) := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      rw [map_sum]
      simp only [map_smul]
    have hfun : (ψ : (Fin n → k) → Matrix (Fin n) (Fin n) k) =
        fun v => ∑ i, v i • ψ (fun j => if i = j then 1 else 0) := funext hrep
    rw [hfun]
    exact continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)
  let Φ : Wt e → Matrix (Fin n) (Fin n) k := fun w' => 1 + ψ (w'.1 - w.1)
  have hΦ : Continuous Φ :=
    continuous_const.add (hψc.comp (continuous_subtype_val.sub continuous_const))
  have hΦw : Φ w = 1 := by simp [Φ]
  have hU : {A : Matrix (Fin n) (Fin n) k | A.det ≠ 0} ∩
      ({A : Matrix (Fin n) (Fin n) k | sm γ (A - 1)} ∩ {A | sm γ (A⁻¹ - 1)}) ∈ 𝓝 (Φ w) := by
    rw [hΦw]
    refine Filter.inter_mem ?_ (Filter.inter_mem ?_ ?_)
    · exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)
    · exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        ((isOpen_sm γ).mem_nhds (by simpa using sm_zero γ))
    · exact (cont_inv_one.sub continuousAt_const).preimage_mem_nhds
        ((isOpen_sm γ).mem_nhds (by simpa using sm_zero γ))
  refine Filter.mem_of_superset (hΦ.continuousAt.preimage_mem_nhds hU) ?_
  rintro w' ⟨hdet, hs1, hs2⟩
  obtain ⟨huZ, hue, huw⟩ := hψ (w'.1 - w.1)
  have hA : Φ w' = 1 + ψ (w'.1 - w.1) := rfl
  have hmemG : (Matrix.nonsingInvUnit (Φ w') (isUnit_iff_ne_zero.mpr hdet) : GL (Fin n) k) ∈ Gs Z e := by
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · show a * Φ w' = Φ w' * a
      rw [hA, mul_add, add_mul, mul_one, one_mul, hZ.1 a ha _ huZ]
    · show Φ w' * e = e * Φ w'
      rw [hA, add_mul, mul_add, one_mul, mul_one, hZ.1 _ huZ e he]
    · show Φ w' * (1 - e) = 1 - e
      rw [hA, add_mul, one_mul, mul_sub, mul_one, hue, sub_self, add_zero]
  refine ⟨⟨_, hmemG⟩, ⟨hs1, hs2⟩, ?_⟩
  apply Subtype.ext
  rw [smul_val]
  show Φ w' *ᵥ w.1 = w'.1
  rw [hA, add_mulVec, one_mulVec, huw, mulVec_sub, w'.2, w.2]
  abel

theorem isOpen_orbit (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (γ : (ValueGroupWithZero k)ˣ) (w : Wt e) (hw0 : w.1 ≠ 0) :
    IsOpen {w' | ∃ g ∈ Ks Z e γ, g • w = w'} := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨g, hg, rfl⟩
  have hne : (g • w).1 ≠ 0 := by
    intro h
    apply hw0
    have h' := congrArg (fun x => ((g : GL (Fin n) k)⁻¹ : GL (Fin n) k).val *ᵥ x) h
    simp only [smul_val, mulVec_mulVec, mulVec_zero] at h'
    simpa using h'
  refine Filter.mem_of_superset (orbit_nhds Z hZ h0 e he hee hprim γ (g • w) hne) ?_
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h * g, (Ks Z e γ).mul_mem hh hg, mul_smul h g w⟩

theorem unif (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (hee : e * e = e)
    {Y : Type*} [TopologicalSpace Y] (f : Y × Wt e → ℂ) (hf : f ∈ TF (Y × Wt e)) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ g ∈ Ks Z e γ, ∀ p : Y × Wt e, f (p.1, g • p.2) = f p := by
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ᶠ A in 𝓝 (1 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport f,
      ∀ q' : Y × Wt e, q'.1 = q.1 → q'.2.1 = A *ᵥ q.2.1 → f q' = f q := by
    refine hcs.eventually_forall_of_forall_eventually (fun p _ => ?_)
    have hS : IsOpen {x | f x = f p} := hlc.isOpen_fiber _
    have hι : Topology.IsInducing (Prod.map id Subtype.val : Y × Wt e → Y × (Fin n → k)) :=
      Topology.IsInducing.id.prodMap Topology.IsInducing.subtypeVal
    obtain ⟨t, ht, hte⟩ := hι.isOpen_iff.mp hS
    have hH : Continuous (fun z : Matrix (Fin n) (Fin n) k × (Y × Wt e) => (z.2.1, z.1 *ᵥ z.2.2.1)) :=
      continuous_snd.fst.prodMk (continuous_fst.matrix_mulVec (continuous_subtype_val.comp continuous_snd.snd))
    have hpt : p ∈ Prod.map id Subtype.val ⁻¹' t := by
      rw [hte]
      exact rfl
    have h1 : ∀ᶠ z : Matrix (Fin n) (Fin n) k × (Y × Wt e) in 𝓝 (1, p), (z.2.1, z.1 *ᵥ z.2.2.1) ∈ t := by
      apply hH.continuousAt.preimage_mem_nhds
      apply ht.mem_nhds
      show (p.1, (1 : Matrix (Fin n) (Fin n) k) *ᵥ p.2.1) ∈ t
      rw [one_mulVec]
      exact hpt
    have hm : ∀ᶠ x in 𝓝 p, f x = f p := hS.mem_nhds rfl
    have h2 : ∀ᶠ z : Matrix (Fin n) (Fin n) k × (Y × Wt e) in 𝓝 (1, p), f z.2 = f p :=
      (continuous_snd.tendsto ((1 : Matrix (Fin n) (Fin n) k), p)).eventually hm
    filter_upwards [h1, h2] with z hz1 hz2 q' hq1 hq2
    have hq' : q' ∈ Prod.map id Subtype.val ⁻¹' t := by
      show (q'.1, q'.2.1) ∈ t
      rw [hq1, hq2]
      exact hz1
    rw [hte] at hq'
    exact (hq' : f q' = f p).trans hz2.symm
  obtain ⟨γ, hγ⟩ := nhds_one_ball key
  have hP : ∀ g ∈ Ks Z e γ, ∀ q ∈ tsupport f, f (q.1, g • q.2) = f q := fun g hg q hq =>
    hγ _ (fun i j => (hg.1 i j).1) q hq (q.1, g • q.2) rfl (smul_val Z e g q.2)
  refine ⟨γ, fun g hg p => ?_⟩
  by_cases hp : p ∈ tsupport f
  · exact hP g hg p hp
  · by_cases hp' : (p.1, g • p.2) ∈ tsupport f
    · have h' := hP g⁻¹ ((Ks Z e γ).inv_mem hg) _ hp'
      simp only [inv_smul_smul] at h'
      exact h'.symm
    · rw [image_eq_zero_of_notMem_tsupport hp', image_eq_zero_of_notMem_tsupport hp]

end PositivityTheory.RgUd.T.Nil.BasePf
