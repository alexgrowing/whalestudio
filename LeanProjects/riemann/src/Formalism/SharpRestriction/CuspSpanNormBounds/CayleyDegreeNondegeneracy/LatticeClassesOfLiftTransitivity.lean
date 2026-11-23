import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsDecompOrthIsotropicPlus

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_latticeWithZ_iff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (Λ : LatV D) (w : (D.sp.X 0).V) (c : D.host.E) :
    (w, c) ∈ latticeWithZ D F Λ ↔ D.sp.iXY 0 w + c • F.z ∈ Lsub Λ (lf D F) := by
  unfold latticeWithZ
  rw [Submodule.mem_comap]
  simp [embedWithZ]

include he hz in
theorem extendByIdentity_mem_flag_stabilizer (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ stabF D F0 := by
  have hfix : ∀ y ∈ F0.X, (extendByIdentity D γ).symm y = y :=
    fun y hy => extendByIdentity_symm_fix_orth D γ y (isotropic_le_orth_range D u F0 he hy)
  refine ⟨extendByIdentity_mem_isom D γ hγ, fun j => ?_, ?_⟩
  · ext x
    rw [Submodule.mem_map_equiv]
    constructor
    · intro h
      have e : (extendByIdentity D γ).symm x = x := (extendByIdentity D γ).symm.injective (hfix _ (partial_isotropic_le F0 j h))
      rwa [e] at h
    · intro h
      rw [hfix x (partial_isotropic_le F0 j h)]
      exact h
  · rw [← LinearEquiv.eq_symm_apply]
    exact (extendByIdentity_symm_fix_orth D γ _ (z_mem_orth_range D u F0 hz)).symm

include he hz in

theorem transport_isLattice_latticeWithZ (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap (extendByIdentity D γ) Λ) ∧
      latticeWithZ D F0 (gmap (extendByIdentity D γ) Λ) = gmap (extendByOne D γ) (latticeWithZ D F0 Λ) := by
  have hzO := z_mem_orth_range D u F0 hz
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (isotropic_le_orth_range D u F0 he hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ hΛ
  refine ⟨hrow, ?_⟩
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLsub, isomAct_mem_gmap,
    extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem lattice_classes_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : LatticeClassesIff D u := by
  intro hTp hT3 hsp F0 he hz Λ₁ Λ₂ h₁ h₂
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨γ, hγ, ?_⟩
    have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      have := hσ.2.1 D.R.rS
      rwa [partial_isotropic_top] at this
    have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ₁
    ext ⟨w, c⟩
    have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
    have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
      have h1 := hind (γ.symm w)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
        rw [← Submodule.mem_map_equiv, hX]
        exact h1
      have hzs : σ.symm F0.z = F0.z := by
        rw [LinearEquiv.symm_apply_eq]
        exact hσ.2.2.symm
      have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
          -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
        rw [map_add, map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
        abel
      rw [e3]
      exact F0.X.neg_mem h2
    have hd' := isotropic_le_Lsub F0 Λ₁ hd
    constructor
    · intro ha
      have := (Lsub Λ₁ (lf D F0)).add_mem ha hd'
      simpa using this
    · intro hb
      have := (Lsub Λ₁ (lf D F0)).sub_mem hb hd'
      simpa using this
  · rintro ⟨γ, hγ, hγe⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ₁ h₁
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγe)
    obtain ⟨n, hn, _, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow h₂ hLs
    exact ⟨n * extendByIdentity D γ, mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ), by rw [gmap_mul, hne]⟩

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
