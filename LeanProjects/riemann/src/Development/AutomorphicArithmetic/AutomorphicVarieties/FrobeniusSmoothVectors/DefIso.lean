import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExtA
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_residueField_map_comp_res {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_comp_map_iff {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) : NRep.IsBar (j.comp f) (NRep.map j σ) ↔ NRep.IsBar f σ := by
  unfold NRep.IsBar
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => j.injective (h1 g i), fun v i g => j.injective (h2 v i g)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => congrArg j (h1 g i), fun v i g => congrArg j (h2 v i g)⟩

theorem UpperTheory.V.Fr.def_iso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ (C : Type) [CommRing C] [Algebra L.O' C] [IsCO L.O' C] (ρ : NRep F n C), ρ.Cont (maximalIdeal C) → ρ.map (res L.O' C : C →+* ResidueField L.O') = L.ρ.map (res L.O' L.R : L.R →+* ResidueField L.O') → ∃! g : L.R →ₐ[L.O'] C, L.ρ.map (g : L.R →+* C) = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L C _ _ _ ρ hc hres
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' C) := IsCO.isLocalHom
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  letI : Algebra O C := ((algebraMap L.O' C).comp (algebraMap O L.O')).toAlgebra
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCloc : IsLocalHom (algebraMap O C) :=
    inferInstanceAs (IsLocalHom ((algebraMap L.O' C).comp (algebraMap O L.O')))
  have hCL : UpperTheory.V.CA.IsCL O C := by
    refine ⟨inferInstance, IsCO.complete (O := L.O'), hCloc, ?_⟩
    let φ : L.O' →ₐ[O] ResidueField C :=
      (IsScalarTower.toAlgHom O C (ResidueField C)).comp (IsScalarTower.toAlgHom O L.O' C)
    refine Module.Finite.of_surjective φ.toLinearMap ?_
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := L.O') z
    refine ⟨a, ?_⟩
    show IsLocalRing.residue C (algebraMap L.O' C a) = IsLocalRing.residue C z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
    exact neg_mem ha
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jC : ResidueField L.O' →+* ResidueField C := IsLocalRing.ResidueField.map (algebraMap L.O' C)
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hfC : IsResMap O C (jC.comp f0) := by
    intro a
    show jC (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    rfl
  have hfR : IsResMap O L.R (jR.comp f0) := by
    intro a
    show jR (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsScalarTower.algebraMap_apply O L.O' L.R a]
  have hbR := (loc_rho hF hn S x L).2.1 _ hfR
  rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := L.R)] at hbR
  have hσ : NRep.IsBar f0 (NRep.map (res L.O' L.R : L.R →+* ResidueField L.O') L.ρ) :=
    (nRep_isBar_comp_map_iff f0 jR _).mp hbR
  have hbar : NRep.IsBar (jC.comp f0) (NRep.map (IsLocalRing.residue C) ρ) := by
    rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := C)]
    show NRep.IsBar (jC.comp f0) (NRep.map jC (NRep.map (res L.O' C : C →+* ResidueField L.O') ρ))
    rw [hres]
    exact (nRep_isBar_comp_map_iff f0 jC _).mpr hσ
  obtain ⟨ξ, hξ, hξx⟩ := point_loc hF hn S C hCL (jC.comp f0) hfC ρ hc hbar
  have hx0 : S.x0 ≤ x := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr (loc_flat hF hn S x L).2.2
  let ξ1 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' C).restrictScalars O).comp ξ
  let ξ2 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' L.R).restrictScalars O).comp L.ι
  have h12 : ξ1 = ξ2 := by
    refine ext_A hF hn S (ResidueField L.O') ξ1 ξ2 ?_ ?_ ?_
    · exact (congrArg (NRep.map (res L.O' C : C →+* ResidueField L.O')) hξ).trans hres
    · intro a ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' C (ξ a) ∈ _
      rw [(res_eq_zero_iff L.O' C (ξ a)).mpr (hξx ha)]
      exact zero_mem _
    · intro a ha
      have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
        rw [L.lies]
        exact hx0 ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' L.R (L.ι a) ∈ _
      rw [(res_eq_zero_iff L.O' L.R (L.ι a)).mpr hm]
      exact zero_mem _
  obtain ⟨g, hg, huniq⟩ := L.univ C ξ (fun a => AlgHom.congr_fun h12 a)
  have hgι : (g : L.R →+* C).comp (L.ι : S.A →+* L.R) = (ξ : S.A →+* C) := RingHom.ext hg
  refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
  · show NRep.map ((g : L.R →+* C).comp (L.ι : S.A →+* L.R)) S.u = ρ
    rw [hgι]
    exact hξ
  · let ξ' : S.A →ₐ[O] C := (g'.restrictScalars O).comp L.ι
    have h' : ξ' = ξ := by
      refine ext_A hF hn S C ξ' ξ ?_ ?_ hξx
      · exact hg'.trans hξ.symm
      · intro a ha
        have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
          rw [L.lies]
          exact hx0 ha
        refine Ideal.mem_comap.mpr ?_
        show g' (L.ι a) ∈ maximalIdeal C
        rw [← res_eq_zero_iff L.O' C, res_map]
        exact (res_eq_zero_iff L.O' L.R _).mpr hm
    intro a
    exact AlgHom.congr_fun h' a
