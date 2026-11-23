import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Topology

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "𝒩" => Fintype.card (ι × κ)

theorem continuous_coords : Continuous (coords b R) :=
  (tensorCoordsHomeomorph R b).continuous

theorem continuous_coords_symm : Continuous (coords b R).symm :=
  (tensorCoordsHomeomorph R b).symm.continuous

theorem continuous_resHom :
    Continuous (resHom (ι := ι) b R : Matrix ι ι (R ⊗[K] E) → Matrix (Fin 𝒩) (Fin 𝒩) R) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun M : Matrix ι ι (R ⊗[K] E) => coords b R
    (baseBasis b R ((Fintype.equivFin (ι × κ)).symm p).2 *
      M ((Fintype.equivFin (ι × κ)).symm p).1 ((Fintype.equivFin (ι × κ)).symm q).1)
        ((Fintype.equivFin (ι × κ)).symm q).2
  exact (continuous_apply _).comp ((continuous_coords b R).comp
    (continuous_const.mul (continuous_id.matrix_elem _ _)))

theorem continuous_trHom : Continuous (trHom (ι := ι) b R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_resHom b R).comp Units.continuous_coe_inv.matrix_transpose
  · exact (continuous_resHom b R).comp Units.continuous_val.matrix_transpose

def readoff (A : Matrix (Fin 𝒩) (Fin 𝒩) R) : Matrix ι ι (R ⊗[K] E) := fun i j =>
  (coords b R).symm fun l => ∑ k, coords b R 1 k *
    A (Fintype.equivFin (ι × κ) (i, k)) (Fintype.equivFin (ι × κ) (j, l))

theorem readoff_resHom (M : Matrix ι ι (R ⊗[K] E)) : readoff b R (resHom b R M) = M := by
  ext i j
  apply (coords b R).injective
  rw [readoff, LinearEquiv.apply_symm_apply]
  funext l
  have h := congrFun (coords_mul b R 1 (M i j)) l
  rw [one_mul] at h
  rw [h]
  simp only [vecMul, dotProduct, resHom_apply, Equiv.symm_apply_apply, blockHom_apply]

theorem continuous_readoff : Continuous (readoff (ι := ι) b R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_coords_symm b R).comp (continuous_pi fun l => ?_)
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.matrix_elem _ _)

end Topology

section Star

variable {R : Type*} [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

def cstar (X : Matrix ι ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E) := (X.map (conjBase K E R))ᵀ

theorem cstar_mul (X Y : Matrix ι ι (R ⊗[K] E)) : cstar (X * Y) = cstar Y * cstar X := by
  simp only [cstar, Matrix.map_mul, transpose_mul]

theorem cstar_one : cstar (1 : Matrix ι ι (R ⊗[K] E)) = 1 := by
  simp [cstar]

theorem map_baseMap_mul (f : R →ₐ[K] R') (X Y : Matrix ι ι (R ⊗[K] E)) :
    (X * Y).map (baseMap f) = X.map (baseMap f) * Y.map (baseMap f) :=
  Matrix.map_mul (f := (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E).toRingHom)

theorem cstar_baseMap (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    cstar (X.map (baseMap f)) = (cstar X).map (baseMap f) := by
  ext i j
  simp only [cstar, transpose_apply, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_conjBase]

theorem baseMatrix_baseMap (f : R →ₐ[K] R') :
    (baseMatrix K H R).map (baseMap f) = baseMatrix K H R' := by
  ext i j
  simp only [baseMatrix, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_includeRight]

theorem cstar_mul_baseMatrix_map (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    (cstar X * baseMatrix K H R * X).map (baseMap f) =
      cstar (X.map (baseMap f)) * baseMatrix K H R' * X.map (baseMap f) := by
  rw [map_baseMap_mul, map_baseMap_mul, cstar_baseMap, baseMatrix_baseMap]

end Star

section Main

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable [NumberField K]

local notation "𝒩'" => Fintype.card (ι × Fin (Module.finrank K E))

theorem baseMap_ofId_injective :
    Function.Injective (baseMap (Algebra.ofId K 𝔸[K]) : K ⊗[K] E → 𝔸[K] ⊗[K] E) := by
  let b := Module.finBasis K E
  intro z z' h
  apply (coords b K).injective
  funext k
  have h1 := congrFun (congrArg (coords b 𝔸[K]) h) k
  rw [coords_baseMap, coords_baseMap] at h1
  exact AdeleRing.algebraMap_injective (𝓞 K) K h1

theorem mem_unitaryPoints_of_diagGL {m : GL ι (K ⊗[K] E)}
    (hm : diagGL (Algebra.ofId K 𝔸[K]) m ∈ unitaryPoints K E H 𝔸[K]) : m ∈ unitaryPoints K E H K := by
  have hm' : cstar ((diagGL (Algebra.ofId K 𝔸[K]) m : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι _) *
      baseMatrix K H 𝔸[K] * (diagGL (Algebra.ofId K 𝔸[K]) m : Matrix ι ι _) =
      baseMatrix K H 𝔸[K] := hm
  show cstar (m : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * m = baseMatrix K H K
  rw [diagGL_val, ← cstar_mul_baseMatrix_map, ← baseMatrix_baseMap H (Algebra.ofId K 𝔸[K])] at hm'
  exact Matrix.map_injective baseMap_ofId_injective hm'

theorem exists_isCompact_unitary (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ Ω : Set (unitaryPoints K E H 𝔸[K]), IsCompact Ω ∧ ∀ u : unitaryPoints K E H 𝔸[K],
      ∃ θ ∈ (unitaryDiagonal K H).range, θ⁻¹ * u ∈ Ω := by
  classical
  let b := Module.finBasis K E
  obtain ⟨C, hC, hred⟩ := exists_isCompact_trHom H b hH haniso
  set α := Algebra.ofId K 𝔸[K] with hα
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun x =>
    cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x
  let Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun g => Ψ g⁻¹
  have hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y := by
    intro x y
    simp only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]
  have hΨone : Ψ 1 = Hb := by
    simp [Ψ, cstar_one]
  have hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)),
      cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
          ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X := by
    intro z X
    have h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := by
      rw [← cstar_mul, z.inv_mul, cstar_one]
    have h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := z.inv_mul
    calc _ = (cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
          cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * X *
          (((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
            (z : Matrix ι ι (𝔸[K] ⊗[K] E))) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K] := by
    intro g g'
    have e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g⁻¹ = _
      rw [← hΨmul, mul_inv_cancel_right]
    have e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g'⁻¹ = _
      rw [← hΨone, ← hΨmul, one_mul]
    rw [e1, e2]
    constructor
    · intro he
      have h := congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
        (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he
      simp only [hcancel] at h
      exact h
    · intro hu
      have h : Ψ (g⁻¹ * g') = Hb := hu
      rw [h]
  let Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E)) := (diagGL (ι := ι) α).range
  let C₂ : Set (GL ι (𝔸[K] ⊗[K] E)) := {w | trHom b 𝔸[K] w ∈ C}
  let Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E) := fun A =>
    cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ
  have hΨ'c : Continuous Ψ' := by
    have h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι := ι) b 𝔸[K] A)ᵀ :=
      (continuous_readoff b 𝔸[K]).matrix_transpose
    have h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        cstar (readoff (ι := ι) b 𝔸[K] A)ᵀ := by
      show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ
      exact (h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose
    exact (h2.matrix_mul continuous_const).matrix_mul h1
  have hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K]) := by
    intro w _
    show Ψ w⁻¹ = _
    simp only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]
  have hX : IsCompact (Ψ' '' (Units.val '' C)) := (hC.image Units.continuous_val).image hΨ'c
  let ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun V => V.map (baseMap α)
  have hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) =
      ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))) := by
    intro M
    show Ψ (diagGL α M)⁻¹ = _
    rw [← map_inv]
    simp only [Ψ, ψ, diagGL_val]
    rw [cstar_mul_baseMatrix_map]
  have hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite := by
    refine finite_of_isCompact_coords hX ψ
      (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2)
      (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp
        (continuous_id.matrix_elem _ _)))
      (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_
    · intro V V' h
      ext i j
      apply (coords b K).injective
      funext k
      exact congrFun h (i, j, k)
    · intro V p
      simp only [ψ, Matrix.map_apply, coords_baseMap]
      rfl
  have hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite := by
    refine (hfinV.image ψ).subset ?_
    rintro _ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩
    refine ⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩
    · show ψ _ ∈ Ψ' '' (Units.val '' C)
      rw [← hΓ M, he, hC₂ w hw]
      exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
    · rw [← hΓ M, he]
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin
  let C₃ : Set (GL (Fin 𝒩') 𝔸[K]) := ⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C
  have hC₃ : IsCompact C₃ :=
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)
  let Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}
  refine ⟨Ω, ?_, ?_⟩
  · have hΩcl : IsClosed Ω :=
      hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)
    let F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K] :=
      fun A p =>
      coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2
    have hFc : Continuous F := continuous_pi fun p => (continuous_apply _).comp
      ((continuous_coords b 𝔸[K]).comp
        (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))
    set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD
    have hDc : IsCompact D := (isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage
      ((hC₃.image Units.continuous_val).image hFc)
    have hsub : Ω ⊆ D⁻¹ := by
      intro v hv
      show v⁻¹ ∈ D
      refine ⟨_, ⟨_, hv, rfl⟩, ?_⟩
      funext p
      simp only [F, trHom_val, readoff_resHom, transpose_transpose]
      rfl
    exact hDc.inv.of_isClosed_subset hΩcl hsub
  · intro u
    obtain ⟨M, hM⟩ := hred u
    obtain ⟨δ, hδT, hηδ, -⟩ := hT u u.2 (diagGL α M) ⟨M, rfl⟩
      ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])
    obtain ⟨m, rfl⟩ := hTΓ δ hδT
    rw [← map_mul] at hηδ
    have hU := mem_unitaryPoints_of_diagGL H hηδ
    refine ⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩
    have e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) :
        GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m) := Units.ext rfl
    show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) :
      GL ι (𝔸[K] ⊗[K] E)) ∈ C₃
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    refine Set.mem_biUnion hδT ⟨_, hM, ?_⟩
    simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]

theorem compactSpace_unitaryQuotient_of_anisotropic' (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    CompactSpace (RightCosetSpace (unitaryDiagonal K H).range) := by
  obtain ⟨Ω, hΩ, hdec⟩ := exists_isCompact_unitary H hH haniso
  have himage : RightCosetSpace.mk (unitaryDiagonal K H).range '' Ω = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨u, rfl⟩ := RightCosetSpace.mk_surjective _ q
    obtain ⟨θ, hθ, hθu⟩ := hdec u
    exact ⟨θ⁻¹ * u, hθu, RightCosetSpace.mk_eq_mk_iff.2 ⟨⟨θ⁻¹, inv_mem hθ⟩, rfl⟩⟩
  exact ⟨by rw [← himage]; exact hΩ.image (RightCosetSpace.continuous_mk _)⟩

end Main

end Anisotropic

end

end GroundTheory.Automorphic
