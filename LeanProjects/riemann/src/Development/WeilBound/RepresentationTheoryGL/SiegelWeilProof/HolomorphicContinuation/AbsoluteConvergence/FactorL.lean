import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol

noncomputable section

open MeasureTheory Set Filter Topology Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem factorL : FactorL := by
  intro G _ S l C hC hcont hlin hbd
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hl0 : l 0 = 0 := by
    have h := hbd 0 S.zero_mem 0 (by simp)
    simpa using h
  let lS : S →ₗ[ℂ] ℂ :=
    { toFun := fun F => l F.1
      map_add' := fun F₁ F₂ => by
        have h := hlin 1 F₁.1 F₁.2 F₂.1 F₂.2
        simpa using h
      map_smul' := fun a F => by
        have h := hlin a F.1 F.2 0 S.zero_mem
        simpa [hl0] using h }
  let R : S →ₗ[ℂ] C(C, ℂ) :=
    { toFun := fun F => ⟨fun x => F.1 x, (hcont F.1 F.2).comp continuous_subtype_val⟩
      map_add' := fun F₁ F₂ => by
        ext x
        simp
      map_smul' := fun a F => by
        ext x
        simp }
  have hRnorm : ∀ F : S, ‖l F.1‖ ≤ ‖R F‖ := by
    intro F
    apply hbd F.1 F.2
    intro x hx
    exact (R F).norm_coe_le_norm ⟨x, hx⟩
  have hker : LinearMap.ker R ≤ LinearMap.ker lS := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := hRnorm F
    rw [hF, norm_zero] at h
    exact norm_le_zero_iff.mp h
  let f : LinearMap.range R →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ lS hker).comp
      (R.quotKerEquivRange.symm : LinearMap.range R →ₗ[ℂ] S ⧸ LinearMap.ker R)
  have hf : ∀ F : S, f ⟨R F, LinearMap.mem_range_self R F⟩ = l F.1 := by
    intro F
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hfb : ∀ v : LinearMap.range R, ‖f v‖ ≤ 1 * ‖v‖ := by
    rintro ⟨v, F, rfl⟩
    rw [hf F, one_mul]
    exact hRnorm F
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range R) (f.mkContinuous 1 hfb)
  refine ⟨g, fun F hFS hF => ?_⟩
  have h1 := hg ⟨R ⟨F, hFS⟩, LinearMap.mem_range_self R _⟩
  rw [LinearMap.mkContinuous_apply, hf] at h1
  exact h1.symm

theorem kRCpt : KRCpt := by
  intro n
  let S : Set (M2 n) := {g | InG g ∧ gᴴ * g = 1}
  have hcl : IsClosed S := by
    show IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | gᴴ * g = 1})
    apply IsClosed.inter
    · exact isClosed_eq
        ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hsub : S ⊆ univ.pi (fun _ => univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro g hg i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hg.2
    exact entry_norm_bound_of_unitary hu i j
  have hcpt : IsCompact S :=
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset
      hcl hsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hcpt
  have hinv : ∀ g : S, g.1 * g.1ᴴ = 1 := fun g => mul_eq_one_comm.mp g.2.2
  let u : S → GL (Fin n ⊕ Fin n) ℂ := fun g => ⟨g.1, g.1ᴴ, hinv g, g.2.2⟩
  have hu : Continuous u :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  let ψ : S → KR n := fun g => ⟨⟨u g, g.2.1⟩, g.2⟩
  have hψ : Continuous ψ := (hu.subtype_mk _).subtype_mk _
  have hsurj : Function.Surjective ψ := by
    intro k
    refine ⟨⟨mR k.1, k.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  exact Function.Surjective.compactSpace hψ hsurj

end PositivityTheory.Rg.Sw.AbsSt
