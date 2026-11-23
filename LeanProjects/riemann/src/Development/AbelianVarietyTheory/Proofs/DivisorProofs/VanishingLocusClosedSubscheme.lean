import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.ZeroLocus

variable {Y T : Scheme.{0}} {G Q : Y.Modules}

theorem mem_annihilator_cokernel_iff (u : G ⟶ Q) [G.IsQuasicoherent] [Q.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
    a ∈ Module.annihilator Γ(Y, U) Γ(cokernel u, U) ↔ ∃ t, u.app U t = a • e 0 := by
  have hex := QCoh.exact_cokernel_π_app u hU
  have hsur := QCoh.surjective_cokernel_π_app u hU
  have hsm (b : Γ(Y, U)) (s : Γ(Q, U)) :
      (cokernel.π u).app U (b • s) = b • (cokernel.π u).app U s :=
    Scheme.Modules.Hom.app_smul _ b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨t, ht⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (cokernel.π u).app U (e 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨t, ht⟩
    have hs := (he.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

theorem pullbackSections_smul_self (h : T ⟶ Y) {U : Y.Opens} (a : Γ(Y, U)) (s : Γ(Q, U)) :
    QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) (a • s) =
      h.app U a • QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) s := by
  rw [QCoh.pullbackSections_smul, Scheme.Hom.appLE_eq_app]

theorem eq_zero_of_pullbackSections (f : T ⟶ Y) {E : T.Modules}
    (α : (Scheme.Modules.pullback f).obj G ⟶ E)
    (H : ∀ (V : Y.Opens) (s : Γ(G, V)), α.app _ (QCoh.pullbackSections f G (le_refl (f ⁻¹ᵁ V)) s) = 0) :
    α = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have := H V s
  rw [QCoh.pullbackSections_apply] at this
  erw [Twist.resM_self] at this
  exact this

theorem exists_closed_zeroLocus : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 →
    ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y),
      (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  intro Y G Q u hG hQ
  haveI := hQ.isFiniteQC
  let I := QCoh.annihilatorSheaf (cokernel u)
  have hI (U : Y.Opens) (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
      (I.subschemeι.app U).hom a = 0 ↔ ∃ t, u.app U t = a • e 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app ⟨U, hU⟩, QCoh.annihilatorSheaf_ideal]
    exact mem_annihilator_cokernel_iff u hU he a
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T h => ⟨fun H => ?_, ?_⟩⟩
  · choose U e hU hy hle he using fun y : Y => hQ.exists_affine (V := ⊤) (x := y) trivial
    refine ProjSpace.exists_lift_of_cover I.subschemeι h U hU
      (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) fun y s hs => ?_
    obtain ⟨t, ht⟩ := (hI _ (hU y) (he y) s).1 hs
    have h1 : ((Scheme.Modules.pullback h).map u).app (h ⁻¹ᵁ U y)
        (QCoh.pullbackSections h G (le_refl _) t) = 0 := by rw [H]; rfl
    rw [QCoh.pullback_map_app_pullbackSections, ht, pullbackSections_smul_self] at h1
    have hf := ((he y).pullback h) (h ⁻¹ᵁ U y) le_rfl
    have : (fun _ : Fin 1 => h.app (U y) s) = 0 := hf.1 (by
      simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self, map_zero]
      exact h1)
    simpa using congrFun this 0
  · rintro ⟨h', rfl⟩
    refine eq_zero_of_pullbackSections _ _ fun V t => ?_
    rw [QCoh.pullback_map_app_pullbackSections]
    choose W e hW hyW hWV he using fun y : V => hQ.exists_affine y.2
    refine sec_ext_of_cover (fun y => (h' ≫ I.subschemeι) ⁻¹ᵁ W y)
      (fun y => Scheme.Hom.preimage_mono _ (hWV y))
      (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, hx⟩, hyW _⟩) fun y => ?_
    rw [map_zero]
    have e1 := QCoh.res_pullbackSections (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ V))
      (Scheme.Hom.preimage_mono _ (hWV y)) (u.app V t)
    have e2 := QCoh.pullbackSections_res (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ W y)) (hWV y)
      (u.app V t)
    refine (e1.trans e2.symm).trans ?_
    obtain ⟨c, hc⟩ := (he y (W y) le_rfl).2 (u.app (W y) (resM G (hWV y) t))
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self] at hc
    have ha : (I.subschemeι.app (W y)).hom (c 0) = 0 := (hI _ (hW y) (he y) (c 0)).2 ⟨_, hc.symm⟩
    change QCoh.pullbackSections _ Q _ (resM Q (hWV y) (u.app V t)) = 0
    rw [← app_resM, ← hc, pullbackSections_smul_self]
    have hz : (ConcreteCategory.hom ((h' ≫ I.subschemeι).app (W y))) (c 0) = 0 :=
      (congrArg (h'.app (I.subschemeι ⁻¹ᵁ W y)).hom ha).trans (map_zero _)
    rw [hz, zero_smul]

end GlobalTheory.ZeroLocus

end
