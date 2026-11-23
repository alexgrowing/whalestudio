import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.KernelCut

private theorem subsingleton_kernel_sections_of_app_injective {Y : Scheme.{0}} {M N : Y.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (hφ : ∀ t, φ.app V t = 0 → t = 0) : Subsingleton Γ(kernel φ, V) := by
  have hmono : Mono ((kernel.ι φ).app V) := by
    have h1 : Mono ((Scheme.Modules.toPresheaf Y).map (kernel.ι φ)) := inferInstance
    exact (NatTrans.mono_iff_mono_app _).1 h1 (Opposite.op V)
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  have key : ∀ c : Γ(kernel φ, V), c = 0 := by
    intro c
    apply hinj
    rw [map_zero]
    apply hφ
    have h2 : (kernel.ι φ ≫ φ).app V c = 0 := by simp
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
    exact h2
  exact ⟨fun a b => by rw [key a, key b]⟩

private theorem notMem_support_of_subsingleton_sections {Y : Scheme.{0}} (K : Y.Modules) {x : Y} (W : Y.Opens)
    (hxW : x ∈ W) (h : ∀ V : Y.Opens, V ≤ W → Subsingleton Γ(K, V)) : x ∉ support K := by
  unfold support
  simp only [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton]
  have key : ∀ c : K.presheaf.stalk x, c = 0 := by
    intro c
    obtain ⟨U, hxU, t, rfl⟩ := K.presheaf.exists_germ_eq c
    rw [← K.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x ⟨hxU, hxW⟩ t]
    have := h (U ⊓ W) inf_le_right
    rw [Subsingleton.elim (K.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op t) 0, map_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem notMem_support_kernel_cutHom : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  intro Y L hL s G _ x hx
  have hx' : x ∈ ⨆ k, Y.basicOpen (s.f k) := by
    unfold Out.nonzeroLocus at hx
    exact hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  have hle : Y.basicOpen (s.f k) ≤ Out.nonzeroLocus s := by
    unfold Out.nonzeroLocus
    exact le_iSup (fun j => Y.basicOpen (s.f j)) k
  refine notMem_support_of_subsingleton_sections _ (Y.basicOpen (s.f k)) hk fun V hV => ?_
  have hVU : V ≤ L.U k := hV.trans (Y.basicOpen_le _)
  have hmb := isMulBy_cutHom G hL s
  obtain ⟨e, he⟩ := hmb k V hVU
  have hunit : IsUnit (resG Y hVU (s.f k)) := by
    have h3 := isUnit_resG_zfun (zofSec s) k hVU
      (by rw [nonzeroLocus_zofSec hL s]; exact hV.trans hle)
    simpa using h3
  refine subsingleton_kernel_sections_of_app_injective _ V fun t ht => ?_
  rw [he] at ht
  have h4 : e t = 0 := hunit.smul_eq_zero.1 ht
  exact e.injective (h4.trans e.map_zero.symm)

end GlobalTheory.KernelCut
