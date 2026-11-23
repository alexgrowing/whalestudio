import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.PSupp

noncomputable section

variable {X : Scheme.{0}}

lemma eq_zero_basicOpen_of_affine (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)) :
    m = 0 := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV f m
  refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
  rw [← hm', h0 m', map_zero]

lemma eq_zero_of_le_affine (F : X.Modules) [F.IsQuasicoherent] {V W : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (hW : W ≤ V) (m : Γ(F, W)) : m = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, V) // X.basicOpen f ≤ W} => X.basicOpen i.1) W
    (fun i => homOfLE i.2) ?_ m 0 ?_
  · intro x hx
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hW hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfW⟩, hxf⟩
  · intro i
    rw [map_zero]
    exact eq_zero_basicOpen_of_affine F hV h0 i.1 _

lemma cokernel_sections_eq_zero {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (hS : secs S V = Set.univ) (s : Γ(cokernel S.arrow, V)) : s = 0 := by
  obtain ⟨y, rfl⟩ := surjective_cokernel_π_app S.arrow hV s
  have hmem : y ∈ secs S V := by rw [hS]; trivial
  exact (mem_range_app_iff S.arrow hV y).1 hmem

lemma supportedIn_badSet {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] :
    Scheme.Modules.SupportedIn (cokernel S.arrow) (badSet S) := by
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {V : X.affineOpens // secs S (V : X.Opens) = Set.univ} => U ⊓ (i.1 : X.Opens)) U
    (fun i => homOfLE inf_le_left) ?_ s 0 ?_
  · intro x hx
    have hxb : x ∉ badSet S := fun hb => Set.disjoint_left.1 hU hx hb
    have hxc : x ∈ (badSet S)ᶜ := hxb
    rw [badSet_compl_eq] at hxc
    simp only [Set.mem_iUnion, exists_prop] at hxc
    obtain ⟨V, hV, hxV⟩ := hxc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
  · intro i
    rw [map_zero]
    exact eq_zero_of_le_affine _ i.1.2 (cokernel_sections_eq_zero S i.1.2 i.2) inf_le_right _

theorem secs_eq_univ_of_disjoint_badSet {X : Scheme.{0}} {P : X.Modules} (hP : P.IsQuasicoherent)
    (S : Subobject P) (hS : (S : X.Modules).IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) (badSet S)) : secs S U = Set.univ := by
  haveI : P.IsQuasicoherent := hP
  haveI : (S : X.Modules).IsQuasicoherent := hS
  exact GlobalTheory.CompanionTheory.GE.Comb.secs_eq_univ_of_supportedIn hP hS (supportedIn_badSet S) hU hd

end

end GlobalTheory.CompanionTheory.GE.PSupp
