import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
open Matrix
open scoped Classical

namespace GlobalTheory.CentProd

open GlobalTheory.LKRes

noncomputable def incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) : GL (Fin n) S →* GL (Fin n) R :=
  (glPiEquiv d n e).symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i)

theorem glPiEquiv_incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) (g : GL (Fin n) S) : glPiEquiv d n e (incl d n e i g) = Pi.mulSingle i g := by
  simp [incl]

theorem mem_centralizer_iff_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N z : GL (Fin n) R) :
    z ∈ Subgroup.centralizer {N} ↔ ∀ i, glPiEquiv d n e z i ∈ Subgroup.centralizer {glPiEquiv d n e N i} := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i
    have := congrArg (fun x => glPiEquiv d n e x i) h
    simpa [map_mul] using this
  · intro h
    apply (glPiEquiv d n e).injective
    funext i
    simpa [map_mul] using h i

theorem charpoly_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N : GL (Fin n) R) (i : Fin (d + 1)) :
    (glPiEquiv d n e N i).val.charpoly = N.val.charpoly.map ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)) := by
  have h : (glPiEquiv d n e N i).val = ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)).mapMatrix N.val := by
    ext a b
    rfl
  rw [h, RingHom.mapMatrix_apply, Matrix.charpoly_map]

theorem centralizer_fg_of_pi : ∀ (R S : Type) [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S), (∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) →
    (∀ N : GL (Fin n) S, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) S),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) S)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) →
    ∀ N : GL (Fin n) R, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) R),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) := by
  intro R S _ _ d n e A B hAB hS N hN
  set ψ := glPiEquiv d n e with hψ
  have hNi : ∀ i, (ψ N i).val.charpoly.Separable := fun i => by
    rw [hψ, charpoly_comp]; exact hN.map
  choose Gs hGs1 hGs2 using fun i => hS (ψ N i) (hNi i)

  have hinclC : ∀ i g, g ∈ Subgroup.centralizer {ψ N i} → incl d n e i g ∈ Subgroup.centralizer {N} := by
    intro i g hg
    rw [mem_centralizer_iff_comp d n e]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  have hinclA : ∀ i g, g ∈ (GeneralLinearGroup.map (n := Fin n) B.subtype).range →
      incl d n e i g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range := by
    intro i g hg
    rw [glPiEquiv_mem_iff d n e A B hAB]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  refine ⟨Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)), ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg
    obtain ⟨i, g', hg', rfl⟩ := hg
    exact hinclC i g' (hGs1 i g' hg')
  · intro z hz
    set K := Subgroup.closure (((Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)) : Finset _) :
      Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) with hK
    have hpi : ψ z ∈ Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) := by
      intro i _
      exact hGs2 i ((mem_centralizer_iff_comp d n e N z).1 hz i)
    have hle : Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) ≤ K.map ψ.toMonoidHom := by
      rw [Subgroup.pi_le_iff]
      intro i
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
      have : (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i) g = ψ (incl d n e i g) := by
        rw [hψ, glPiEquiv_incl]; rfl
      rw [this, MulEquiv.symm_apply_apply]
      apply Subgroup.subset_closure
      rcases hg with hg | hg
      · left
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
          Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨i, g, hg, rfl⟩
      · right
        exact ⟨hinclC i g hg.1, hinclA i g hg.2⟩
    have := hle hpi
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this

end GlobalTheory.CentProd
