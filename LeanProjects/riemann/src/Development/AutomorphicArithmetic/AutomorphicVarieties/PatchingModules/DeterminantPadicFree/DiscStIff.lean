import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GroupDetExistsSemisimpleRepresentation
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IrredIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices
open UpperTheory.V.CA

private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  obtain ⟨-, -, hm, -⟩ := UpperTheory.V.CA.d_gmap D
  have e1 := (hm f (MonoidAlgebra.single g 1)).2 1
  have hs : (MonoidAlgebra.mapRingHom G f) (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    simp [MonoidAlgebra.mapRingHom]
  rw [hs, h] at e1
  have e2 : (GDet.ofRep ρ).tr (MonoidAlgebra.single g 1) = (ρ g).trace := by
    rw [← (UpperTheory.V.CA.d_toDet (GDet.ofRep ρ) _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
      ((UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 (by simpa using hn))]
    simp [GDet.repAlg]
  unfold GDet.tr at e2
  unfold GDet.tr
  rw [← e1, e2]

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Matrix.vecMul c (Matrix.of fun a b => (x a * y b).trace) = 0 := by
      funext b
      have h0 : ((∑ a, c a • x a) * y b).trace = 0 := by rw [hc]; simp
      rw [Finset.sum_mul, Matrix.trace_sum] at h0
      simpa [Matrix.vecMul, dotProduct, Matrix.trace_smul, smul_mul_assoc] using h0
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro i
    simp [this]
  by_cases hn : n = 0
  · subst hn
    exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin (n * n)) := ⟨⟨0, Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)⟩⟩
    have htop := hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K]
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : IsEmpty (Fin (0 * 0)) := ⟨fun i => Fin.elim0 i⟩
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      refine ⟨fun _ => 1, fun _ => 1, ?_⟩
      rw [Matrix.det_isEmpty, ← hQ, map_one]
      exact one_ne_zero
  · have key : ∀ g h' : Fin (n * n) → G,
        (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det ∉ Q ↔
          (Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace).det ≠ 0 := by
      intro g h'
      have hm : f.mapMatrix (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)) =
          Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace := by
        ext i j
        simp [tr_of_map hn D f ρ h, map_mul]
      have e := hQ (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det
      rw [RingHom.map_det, hm] at e
      exact not_congr e.symm
    unfold DiscSt
    constructor
    · rintro ⟨g, h', hd⟩
      rw [key] at hd
      exact span_of_gram _ (fun a => ρ (g a)) (fun b => ρ (h' b)) (fun a => ⟨g a, rfl⟩) hd
    · intro hs
      obtain ⟨x, hx, hd⟩ := (UpperTheory.V.CA.g_gram K (Fin n) _).1 hs
      choose gg hgg using hx
      refine ⟨fun i => gg (finProdFinEquiv.symm i), fun i => gg (finProdFinEquiv.symm i), ?_⟩
      rw [key]
      have hr : (Matrix.of fun i j => (ρ (gg (finProdFinEquiv.symm i)) * ρ (gg (finProdFinEquiv.symm j))).trace) =
          Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.of fun a b => (x a * x b).trace) := by
        ext i j
        simp [hgg]
      rw [hr, Matrix.det_reindex_self]
      exact hd

private theorem irr_iff_span {n : ℕ} {G K : Type} [Group G] [Field K] [IsAlgClosed K]
    (ρ : G →* Matrix (Fin n) (Fin n) K) :
    UpperTheory.V.U3.MatIrr ⊤ ρ ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rw [← (UpperTheory.V.AlgebraTools.irred_iff_span (RingHom.id K) ρ).1]
  exact ⟨fun h N hN => h N fun g _ => hN g, fun h N hN => h N fun g => hN g (Subgroup.mem_top g)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.discStIff :
    ∀ {n : ℕ} {R G κ : Type} [CommRing R] [Group G] [Field κ] [IsAlgClosed κ] (D : GDet n R G) (f : R →+* κ), DiscSt D (RingHom.ker f) ↔ ∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ := by
  intro n R G κ _ _ _ _ D f
  have hQ : ∀ b, f b = 0 ↔ b ∈ RingHom.ker f := fun b => RingHom.mem_ker.symm
  constructor
  · intro h
    obtain ⟨ρ, -, hρ, -⟩ := UpperTheory.V.CA.groupDet_exists_semisimple_representation (D.map f)
    exact ⟨ρ, (irr_iff_span ρ).2 ((discSt_iff D f ρ hρ.symm _ hQ).1 h), hρ.symm⟩
  · rintro ⟨ρ, hirr, hρ⟩
    exact (discSt_iff D f ρ hρ _ hQ).2 ((irr_iff_span ρ).1 hirr)
