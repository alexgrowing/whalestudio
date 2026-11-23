import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open UpperTheory.V.CA in
private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_top {n : ℕ} {A L : Type} [CommRing A] [Field L] [Algebra A L] (t : A)
    (ht : algebraMap A L t ≠ 0) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ Z, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A S) :
    Submodule.span L ((algebraMap A L).mapMatrix '' S) = ⊤ := by
  have h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y := by
        ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hy
  have h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z
    obtain ⟨s, hs⟩ := hS Z
    have h := h1 _ hs
    have e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z := by
      ext i j; simp
    rw [e] at h
    exact (Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h
  rw [eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A)) := by
    ext a b
    by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]
  rw [e]
  exact Submodule.smul_mem _ _ (h2 _)

theorem UpperTheory.V.Pa.Det.typeIDisc :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {R : Type} [CommRing R] (D : GDet n R F.G₀) (f : R →+* x.A), x.a = n → D.map f = GDet.ofRep (mat x.ρ) → ∀ q : Ideal R, q ≤ RingHom.ker f → DiscSt D q := by
  intro l _ F n x R _ D f ha hD q hq
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero
  have hsp := span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z =>
    x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩
  obtain ⟨y, hy, hdet⟩ := (UpperTheory.V.CA.g_gram _ _ _).1 hsp
  have hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a := fun a => by
    obtain ⟨_, ⟨g, -, rfl⟩, h⟩ := hy a
    exact ⟨g, h⟩
  choose g hg using hy'
  refine ⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩
  have h0 := congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))
  rw [map_zero, ← RingHom.comp_apply, RingHom.map_det] at h0
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]
  congr 1
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD,
    Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm
