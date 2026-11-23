import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

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

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hrank : Module.finrank K (Matrix (Fin n) (Fin n) K) = Fintype.card (Fin (n * n)) := by
    simp [Module.finrank_matrix]
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : g = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero hdet
      funext c
      have hvec : Matrix.vecMul g (Matrix.of fun a b => (x a * y b).trace) c
          = ((∑ a, g a • x a) * y c).trace := by
        simp [Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.trace_sum]
      rw [hvec, hg]
      simp
    intro i
    simp [this]
  have := hli.span_eq_top_of_card_eq_finrank' hrank.symm
  rw [eq_top_iff, ← this]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  have key : ∀ g g' : Fin (n * n) → G,
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (g a * g' b) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g' b)).trace) := by
    intro g g'
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
      tr_of_map hn D f ρ h, map_mul]
  constructor
  · rintro ⟨g, g', hg⟩
    refine span_of_gram _ (fun a => ρ (g a)) (fun a => ρ (g' a)) (fun a => ⟨_, rfl⟩) fun h0 => hg ?_
    rw [← hQ, key]
    exact h0
  · intro hs
    obtain ⟨x, hx, hdet⟩ := (g_gram _ _ _).1 hs
    choose g hg using hx
    refine ⟨fun a => g (finProdFinEquiv.symm a), fun a => g (finProdFinEquiv.symm a), fun hm => hdet ?_⟩
    rw [← hQ, key] at hm
    rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← hm]
    congr 1
    ext a b
    simp only [hg, Matrix.submatrix_apply, Matrix.of_apply]

private theorem top_of_single {n : ℕ} {K : Type} [Field K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (h : ∀ i j, ∃ c : K, c ≠ 0 ∧ Matrix.single i j c ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  obtain ⟨c, hc, hm⟩ := h i j
  have := S.smul_mem (M i j * c⁻¹) hm
  rwa [Matrix.smul_single, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one] at this

private theorem single_mem_blk {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}
    (V₁ V₂ : Submodule A R) (i j : Fin n) (c : R)
    (h1 : (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₁) (h2 : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₂) :
    Matrix.single i j c ∈ blkMat n a V₁ V₂ := by
  intro i' j'
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    rw [Matrix.single_apply_same]
    exact ⟨h1, h2⟩
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij]
    exact ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩

theorem UpperTheory.V.Pa.urep_stable :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] {rF : Bh →+* FractionRing x.A} {e : G.G₀ →* Bˣ} (V : URep h x D I Bh rF e), ∀ Q : Ideal Bh, Q.IsPrime → (DiscSt (D.map (algebraMap B Bh)) Q ↔ x.a = n ∨ ∃ y ∈ V.N, ∃ z ∈ V.N, ∃ b : Bh, b ∉ Q ∧ y * z = algebraMap Bh V.AA b) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ rF e V Q hQp
  haveI := V.fin
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := V.AA) Q ⊥ (by
    intro b hb
    have : b = 0 := V.inj (by simpa using hb)
    rw [this]; exact Q.zero_mem)
  let f : V.AA →+* Q'.ResidueField := algebraMap _ _
  have hf : ∀ b, (f.comp (algebraMap Bh V.AA)) b = 0 ↔ b ∈ Q := fun b => by
    rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero, ← hc, Ideal.mem_comap]
  let ρ : G.G₀ →* Matrix (Fin n) (Fin n) Q'.ResidueField := f.mapMatrix.toMonoidHom.comp V.vr
  have hρ : (D.map (algebraMap B Bh)).map (f.comp (algebraMap Bh V.AA)) = GDet.ofRep ρ := by
    rw [(d_gmap D).2.1, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← (d_gmap D).2.1, V.det]
    exact (d_gmap (GDet.ofRep V.vr)).2.2.2 f V.vr
  rw [discSt_iff hn _ _ ρ hρ Q hf]
  have hmem : ∀ Y ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N,
      Y.map f ∈ Submodule.span Q'.ResidueField (Set.range ρ) := by
    intro Y hY
    rw [← V.span] at hY
    induction hY using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => rw [Matrix.map_zero _ (map_zero f)]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Matrix.map_add _ (map_add f)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (c • a).map f = f (algebraMap Bh V.AA c) • a.map f := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, map_mul, smul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ ha
  have hone : (1 : V.AA) ∈ (1 : Submodule Bh V.AA) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hsing : ∀ (i j : Fin n) (c : V.AA), (Matrix.single i j c).map f = Matrix.single i j (f c) :=
    fun i j c => Matrix.map_single i j c f
  constructor
  · intro hs
    by_cases ha : x.a = n
    · exact Or.inl ha
    right
    have hlt : x.a < n := lt_of_le_of_ne x.a_le ha
    have hex : ∃ y ∈ V.N, f y ≠ 0 := by
      by_contra hne
      push Not at hne
      let i : Fin n := ⟨0, hn⟩
      let j : Fin n := ⟨x.a, hlt⟩
      have hall : ∀ M ∈ Submodule.span Q'.ResidueField (Set.range ρ), M i j = 0 := by
        intro M hM
        induction hM using Submodule.span_induction with
        | mem _ hy =>
          obtain ⟨g, rfl⟩ := hy
          have hg : V.vr g ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N := by
            rw [← V.span]; exact Submodule.subset_span ⟨g, rfl⟩
          refine hne _ ((hg i j).2 fun hh => ?_)
          exact lt_irrefl _ (hh.1 x.a_pos)
        | zero => rfl
        | add a b _ _ ha hb => rw [Matrix.add_apply, ha, hb, add_zero]
        | smul c a _ ha => rw [Matrix.smul_apply, ha, smul_zero]
      have := hall (Matrix.single i j 1) (hs ▸ Submodule.mem_top)
      rw [Matrix.single_apply_same] at this
      exact one_ne_zero this
    obtain ⟨y, hy, hfy⟩ := hex
    obtain ⟨c, -, hc'⟩ := V.mul_mem y hy y hy
    refine ⟨y, hy, y, hy, c, fun hcQ => ?_, hc'⟩
    have := (hf c).2 hcQ
    rw [RingHom.comp_apply, ← hc', map_mul] at this
    exact hfy (mul_self_eq_zero.1 this)
  · intro hR
    refine top_of_single _ fun i j => ?_
    by_cases hij : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
    · refine ⟨f 1, by simp, ?_⟩
      rw [← hsing]
      exact hmem _ (single_mem_blk _ _ i j 1 (fun _ => hone) fun h' => (h' hij).elim)
    · rcases hR with ha | ⟨y, hy, z, -, b, hb, hyz⟩
      · exact (hij (by rw [ha]; exact ⟨fun _ => j.2, fun _ => i.2⟩)).elim
      · refine ⟨f y, fun h0 => hb ((hf b).1 ?_), ?_⟩
        · rw [RingHom.comp_apply, ← hyz, map_mul, h0, zero_mul]
        · rw [← hsing]
          exact hmem _ (single_mem_blk _ _ i j y (fun h' => (hij h').elim) fun _ => hy)
