import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ArtinRees
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AddMulSelfEqOfOrthogonalIdempotents

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_dim {K : Type} [Field K] (W : Submodule K (Fin 2 → K))
    (hE : ∀ v ∈ W, (![v 0, 0] : Fin 2 → K) ∈ W) (a b : Matrix (Fin 2) (Fin 2) K)
    (ha : ∀ v ∈ W, a *ᵥ v ∈ W) (hb : ∀ v ∈ W, b *ᵥ v ∈ W) (ha' : a 1 0 ≠ 0) (hb' : b 0 1 ≠ 0) :
    W = ⊥ ∨ W = ⊤ := by
  have h0 : ∀ v ∈ W, v 0 ≠ 0 → (![1, 0] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 0)⁻¹ (hE v hv) using 1
    ext i; fin_cases i <;> simp [h]
  have h1 : ∀ v ∈ W, v 1 ≠ 0 → (![0, 1] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 1)⁻¹ (W.sub_mem hv (hE v hv)) using 1
    ext i; fin_cases i <;> simp [h, vecHead, vecTail]
  have h01 : (![1, 0] : Fin 2 → K) ∈ W → (![0, 1] : Fin 2 → K) ∈ W := fun h =>
    h1 _ (ha _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using ha')
  have h10 : (![0, 1] : Fin 2 → K) ∈ W → (![1, 0] : Fin 2 → K) ∈ W := fun h =>
    h0 _ (hb _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hb')
  rw [or_iff_not_imp_left]
  intro hW
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
  have key : (![1, 0] : Fin 2 → K) ∈ W ∧ (![0, 1] : Fin 2 → K) ∈ W := by
    by_cases h : v 0 = 0
    · have h' : v 1 ≠ 0 := fun h' => hv0 (by ext i; fin_cases i <;> simp [h, h'])
      exact ⟨h10 (h1 v hv h'), h1 v hv h'⟩
    · exact ⟨h0 v hv h, h01 (h0 v hv h)⟩
  rw [eq_top_iff]
  intro x _
  convert W.add_mem (W.smul_mem (x 0) key.1) (W.smul_mem (x 1) key.2) using 1
  ext i; fin_cases i <;> simp

theorem UpperTheory.V.Fr.typeE :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (K : Type) [Field K] (f : S.A →+* K), S.u.TE (RingHom.ker f) → MatIrr ⊤ fun g : F.G0 => ((S.u.map f).r g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ F C₀ hF S K _ f hT W hW
  obtain ⟨⟨hP, hM⟩, -, hee⟩ := hT
  obtain ⟨hco, -⟩ := co_B hF (Or.inr rfl) S
  have hid := idem hF (Or.inr rfl) S.B S.A S.u (cone_u hF (Or.inr rfl) S).2 0
  have hspan : ∀ M ∈ Submodule.span S.B (Set.range S.u.r), ∀ v ∈ W,
      ((M.map f).submatrix ![0, 2] ![0, 2]) *ᵥ v ∈ W := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g (Subgroup.mem_top g)
    | zero =>
      intro v _
      rw [Matrix.map_zero _ (map_zero f), Matrix.submatrix_zero]
      simp
    | add x y _ _ hx hy =>
      intro v hv
      convert W.add_mem (hx v hv) (hy v hv) using 1
      rw [← Matrix.add_mulVec]
      congr 1
      ext i j
      exact map_add f _ _
    | smul c x _ hx =>
      intro v hv
      convert W.smul_mem (f (algebraMap S.B S.A c)) (hx v hv) using 1
      rw [← Matrix.smul_mulVec]
      congr 1
      ext i j
      exact map_mul f (algebraMap S.B S.A c) _
  have hodd : ∀ g i j, Odd (w 3 i - w 3 j) → f (S.u.r g i j) = 0 := fun g i j h =>
    hee (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  obtain ⟨g, hg⟩ : ∃ g, f (S.u.r g 2 0) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hP (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  obtain ⟨g', hg'⟩ : ∃ g, f (S.u.r g 0 2) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hM (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  refine two_dim W (fun v hv => ?_) _ _ (hW g (Subgroup.mem_top g)) (hW g' (Subgroup.mem_top g')) hg hg'
  convert hspan _ hid v hv using 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.single]
