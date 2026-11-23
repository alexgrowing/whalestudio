import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

section
variable (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k]

private theorem spDim_JR : (form O).JR k = J4 k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Alg.FormData.JR, form, J4]

private theorem spDim_mem (j : ℤ × ℤ) (Y : M4 k) : Y ∈ (form O).gw k j ↔
    (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) ∧
      ∀ a b, wt a b ≠ j → Y a b = 0 := by
  have e : Y ∈ (form O).gw k j ↔ (Y.transpose * (form O).JR k + (form O).JR k * Y = 0 ∧
      ∀ a b, (form O).blk a ≠ (form O).blk b → Y a b = 0) ∧ ∀ a b, wt a b ≠ j → Y a b = 0 := Iff.rfl
  rw [e, spDim_JR]
  refine and_congr_left fun _ => ⟨fun ⟨h, _⟩ => ?_, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨?_, fun a b h => absurd rfl h⟩⟩
  · have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 0) 2
    have h3 := congrFun (congrFun h 0) 3
    have h4 := congrFun (congrFun h 1) 2
    have h5 := congrFun (congrFun h 1) 3
    have h6 := congrFun (congrFun h 2) 3
    simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5
    · linear_combination -h6
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, h1, h2, h3, h4, h5, h6]

private theorem spDim_one (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hB : B ∈ (form O).gw k j) (hab : B a b = 1)
    (h : ∀ Y ∈ (form O).gw k j, Y a b = 0 → Y = 0) : finrank k ((form O).gw k j) = 1 := by
  refine finrank_eq_one (⟨B, hB⟩ : (form O).gw k j) ?_ ?_
  · intro e
    have : B = 0 := congrArg Subtype.val e
    rw [this] at hab
    simp at hab
  · intro Y
    refine ⟨Y.1 a b, Subtype.ext ?_⟩
    have := h (Y.1 a b • B - Y.1) (Submodule.sub_mem _ (Submodule.smul_mem _ _ hB) Y.2) (by simp [hab])
    exact sub_eq_zero.mp this

private theorem spDim_root (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hj : wt a b = j)
    (hB : B ∈ (form O).gw k (wt a b)) (hab : B a b = 1)
    (h : ∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
      Y a b = 0 → Y b.rev a.rev = 0)
    (h' : ∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) :
    finrank k ((form O).gw k j) = 1 := by
  subst hj
  refine spDim_one O k _ B a b hB hab fun Y hY h0 => ?_
  obtain ⟨y1, y2⟩ := (spDim_mem O k _ Y).1 hY
  ext c d
  by_cases e : wt c d = wt a b
  · rcases h' c d e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h0
    · exact h Y y1 h0
  · exact y2 c d e

private theorem spDim_zero : finrank k ((form O).gw k 0) = 2 := by
  let f : (form O).gw k 0 →ₗ[k] k × k :=
    { toFun := fun Y => (Y.1 0 0, Y.1 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro Y hY
      have h0 : Y.1 0 0 = 0 := congrArg Prod.fst hY
      have h1 : Y.1 1 1 = 0 := congrArg Prod.snd hY
      obtain ⟨⟨-, -, y3, y4, -, -⟩, y2⟩ := (spDim_mem O k _ Y.1).1 Y.2
      ext c d
      by_cases e : c = d
      · subst e
        fin_cases c <;> simp [h0, h1, y3, y4]
      · exact y2 c d fun n => e ((wt_eq_zero c d).1 n)
    · rintro ⟨x, y⟩
      refine ⟨⟨Matrix.diagonal ![x, y, -y, -x], (spDim_mem O k _ _).2 ⟨by simp, fun a b h => ?_⟩⟩, ?_⟩
      · exact Matrix.diagonal_apply_ne _ fun n => h ((wt_eq_zero a b).2 n)
      · rfl
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

private theorem spDim_B (a b : Fin 4) (B : M4 k)
    (h : B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2)
    (h' : ∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) : B ∈ (form O).gw k (wt a b) := by
  refine (spDim_mem O k _ _).2 ⟨h, fun c d e => h' c d ?_ ?_⟩
  · rintro ⟨rfl, rfl⟩; exact e rfl
  · rintro ⟨rfl, rfl⟩; exact e (wt_rev _ _)

end

theorem UpperTheory.V.X.spDim :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k] (j : ℤ × ℤ), finrank k ((form O).gw k j) = dimP j := by
  intro O _ k _ _ j
  unfold dimP
  split_ifs with h0 hw
  · subst h0; exact spDim_zero O k
  · have key : ∀ (a b : Fin 4) (B : M4 k), wt a b = j → B a b = 1 →
        (B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2) →
        (∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) →
        (∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
          Y a b = 0 → Y b.rev a.rev = 0) →
        (∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) → finrank k ((form O).gw k j) = 1 :=
      fun a b B e h1 h2 h3 h4 h5 => spDim_root O k j B a b e (spDim_B O k a b B h2 h3) h1 h4 h5
    simp only [wts, oddRoots, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · refine key 0 1 !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 3 = 0
        simp [*]
    · refine key 1 0 !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 2 = 0
        simp [*]
    · refine key 1 2 !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 2 = 0
        simp [*]
    · refine key 2 1 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 1 = 0
        simp [*]
    · refine key 0 3 !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 0 3 = 0
        simp [*]
    · refine key 3 0 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 0 = 0
        simp [*]
    · refine key 0 2 !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 3 = 0
        simp [*]
    · refine key 2 0 !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 1 = 0
        simp [*]
    · exact absurd rfl h0
  · rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro Y hY
    obtain ⟨-, y2⟩ := (spDim_mem O k _ Y).1 hY
    ext c d
    exact y2 c d fun n => hw (n ▸ wt_mem c d)
