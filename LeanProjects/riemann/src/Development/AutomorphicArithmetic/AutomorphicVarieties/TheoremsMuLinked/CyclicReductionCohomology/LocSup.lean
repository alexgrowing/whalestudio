import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.BorCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumCount

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem up_mul {R : Type} [CommRing R] {n : ℕ} {P Q : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j, j < i → P i j = 0) (hQ : ∀ i j, j < i → Q i j = 0) : ∀ i j, j < i → (P * Q) i j = 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hP i c hc, zero_mul]
  · rw [hQ c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem up_conj {R : Type} [CommRing R] {n : ℕ} {w wi r s y : Matrix (Fin n) (Fin n) R}
    (h2 : w * wi = 1)
    (hr : ∀ i j, j < i → (wi * r * w) i j = 0) (hs : ∀ i j, j < i → (wi * s * w) i j = 0)
    (hy : ∀ i j, j < i → (wi * y * w) i j = 0) :
    ∀ i j, j < i → (wi * (r * y * s - y) * w) i j = 0 := by
  have e : wi * (r * y * s - y) * w = (wi * r * w) * (wi * y * w) * (wi * s * w) - wi * y * w := by
    calc wi * (r * y * s - y) * w = wi * r * (w * wi) * y * (w * wi) * s * w - wi * y * w := by
          rw [h2]; noncomm_ring
      _ = _ := by noncomm_ring
  intro i j h
  rw [e, Matrix.sub_apply, up_mul (up_mul hr hy) hs i j h, hy i j h, sub_zero]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem UpperTheory.V.Th.locSup :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)) (v : L.Vl), IsAd0 h y m rep → LC rep → Finite (Zbor y m v) → ((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v ≤ (Zl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup) ∧ Finite ↥((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ Nat.card ↥((Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) * Nat.card (ResidueField O) ^ (m * (n + n.choose 2)) ≤ Nat.card (Mm O n m) * Nat.card (Zbor y m v) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep v hrep hLC hZ
  haveI : Finite (Om O m) := ((omFacts l O).2 m).1
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  have hpφ : ∀ g, h.p₀ (G.φ v g) = G0.φ v g := fun g => Subtype.ext (h.φ v g)
  have hv : ∀ (g : L.Gv v) (Z : Mm O n m), rep (G.φ v g : G.Γ) Z =
      y.ρ0 m (G0.φ v g) * Z * y.ρ0 m (G0.φ v g)⁻¹ := fun g Z => by
    have := hrep.1 (G.φ v g) Z
    simp only [one_smul, Pt.ρm, map_inv, hpφ] at this
    exact this
  have hLCv : LC (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _) := fun Z =>
    (hLC Z).comp_continuous (continuous_subtype_val.comp (G.φ_cont v))
  have hle := block_le₂ _ hLCv
  refine ⟨sup_le hle fun β hβ => ⟨hβ.1, fun g g' => ?_⟩, ?_⟩
  · exact (hβ.2.1 g g').trans (congrArg (_ + ·) (hv g (β g')).symm)
  · rw [← borCard l L G0 O n y m v]
    refine sumCount O (L.Gv v) _ _ (bor y m v) (Zbor y m v) hZ fun Y hY => ?_
    have hmem := hle (show (fun g => (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _) g Y - Y) ∈ _ from
      (mem_Bl _).2 ⟨Y, fun _ => rfl⟩)
    have hw : red m (y.w v : Matrix (Fin n) (Fin n) O) *
        red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have t : ∀ (g : L.Gv v) i j, j < i → (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) *
        y.ρ0 m (G0.φ v g) * red m (y.w v : Matrix (Fin n) (Fin n) O) : Mm O n m) i j = 0 := fun g i j hij => by
      have := congrArg (Ideal.Quotient.mk (maximalIdeal O ^ m)) ((y.tri v g).1 i j hij)
      rw [map_zero] at this
      rw [Pt.ρ0, ← red_mul, ← red_mul]
      exact this
    refine ⟨hmem.1, fun g g' => ?_, fun g i j hij => ?_⟩
    · exact (hmem.2 g g').trans (congrArg (_ + ·) (hv g _))
    · have := up_conj hw (t g) (by have := t g⁻¹; rwa [map_inv] at this) hY i j hij
      rw [← hv g Y] at this
      exact this
