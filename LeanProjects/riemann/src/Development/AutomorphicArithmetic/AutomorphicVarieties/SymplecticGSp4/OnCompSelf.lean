import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Diag

variable {R : Type} [CommRing R]

private theorem prj_diag (c : Fin 4 → R) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun a => ∏ j ∈ Finset.univ.erase i, (c a - c j) := by
  unfold prj
  have h : Matrix.diagonal c = Matrix.diagonalAlgHom (n := Fin 4) (α := R) R c := rfl
  rw [h, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext a
  simp [map_prod, Finset.prod_apply, Pi.algebraMap_apply]

private theorem prj_zero (c : Fin 4 → R) {i a : Fin 4} (h : a ≠ i) :
    ∏ j ∈ Finset.univ.erase i, (c a - c j) = 0 :=
  Finset.prod_eq_zero (i := a) (by simp [h]) (sub_self _)

private theorem ord_diag {H : Type} [Group H] (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R)
    (hr : ∀ g, r g = Matrix.diagonal fun i => ps i g) : Ord I ps s₀ r where
  charpoly := by rw [hr, Matrix.charpoly_diagonal]
  stable g i j hij := by
    rw [hr s₀, hr g, prj_diag, prj_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [prj_zero (fun a => ps a s₀) (i := j) (a := a) (by rw [h]; exact hij.ne), zero_mul, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]
  inert s _ i := by
    rw [hr s₀, hr s, prj_diag, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [h, sub_self, mul_zero, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]

private theorem gsp_diag (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (Matrix.diagonal d) := by
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  have ha : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    rw [adj_apply]
    by_cases hij : i = j
    · subst hij
      simp [hs]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (fun e => hij (Fin.rev_injective e).symm), smul_zero]
  unfold IsGSp
  rw [ha, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [mul_comm, h]

private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsCO O O] (x : O) : res O O x = residue O x :=
  (res O O).commutes x

private theorem onComp_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsCO O O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} (P : Cond O rbar)
    (ρ : Lift O rbar O) (h : P O ρ) : OnComp P ρ.hom ρ :=
  ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ρ, h, ⟨AlgHom.id O O, fun _ _ _ => rfl⟩,
    AlgHom.id O O, Lift.ext (MonoidHom.ext fun _ => Matrix.ext fun _ _ => rfl)⟩

end Diag

theorem UpperTheory.V.GradeZeroInterpolatingElement.r0pt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∃ ρ : Lift c.O D.rbar c.O, ρ.hom = D.r0 ∧ D.IsPt ρ := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, -, hunr, -, hP, hrev, -, -, -, -, hcont, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hr : ∀ g, D.r0 g = Matrix.diagonal fun i => (D.ps i g : c.O) := fun _ => rfl
  have hoff : ∀ g i j, i ≠ j → D.r0 g i j = 0 := fun g i j h => by rw [hr, Matrix.diagonal_apply_ne _ h]
  have hmult : D.Mult D.r0 := fun g => by
    rw [hr]
    refine gsp_diag _ _ fun i => ?_
    rw [← hrev i]
    rfl
  have hone : ∀ g, (∀ i, D.ps i g = 1) → D.r0 g = 1 := fun g h => by
    rw [hr, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [h i]
    rfl
  let ρ : Lift c.O D.rbar c.O :=
    { hom := D.r0
      cont := fun a b => by
        by_cases h : a = b
        · subst h
          simpa only [hr, Matrix.diagonal_apply_eq] using hcont a
        · intro N
          simp only [hoff _ _ _ h]
          exact IsLocallyConstant.const _
      red := fun g a b => res_self _ _ }
  refine ⟨ρ, rfl, hmult, fun A hA g hg h1 => hone g fun i => hunr i A hA g hg h1, ⟨fun i j h => hoff _ _ _ ?_, ?_, ?_⟩,
    onComp_self _ (D.loc ρ l) ⟨fun g => hmult g, ord_diag _ _ _ _ fun g => hr g⟩,
    fun p hp => onComp_self _ (D.loc ρ p) ⟨fun g => hmult g, fun g hg => hone g fun i => ?_⟩⟩
  · rintro rfl
    exact h rfl
  · show D.r0 _ 0 2 + _ * D.r0 _ 0 2 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · show D.r0 _ 2 0 + _ * D.r0 _ 2 0 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · obtain ⟨h1, h2, h3⟩ := hP p hp g hg.1
    have h4 : D.ψ g = 1 := hg.2
    fin_cases i
    · exact h3.trans h4
    · exact h2.trans h4
    · exact h1
    · rfl
