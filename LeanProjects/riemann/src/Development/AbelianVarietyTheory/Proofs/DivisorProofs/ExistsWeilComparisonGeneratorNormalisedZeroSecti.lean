import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp
variable {S : Scheme.{0}}
theorem comp_psum_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T T' : Over S} (g : T' ⟶ T) (x : Fin n → (T ⟶ G))
    (I : Finset (Fin n)) : g ≫ psum G x I = psum G (fun k => g ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, toUnit_unique (g ≫ toUnit T) (toUnit T')]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [padd, padd, ← Category.assoc, comp_lift, ih]

theorem psum_one_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T : Over S} (I : Finset (Fin n)) :
    psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

theorem zeroPair_comp_partialSum_eq_unit (P₀ P : PolAV S) (f g : P₀.A ⟶ P.A) [IsMonHom f] [IsMonHom g] (I : Finset (Fin 2)) :
    zero2 P₀.A ≫ (psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I).left = η[P.A].left := by
  have e : lift η[P₀.A] η[P₀.A] ≫ psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I = η[P.A] := by
    rw [comp_psum_nrm]
    have : (fun k => lift η[P₀.A] η[P₀.A] ≫ (![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] : Fin 2 → _) k) =
        fun _ => (1 : 𝟙_ (Over S) ⟶ P.A) := by
      funext k
      fin_cases k <;> simp [IsMonHom.one_hom, Hom.one_def]
    rw [this, psum_one_nrm, Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  exact congrArg (fun q => q.left) e

theorem prod_zpow_nrm {α U : Type} [CommGroup U] (a : U) (e : α → ℤ) (s : Finset α) :
    ∏ i ∈ s, a ^ e i = a ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_nrm (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left]
    (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen) :
    ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J),
      Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  let π := (P₀.A ⊗ P₀.A).hom
  have z2 : zero2 P₀.A ≫ π = 𝟙 S := Over.w (lift η[P₀.A] η[P₀.A])
  have cst : ∀ k, zero2 P₀.A ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k =
      Sum.elim (fun _ => η[P₂.A].left ≫ coprod.inr) (fun _ => η[P₁.A].left ≫ coprod.inl) k := by
    rintro (I | I)
    · show zero2 P₀.A ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] I.down).left ≫ coprod.inr = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
    · show zero2 P₀.A ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] I.down).left ≫ coprod.inl = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
  have s₁ : ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) = 0 := by decide
  have s₂ : ∑ I : ULift.{0} (Finset (Fin 2)), (-((-1 : ℤ) ^ (2 - I.down.card))) = 0 := by decide
  have hF : FormEq (Sum.elim (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) (fun k => (π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k))
      (Sum.elim (cmpε) (fun k => -cmpε k)) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) cmpε := by
    intro U _ h
    have one : ∏ k, h ((π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k = 1 := by
      simp only [Category.assoc, cst]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cmpε]
      rw [prod_zpow_nrm, prod_zpow_nrm, s₁, s₂, zpow_zero, zpow_zero, _root_.mul_one]
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [DVR.prod_neg _ _ one, inv_one, _root_.mul_one]
  obtain ⟨u', hu', hv⟩ := exists_gen (join_isLB P₁.isLB P₂.isLB) hF
    (LB.mulGen _ _ _ _ _ u (LB.invGen _ _ _ (LB.pullGen _ _ _ u (π ≫ zero2 P₀.A))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ]
  have : (r ≫ zero2 P₀.A) ≫ π ≫ zero2 P₀.A = r ≫ zero2 P₀.A := by
    rw [Category.assoc, ← Category.assoc (zero2 P₀.A), z2]
    exact congrArg (r ≫ ·) (Category.id_comp _)
  rw [this, mul_inv_cancel]

end GlobalTheory.Mum.Two.WeilCmp
