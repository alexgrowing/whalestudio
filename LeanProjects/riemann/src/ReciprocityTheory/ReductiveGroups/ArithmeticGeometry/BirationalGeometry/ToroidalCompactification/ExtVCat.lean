import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem eta_eq_one (M : Over S) [MonObj M] : (η[M] : 𝟙_ (Over S) ⟶ M) = 1 := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem comp_psum {n : ℕ} {T T' : Over S} (g : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    g ≫ psum G x I = psum G (fun k => g ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, toUnit_unique (g ≫ toUnit T) (toUnit T')]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [padd, padd, ← Category.assoc, comp_lift, ih]

theorem psum_one {n : ℕ} {T : Over S} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

theorem one_comp_proj_three (k : Fin 3) : (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ x3 G k = 1 := by
  fin_cases k
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ fst _ _ = 1
    exact MonObj.one_comp _
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ (snd _ _ ≫ fst _ _) = 1
    rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ (snd _ _ ≫ snd _ _) = 1
    rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]

theorem eSec_thφ (I : thK) : eSec (G3 G) ≫ thφ G (x3 G) I = eSec G := by
  show (η[G3 G]).left ≫ (psum G (x3 G) I.down).left = (η[G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one, comp_psum]
  simp only [one_comp_proj_three]
  rw [psum_one]

theorem one_comp_proj_two (k : Fin 2) : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ x2 G k = 1 := by
  fin_cases k
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ fst _ _ = 1
    exact MonObj.one_comp _
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ snd _ _ = 1
    exact MonObj.one_comp _

theorem lift_one_one : lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) 1) = (1 : 𝟙_ (Over S) ⟶ G3 G) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, MonObj.one_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_snd, lift_fst, Category.assoc, MonObj.one_comp]
    · rw [lift_snd, lift_snd, Category.assoc, MonObj.one_comp]

theorem eSec_face (i : Fin 3) : eSec (G2 G) ≫ (faceMap G i).left = eSec (G3 G) := by
  show (η[G2 G]).left ≫ (faceMap G i).left = (η[G3 G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one]
  congr 1
  have hp : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ pzero G (G2 G) = 1 := by
    rw [pzero, ← Category.assoc, toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G2 G) ≫ toUnit _) (toUnit _)]; rfl
  fin_cases i
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (pzero G _) (lift (x2 G 0) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (pzero G _) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (x2 G 1) (pzero G _)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]

theorem cub_at_one {L : RigLB G} (c : CubicalStr G L) (z : (𝟙_ (Over S)).left) (q₀ : L.L.ι)
    (hq₀ : eSec G z ∈ L.L.U q₀) :
    gm (eSec (G3 G)) z (LB.wchart L.L (thφ G (x3 G)) (fun _ => q₀)) (c.t.s (fun _ => q₀)) = 1 := by
  classical
  let J : ((𝟙_ (Over S)).left ⟶ G.left) → L.L.ι := fun χ =>
    if χ = eSec G then q₀ else (exists_chart L.isLB (χ z)).choose
  have hJ : Good L.L z J := fun χ => by
    by_cases h : χ = eSec G
    · subst h; simp only [J, if_pos rfl]; exact hq₀
    · simp only [J, if_neg h]; exact (exists_chart L.isLB (χ z)).choose_spec
  have hv := val_corr hJ (c.face 0) (eSec (G2 G))
  have hv2 : val (φ := thφ G (x3 G)) (ε := thε) c.t (eSec (G2 G) ≫ (faceMap G 0).left) z J = 1 :=
    (val_pull hJ (φ := thφ G (x3 G)) (ε := thε) c.t (faceMap G 0).left (eSec (G2 G))).symm.trans
      (hv.trans (val_one _))
  have hm : ∀ I, J ((eSec (G2 G) ≫ (faceMap G 0).left) ≫ thφ G (x3 G) I) = q₀ := fun I => by
    rw [eSec_face, eSec_thφ]; simp [J]
  rw [val_of (φ := thφ G (x3 G)) (ε := thε) c.t _ z J (fun _ => q₀) hm, eSec_face] at hv2
  exact hv2

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
