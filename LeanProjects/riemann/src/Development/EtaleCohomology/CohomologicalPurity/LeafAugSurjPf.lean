import Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem altSum (m : ℕ) : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if Even m then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) (m + 2)]
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd m with h | h
    · have h' : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using h
      have hn : ¬ Even m := Nat.not_even_iff_odd.2 h
      simp [hn, h', pow_succ, h.neg_one_pow]

theorem dL {R : Type} [CommRing R] (Y : PSh) (m : ℕ) (T : Scheme.{0}ᵒᵖ) (z : ((((chainsP R).obj (disc.obj Y)).X (m + 1)).obj T)) :
    ((((chainsP R).obj (disc.obj Y)).d (m + 1) m).app T).hom z = (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ)) • z := by
  have e : ∀ i : Fin (m + 2), SimplicialObject.δ (disc.obj Y) i = 𝟙 _ := fun _ => rfl
  simp [chainsP, e]
  erw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [NatTrans.app_zsmul]
  rfl

section
variable {R : Type} [CommRing R]

theorem bdyL (Y : PSh) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (disc.obj Y)).X (n + 1)).obj T))
    (hx : Cyc ((chainsP R).obj (disc.obj Y)) (n + 1) T x) : Bdy ((chainsP R).obj (disc.obj Y)) (n + 1) T x := by
  by_cases h : Even (n + 1)
  · have h0 := hx n
    rw [dL, altSum, if_neg (by simpa [Nat.even_add_one] using h)] at h0
    simp only [one_smul] at h0
    exact ⟨0, by rw [map_zero]; exact h0.symm⟩
  · refine ⟨x, ?_⟩
    have e := dL (R := R) Y (n + 1) T x
    rw [altSum, if_neg h] at e
    exact e.trans (one_smul ℤ _)

def imSv {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) : Sieve T where
  arrows U f := ∃ x', ((φ.f n).app (op U)).hom x' = ((L.X n).map f.op).hom y
  downward_closed := by
    rintro U V f ⟨x', hx⟩ g
    refine ⟨((K.X n).map g.op).hom x', ?_⟩
    have h1 := congrArg (fun h => h.hom x') ((φ.f n).naturality g.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, hx, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem imSv_add {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y z : (L.X n).obj (op T)) :
    imSv φ n y ⊓ imSv φ n z ≤ imSv φ n (y + z) := by
  rintro U f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

theorem imSv_smul {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) (r : ULift.{1} R) :
    imSv φ n y ≤ imSv φ n (r • y) := by
  rintro U f ⟨a, ha⟩
  exact ⟨r • a, by rw [map_smul, map_smul, ha]⟩

theorem imSv_zero {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} :
    imSv φ n (0 : (L.X n).obj (op T)) = ⊤ := by
  ext U f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

end

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]

theorem gen_mem (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)]
    {T : Scheme.{0}} (g : T ⟶ X) :
    imSv ((chainsP R).map (aug _ hc)) 0
      (ModuleCat.freeMk (ULift.up g) : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) ∈
      Scheme.etaleTopology T := by
  let j : T → J := fun t => (hcov (g t)).choose
  let V : T → T.Opens := fun t => g ⁻¹ᵁ (c (j t)).opensRange
  have hV : ∀ t, t ∈ V t := fun t => (hcov (g t)).choose_spec
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers T (fun t => (V t).toScheme)
    (fun t => (V t).ι) (fun t => ⟨t, ⟨t, hV t⟩, by simp⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨t⟩
  have hr : Set.range ((V t).ι ≫ g) ⊆ Set.range (c (j t)) := by
    rintro _ ⟨y, rfl⟩
    have := (V t).range_ι ▸ Set.mem_range_self (f := (V t).ι) y
    simpa [V] using this
  let a := IsOpenImmersion.lift (c (j t)) ((V t).ι ≫ g) hr
  let σ : Fin (0 + 1) ⥤ J := (Functor.const _).obj (j t)
  refine ⟨ModuleCat.freeMk (ULift.up ((inj (D ⋙ yoneda) (op (SimplexCategory.mk 0)) σ).app (op (V t).toScheme) a)), ?_⟩
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  refine congrArg ModuleCat.freeMk (ULift.ext _ _ ?_)
  show (a ≫ D.map (𝟙 (j t))) ≫ c (j t) = (V t).ι ≫ g
  rw [D.map_id, Category.comp_id]
  exact IsOpenImmersion.lift_fac _ _ _
end

theorem all_mem {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]
    (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)] {T : Scheme.{0}}
    (x : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) :
    imSv ((chainsP R).map (aug _ hc)) 0 x ∈ Scheme.etaleTopology T := by
  let M := (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)
  let b : Module.Basis (ULift.{1} (T ⟶ X)) (ULift.{1} R) M := Finsupp.basisSingleOne
  have hx : x ∈ Submodule.span (ULift.{1} R) (Set.range b) := b.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g⟩, rfl⟩ := hy
    exact gen_mem D X c hc R hcov g
  | zero => rw [imSv_zero]; exact GrothendieckTopology.top_mem _ _
  | add y z _ _ hy hz =>
    exact GrothendieckTopology.superset_covering _ (imSv_add _ _ y z)
      (GrothendieckTopology.intersection_covering _ hy hz)
  | smul r y _ hy => exact GrothendieckTopology.superset_covering _ (imSv_smul _ _ y r) hy

theorem LeafAugSurj_of : LeafAugSurj := by
  intro J _ D X c ho hcov hc R _ n T x hx
  rcases n with _ | n
  · refine ⟨imSv ((chainsP R).map (aug _ hc)) 0 x, ?_, ?_⟩
    · have := ho
      exact all_mem D X c hc R hcov x
    · rintro U f ⟨x', hx'⟩
      refine ⟨x', fun m => ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ 0 m (by simp)]
        rfl
      · rw [map_zero, hx', sub_self]
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun U f _ => ⟨0, fun m => by simp, ?_⟩⟩
    obtain ⟨y, hy⟩ := bdyL _ n T x hx
    refine ⟨-((((chainsP R).obj (disc.obj (yoneda.obj X))).X (n + 1 + 1)).map f.op).hom y, ?_⟩
    have h := congrArg (fun h => h.hom y) ((((chainsP R).obj (disc.obj (yoneda.obj X))).d (n + 1 + 1) (n + 1)).naturality f.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [map_neg, map_zero, zero_sub, h, hy]

end LateralTheory.CohomologicalPurity.TubeCut
