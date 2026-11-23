import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.HomogCochains

open GroundTheory.ProfCoh groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Rep.{0} k G} [IsDiscreteRep M] {C : CosimplicialObject AddCommGrpCat.{1}}
  {e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)}

theorem neg_one_pow_smul_eq (m : ℕ) (x : M) : ((-1 : k) ^ m) • x = ((-1 : ℤ) ^ m) • x := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp

section
variable (he : ∀ m, Function.Injective (e m))
  (hr : ∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔
    IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ))
  (hd : ∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G),
    e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove))

include hr in
theorem isLocallyConstant_e (m : ℕ) (c : C.obj ⦋m⦌) : IsLocallyConstant (e m c) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).1

include hr in
theorem e_mul (m : ℕ) (c : C.obj ⦋m⦌) (τ : G) (σ : Fin (m + 1) → G) :
    e m c (fun i => τ * σ i) = M.ρ τ (e m c σ) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).2 τ σ

def toInh (m : ℕ) : C.obj ⦋m⦌ →+ locallyConstantCochains M m where
  toFun c := ⟨fun g => e m c (Fin.partialProd g),
    (isLocallyConstant_e hr m c).comp_continuous (continuous_partialProd m)⟩
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp

theorem toInh_apply (m : ℕ) (c : C.obj ⦋m⦌) (g : Fin m → G) :
    ((toInh hr m c : locallyConstantCochains M m) : (Fin m → G) → M) g = e m c (Fin.partialProd g) :=
  rfl

include he in
theorem toInh_bijective (m : ℕ) : Function.Bijective (toInh hr m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    apply he m
    rw [map_zero]
    funext σ
    have h0 : ∀ g, e m c (Fin.partialProd g) = 0 := fun g => by
      have := congrArg (fun f : locallyConstantCochains M m => (f : (Fin m → G) → M) g) hc
      simpa [toInh_apply] using this
    have hσ : σ = fun i => σ 0 * Fin.partialProd (fun j => (σ (Fin.castSucc j))⁻¹ * σ j.succ) i := by
      have := Fin.partialProd_left_inv σ
      funext i
      conv_lhs => rw [← this]
      rfl
    rw [hσ, e_mul hr, h0, map_zero]
    rfl
  · intro φ
    let F : (Fin (m + 1) → G) → M := fun x => M.ρ (x 0) (φ.1 fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
    have hF : IsLocallyConstant F :=
      isLocallyConstant_ρ_apply M (continuous_apply 0)
        (φ.2.comp_continuous (continuous_pi fun _ =>
          ((continuous_apply _).inv).mul (continuous_apply _)))
    have hFm : ∀ (τ : G) (σ : Fin (m + 1) → G), F (fun i => τ * σ i) = M.ρ τ (F σ) := by
      intro τ σ
      simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
      rfl
    obtain ⟨c, hc⟩ := (hr m F).2 ⟨hF, hFm⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext g
    rw [toInh_apply, hc]
    simp only [F, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
    rfl

theorem sum_hom_apply {X Y : AddCommGrpCat.{1}} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

theorem zsmul_hom_apply {X Y : AddCommGrpCat.{1}} (n : ℤ) (f : X ⟶ Y) (x : X) :
    (n • f) x = n • f x := by
  change (n • f).hom x = _
  rw [AddCommGrpCat.hom_zsmul]
  rfl

include hd hr in
theorem toInh_d (n : ℕ) (c : C.obj ⦋n⦌) :
    toInh hr (n + 1) ((AlgebraicTopology.AlternatingCofaceMapComplex.objD C n) c) =
      (dLocallyConstant M n).hom (toInh hr n c) := by
  apply Subtype.ext
  funext g
  rw [toInh_apply, dLocallyConstant_hom_apply, inhomogeneousCochains.d_hom_apply]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_hom_apply, zsmul_hom_apply,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, hd]
  rw [Fin.sum_univ_succ]
  congr 1
  · have : (Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      simp only [Function.comp_apply, Fin.succAbove_zero]
      exact Fin.partialProd_succ' g j
    rw [this, e_mul hr, Fin.val_zero, pow_zero, one_smul, toInh_apply]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInh_apply, Fin.partialProd_contractNth, Fin.val_succ, neg_one_pow_smul_eq]

abbrev upF (k : Type) [CommRing k] : ModuleCat.{0} k ⥤ AddCommGrpCat.{1} :=
  forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0} ⋙ AddCommGrpCat.uliftFunctor.{1, 0}

theorem alt_d (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD C n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]

include he hr hd in

noncomputable def complexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C ≅
      ((upF k).mapHomologicalComplex _).obj (cochainsComplex M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (((AddEquiv.ofBijective (toInh hr n) (toInh_bijective he hr n)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso :
        (C.obj ⦋n⦌ : AddCommGrpCat.{1}) ≅ (upF k).obj (ModuleCat.of k (locallyConstantCochains M n))))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [alt_d, Functor.mapHomologicalComplex_obj_d, cochainsComplex_d]
      ext c
      apply ULift.ext
      exact (toInh_d hr hd i c).symm)

end

end GlobalTheory.HomogCochains

open GlobalTheory.HomogCochains in
theorem GlobalTheory.homogeneousCochains_homology_addEquiv : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  intro k _ G _ _ _ M _ C e he hr hd n
  let i1 := (HomologicalComplex.homologyFunctor AddCommGrpCat.{1} _ n).mapIso (complexIso he hr hd)
  let i2 : (((upF k).mapHomologicalComplex _).obj (GroundTheory.ProfCoh.cochainsComplex M)).homology n ≅
      (upF k).obj ((GroundTheory.ProfCoh.cochainsComplex M).homology n) :=
    ((GroundTheory.ProfCoh.cochainsComplex M).sc n).mapHomologyIso (upF k)
  exact ⟨(i1 ≪≫ i2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
