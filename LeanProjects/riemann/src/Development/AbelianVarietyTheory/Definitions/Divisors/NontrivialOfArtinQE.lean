import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CircleAsphGNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb

noncomputable section
namespace GlobalTheory.KS
namespace Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

theorem act_zero {A : Over S} [GrpObj A] (act : OActN O A) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have : act.act 0 * act.act 0 = act.act 0 * 1 := h.symm.trans (_root_.mul_one _).symm
  exact mul_left_cancel this

theorem matEnd_one {A : Over S} [GrpObj A] (act : OActN O A) (m : ℕ) :
    matEnd act (1 : Matrix (Fin m) (Fin m) O) = 𝟙 _ := by
  classical
  unfold matEnd
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Pi.lift_π, Category.id_comp, List.ofFn_eq_map]
  rw [List.prod_map_eq_pow_single i]
  · rw [List.count_finRange, pow_one, Matrix.one_apply_eq, act.one, Category.comp_id]
  · intro j hj _
    rw [Matrix.one_apply_ne' hj, act_zero, comp_one]

theorem matBC_one {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) (m : ℕ) :
    matBC act p b (1 : Matrix (Fin m) (Fin m) O) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [matBC, matEnd_one]

theorem op_single_one (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E] {A : Over S} [GrpObj A]
    (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) (m : ℕ) (n : ℤ) :
    op l act p b (Finsupp.single (1 : Matrix (Fin m) (Fin m) O) (1 : E)) n = 1 := by
  simp only [op, Finsupp.sum_single_index, zero_smul, one_smul, matBC_one]
  unfold pullE pullHQ
  rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id, LinearMap.baseChange_id]
  rfl

theorem Hxi_single_one (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E] {A : Over S} [GrpObj A]
    (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) (m : ℕ) (k : ℕ) (i : ℤ) :
    Hxi l act p b (Finsupp.single (1 : Matrix (Fin m) (Fin m) O) (1 : E)) k i = ⊤ := by
  rw [Hxi, op_single_one]
  exact LinearMap.range_id

theorem pts_comm {A : Over S} [GrpObj A] (act : OActN O A) {T : Over S} (x y : T ⟶ A) : x * y = y * x := by
  have hh := act.hom (1 + 1)
  have h2 : ∀ z : T ⟶ A, z ≫ act.act (1 + 1) = z * z := fun z => by
    rw [act.add, act.one, comp_mul, Category.comp_id]
  have h : (x * y) ≫ act.act (1 + 1) = (x ≫ act.act (1 + 1)) * (y ≫ act.act (1 + 1)) := mul_comp _ _ _
  rw [h2, h2, h2] at h
  have h' : x * (y * x) * y = x * (x * y) * y := by simpa [_root_.mul_assoc] using h
  exact (mul_left_cancel (mul_right_cancel h')).symm

theorem comp_matEnd_pr {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) {T : Over S}
    (x : T ⟶ pow A m) (i : Fin m) :
    x ≫ matEnd act M ≫ pr A i = (List.ofFn fun j => (x ≫ pr A j) ≫ act.act (M i j)).prod := by
  unfold matEnd
  rw [Pi.lift_π]
  let φ : (pow A m ⟶ A) →* (T ⟶ A) := { toFun := fun g => x ≫ g, map_one' := comp_one _, map_mul' := fun _ _ => comp_mul _ _ _ }
  change φ _ = _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  all_goals (funext j; simp [φ])

theorem matEnd_mul {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M N : Matrix (Fin m) (Fin m) O) :
    matEnd act (M * N) = matEnd act N ≫ matEnd act M := by
  letI : CommGroup (pow A m ⟶ A) := { (inferInstance : Group (pow A m ⟶ A)) with mul_comm := pts_comm act }
  refine Pi.hom_ext _ _ fun i => ?_
  have h1 := comp_matEnd_pr act (M * N) (𝟙 _) i
  have h2 := comp_matEnd_pr act M (matEnd act N) i
  have h3 := fun j => comp_matEnd_pr act N (𝟙 _) j
  simp only [Category.id_comp] at h1 h3
  rw [Category.assoc]
  refine h1.trans (Eq.trans ?_ h2.symm)
  simp only [h3, List.prod_ofFn]
  have hψ : ∀ (b : O) (g : Fin m → (pow A m ⟶ A)), (∏ k, g k) ≫ act.act b = ∏ k, g k ≫ act.act b := fun b g => by
    have := act.hom b
    let ψ : (pow A m ⟶ A) →* (pow A m ⟶ A) :=
      { toFun := fun g => g ≫ act.act b, map_one' := one_comp _, map_mul' := fun _ _ => mul_comp _ _ _ }
    exact map_prod ψ g Finset.univ
  have hχ : ∀ (z : pow A m ⟶ A) (c : Fin m → O), z ≫ act.act (∑ j, c j) = ∏ j, z ≫ act.act (c j) := fun z c => by
    let χ : Multiplicative O →* (pow A m ⟶ A) :=
      { toFun := fun b => z ≫ act.act b.toAdd
        map_one' := by change z ≫ act.act 0 = 1; rw [act_zero, comp_one]
        map_mul' := fun a b => by change z ≫ act.act (a.toAdd + b.toAdd) = _; rw [act.add, comp_mul] }
    exact map_prod χ (fun j => Multiplicative.ofAdd (c j)) Finset.univ
  simp only [hψ, Matrix.mul_apply, hχ, act.mul, Category.assoc]
  exact Finset.prod_comm

theorem matBC_mul {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) {m : ℕ}
    (M N : Matrix (Fin m) (Fin m) O) : matBC act p b (M * N) = matBC act p b N ≫ matBC act p b M := by
  apply pullback.hom_ext <;> simp [matBC, matEnd_mul, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

variable (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E]

theorem pullEt_id (Y : Scheme.{0}) (n t : ℤ) : pullEt l E (𝟙 Y) n t = LinearMap.id := by
  unfold pullEt pullHQ
  rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id, LinearMap.baseChange_id]

theorem pullEt_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n t : ℤ) :
    pullEt l E (f ≫ g) n t = pullEt l E f n t ∘ₗ pullEt l E g n t := by
  unfold pullEt pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp]

theorem opT_single {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) O) (c : E) (n t : ℤ) :
    opT l act p b (Finsupp.single M c) n t = c • pullEt l E (matBC act p b M) n t := by
  simp only [opT, Finsupp.sum_single_index, zero_smul]

theorem opT_single_mul {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) {m : ℕ}
    (M N : Matrix (Fin m) (Fin m) O) (n t : ℤ) :
    opT l act p b (Finsupp.single (M * N) (1 : E)) n t =
      opT l act p b (Finsupp.single N (1 : E)) n t * opT l act p b (Finsupp.single M (1 : E)) n t := by
  simp only [opT_single, one_smul, matBC_mul, pullEt_comp]
  rfl

theorem altOp_single_mul {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Algebra R E]
    (ρ : O →+* Module.End R V) {m : ℕ} (M N : Matrix (Fin m) (Fin m) O) (q : ℕ) :
    altOp ρ (Finsupp.single (M * N) (1 : E)) q =
      altOp ρ (Finsupp.single N (1 : E)) q * altOp ρ (Finsupp.single M (1 : E)) q := by
  ext f x
  simp only [altOp, Finsupp.sum_single_index, zero_smul, one_smul, altPull_apply, Module.End.mul_apply]
  congr 1
  funext a i
  simp only [matAct_apply, Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply]
  exact Finset.sum_comm

theorem HxiT_single_one {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B)
    (m k : ℕ) (t i : ℤ) : HxiT l act p b (Finsupp.single (1 : Matrix (Fin m) (Fin m) O) (1 : E)) k t i = ⊤ := by
  rw [HxiT, opT_single, one_smul, matBC_one, pullEt_id]
  exact LinearMap.range_id

section Gal
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem galEt_eq {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (n t : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    galEt l E Ω q n t σ = (galHQ l Ω q n t σ).baseChange E := rfl

theorem galEt_mul {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (n t : ℤ) (σ τ : Ω ≃ₐ[k] Ω) :
    galEt l E Ω q n t (σ * τ) = galEt l E Ω q n t σ * galEt l E Ω q n t τ := by
  unfold galEt
  rw [galMap_mul, pullEt_comp]
  rfl

theorem opT_comm_pull {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (n t : ℤ) (u : ksBC A m p b ⟶ ksBC A m p b)
    (h : ∀ M, u ≫ matBC act p b M = matBC act p b M ≫ u) (y : HEt l E (ksBC A m p b) n t) :
    pullEt l E u n t (opT l act p b ε n t y) = opT l act p b ε n t (pullEt l E u n t y) := by
  unfold opT Finsupp.sum
  simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
  refine Finset.sum_congr rfl fun M _ => ?_
  have h1 := LinearMap.congr_fun (pullEt_comp (E := E) l u (matBC act p b M) n t) y
  have h2 := LinearMap.congr_fun (pullEt_comp (E := E) l (matBC act p b M) u n t) y
  rw [h] at h1
  exact congrArg _ (h1.symm.trans h2)

theorem galMap_matBC {A : Over S} [GrpObj A] (act : OActN O A) (p : S ⟶ Spec (CommRingCat.of k)) {m : ℕ}
    (σ : Ω ≃ₐ[k] Ω) (M : Matrix (Fin m) (Fin m) O) :
    GlobalTheory.Et.galMap Ω ((pow A m).hom ≫ p) σ ≫ matBC act p _ M = matBC act p _ M ≫ GlobalTheory.Et.galMap Ω ((pow A m).hom ≫ p) σ := by
  apply pullback.hom_ext
  · simp [matBC, pullback.map, pullback.lift_fst, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.galMap_fst_assoc]
  · simp [matBC, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, GlobalTheory.Et.galMap_snd]

theorem HxiT_gal_stable {A : Over S} [GrpObj A] (act : OActN O A) (p : S ⟶ Spec (CommRingCat.of k)) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (d : ℕ) (t i : ℤ) (σ : Ω ≃ₐ[k] Ω)
    (x : HEt l E (GlobalTheory.Et.geom Ω ((pow A m).hom ≫ p)) (i + d) t)
    (hx : x ∈ HxiT l act p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ε d t i) :
    galEt l E Ω ((pow A m).hom ≫ p) (i + d) t σ x ∈ HxiT l act p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ε d t i := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, (opT_comm_pull l act p _ ε (i + d) t _ (galMap_matBC Ω act p σ) y).symm⟩

end Gal

theorem powMap_pr {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) : powMap f φ h m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_π]
  rfl

theorem powMap_over {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) : powMap f φ h m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

theorem nontrivial_of_artinQE (F : Type) [Field F] [Algebra ℚ_[l] F] (h : ArtinQE l F) :
    Nontrivial (HE l F (Spec (CommRingCat.of ℂ)) (0 : ℕ)) := by
  obtain ⟨e, -⟩ := h
  have e0 := e _ (𝟙 (Spec (CommRingCat.of ℂ))) 0
  haveI : Unique (GlobalTheory.CxPts (𝟙 (Spec (CommRingCat.of ℂ))) (RingHom.id ℂ)) :=
    { default := ⟨_, Category.comp_id _⟩
      uniq := fun y => Subtype.ext ((Category.comp_id _).symm.trans y.2) }
  have iso := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{0} F) (ModuleCat.of F F)
    (TopCat.of (GlobalTheory.CxPts (𝟙 (Spec (CommRingCat.of ℂ))) (RingHom.id ℂ)))
  have iso2 := iso ≪≫ coproductUniqueIso _
  have : Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} F) 0).obj (ModuleCat.of F F)).obj
      (TopCat.of (GlobalTheory.CxPts (𝟙 (Spec (CommRingCat.of ℂ))) (RingHom.id ℂ)))) :=
    iso2.toLinearEquiv.toEquiv.nontrivial
  exact e0.toEquiv.nontrivial

def intAct (A : Over S) [GrpObj A] [IsCommMonObj A] : OActN ℤ A where
  act n := 𝟙 A ^ n
  hom n := by
    have hn : ∀ j : ℕ, IsMonHom (𝟙 A ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
      | succ j ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 A ^ j) (𝟙 A) ≫ μ[A]))
    obtain ⟨j, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast]; exact hn j
    · rw [zpow_neg, zpow_natCast]
      have := hn j
      exact inferInstanceAs (IsMonHom ((𝟙 A ^ j) ≫ ι[A]))
  one := zpow_one _
  mul b c := by
    let φ : (A ⟶ A) →* (A ⟶ A) :=
      { toFun := fun g => (𝟙 A ^ c) ≫ g, map_one' := comp_one _, map_mul' := fun _ _ => comp_mul _ _ _ }
    change _ = φ _
    rw [map_zpow, mul_comm b c, zpow_mul]
    simp [φ]
  add b c := zpow_add _ _ _

theorem matEnd_shear {A : Over S} [GrpObj A] (act : OActN O A) :
    matEnd act !![1, 1; 0, 1] ≫ pr A 0 = pr A 0 * pr A 1 ∧ matEnd act !![1, 1; 0, 1] ≫ pr A 1 = pr A 1 := by
  have h := comp_matEnd_pr act !![1, 1; 0, 1] (𝟙 _)
  simp only [Category.id_comp] at h
  constructor
  · rw [h]; simp [act.one]
  · rw [h]; simp [act.one, act_zero]

end Model
end GlobalTheory.KS
