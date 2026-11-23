import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HasGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}

def lf (F : (T ⟶ A) →₀ ℤ) : (T.left ⟶ A.left) →₀ ℤ := Finsupp.mapDomain (fun x => x.left) F

lemma lf_add (F G : (T ⟶ A) →₀ ℤ) : lf (F + G) = lf F + lf G := by
  unfold lf
  exact Finsupp.mapDomain_add
lemma lf_neg (F : (T ⟶ A) →₀ ℤ) : lf (-F) = - lf F := by
  unfold lf
  exact map_neg (Finsupp.mapDomain.addMonoidHom _) F
lemma lf_sub (F G : (T ⟶ A) →₀ ℤ) : lf (F - G) = lf F - lf G := by
  unfold lf
  exact map_sub (Finsupp.mapDomain.addMonoidHom _) F G
lemma lf_smul (n : ℤ) (F : (T ⟶ A) →₀ ℤ) : lf (n • F) = n • lf F := by
  unfold lf
  exact map_zsmul (Finsupp.mapDomain.addMonoidHom _) n F
lemma lf_single (x : T ⟶ A) (n : ℤ) : lf (Finsupp.single x n) = Finsupp.single x.left n := by
  unfold lf
  exact Finsupp.mapDomain_single

lemma lf_pull (h : T' ⟶ T) (F : (T ⟶ A) →₀ ℤ) :
    Finsupp.mapDomain (fun ψ => h.left ≫ ψ) (lf F) = lf (Finsupp.mapDomain (fun x => h ≫ x) F) := by
  unfold lf
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

lemma padd_eq_mul (a b : T ⟶ A) : padd A a b = a * b := rfl
lemma pzero_eq_one : pzero A T = 1 := rfl

lemma comp_psum {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one h
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [padd_eq_mul, padd_eq_mul, MonObj.comp_mul, ih]

lemma cartesian_lift_three_comp_projection (x y z : T ⟶ A) : (fun k => lift x (lift y z) ≫ x3 A k) = ![x, y, z] := by
  funext k
  fin_cases k <;> simp [x3]

def lamP (u v : T ⟶ A) : (T ⟶ A) →₀ ℤ :=
  Finsupp.single (u * v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 1 1

open scoped Classical in
lemma univ_finset_powerset_fin_three : (Finset.univ : Finset (Finset (Fin 3))) =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
  first
  | decide
  | rfl
  | (ext I; fin_cases I <;> simp)

private lemma fsum_eq_sum_single {X Y : Scheme} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    fsum φ ε = ∑ k, Finsupp.single (φ k) (ε k) := rfl

lemma fsum_theta (x y z : T ⟶ A) :
    fsum (fun I : ULift.{0} (Finset (Fin 3)) => (psum A ![x, y, z] I.down).left)
        (fun I => (-1 : ℤ) ^ (3 - I.down.card)) =
      lf (lamP x (y * z) - lamP x y - lamP x z) := by
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
    decide
  have p0 : psum A ![x, y, z] ∅ = 1 := rfl
  have p1 : psum A ![x, y, z] {0} = x := by
    rw [show psum A ![x, y, z] {0} = x * 1 from rfl, _root_.mul_one]
  have p2 : psum A ![x, y, z] {1} = y := by
    rw [show psum A ![x, y, z] {1} = y * 1 from rfl, _root_.mul_one]
  have p3 : psum A ![x, y, z] {2} = z := by
    rw [show psum A ![x, y, z] {2} = z * 1 from rfl, _root_.mul_one]
  have p01 : psum A ![x, y, z] {0, 1} = x * y := by
    rw [show psum A ![x, y, z] {0, 1} = x * (y * 1) from rfl, _root_.mul_one]
  have p02 : psum A ![x, y, z] {0, 2} = x * z := by
    rw [show psum A ![x, y, z] {0, 2} = x * (z * 1) from rfl, _root_.mul_one]
  have p12 : psum A ![x, y, z] {1, 2} = y * z := by
    rw [show psum A ![x, y, z] {1, 2} = y * (z * 1) from rfl, _root_.mul_one]
  have p012 : psum A ![x, y, z] {0, 1, 2} = x * (y * z) := by
    rw [show psum A ![x, y, z] {0, 1, 2} = x * (y * (z * 1)) from rfl, _root_.mul_one]
  rw [fsum_eq_sum_single, ← Equiv.sum_comp Equiv.ulift.symm]
  simp only [Equiv.ulift_symm_down]
  rw [hu]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, not_false_eq_true, or_self, p0, p1, p2, p3, p01, p02, p12, p012]
  simp (config := {decide := true}) only [Finset.card_empty, Finset.card_singleton, Finset.card_insert_of_notMem,
    Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_self]
  unfold lamP
  simp only [lf_add, lf_sub, lf_single]
  norm_num
  abel

variable {M : LB A.left}

private lemma mapDomain_comp_fsum {X Y Z : Scheme} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) :
    Finsupp.mapDomain (fun ψ => h ≫ ψ) (fsum φ ε) = fsum (fun k => h ≫ φ k) ε := by
  rw [fsum_eq_sum_single, fsum_eq_sum_single, Finsupp.mapDomain_finset_sum]
  simp only [Finsupp.mapDomain_single]

lemma hasGen_theta (t : LB.Gen (Theta A M)) (ht : t.IsGen) (x y z : T ⟶ A) :
    HasGen M (lf (lamP x (y * z) - lamP x y - lamP x z)) := by
  have h0 := HasGen.of_gen (L := M)
    (φ := fun I : ULift.{0} (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (3 - I.down.card)) t ht
  have h1 := h0.pull (lift x (lift y z)).left
  rw [mapDomain_comp_fsum] at h1
  rw [← fsum_theta]
  convert h1 using 2
  funext I
  rw [← Over.comp_left, comp_psum, cartesian_lift_three_comp_projection]

lemma lambdaMap_one_eq_zero (x : T ⟶ A) : lamP x 1 = 0 := by
  unfold lamP
  rw [_root_.mul_one]
  abel

lemma hasGen_lam_pow (t : LB.Gen (Theta A M)) (ht : t.IsGen) (x y : T ⟶ A) :
    ∀ n : ℕ, HasGen M (lf (lamP x (y ^ n) - (n : ℤ) • lamP x y))
  | 0 => by simpa [lambdaMap_one_eq_zero, lf] using (HasGen.zero (L := M))
  | n + 1 => by
    have h := (hasGen_theta t ht x (y ^ n) y).add (hasGen_lam_pow t ht x y n)
    rw [← lf_add] at h
    convert h using 2
    rw [pow_succ]
    simp only [Nat.cast_succ, add_smul, one_smul]
    abel

lemma mapDomain_single' {α β : Type} (f : α → β) (a : α) (n : ℤ) :
    Finsupp.mapDomain f (Finsupp.single a n) = Finsupp.single (f a) n := by
  exact Finsupp.mapDomain_single

lemma mapDomain_add' {α β : Type} (f : α → β) (F G : α →₀ ℤ) :
    Finsupp.mapDomain f (F + G) = Finsupp.mapDomain f F + Finsupp.mapDomain f G := by
  exact Finsupp.mapDomain_add

lemma mapDomain_sub' {α β : Type} (f : α → β) (F G : α →₀ ℤ) :
    Finsupp.mapDomain f (F - G) = Finsupp.mapDomain f F - Finsupp.mapDomain f G := by
  exact map_sub (Finsupp.mapDomain.addMonoidHom f) F G

lemma mapDomain_lamP (h : T' ⟶ T) (u v : T ⟶ A) :
    Finsupp.mapDomain (fun x => h ≫ x) (lamP u v) = lamP (h ≫ u) (h ≫ v) := by
  unfold lamP
  have hs : ∀ (P Q : (T ⟶ A) →₀ ℤ), Finsupp.mapDomain (fun x => h ≫ x) (P - Q) =
      Finsupp.mapDomain (fun x => h ≫ x) P - Finsupp.mapDomain (fun x => h ≫ x) Q :=
    fun P Q => map_sub (Finsupp.mapDomain.addMonoidHom _) P Q
  rw [Finsupp.mapDomain_add, hs, hs, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, MonObj.comp_mul,
    MonObj.comp_one]

lemma single_two {α : Type} (a : α) : Finsupp.single a (2 : ℤ) = Finsupp.single a 1 + Finsupp.single a 1 := by
  rw [← Finsupp.single_add]
  norm_num

lemma single_neg_two {α : Type} (a : α) : Finsupp.single a (-2 : ℤ) = -Finsupp.single a 1 - Finsupp.single a 1 := by
  rw [← Finsupp.single_neg, ← Finsupp.single_sub]
  norm_num

def psiP (w : A ⟶ A) (y : T ⟶ A) : (T ⟶ A) →₀ ℤ :=
  lamP y (y ≫ w) - Finsupp.single y 1 + Finsupp.single 1 1

lemma hasGen_psi (w : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) w).left, 𝟙 A.left, w.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (hu : u.IsGen) (y : T ⟶ A) : HasGen M (lf (psiP w y)) := by
  have h0 := HasGen.of_gen (L := M) u hu
  have h1 := h0.pull y.left
  rw [mapDomain_comp_fsum] at h1
  convert h1 using 1
  have e1 : y.left ≫ (padd A (𝟙 _) w).left = (y * (y ≫ w)).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, Category.comp_id]
  have e2 : y.left ≫ (𝟙 A : A ⟶ A).left = y.left := by
    rw [← Over.comp_left, Category.comp_id]
  have e3 : y.left ≫ w.left = (y ≫ w).left := by
    rw [← Over.comp_left]
  have e4 : y.left ≫ (toUnit A ≫ η[A]).left = (1 : T ⟶ A).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
    rfl
  rw [fsum_eq_sum_single]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  rw [e1, Category.comp_id, e3, e4]
  unfold psiP lamP
  simp only [lf_add, lf_sub, lf_single, Finsupp.single_neg, single_two]
  abel

lemma hasGen_rosati (f g : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (Out.rosatiφ A f g) Out.rosatiε)) (hu : u.IsGen) (x z : T ⟶ A) :
    HasGen M (lf (lamP (x ≫ f) z - lamP x (z ≫ g))) := by
  have h0 := HasGen.of_gen (L := M) u hu
  have h1 := h0.pull (lift x z).left
  rw [mapDomain_comp_fsum] at h1
  convert h1 using 1
  have r0 : (lift x z).left ≫ (padd A (fst A A ≫ f) (snd A A)).left = ((x ≫ f) * z).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, ← Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]
  have r1 : (lift x z).left ≫ (fst A A ≫ f).left = (x ≫ f).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.lift_fst]
  have r2 : (lift x z).left ≫ (snd A A).left = z.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd]
  have r3 : (lift x z).left ≫ (padd A (fst A A) (snd A A ≫ g)).left = (x * (z ≫ g)).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, CartesianMonoidalCategory.lift_fst, ← Category.assoc,
      CartesianMonoidalCategory.lift_snd]
  have r4 : (lift x z).left ≫ (fst A A).left = x.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst]
  have r5 : (lift x z).left ≫ (snd A A ≫ g).left = (z ≫ g).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.lift_snd]
  rw [fsum_eq_sum_single]
  simp only [Out.rosatiφ, Out.rosatiε, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  rw [r0, r1, r2, r3, r4, r5]
  unfold lamP
  simp only [lf_add, lf_sub, lf_single, Finsupp.single_neg]
  abel

lemma comp_pow' (f : T ⟶ A) (g : A ⟶ A) : ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow' f g n]

variable {O : Type} [CommRing O] [StarRing O]

lemma act_zero' (ra : Out.RingAct A O) : ra.act 0 = 1 := by
  have h := ra.map_add 0 0
  rw [_root_.add_zero, padd_eq_mul] at h
  exact (_root_.mul_eq_left.mp h.symm)

lemma act_natCast (ra : Out.RingAct A O) : ∀ n : ℕ, ra.act (n : O) = (𝟙 A) ^ n
  | 0 => by rw [Nat.cast_zero, act_zero', pow_zero]
  | n + 1 => by rw [Nat.cast_succ, ra.map_add, padd_eq_mul, act_natCast ra n, ra.map_one, pow_succ]

theorem hasGen_pullMul (ra : Out.RingAct A O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (uΨ : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) (ra.act w0)).left, 𝟙 A.left, (ra.act w0).left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen)
    (uR : LB.Gen (LB.LinComb M (Out.rosatiφ A (ra.act a) (ra.act (star a))) Out.rosatiε)) (huR : uR.IsGen)
    (t : LB.Gen (Theta A M)) (ht : t.IsGen) :
    HasGen M (lf (Finsupp.single (ra.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 A) 1 +
      ((N : ℤ) - 1) • Finsupp.single (1 : A ⟶ A) 1)) := by
  have hΨa := hasGen_psi (ra.act w0) uΨ huΨ (ra.act a)
  have hΨ1 := hasGen_psi (ra.act w0) uΨ huΨ (𝟙 A)
  have hR := hasGen_rosati (ra.act a) (ra.act (star a)) uR huR (𝟙 A) (ra.act a ≫ ra.act w0)
  have hP := hasGen_lam_pow t ht (𝟙 A) (ra.act w0) N
  have hz : (ra.act a ≫ ra.act w0) ≫ ra.act (star a) = (ra.act w0) ^ N := by
    rw [← ra.map_mul, ← ra.map_mul]
    have h1 : star a * (w0 * a) = (N : O) * w0 := by
      rw [← hN]
      ring
    rw [h1, ra.map_mul, act_natCast, comp_pow', Category.comp_id]
  have key : Finsupp.single (ra.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 A) 1 +
      ((N : ℤ) - 1) • Finsupp.single (1 : A ⟶ A) 1 =
      -(psiP (ra.act w0) (ra.act a)) +
        (lamP (𝟙 A ≫ ra.act a) (ra.act a ≫ ra.act w0) - lamP (𝟙 A) ((ra.act a ≫ ra.act w0) ≫ ra.act (star a))) +
        (lamP (𝟙 A) (ra.act w0 ^ N) - (N : ℤ) • lamP (𝟙 A) (ra.act w0)) +
        (N : ℤ) • psiP (ra.act w0) (𝟙 A) := by
    rw [hz, Category.id_comp]
    unfold psiP
    rw [Category.id_comp]
    module
  rw [key, lf_add, lf_add, lf_add, lf_neg, lf_smul]
  exact (((hΨa.neg).add hR).add hP).add (hΨ1.zsmul _)

end ReciprocityTheory.ChartRestriction.G.DVR
