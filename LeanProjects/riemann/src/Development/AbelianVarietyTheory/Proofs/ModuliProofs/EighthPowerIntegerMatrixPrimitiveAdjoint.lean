import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegPreBundleMulLeft

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowerAdjoint

open GlobalTheory.CechPic

section Algebra

variable {M : Type} {V : Type 1} [AddCommGroup M] [AddCommGroup V] {n : Type} [Fintype n]

def form (B : M →+ M →+ V) (W : Matrix n n ℤ) (x y : n → M) : V := ∑ u, ∑ v, W u v • B (x u) (y v)

theorem form_left (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W (fun u => ∑ v, m u v • x v) y = form B (m.transpose * W) x y := by
  have hL : form B W (fun u => ∑ v, m u v • x v) y = ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v) := by
    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (m.transpose * W) x y = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  calc ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v)
      = ∑ u, ∑ w, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w, ∑ u, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem form_right (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W x (fun u => ∑ v, m u v • y v) = form B (W * m) x y := by
  have hL : form B W x (fun u => ∑ v, m u v • y v) = ∑ u, ∑ v, ∑ w, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (W * m) x y = ∑ u, ∑ w, ∑ v, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem form_polar (B : M →+ M →+ V) (hB : ∀ a b, B a b = B b a) (W : Matrix n n ℤ) (x y : n → M) :
    form B W (x + y) (x + y) - form B W x x - form B W y y + form B W 0 0 = form B (W + W.transpose) x y := by
  have hyx : ∑ u, ∑ v, W u v • B (y u) (x v) = ∑ u, ∑ v, W v u • B (x u) (y v) := by
    rw [Finset.sum_comm]
    simp only [hB (y _) (x _)]
  simp only [form, Pi.add_apply, Pi.zero_apply, map_add, map_zero, AddMonoidHom.add_apply,
    smul_add, smul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, Matrix.add_apply, Matrix.transpose_apply, add_smul]
  rw [hyx]
  abel

end Algebra

section Square

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

omit [IsCommMonObj B] in

theorem exists_biadditive {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left, (∀ a b, β a b = β b a) ∧
      ∀ x y : T ⟶ B, β (.ofMul x) (.ofMul y) = pull (lift x y).left (cls P hP) := by
  have add1 : ∀ x x' y : T ⟶ B, pull (lift (x * x') y).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x' y).left (cls P hP) := by
    intro x x' y
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hb x x' y)
    rw [cls_linComb hP] at h0
    simp [Fin.sum_univ_three] at h0
    rw [← sub_eq_zero, ← h0]
    abel
  have e1 : cls P hP = pull (lift (snd B B) (fst B B)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP _).2 hs
  have hsym : ∀ x y : T ⟶ B, pull (lift y x).left (cls P hP) = pull (lift x y).left (cls P hP) := by
    intro x y
    have e2 : (lift y x).left ≫ (lift (snd B B) (fst B B)).left = (lift x y).left := by
      rw [← Over.comp_left]
      congr 1
      ext <;> simp
    calc pull (lift y x).left (cls P hP)
        = pull (lift y x).left (pull (lift (snd B B) (fst B B)).left (cls P hP)) := by rw [← e1]
      _ = pull (lift x y).left (cls P hP) := by rw [← pull_comp, e2]
  have add2 : ∀ x y y' : T ⟶ B, pull (lift x (y * y')).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x y').left (cls P hP) := by
    intro x y y'
    rw [hsym (y * y') x, add1, ← hsym y x, ← hsym y' x]
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => pull (lift a.toMul b.toMul).left (cls P hP))
    fun b b' => ?_) fun a a' => ?_, fun a b => ?_, fun x y => rfl⟩
  · rw [toMul_add]
    exact add2 _ _ _
  · ext b
    simp only [toMul_add]
    exact add1 _ _ _
  · exact (hsym a.toMul b.toMul).symm

theorem comp_prod_zpow {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (k : Fin n → ℤ) :
    ρ ≫ (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => (ρ ≫ x v) ^ k v).prod := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => simp [List.ofFn_succ, MonObj.comp_mul, GrpObj.comp_zpow, ih]

theorem ofMul_comp_matrix {Q T : Over S} {n : ℕ} (pr : Fin n → (Q ⟶ B)) (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q)
    (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) (x : T ⟶ Q) :
    (fun u => Additive.ofMul ((x ≫ α) ≫ pr u)) = fun u => ∑ v, m u v • Additive.ofMul (x ≫ pr v) := by
  funext u
  rw [Category.assoc, hα u, comp_prod_zpow]
  simp [ofMul_list_prod, List.sum_ofFn, ofMul_zpow]

theorem exists_form {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : Type} [Fintype n] (pr : n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix n n ℤ)
    (hW : LBIso L (LB.LinComb P (K := n × n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2))) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left,
      (∀ x : T ⟶ Q, pull x.left (cls L hL) =
        form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u))) ∧
      ∀ (x y : T ⟶ Q) hh, cls (cubeLB Q ![x, y] L) hh =
        form β (W + W.transpose) (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (y ≫ pr u)) := by
  obtain ⟨β, hβs, hβ⟩ := exists_biadditive hP hs T hb
  have hpt : ∀ x : T ⟶ Q, pull x.left (cls L hL) =
      form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u)) := by
    intro x
    rw [(cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hW, cls_linComb hP, map_sum, Fintype.sum_prod_type]
    simp only [form]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hβ]
  refine ⟨β, hpt, fun x y hh => ?_⟩
  have hxy : (fun u => Additive.ofMul ((x * y) ≫ pr u)) =
      (fun u => Additive.ofMul (x ≫ pr u)) + fun u => Additive.ofMul (y ≫ pr u) := by
    funext u
    have := hpr u
    simp [MonObj.mul_comp]
  have h1 : (fun u => Additive.ofMul ((1 : T ⟶ Q) ≫ pr u)) = 0 := by
    funext u
    have := hpr u
    simp [MonObj.one_comp]
  rw [cls_cube_two hL x y hh, lam, hpt, hpt, hpt, hpt, hxy, h1]
  exact form_polar β hβs W _ _

theorem primitive_adjoint {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (hb : ∀ (T : Over S) (x x' y : T ⟶ B), ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : ℕ} (pr : Fin n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix (Fin n) (Fin n) ℤ)
    (hW : LBIso L (LB.LinComb P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)))
    (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q) (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) :
    ((W + W.transpose) * m = W → LBIso L (cubeLB Q ![𝟙 Q, α] L)) ∧
      ∀ (m' : Matrix (Fin n) (Fin n) ℤ) (α' : Q ⟶ Q), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) →
        m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
        LBIso (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L) (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L) := by
  refine ⟨fun hm => ?_, fun m' α' hα' hm' => ?_⟩
  · obtain ⟨β, hpt, hcube⟩ := exists_form hP hs Q (hb Q) pr hpr hL W hW
    have hc : (cubeLB Q ![𝟙 Q, α] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL hc).1 ?_
    have e0 := hpt (𝟙 Q)
    rw [Over.id_left, pull_id] at e0
    have hY := ofMul_comp_matrix pr m α hα (𝟙 Q)
    have hR := form_right β (W + W.transpose) m (fun u => Additive.ofMul (pr u)) (fun u => Additive.ofMul (pr u))
    simp only [Category.id_comp] at e0 hY
    rw [e0, hcube (𝟙 Q) α hc]
    simp only [Category.id_comp]
    rw [hY, hR, hm]
  · obtain ⟨β, -, hcube⟩ := exists_form hP hs (Q ⊗ Q) (hb (Q ⊗ Q)) pr hpr hL W hW
    have h1 : (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L).IsLB := LB.isLB_linComb hL _ _
    have h2 : (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff h1 h2).1 ?_
    have hl := form_left β (W + W.transpose) m (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    have hr := form_right β (W + W.transpose) m' (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    rw [hcube _ _ h1, hcube _ _ h2, ofMul_comp_matrix pr m α hα (fst Q Q), ofMul_comp_matrix pr m' α' hα' (snd Q Q), hl, hr, hm']

end Square

theorem matrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  intro hΘ W K _ o _ s h k ζ c P pr hpr huniv hW m α hα
  have : IsCommMonObj P.A := P.isAb.comm
  exact primitive_adjoint c.isLB c.symm
    (fun T x x' y => siegPre_bundle_mul_left hΘ K o s h k ζ c P pr hpr huniv T x x' y) pr hpr P.isLB W hW m α hα

end GlobalTheory.PowerAdjoint
