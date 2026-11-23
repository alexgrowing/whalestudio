import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EighthPower

open GlobalTheory.CechPic Matrix

theorem map_prod_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) : f (∏ i, x i) = ∑ i, f (x i) := by
  simpa only [zpow_one, one_smul] using GlobalTheory.BilinCalc.map_prod_zpow f hf x fun _ => 1

theorem map_zpow_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    (x : G) (c : ℤ) : f (x ^ c) = c • f x := by
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using
    GlobalTheory.BilinCalc.map_prod_zpow f hf (n := 1) (fun _ => x) fun _ => c

section Points

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem comp_prod_zpow (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Fin n → ℤ) :
    h ≫ (∏ i, x i ^ c i) = ∏ i, (h ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun z => h ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (∏ i, x i ^ c i) = ∏ i, F (x i) ^ c i := by simp only [map_prod, map_zpow]
  exact e

theorem prod_comp_hom (f : G ⟶ A) [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ G)) :
    (∏ i, x i) ≫ f = ∏ i, x i ≫ f := by
  let F : (T ⟶ G) →* (T ⟶ A) := MonoidHom.mk' (fun z => z ≫ f) fun a b => MonObj.mul_comp _ _ _
  exact map_prod F x _

omit [IsCommMonObj A] in
theorem comp_id_zpow (x : T ⟶ A) (c : ℤ) : x ≫ (𝟙 A ^ c) = x ^ c := by
  let F : (A ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (𝟙 A ^ c) = F (𝟙 A) ^ c := map_zpow F _ _
  exact e.trans (congrArg (· ^ c) (Category.comp_id x))

end Points

theorem prod_zpow_eq {H : Type*} [CommGroup H] (x : H) {n : ℕ} (c : Fin n → ℤ) : ∏ i, x ^ c i = x ^ ∑ i, c i := by
  have h := map_prod (zpowersHom H x) (fun i => Multiplicative.ofAdd (c i)) Finset.univ
  simp only [zpowersHom_apply, toAdd_prod, toAdd_ofAdd] at h
  exact h.symm

theorem main : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro W S G A _ _ _ _ pr L ρ hE hpr huniv hL hΘ hρ hadj hprim
  obtain ⟨B, hB⟩ : ∃ B, B = W + W.transpose := ⟨_, rfl⟩
  have hdet : IsUnit B.det := by rw [hB, hE.2]; exact isUnit_one
  have hBs : B.transpose = B := by rw [hB, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [← hB] at hadj hprim
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin 8 → ℤ, u₀ = Pi.single 0 1 := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 8 → ℤ, B *ᵥ u₁ = u₀ := ⟨B⁻¹ *ᵥ u₀, by rw [Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]⟩
  have h00 : u₀ ⬝ᵥ u₀ = 1 := by rw [hu₀]; simp
  have hsymB : ∀ v v' : Fin 8 → ℤ, v ⬝ᵥ B *ᵥ v' = v' ⬝ᵥ B *ᵥ v := fun v v' => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs, dotProduct_comm]
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun {T} x x' h =>
    (huniv T fun u => x' ≫ pr u).unique h fun _ => rfl
  choose ψ hψ using fun v : Fin 8 → ℤ => (huniv A fun u => 𝟙 A ^ v u).exists
  have hψ' : ∀ {T : Over S} (x : T ⟶ A) v u, (x ≫ ψ v) ≫ pr u = x ^ v u := fun x v u => by
    rw [Category.assoc, hψ, comp_id_zpow]
  have ψmul : ∀ {T : Over S} (x y : T ⟶ A) v, (x * y) ≫ ψ v = (x ≫ ψ v) * (y ≫ ψ v) := fun x y v =>
    ext _ _ fun u => by rw [hψ', MonObj.mul_comp, hψ', hψ', _root_.mul_zpow]
  have ψone : ∀ {T : Over S} v, (1 : T ⟶ A) ≫ ψ v = 1 := fun v =>
    ext _ _ fun u => by rw [hψ', MonObj.one_comp, _root_.one_zpow]
  have ψsmul : ∀ {T : Over S} (x : T ⟶ A) (c : ℤ) v, x ≫ ψ (c • v) = (x ^ c) ≫ ψ v := fun x c v =>
    ext _ _ fun u => by rw [hψ', hψ', ← _root_.zpow_mul, Pi.smul_apply, smul_eq_mul]
  have ψρ : ∀ {T : Over S} (x : T ⟶ A) v m, (x ≫ ψ v) ≫ ρ m = x ≫ ψ (m *ᵥ v) := fun x v m =>
    ext _ _ fun u => by
      rw [hψ', Category.assoc, hρ, List.prod_ofFn, comp_prod_zpow]
      simp only [hψ', ← _root_.zpow_mul, prod_zpow_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have ρdec : ∀ m, ρ m = ∏ v, pr v ≫ ψ (m *ᵥ Pi.single v 1) := fun m =>
    ext _ _ fun u => by
      rw [hρ, List.prod_ofFn, prod_comp_hom]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hψ']
      simp
  have iddec : 𝟙 G = ∏ v, pr v ≫ ψ (Pi.single v 1) :=
    ext _ _ fun u => by
      rw [Category.id_comp, prod_comp_hom, Finset.prod_eq_single u (fun b _ hb => by
        rw [hψ', Pi.single_eq_of_ne' hb, zpow_zero]) (by simp), hψ', Pi.single_eq_same, zpow_one]
  have lamL := fun {T : Over S} (x y z : T ⟶ G) => lam_mul_left hL hΘ x y z
  obtain ⟨l, hl⟩ : ∃ l, l = cls L hL := ⟨_, rfl⟩
  rw [← hl] at lamL
  have lamR : ∀ {T : Over S} (x y z : T ⟶ G), lam l z (x * y) = lam l z x + lam l z y := fun x y z => by
    rw [lam_comm, lamL, lam_comm l x, lam_comm l y]
  have adj : ∀ {T : Over S} (x y : T ⟶ G) m m', m.transpose * B = B * m' →
      lam l (x ≫ ρ m) y = lam l x (y ≫ ρ m') := by
    intro T x y m m' hm
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj m m' hm)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, ← hl] using h'
  obtain ⟨p, hp⟩ : ∃ p : ∀ {T : Over S}, (T ⟶ A) → (T ⟶ A) → Pic T.left,
      ∀ {T : Over S} (x y : T ⟶ A), p x y = lam l (x ≫ ψ u₀) (y ≫ ψ u₁) := ⟨_, fun _ _ => rfl⟩
  have pL : ∀ {T : Over S} (x x' y : T ⟶ A), p (x * x') y = p x y + p x' y := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamL]
  have pR : ∀ {T : Over S} (x x' y : T ⟶ A), p y (x * x') = p y x + p y x' := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamR]
  have key : ∀ {T : Over S} (x y : T ⟶ A) v v', lam l (x ≫ ψ v) (y ≫ ψ v') = (v ⬝ᵥ B *ᵥ v') • p x y := by
    intro T x y v v'
    have h := adj (x ≫ ψ u₀) (y ≫ ψ v') (vecMulVec v u₀) (vecMulVec u₁ (B *ᵥ v)) (by
      rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hu₁, ← Matrix.mulVec_transpose, hBs])
    have e₁ : vecMulVec v u₀ *ᵥ u₀ = v := by
      rw [Matrix.vecMulVec_mulVec, h00]; simp
    have e₂ : vecMulVec u₁ (B *ᵥ v) *ᵥ v' = (v ⬝ᵥ B *ᵥ v') • u₁ := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_comm, hsymB v' v]; simp
    rw [ψρ, ψρ, e₁, e₂, ψsmul, ← hp] at h
    rw [h]
    exact map_zpow_add (fun z => p x z) (fun a b => pR a b x) y _
  have pS : ∀ {T : Over S} (x y : T ⟶ A), p y x = p x y := fun x y => by
    rw [hp, lam_comm, key, hsymB, hu₁, h00, one_smul]
  have hP : (cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L).IsLB := LB.isLB_linComb hL _ _
  have hc : cls _ hP = p (fst A A) (snd A A) := by rw [cls_cube_two hL, hp, hl]
  have hpull : ∀ {T : Over S} (x y : T ⟶ A), pull (lift x y).left (cls _ hP) = p x y := fun x y => by
    rw [hc, hp, hp, pull_lam, lift_fst_assoc, lift_snd_assoc]
  refine ⟨cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L, hP, ?_, ?_, ?_, fun T x x' y => ⟨?_, ?_⟩, ?_⟩
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_left]
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_right]
  · refine (cls_eq_iff hP (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hc, pS]
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pL]
    abel
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pR]
    abel
  · refine (cls_eq_iff hL (LB.isLB_linComb hP _ _)).1 ?_
    have hw : B * (B⁻¹ * W) = W := by rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
    have h := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 (hprim _ hw)).trans (cls_cube_two hL _ _ _)
    rw [cls_linComb hP, h, ← hl, Fintype.sum_prod_type, iddec, ρdec,
      map_prod_add (fun z => lam l z _) (fun a b => lamL a b _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_prod_add (fun z => lam l _ z) (fun a b => lamR a b _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [key, hpull, Matrix.mulVec_mulVec, hw]
    congr 1
    simp

end GlobalTheory.EighthPower
