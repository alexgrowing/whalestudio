import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilDown

def qf (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) : ℤ := ∑ u, ∑ u', W u u' * (v u * v u')

theorem sum_symm (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) :
    ∑ u, ∑ u', (W + W.transpose) u u' * (v u * v u') = 2 * qf W v := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, two_mul, qf]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem qf_nonneg {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) (v : Fin 8 → ℤ) : 0 ≤ qf W v := by
  have h := hW.1.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  have e : (((2 * qf W v : ℤ)) : ℝ) = star (fun i => (v i : ℝ)) ⬝ᵥ
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)) := by
    rw [← sum_symm]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← e] at h
  have : (0 : ℤ) ≤ 2 * qf W v := by exact_mod_cast h
  omega

theorem qf_add (W : Matrix (Fin 8) (Fin 8) ℤ) (a b : Fin 8 → ℤ) :
    qf W (a + b) = qf W a + qf W b + b ⬝ᵥ (W + W.transpose).mulVec a := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply, Pi.add_apply, add_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e₁ : ∑ u, ∑ u', W u u' * (b u * a u') = ∑ u, ∑ u', b u * (W u u' * a u') :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e₂ : ∑ u, ∑ u', W u u' * (a u * b u') = ∑ u, ∑ u', b u * (W u' u * a u') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e₁, e₂]
  ring

theorem exists_qf_one {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ a b, qf W (a + b) = qf W a + qf W b + 1 := by
  refine ⟨(W + W.transpose).adjugate.mulVec (Pi.single 0 1), Pi.single 0 1, ?_⟩
  rw [qf_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hW.2]
  simp

theorem eq_of_zpow_qf {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) {U : Type*} [CommGroup U] (a b : U)
    (h : ∀ v, a ^ qf W v = b ^ qf W v) : a = b := by
  obtain ⟨v, w, e⟩ := exists_qf_one hW
  have := h (v + w)
  rw [e, zpow_add, zpow_add, zpow_add, zpow_add, h v, h w, zpow_one, zpow_one] at this
  exact mul_left_cancel this

theorem omegaStd_smul {h : ℕ} (m n : ℤ) (x y : Fin h ⊕ Fin h → ℤ) :
    omegaStd (m • x) (n • y) = m * n * omegaStd x y := by
  simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

section Pairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} {T T' : Over S}

def q (π : Pic (A ⊗ A).left) (a b : T ⟶ A) : Pic T.left := pull (lift a b).left π

theorem qp (π : Pic (A ⊗ A).left) (t : T' ⟶ T) (a b : T ⟶ A) : pull t.left (q π a b) = q π (t ≫ a) (t ≫ b) := by
  rw [q, q, ← pull_comp, ← Over.comp_left, comp_lift]

theorem q_comm {π : Pic (A ⊗ A).left} (e : π = pull (lift (snd A A) (fst A A)).left π) (a b : T ⟶ A) :
    q π a b = q π b a := by
  have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
  rw [q, q, ← k, pull_comp, ← e]

variable [GrpObj A]

theorem q_mul {P : LB (A ⊗ A).left} (hP : P.IsLB) (a a' b : T ⟶ A)
    (h : ∃ t : (LB.LinComb P (K := Fin 3) ![(lift (a * a') b).left, (lift a b).left, (lift a' b).left]
      ![1, -1, -1]).Gen, t.IsGen) : q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 h
  rw [cls_linComb hP, Fin.sum_univ_three] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
  rw [← sub_eq_zero, ← e, q, q, q]
  abel

theorem cls_theta {D : LB A.left} (hD : D.IsLB) (k : ℤ) (x : T ⟶ A) (h : (Out.thetaLB A D k x).IsLB) :
    cls _ h = k • pull (snd T A).left (cls D hD) + (-k) • pull ((fst T A ≫ x) * snd T A).left (cls D hD) := by
  refine (cls_linComb hD _ _ h).trans ?_
  rw [Fin.sum_univ_two]
  rfl

variable [IsCommMonObj A]

theorem q_zpow {π : Pic (A ⊗ A).left} (ql : ∀ a a' b : T ⟶ A, q π (a * a') b = q π a b + q π a' b)
    (a b : T ⟶ A) (n : ℤ) : q π (a ^ n) b = n • q π a b := by
  have := BilinCalc.map_prod_zpow (fun z => q π z b) (fun s t => ql s t b) (fun _ : Fin 1 => a) (fun _ => n)
  simpa using this

theorem exists_theta {π : Pic (A ⊗ A).left} {D : LB A.left} (hD : D.IsLB) (cD : cls D hD = q π (𝟙 A) (𝟙 A))
    (ql : ∀ a a' b : T ⊗ A ⟶ A, q π (a * a') b = q π a b + q π a' b) (qs : ∀ a b : T ⊗ A ⟶ A, q π a b = q π b a)
    (k : ℕ) (x : T ⟶ A) (hx : x ^ k = 1) (h0 : q π x x = 0) : ∃ θ : Out.ThetaGrp A D k T, θ.pt = x := by
  have hz : cls (Out.thetaLB A D k x) (LB.isLB_linComb hD _ _) = 0 := by
    have e₁ : q π (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← qp, h0, map_zero]
    have e₂ : (k : ℤ) • q π (fst T A ≫ x) (snd T A) = 0 := by
      rw [← q_zpow ql, zpow_natCast, ← MonObj.comp_pow, hx, MonObj.comp_one, ← zpow_zero 1, q_zpow ql, zero_smul]
    refine (cls_theta hD _ _ _).trans ?_
    rw [cD, qp, qp, Category.comp_id, Category.comp_id, ql, qs (fst _ _ ≫ _), qs (snd _ _) (_ * _),
      ql, ql, e₁, qs (snd _ _) (fst _ _ ≫ _)]
    simp only [smul_add, neg_smul, e₂, smul_zero]
    abel
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hz
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Pairing

open GlobalTheory.CechPic in

theorem weilIs_diag : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  intro hG h k W S G A _ _ _ _ pr L P K _ p lev c hW hGab hA hpr hprod hL hP hsym hbi hLP hadd htor hweil x y
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have ql : ∀ {T : Over S} (a a' b : T ⟶ A), q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b :=
    fun {T} a a' b => q_mul hP a a' b (hbi T a a' b).1
  have qs : ∀ {T : Over S} (a b : T ⟶ A), q (cls P hP) a b = q (cls P hP) b a :=
    q_comm ((cls_eq_iff hP (pull_isLB hP _)).2 hsym)
  have cD : cls _ hD = q (cls P hP) (𝟙 A) (𝟙 A) := rfl
  have q0 : ∀ a b : Over.mk p ⟶ A, q (cls P hP) a b = 0 := fun a b =>
    (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 (DVR.exists_gen_of_local (V := K) P hP _ _)
  have lift_ : ∀ z, ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Over.mk p), θ.pt = lev z := fun z =>
    exists_theta hD cD ql qs k _ (htor z) (q0 _ _)
  have loc : ∀ z (s : (Over.mk p).left), ∃ V : (Over.mk p).left.Opens, s ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Out.overRes V), θ.pt = Out.overResι V ≫ lev z :=
    fun z s => by
      obtain ⟨θ, e⟩ := lift_ z
      obtain ⟨θ', e'⟩ := CommutatorPairing.exists_pull hD θ (Out.overResι ⊤)
      exact ⟨⊤, trivial, θ', by rw [e', e]⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (loc x) (loc y)
  suffices c₀ = c ^ (2 * omegaStd x y) from this ▸ hc₀
  refine eq_of_zpow_qf hW _ _ fun v => ?_
  have levz : ∀ z (n : ℤ), lev (n • z) = lev z ^ n := fun z n => by
    let F : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun w => lev w.toAdd) fun a b => hadd _ _
    exact map_zpow F (Multiplicative.ofAdd z) n
  obtain ⟨ψ, hψ, -⟩ := hprod A fun u => 𝟙 A ^ v u
  have ext : ∀ {T : Over S} (a b : T ⟶ G), (∀ u, a ≫ pr u = b ≫ pr u) → a = b := fun {T} a b e =>
    (hprod T fun u => b ≫ pr u).unique e fun _ => rfl
  have hc : ∀ {T : Over S} (a : T ⟶ A) u, (a ≫ ψ) ≫ pr u = a ^ v u := fun a u => by
    rw [Category.assoc, hψ, GrpObj.comp_zpow, Category.comp_id]
  have hmon : IsMonHom ψ := by
    constructor
    · refine ext _ _ fun u => ?_
      have e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1 := by rw [Hom.one_def]; simp
      rw [hc, IsMonHom.one_hom, e₁, one_zpow]
    · refine ext _ _ fun u => ?_
      have e₁ : μ[A] = fst A A * snd A A := by rw [Hom.mul_def]; simp
      have e₂ : (ψ ⊗ₘ ψ) ≫ μ[G] = (fst A A ≫ ψ) * (snd A A ≫ ψ) := by rw [Hom.mul_def]; congr 1
      rw [hc, e₁, e₂, MonObj.mul_comp, hc, hc, mul_zpow]
  have hd : ((qf W v).toNat : ℤ) = qf W v := Int.toNat_of_nonneg (qf_nonneg hW v)
  have hn : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat).IsLB := LB.isLB_linComb hD _ _
  have hiso : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat) (L.pull ψ.left) := by
    rw [← cls_eq_iff hn (pull_isLB hL _), cls_lbPow hD, cD, cls_pull hL,
      (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP, cls_linComb hP, map_sum, ← natCast_zsmul, hd, qf,
      ← Fintype.sum_prod_type', Finset.sum_smul]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg _ (qp (cls P hP) ψ (pr uv.1) (pr uv.2))).symm
    rw [hψ, hψ, q_zpow ql, qs _ (_ ^ _), q_zpow ql, smul_smul, smul_smul, _root_.mul_assoc]
  have key := (weilIs_along_hom hG S A G ψ _ L _ k _ (lev x) (lev y) c₀ _ hA hGab hD hL hmon hiso
    (hweil (fun u => v u • x) (fun u => v u • y) _ _ (fun u => by rw [hc, levz]) (fun u => by rw [hc, levz]))).2 hc₀
  rw [← hd, zpow_natCast, ← key, hd, ← zpow_mul]
  congr 1
  have e : ∀ a b : ℤ, a * (b * omegaStd x y) = a * b * omegaStd x y := fun a b => (_root_.mul_assoc _ _ _).symm
  simp only [omegaStd_smul, e, ← Finset.sum_mul]
  rw [sum_symm]
  ring

end GlobalTheory.WeilDown
