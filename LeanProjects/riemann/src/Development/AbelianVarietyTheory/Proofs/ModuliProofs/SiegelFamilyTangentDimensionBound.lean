import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SharpRelations
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmCommutantKroneckerLeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PowerTangent

theorem comp_prod_zpow {S : Scheme.{0}} {A C T : Over S} [GrpObj C] [IsCommMonObj C] {n : ℕ} (pr : Fin n → (A ⟶ C))
    (x : T ⟶ A) (m : Fin n → ℤ) : x ≫ ∏ v, pr v ^ m v = ∏ v, (x ≫ pr v) ^ m v :=
  (map_prod (preHom (G := C) x) _ _).trans (Finset.prod_congr rfl fun _ _ => map_zpow (preHom (G := C) x) _ _)

section Bundle

open GlobalTheory.CechPic

theorem cls_cube_two {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.ulift.symm.sum_comp]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := mul_one x
  have p₂ : psum A ![x, y] {1} = y := mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (mul_one y)
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]
  rw [Finset.card_pair (by decide)]
  simp
  abel

theorem polar_sum {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n : ℕ} (x y : Fin n → G)
    (W : Matrix (Fin n) (Fin n) ℤ) :
    ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.1 * y uv.1) (x uv.2 * y uv.2) -
      ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.1) (x uv.2) - ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (y uv.1) (y uv.2) +
      ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B 1 1 = ∑ u, ∑ v, (W + W.transpose) u v • B (x u) (y v) := by
  have hB' : ∀ x y y', B x (y * y') = B x y + B x y' := fun a b c => by simp only [hs a, hB]
  have h1 : B 1 1 = 0 := by simpa using hB 1 1 1
  have e : ∑ u, ∑ v, W v u • B (x u) (y v) = ∑ u, ∑ v, W u v • B (y u) (x v) := by
    rw [Finset.sum_comm]; simp only [hs (x _)]
  simp only [hB, hB', h1, smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type, Matrix.add_apply, add_smul,
    Matrix.transpose_apply, smul_zero, Finset.sum_const_zero, e]
  abel

theorem sum_matrix {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n : ℕ} (x y : Fin n → G)
    (E m : Matrix (Fin n) (Fin n) ℤ) :
    ∑ u, ∑ v, E u v • B (∏ i, x i ^ m u i) (y v) = ∑ u, ∑ v, (m.transpose * E) u v • B (x u) (y v) ∧
    ∑ u, ∑ v, E u v • B (x u) (∏ i, y i ^ m v i) = ∑ u, ∑ v, (E * m) u v • B (x u) (y v) := by
  have h₁ : ∀ (c : Fin n → ℤ) z, B (∏ i, x i ^ c i) z = ∑ i, c i • B (x i) z := fun c z =>
    GlobalTheory.BilinCalc.map_prod_zpow (fun a => B a z) (fun a b => hB a b z) x c
  have h₂ : ∀ (c : Fin n → ℤ) z, B z (∏ i, y i ^ c i) = ∑ i, c i • B z (y i) := fun c z =>
    GlobalTheory.BilinCalc.map_prod_zpow (fun a => B z a) (fun a b => by simp only [hs z, hB]) y c
  simp only [h₁, h₂, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  constructor
  · rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

theorem adjoint_and_diag (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {o : Type} [CommRing o] {s : S ⟶ Sp o} {h k : ℕ} {ζ : o}
    (c : SiegPre h k ζ s) (hc : c.Principal) {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A ⟶ c.A)) (hpr : ∀ u, IsMonHom (pr u))
    (iso : LBIso L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)))
    (m : Matrix (Fin 8) (Fin 8) ℤ) (α : A ⟶ A) (hα : ∀ u, α ≫ pr u = ∏ v, pr v ^ m u v) :
    ((W + W.transpose) * m = W → LBIso L (cubeLB A ![𝟙 A, α] L)) ∧
      ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : A ⟶ A), (∀ u, α' ≫ pr u = ∏ v, pr v ^ m' u v) →
        m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
        LBIso (cubeLB A ![fst A A ≫ α, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ α'] L) := by
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab (pull_isLB c.isLB _) hc.1 c.P c.isLB c.rig₁ c.rig₂
  let B : ∀ {T : Over S}, (T ⟶ c.A) → (T ⟶ c.A) → Pic T.left := fun a b => pull (lift a b).left (cls c.P c.isLB)
  have hB : ∀ {T : Over S} (a a' b : T ⟶ c.A), B (a * a') b = B a b + B a' b := fun {T} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 (hbi T a a' b).1
    rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [B]
    abel
  have hs : ∀ {T : Over S} (a b : T ⟶ c.A), B a b = B b a := fun {T} a b => by
    have e : cls c.P c.isLB = pull (lift (snd c.A c.A) (fst c.A c.A)).left (cls c.P c.isLB) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    have k : (lift b a).left ≫ (lift (snd c.A c.A) (fst c.A c.A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls c.P c.isLB) = pull (lift b a).left (cls c.P c.isLB)
    rw [← k, pull_comp, ← e]
  have hQ : ∀ {T : Over S} (x : T ⟶ A),
      pull x.left (cls L hL) = ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • B (x ≫ pr uv.1) (x ≫ pr uv.2) := fun x => by
    rw [(cls_eq_iff hL (LB.isLB_linComb c.isLB _ _)).2 iso, cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  have hC : ∀ {T : Over S} (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB),
      cls _ h = ∑ u, ∑ v, (W + W.transpose) u v • B (x ≫ pr u) (y ≫ pr v) := fun x y h => by
    rw [cls_cube_two hL, hQ, hQ, hQ, hQ]
    simp only [MonObj.mul_comp, MonObj.one_comp]
    exact polar_sum B hB hs (fun u => x ≫ pr u) (fun u => y ≫ pr u) W
  refine ⟨fun hm => ?_, fun m' α' hα' hm => ?_⟩
  · refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (hC _ _ _).symm)
    simp only [hα, Category.id_comp]
    rw [(sum_matrix B hB hs pr pr _ m).2, hm, ← pull_id (cls L hL)]
    simpa only [Category.id_comp, Fintype.sum_prod_type, Over.id_left] using hQ (𝟙 A)
  · refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((hC _ _ _).trans (Eq.trans ?_ (hC _ _ _).symm))
    simp only [Category.assoc, hα, hα', comp_prod_zpow]
    rw [(sum_matrix B hB hs (fun v => fst A A ≫ pr v) (fun v => snd A A ≫ pr v) _ m).1,
      (sum_matrix B hB hs (fun v => fst A A ≫ pr v) (fun v => snd A A ≫ pr v) _ m').2, hm]

end Bundle

section Linear

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}

def matrixRep {N : Type} [AddCommGroup N] (π : Fin n → (V →+ N)) (hπ : ∀ y y', (∀ u, π u y = π u y') → y = y')
    (F : Matrix (Fin n) (Fin n) ℤ → Module.End K V) (hF : ∀ M u y, π u (F M y) = ∑ v, M u v • π v y) :
    Matrix (Fin n) (Fin n) ℤ →+* Module.End K V where
  toFun := F
  map_one' := LinearMap.ext fun y => hπ _ _ fun u => by simp [hF, Matrix.one_apply]
  map_mul' M M' := LinearMap.ext fun y => hπ _ _ fun u => by
    simp only [hF, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  map_zero' := LinearMap.ext fun y => hπ _ _ fun u => by simp [hF]
  map_add' M M' := LinearMap.ext fun y => hπ _ _ fun u => by simp [hF, add_smul, Finset.sum_add_distrib]

theorem exists_basis_matrixRep [Module.Finite K V] {h : ℕ} (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ →+* Module.End K V)
    (hd : Module.finrank K V = (n + 1) * h) :
    ∃ b : Module.Basis (Fin (n + 1) × Fin h) K V, ∀ M j l, ρ M (b (j, l)) = ∑ i, (M i j : K) • b (i, l) := by
  let e : Fin (n + 1) → Fin (n + 1) → Module.End K V := fun u v => ρ (Matrix.single u v 1)
  have he : ∀ u v v' w y, e u v (e v' w y) = if v = v' then e u w y else 0 := fun u v v' w y => by
    rw [← Module.End.mul_apply, ← map_mul]
    split_ifs with hv
    · subst hv; simp [e]
    · simp [hv]
  have hs : ∀ y, ∑ u, e u u y = y := fun y => by
    rw [← LinearMap.sum_apply, ← map_sum, Matrix.sum_single_one, map_one, Module.End.one_apply]
  let V₀ := LinearMap.range (e 0 0)
  have h₀ : ∀ z : V₀, e 0 0 z = z := by
    rintro ⟨_, y, rfl⟩
    simp [he]
  let Φ : (Fin (n + 1) → V₀) ≃ₗ[K] V := LinearEquiv.ofLinear
    (∑ u, e u 0 ∘ₗ V₀.subtype ∘ₗ LinearMap.proj u)
    (LinearMap.pi fun u => (e 0 u).codRestrict V₀ fun y => ⟨e 0 u y, by simp [he]⟩)
    (LinearMap.ext fun y => by
      refine (LinearMap.sum_apply _ _ _).trans (Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (hs y))
      exact (he u 0 0 u y).trans (if_pos rfl))
    (LinearMap.ext fun z => funext fun u => Subtype.ext (by
      show e 0 u ((∑ u, e u 0 ∘ₗ V₀.subtype ∘ₗ LinearMap.proj u : (Fin (n + 1) → V₀) →ₗ[K] V) z) = z u
      simp [he, h₀]))
  have hΦ : ∀ z, Φ z = ∑ u, e u 0 (z u) := fun z => by simp [Φ]
  have hr : Module.finrank K V₀ = h := by
    have := Φ.finrank_eq
    rw [Module.finrank_pi_fintype, hd] at this
    simpa using this
  let b₀ := Module.finBasisOfFinrankEq K V₀ hr
  let b := ((Pi.basis fun _ : Fin (n + 1) => b₀).map Φ).reindex (Equiv.sigmaEquivProd _ _)
  have hb : ∀ j l, b (j, l) = e j 0 (b₀ l) := fun j l => by
    simp only [b, Module.Basis.reindex_apply, Module.Basis.map_apply, hΦ, Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply]
    rw [Finset.sum_eq_single j] <;> simp +contextual [Pi.single_eq_of_ne]
  refine ⟨b, fun M j l => ?_⟩
  have hM : M * Matrix.single j 0 1 = ∑ i, M i j • Matrix.single i (0 : Fin (n + 1)) (1 : ℤ) := by
    ext p q
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp only [hb, e]
  rw [← Module.End.mul_apply, ← map_mul, hM, map_sum, LinearMap.sum_apply]
  simp only [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

end Linear

section Lie

open GlobalTheory.Serre GlobalTheory.SharpRel

theorem isMonHom_of_matrix {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C] {n : ℕ}
    (pr : Fin n → (A ⟶ C)) (hpr : ∀ u, IsMonHom (pr u))
    (hinj : ∀ (T : Over S) (y y' : T ⟶ A), (∀ u, y ≫ pr u = y' ≫ pr u) → y = y')
    (m : Matrix (Fin n) (Fin n) ℤ) (f : A ⟶ A) (hf : ∀ u, f ≫ pr u = ∏ v, pr v ^ m u v) : IsMonHom f :=
  isMonHom_of_mul_comp _ fun T x y => hinj _ _ _ fun u => by
    simp only [Category.assoc, MonObj.mul_comp, hf, comp_prod_zpow, mul_zpow, Finset.prod_mul_distrib]

theorem exists_isLieBasis_kronecker {K : Type} [Field K] {S : Scheme.{0}} {A C : Over S} {A₀ : Over (Sp K)} [GrpObj A]
    [GrpObj C] [IsCommMonObj C] [GrpObj A₀] [IsCommMonObj A₀] {x : Sp K ⟶ S} {φ : A₀.left ⟶ A.left}
    (hφ : IsGrpPullback A₀ A x φ) {n h : ℕ} (pr : Fin (n + 1) → (A ⟶ C)) (hpr : ∀ u, IsMonHom (pr u))
    (hinj : ∀ (T : Over S) (y y' : T ⟶ A), (∀ u, y ≫ pr u = y' ≫ pr u) → y = y')
    (f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ → (A ⟶ A)) (hf : ∀ m u, f m ≫ pr u = ∏ v, pr v ^ m u v)
    (hd : SmoothOfRelativeDimension ((n + 1) * h) A₀.hom) :
    ∃ (v : Fin ((n + 1) * h) → (epsR K ⟶ A₀)) (f₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ → (A₀ ⟶ A₀)),
      IsLieBasis v ∧ (∀ m, (f₀ m).left ≫ φ = φ ≫ (f m).left) ∧ ∀ m j,
        IsLieComb (fun i => Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kronecker (m.map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)) i j) v (v j ≫ f₀ m) := by
  let f₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ → (A₀ ⟶ A₀) := fun m =>
    Over.homMk (hφ.1.lift (φ ≫ (f m).left) A₀.hom (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have h₀ : ∀ m, (f₀ m).left ≫ φ = φ ≫ (f m).left := fun m => hφ.1.lift_fst _ _ _
  have hm : ∀ m, IsMonHom (f₀ m) := fun m =>
    haveI := isMonHom_of_matrix pr hpr hinj m (f m) (hf m)
    isMonHom_of_mul_comp _ fun T y y' => push_inj hφ (by
      simp only [map_mul, push_comp hφ (h₀ m), MonObj.mul_comp])
  let π : Fin (n + 1) → (Lie (intAct A₀) →+ Additive (Over.mk ((epsR K).hom ≫ x) ⟶ C)) := fun u =>
    AddMonoidHom.mk' (fun y => Additive.ofMul (pushHom hφ _ y.hom ≫ pr u)) fun y y' => by
      rw [Lie.hom_add, map_mul, MonObj.mul_comp, ofMul_mul]
  have hπ : ∀ u y, π u y = Additive.ofMul (pushHom hφ _ y.hom ≫ pr u) := fun _ _ => rfl
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis A₀ hd
  let b₀ := Lie.basis (intAct A₀) hv₀
  haveI := Module.Finite.of_basis b₀
  obtain ⟨b, hb⟩ := exists_basis_matrixRep (h := h) (matrixRep π
    (fun y y' e => Lie.ext (push_inj hφ (hinj _ _ _ fun u => Additive.ofMul.injective (e u))))
    (fun m => Lie.map (intAct A₀) (intAct A₀) (f₀ m)) fun m u y => by
      simp only [hπ, Lie.hom_map, push_comp hφ (h₀ m), Category.assoc, hf, comp_prod_zpow, ofMul_prod, ofMul_zpow])
    (by rw [Module.finrank_eq_card_basis b₀, Fintype.card_fin])
  refine ⟨fun i => (b.reindex finProdFinEquiv i).hom, f₀, Lie.isLieBasis_basis _, h₀, fun m j => ?_⟩
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [Lie.isLieComb_iff, ← finProdFinEquiv.sum_comp]
  refine (congrArg Lie.hom ?_ : (Lie.map (intAct A₀) (intAct A₀) (f₀ m) _).hom = _)
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  refine (hb m j l).trans ?_
  simp [Fintype.sum_prod_type, Matrix.one_apply, ite_smul]

end Lie

open GlobalTheory.CechPic in

theorem cls_cube_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {T : Over S} {T' : Over S'}
    (U : Over.mk (T'.hom ≫ f) ⟶ T) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : a'.left ≫ φ = U.left ≫ a.left)
    (hb : b'.left ≫ φ = U.left ≫ b.left) :
    cls (cubeLB G' ![a', b'] L') (LB.isLB_linComb hL' _ _) =
      pull U.left (cls (cubeLB G ![a, b] L) (LB.isLB_linComb hL _ _)) := by
  refine (cls_linComb hL' _ _ _).trans (Eq.trans ?_ (congrArg _ (cls_linComb hL _ _ _)).symm)
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, (cls_eq_iff hL' (pull_isLB hL _)).2 H, cls_pull hL, ← pull_comp, ← pull_comp,
    psum_push h _ ![a, b] U (fun i => by
      fin_cases i
      exacts [Over.OverMorphism.ext ha, Over.OverMorphism.ext hb]) I.down]

open GlobalTheory.CechPic GlobalTheory.SharpRel in

theorem prim_pull {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {w w' : J} {S S' : Scheme.{0}}
    {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {f : S' ⟶ S} {t : TObj g k J b s} {t' : TObj g k J b s'} (m : TMap t' t f)
    (H : t.Prim w w') : t'.Prim w w' := by
  obtain ⟨φ, h, hL, -, hact⟩ := m
  letI := t.ab.comm
  letI := t'.ab.comm
  refine ⟨push_inj h ?_, ?_, ?_⟩
  · have e : ∀ j, pushHom h _ (t'.act j) = pushHom h _ (𝟙 t'.A) ≫ t.act j := fun j => by
      rw [← push_comp h (hact j), Category.id_comp]
    rw [map_mul, e, e, ← MonObj.comp_mul, H.1, Category.comp_id]
  · let U := lift (pushPt h.1.w (fst t'.A t'.A)) (pushPt h.1.w (snd t'.A t'.A))
    have e₁ : (fst t'.A t'.A).left ≫ φ = U.left ≫ (fst t.A t.A).left :=
      congrArg (fun q => q.left) (lift_fst _ _ : U ≫ _ = _).symm
    have e₂ : (snd t'.A t'.A).left ≫ φ = U.left ≫ (snd t.A t.A).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : U ≫ _ = _).symm
    refine (cls_eq_iff (LB.isLB_linComb t'.isLB _ _) (LB.isLB_linComb t'.isLB _ _)).1
      ((cls_cube_push h t.isLB t'.isLB hL U ?_ e₂).trans ((congrArg _ ((cls_eq_iff _ _).2 H.2.1)).trans
        (cls_cube_push h t.isLB t'.isLB hL U e₁ ?_).symm))
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, e₁, Category.assoc]
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, e₂, Category.assoc]
  · let U : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk φ h.1.w
    refine (cls_eq_iff t'.isLB (LB.isLB_linComb t'.isLB _ _)).1
      (((cls_eq_iff t'.isLB (pull_isLB t.isLB _)).2 hL).trans
        ((congrArg (pull φ) ((cls_eq_iff t.isLB _).2 H.2.2)).trans
        (cls_cube_push h t.isLB t'.isLB hL U ((Category.id_comp _).trans (Category.comp_id _).symm) (hact w)).symm))

theorem tmap_constPt (L1 : Out.Laws) (L2 : Out.Laws2)
    (hT : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {g k : ℕ} {J : Type} {w w' : J} {o : Type} [CommRing o] {b : TBase o k} {K : Type} [Field K] {r : ℕ} {β : o →+* K}
    (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (ht : t.Prim w w')
    (t₀ : TObj g k J b (spMap β)) (φ₀ : t₀.A.left ⟶ t.A.left)
    (hφ : IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀)
    (hL : LBIso t₀.L (t.L.pull φ₀))
    (hp : ∀ i, (t₀.pt i).left ≫ φ₀ = spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom ≫ (t.pt i).left)
    (ha : ∀ j, (t₀.act j).left ≫ φ₀ = φ₀ ≫ (t.act j).left) (lam : (Fin r → K) →ₗ[K] K)
    (H : ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ t.A.left), IsGrpPullback G t.A (spMap (dirMap lam)) ψ →
      ∃ ψ₀ : G.left ⟶ t₀.A.left, IsGrpPullback G t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧
        ∀ io : t₀.A.left ⟶ G.left, io ≫ ψ = φ₀ →
          io ≫ G.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _) :
    ∃ t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β)),
      TMap t' t (spMap (dirMap lam)) ∧ TMap t' t (constPt (spMap (dirMap lam))) := by
  have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun z => by simp [dirMap]))
  obtain ⟨t', m'⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ (spMap ((algebraMap K (DualNumber K)).comp β)) (spMap (dirMap lam)) t
    ((spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun z => by simp [dirMap])))
  refine ⟨t', m', ?_⟩
  have hp' := prim_pull m' ht
  obtain ⟨ψ, hψ, hψL, hψp, hψa⟩ := m'
  obtain ⟨ψ₀, hψ₀, hio⟩ := H t'.A ψ hψ
  let io : t₀.A.left ⟶ t'.A.left := hψ.1.lift φ₀ (t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
    (by rw [Category.assoc, e, hφ.1.w])
  have i₁ : io ≫ ψ = φ₀ := hψ.1.lift_fst _ _ _
  have i₂ : io ≫ t'.A.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := hψ.1.lift_snd _ _ _
  have key := GlobalTheory.T.thetaLevelAbelianScheme_const_over_dualNumbers L1 L2 hT o g k J b w w' K _ _ t' t₀ io ψ₀ hp' (hψ.cancel (hφ.congr e.symm i₁.symm) i₂)
    (by
      refine (GlobalTheory.CechPic.cls_eq_iff t₀.isLB (pull_isLB t'.isLB _)).1 ?_
      rw [(GlobalTheory.CechPic.cls_eq_iff t₀.isLB (pull_isLB t.isLB _)).2 hL, GlobalTheory.CechPic.cls_pull t'.isLB,
        (GlobalTheory.CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB _)).2 hψL, GlobalTheory.CechPic.cls_pull t.isLB,
        GlobalTheory.CechPic.cls_pull t.isLB, ← GlobalTheory.CechPic.pull_comp, i₁])
    (fun i => hψ.1.hom_ext
      (by rw [Category.assoc, i₁, hp, Category.assoc, hψp, ← Category.assoc, e])
      (by
        rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm))
    (fun j => hψ.1.hom_ext
      (by rw [Category.assoc, i₁, ha, Category.assoc, hψa, ← Category.assoc, i₁])
      (by rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w, i₂]))
    hψ₀ (hio io i₁ i₂)
  have := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ ⟨φ₀, hφ, hL, hp, ha⟩).1 key
  rwa [← e] at this

theorem main : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (w w' : J), (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (c : SiegPre h k (b.ζ : o) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → IsSharp W a bas t c → (∀ (lam : (Fin r → K) →ₗ[K] K) (t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β))), TMap t' t (spMap (dirMap lam)) → TMap t' t (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro L1 L2 hT h g W J a bas hW _ w w' hw hw' k o _ b K _ _ r β t c hc ⟨pr, hpr, hu, hL, ha, _⟩ hun
  obtain rfl : g = 8 * h := by
    have := bas.finrank_eq
    simp [Module.finrank_pi_fintype] at this
    omega
  letI := t.ab.comm
  simp only [List.prod_ofFn] at ha
  have hinj : ∀ (T : Over _) (y y' : T ⟶ t.A), (∀ u, y ≫ pr u = y' ≫ pr u) → y = y' := fun T y y' e =>
    (hu T fun u => y' ≫ pr u).unique e fun _ => rfl
  have hsym : (W + W.transpose).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hdet : IsUnit (W + W.transpose).det := hW.2 ▸ isUnit_one
  have hadj := adjoint_and_diag L1.globalFns c hc t.isLB W pr hpr hL
  have hprim : t.Prim w w' := by
    have h₁ : a w + a w' = 1 := ((Matrix.isUnit_iff_isUnit_det _).2 hdet).mul_left_cancel (by
      rw [Matrix.mul_add, hw, hw', Matrix.mul_one])
    have h₂ : (a w).transpose * (W + W.transpose) = (W + W.transpose) * a w' := by
      have e := congrArg Matrix.transpose hw
      rw [Matrix.transpose_mul, hsym.eq] at e
      rw [hw', e]
    refine ⟨hinj _ _ _ fun u => ?_, (hadj _ _ (ha w)).2 _ _ (ha w') h₂, (hadj _ _ (ha w)).1 hw⟩
    rw [MonObj.mul_comp, ha, ha, ← Finset.prod_mul_distrib, Category.id_comp]
    simp only [← zpow_add, ← Matrix.add_apply, h₁, Matrix.one_apply]
    simp
  choose f hf using fun m : Matrix (Fin 8) (Fin 8) ℤ => (hu t.A fun u => ∏ v, pr v ^ m u v).exists
  obtain ⟨t₀, φ₀, hφ, hL₀, hp₀, ha₀⟩ := GlobalTheory.tObj_pull o _ k J b _ _ _ (spMap β)
    (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) t
    ((spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun z => by simp)))
  letI := t₀.ab.comm
  obtain ⟨v, f₀, hv, hf₀, hF⟩ := exists_isLieBasis_kronecker (n := 7) hφ pr hpr hinj f hf t₀.dim
  obtain ⟨Θ, hs, hcomm, hzero⟩ := GlobalTheory.T.exists_ksMatrix_alt L1 L2 hT K r t.pol t₀.pol φ₀ _ v hφ hL₀ hv
  let Θ' := (Matrix.reindexLinearEquiv K K finProdFinEquiv.symm finProdFinEquiv.symm).toLinearMap ∘ₗ Θ
  have hΘ : Function.Injective Θ' := by
    refine (Matrix.reindexLinearEquiv K K finProdFinEquiv.symm finProdFinEquiv.symm).injective.comp
      ((injective_iff_map_eq_zero Θ).2 fun lam h0 => ?_)
    obtain ⟨t', m₁, m₂⟩ := tmap_constPt L1 L2 hT t hprim t₀ φ₀ hφ hL₀ hp₀ ha₀ lam (hzero lam h0)
    exact hun lam t' m₁ m₂
  have hr : Module.finrank K (LinearMap.range Θ') = r := by
    rw [LinearMap.finrank_range_of_inj hΘ]
    simp
  rw [← hr]
  refine GlobalTheory.T.finrank_symm_commutant_kronecker_le K h (W + W.transpose) (W + W.transpose)⁻¹ _ hsym (Matrix.nonsing_inv_mul _ hdet) ?_
  rintro _ ⟨lam, rfl⟩
  refine ⟨(hs lam).submatrix _, fun u u' => ?_⟩
  have key := hcomm _ _ _ _ _ _ (isMonHom_of_matrix pr hpr hinj _ _ (hf _)) (isMonHom_of_matrix pr hpr hinj _ _ (hf _))
    (hf₀ _) (hf₀ _) ((hadj (Matrix.single u u' 1) _ (hf _)).2
      ((W + W.transpose)⁻¹ * (Matrix.single u u' (1 : ℤ)).transpose * (W + W.transpose)) _ (hf _)
      (by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet])) (hF _) (hF _) lam
  have key' := congrArg (fun M => Matrix.submatrix M finProdFinEquiv finProdFinEquiv) key
  simp only [← Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at key'
  exact key'

end GlobalTheory.PowerTangent
