import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBimultPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.PolTensBimult

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TensCub

theorem interchange {U X : Type} [CommGroup U] [AddCommGroup X] (t : X → X → U) (hs : ∀ u v, t u v = t v u)
    (hc : ∀ u u' v, t u' v * (t (u + u') v)⁻¹ * t u v = t v u' * (t (u + v) u')⁻¹ * t u u') (x x' y y' : X) :
    t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹ := by
  have h₁ := hc y y' (x + x')
  have h₂ := hc x' y' (x + y)
  have h₃ := hc x x' y
  rw [hs (y + y'), hs y' (x + x'), hs y (x + x')] at h₁
  rw [hs (x' + y'), hs y' (x + y), hs x' (x + y), show x' + (x + y) = y + (x + x') by abel] at h₂
  rw [hs y x'] at h₃
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  have k₃ := congrArg Additive.ofMul h₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k₁ k₂ k₃ ⊢
  rw [← sub_eq_zero] at k₁ k₂ k₃ ⊢
  have k := congrArg₂ (· - ·) (congrArg₂ (· - ·) k₂ k₁) k₃
  simp only [sub_zero] at k
  rw [← k]
  abel

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (h0 : t 0 0 = 1)
    (ht : ∀ x x' y y', t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  have hτ' : ∀ u v, τ' u v = O (u + v) * (O u)⁻¹ * (O v)⁻¹ * O 0 *
      ∏ i, ∏ j, (t (e u i + e u j) (e v i + e v j) * (t (e u i) (e v i))⁻¹ * (t (e u j) (e v j))⁻¹) ^ W i j := by
    intro u v
    rw [hτ, hr']
    simp only [hψ, map_add, Pi.add_apply, map_zero, Pi.zero_apply, h0, one_zpow, Finset.prod_const_one, ← ht (e u _) (e v _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ofMul_one]
    abel
  rw [eq_mul_inv_of_mul_eq hc, hτ', hτ', hτ']
  simp only [Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply,
    add_zero, h0]
  have e1 : ∀ i j, e a i + e a j + (e a' i + e a' j) = e a i + e a' i + (e a j + e a' j) := fun i j => by abel
  simp only [e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul, ofMul_one, smul_zero, Finset.sum_const_zero]
  abel

theorem cubV_prod (hG : GlobalFnsSt) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {M' : RigLB A} {M : RigLB B} (c' : CubicalStr A M') (c : CubicalStr B M) {N : Type} [Fintype N]
    (P : N → (A ⟶ B)) (hP : ∀ k, IsMonHom (P k)) (φ : N → (A.left ⟶ B.left)) (hφ : ∀ k, (P k).left = φ k) (n : N → ℤ)
    (w : LB.Iso M'.L (LB.LinComb M.L φ n)) (hw : w.IsGen) {T : Over S} (z : T.left) (J J') (hJ : Good M.L z J)
    (hJ' : Good M'.L z J') (x x' y : T ⟶ A) (om : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ)
    (hom : om = fun p => bwg w p.left z (fun k => J (p.left ≫ φ k)) (J' p.left)) :
    cubV c' z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y *
      (om 1)⁻¹) = ∏ k, cubV c z J (x ≫ P k) (x' ≫ P k) (y ≫ P k) ^ n k := by
  subst hom
  let ρ : N → ((G3 A).left ⟶ (G3 B).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ A (x3 A) a ≫ φ k = ρ k ≫ thφ B (x3 B) a := fun k a => by
    rw [← hφ k]
    letI := hP k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over S} (a b c : T ⟶ A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := φ) (εp := n) M.isLB M'.isLB w hw (ε := thε) hψ
    c'.isGen c.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV c' (T := 𝟙_ (Over S)) s I') := isCub_cubV c' hI'
      have C : IsCub (cubV c (T := 𝟙_ (Over S)) s I) := isCub_cubV c hI
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A) 1 1
        (fun q => bwg w q s (fun i => I (q ≫ φ i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := hP k
      have o : (1 : 𝟙_ (Over S) ⟶ A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ n k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg w q z (fun i => J (q ≫ φ i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ Q D' r W pr xe T hn a a' b
  obtain ⟨hpr, -, hcp, w, hw, hpsi⟩ := T
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.M.L y J :=
    ⟨fun ψ => (exists_chart Q.M.isLB (ψ y)).choose, fun ψ => (exists_chart Q.M.isLB (ψ y)).choose_spec⟩
  let P : (Fin r × Fin r) × Fin 4 → (D'.P.A ⟶ Q.B) := fun k => ![pr k.1.1 * pr k.1.2, pr k.1.1, pr k.1.2, 1] k.2
  have hPh : ∀ k, IsMonHom (P k) := by
    rintro ⟨⟨i, j⟩, m⟩
    have := hpr i
    have := hpr j
    fin_cases m
    · exact GlobalTheory.Serre.isMonHom_mul _ _
    · exact hpr i
    · exact hpr j
    · exact GlobalTheory.Serre.isMonHom_one
  have hPl : ∀ k, (P k).left = tensφ pr k := by
    rintro ⟨⟨i, j⟩, m⟩
    fin_cases m <;> rfl
  have key := cubV_prod hG D'.P.isAb D'.cub Q.cub P hPh (tensφ pr) hPl (tensε W) w hw (T := TK R) y J J' hJ hJ'
    (cP D' _ a) (cP D' _ a') (cP D' _ b) _ rfl
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left) * ∏ i, ∏ j, val (Q.tau (xe u i) (xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => hpsi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have c0 : cP D' (TK R) 0 = 1 := by
    have := cPoint_add D' (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hP : ∀ u k, cP D' (TK R) u ≫ P k = toUnit (TK R) ≫ Q.c (![xe u k.1.1 + xe u k.1.2, xe u k.1.1, xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ pr i = toUnit (TK R) ≫ Q.c (xe u i) := fun i => by
      rw [cP, Category.assoc, hcp]
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · show cP D' (TK R) u ≫ (pr i * pr j) = toUnit (TK R) ≫ Q.c (xe u i + xe u j)
      rw [MonObj.comp_mul, e, e, Q.c_add, MonObj.comp_mul]
    · exact e i
    · exact e j
    · show cP D' (TK R) u ≫ 1 = toUnit (TK R) ≫ Q.c 0
      rw [q0, MonObj.comp_one, MonObj.comp_one]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV Q.cub y J (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v) = val (Q.tau u v) (𝟙 _) y J * val (Q.tau u' v) (𝟙 _) y J * (val (Q.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← Q.tau_add u u' v y J hJ, mul_comm, inv_mul_cancel_left]
  have hI := interchange (fun u v => val (Q.tau u v) (𝟙 _) y J) (fun u v => Q.tau_symm u v y J hJ) (fun u u' v => by
    have := (isCub_cubV Q.cub hJ).s12 (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v)
    rw [hC, hC, _root_.mul_assoc, _root_.mul_assoc, mul_comm, mul_comm (val (Q.tau u _) (𝟙 _) y J)] at this
    first | exact this | exact this.symm)
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0] at key
  refine alg W xe
    (fun u => bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (Q.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b
    (Q.val_tau_zero 0 y J hJ) hI hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.PolTensBimult
