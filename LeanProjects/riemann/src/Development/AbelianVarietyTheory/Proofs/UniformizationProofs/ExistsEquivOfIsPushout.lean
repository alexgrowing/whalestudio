import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatSec

theorem exists_equiv_of_isPushout {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A A' : CommRingCat.{0}}
    [Algebra R A] (p : A ⟶ A') (s' : R' →+* A')
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R')) p
      (CommRingCat.ofHom s')) :
    ∃ e : R' ⊗[R] A ≃+ A', ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v := by
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra R' A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R R' A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  exact ⟨h.out.equiv.toAddEquiv, fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)⟩

theorem exists_comb_ker {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {I J : Type} [Fintype I] [Fintype J] {A : I → Type} {B : J → Type} {A' : I → Type} {B' : J → Type}
    [∀ a, AddCommGroup (A a)] [∀ a, Module R (A a)] [∀ b, AddCommGroup (B b)] [∀ b, Module R (B b)]
    [∀ a, AddCommGroup (A' a)] [∀ b, AddCommGroup (B' b)]
    (e : ∀ a, R' ⊗[R] A a ≃+ A' a) (e' : ∀ b, R' ⊗[R] B b ≃+ B' b) (d : (∀ a, A a) →ₗ[R] (∀ b, B b))
    (x : ∀ a, A' a)
    (hx : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ b, ∑ i, e' b (c i ⊗ₜ d (v i) b) = 0) :
    ∃ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) ∧ ∀ i, d (v i) = 0 := by
  classical
  obtain ⟨t, ht⟩ := (TensorProduct.piRight R R R' A).surjective (fun a => (e a).symm (x a))
  have key : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), t = ∑ i, c i ⊗ₜ v i →
      ∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a) := fun n c v h a => by
    have := congrFun ht a
    rw [h, map_sum, Finset.sum_apply, AddEquiv.eq_symm_apply, map_sum] at this
    rw [← this]
    rfl
  have h0 : d.lTensor R' t = 0 := by
    obtain ⟨n, c, v, h⟩ := TensorProduct.exists_sum_tmul_eq t
    apply (TensorProduct.piRight R R R' B).injective
    funext b
    apply (e' b).injective
    rw [map_zero, Pi.zero_apply, map_zero, ← hx n c v (key n c v h) b, h, map_sum, map_sum, Finset.sum_apply, map_sum]
    rfl
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map d) t).1 h0
  obtain ⟨n, c, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  refine ⟨n, c, fun i => (v i).1, key n c _ ?_, fun i => (v i).2⟩
  rw [← hw, map_sum]
  rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Z : Scheme.{0}}

theorem isPushout_app {g : R →+* R'} (hg : g.Flat) {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    IsPushout (CommRingCat.ofHom (cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (cst f' (π ⁻¹ᵁ U))) := by
  have : Flat (Spec.map (CommRingCat.ofHom g)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact hg
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst f U c) = gs r z ⊤ (cst f ⊤ c) := by
  rw [← rs_cst f (le_top : U ≤ ⊤) c]
  exact gs_res r z _ h _

theorem gs_comb (f' : X' ⟶ Spec (CommRingCat.of R')) (π : X' ⟶ X) (U : X.Opens) (z : X') (h : π z ∈ U) {n : ℕ}
    (c : Fin n → R') (v : Fin n → Γ(X, U)) :
    gs (𝟙 X') z (π ⁻¹ᵁ U) (∑ i, cst f' (π ⁻¹ᵁ U) (c i) * (π.app U).hom (v i)) =
      ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z U (v i) := by
  rw [gs_sum (𝟙 X') z (π ⁻¹ᵁ U) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul (𝟙 X') z (π ⁻¹ᵁ U) h, gs_cst f' (𝟙 X') z (π ⁻¹ᵁ U) h, gs_pull (𝟙 X') π z U h, Category.id_comp]

theorem gs_pull_trans {M : LB X} {π : X' ⟶ X} (σ : LB.Sec (M.pull π)) (z : X') {k l : M.ι} (hk : π z ∈ M.U k)
    (hl : π z ∈ M.U l) : gs (𝟙 X') z _ (σ.f (fun _ => k)) =
      (gm π z (M.U k ⊓ M.U l) (M.g k l)).val * gs (𝟙 X') z _ (σ.f (fun _ => l)) := by
  refine (sec_trans σ (𝟙 X') z (j := fun _ => k) (j' := fun _ => l) (Set.mem_iInter.2 fun _ => hk)
    (Set.mem_iInter.2 fun _ => hl)).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  rfl

theorem gs_sec_trans {M : LB X} (s : LB.Sec M) (r : Z ⟶ X) (z : Z) {k l : M.ι} (hk : r z ∈ M.U k)
    (hl : r z ∈ M.U l) : gs r z _ (s.f k) = (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z _ (s.f l) := by
  have hm : r z ∈ M.U k ⊓ M.U l := ⟨hk, hl⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat k l)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem gs_diff {M : LB X} {V W : X.Opens} {k l : M.ι} (hV : V ≤ M.U k) (hW : W ≤ M.U l) (a : Γ(X, V)) (b : Γ(X, W))
    (r : Z ⟶ X) (z : Z) (h : r z ∈ V ⊓ W) :
    gs r z (V ⊓ W) (rs X inf_le_left a - rs X (inf_le_inf hV hW) (M.g k l).val * rs X inf_le_right b) =
      gs r z V a - (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z W b := by
  rw [LBGerm.gs_sub r z _ h, gs_mul r z _ h, gs_res r z _ h, gs_res r z _ h, gs_res r z _ h,
    gs_unit r z (M.U k ⊓ M.U l) ⟨hV h.1, hW h.2⟩]

theorem exists_comb_of_flat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R'), g.Flat → ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull π), ∃ (n : ℕ) (c : Fin n → R') (u : Fin n → LB.Sec M), ∀ (z : X') (k : M.ι), π z ∈ M.U k → gs (𝟙 X') z _ (σ.f (fun _ => k)) = ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ ((u i).f k) := by
  intro R R' _ _ g hg X _ _ f X' π f' H M hM σ
  obtain ⟨α, _, W, j, hA, hW, hc⟩ := exists_finite_affine_refinement hM
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, Γ(X, W a)) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1) -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2)
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, map_add]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, Γ(X, W a)},
      (∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a) := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (h a)
    simp only [he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker e e' d (fun a => rs X' (le_pull M π (hW a)) (σ.f fun _ => j a))
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1) (v i p.2) π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (v i) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a) (v i b) (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = v i a := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  refine ⟨n, c, u, fun z k hk => ?_⟩
  obtain ⟨a, ha⟩ := hc (π z)
  rw [gs_pull_trans σ z hk (hW a ha), hx hv a z ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_sec_trans (u i) π z hk (hW a ha), ← hu' i a, gs_res π z _ ha]
  ring

end GlobalTheory.FlatSec
