import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsVeryAmpleFamiliesStableMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C3
open GlobalTheory

theorem appTop_cst {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add])

theorem secPull_smul {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add, secPull_smul, ih]

theorem secMaps_sum_smul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add, map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem spMap_tower (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] :
    spMap (algebraMap S T) ≫ spMap (algebraMap R S) = spMap (algebraMap R T) := by
  rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R S T]
  rfl

theorem exists_compatible_projective_embeddings : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (P : Over (Sp R)) (_ : QuasiSeparated P.hom) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)) (_ : IsClosedImmersion (pullback.lift iA A.hom hA)) (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)) (_ : IsClosedImmersion (pullback.lift iG G.hom hG)), e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨N, H, s, M, t, w, g, hH, hM, hs, ht, hg, hw, hD⟩ := UpperTheory.Lit.Nos.C2.exists_veryAmple_families_stable_matrix R K W K' hm D hD1 hD2 hres A hA G hG e he hφ
  obtain ⟨h, k, hh, hk⟩ := GlobalTheory.T.matrix_descent_unramified_dvr R K W K' hm D hD1 hD2 hres (N + 1) g hg hD
  have hkdet : IsUnit k.det := by
    have e1 : algebraMap K K' k.det = algebraMap W K' h.det * g.det := by
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]; exact congrArg Matrix.det hk
    have hu : IsUnit (algebraMap K K' k.det) := by
      rw [e1]; exact ((hh.map (algebraMap W K')).mul hg)
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hs' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change K A.left A.hom H N s k hkdet hH hs
  have ht' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change W G.left G.hom M N t h hh hM ht
  obtain ⟨hs0, hsci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 hs'
  obtain ⟨ht0, htci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 ht'
  have hqA : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap K K') := by
    have h1 : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) = (pullback.snd G.hom (spMap (algebraMap W K'))) := Over.w e.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1]
  have hqG : (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap W K') := pullback.condition
  have hbase : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K) = (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W) := by
    rw [← Category.assoc, hqA, ← Category.assoc, hqG, Category.assoc, Category.assoc,
      spMap_tower R K K', spMap_tower R W K']
  have hsec : ∀ j, Cartier.SecMaps w (Cartier.secPull (∑ l, GlobalTheory.AbLaw.cst G.hom ⊤ (h j l) • t l) (pullback.fst G.hom (spMap (algebraMap W K'))))
      (Cartier.secPull (∑ m, GlobalTheory.AbLaw.cst A.hom ⊤ (k j m) • s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
    intro j
    rw [UpperTheory.Lit.Nos.C3.secPull_sum_smul, UpperTheory.Lit.Nos.C3.secPull_sum_smul]
    have e2 : ∑ m, (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))).appTop (GlobalTheory.AbLaw.cst A.hom ⊤ (k j m)) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
        ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (h j l)) •
          ∑ m, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l m) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by
      simp only [UpperTheory.Lit.Nos.C3.appTop_cst (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) A.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap K K') hqA,
        UpperTheory.Lit.Nos.C3.appTop_cst (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') hqG, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      have e3 := congrFun (congrFun hk j) m
      simp only [Matrix.map_apply, Matrix.mul_apply] at e3
      rw [e3, map_sum]
      simp only [map_mul]
    rw [e2]
    exact UpperTheory.Lit.Nos.C3.secMaps_sum_smul w _ _ _ _ hw
  refine ⟨Over.mk (PSpace.str R N), by show QuasiSeparated (PSpace.str R N); unfold PSpace.str; infer_instance,
    GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_,
    GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_, ?_⟩
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
      (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
        (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
      (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
        (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · rw [GlobalTheory.ProjSpace.toProj_baseChange, GlobalTheory.ProjSpace.toProj_baseChange, ← Category.assoc,
      ← GlobalTheory.ProjSpace.toProj_secPull hs0, ← GlobalTheory.ProjSpace.toProj_secPull ht0]
    change GlobalTheory.ProjSpace.toProj ((e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K)) _ _ =
      GlobalTheory.ProjSpace.toProj ((pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W)) _ _
    rw [hbase]
    exact GlobalTheory.ProjSpace.toProj_eq_of_secMaps _ _ hsec

end UpperTheory.Lit.Nos.C3
