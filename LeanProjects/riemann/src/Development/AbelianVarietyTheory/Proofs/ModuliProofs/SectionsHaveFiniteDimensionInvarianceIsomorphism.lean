import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.SecDim

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def constHom (p : X ⟶ Sp K) : K →+* Γ(X, ⊤) :=
  RingHom.comp (p.appLE ⊤ ⊤ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem resG_constHom (p : X ⟶ Sp K) (U : X.Opens) (a : K) :
    resG X (le_top : U ≤ ⊤) (constHom p a) = constFn p U a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := ⊤) (V' := U) (by simp) (homOfLE le_top).op)

theorem appLE_constFn (p : X ⟶ Sp K) (φ : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ φ ⁻¹ᵁ U) (a : K) :
    (φ.appLE U W e).hom (constFn p U a) = constFn (φ ≫ p) W a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE φ p ⊤ U W (by simp) e)

abbrev secModule (p : X ⟶ Sp K) (M : LB X) : Module K M.Sec := Module.compHom M.Sec (constHom p)

theorem sum_f {M : LB X} {T : Type} (S : Finset T) (s : T → M.Sec) (j : M.ι) :
    (∑ i ∈ S, s i).f j = ∑ i ∈ S, (s i).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

private theorem sum_constHom_smul_sec_apply (p : X ⟶ Sp K) (M : LB X) {r : ℕ} (s : Fin r → M.Sec) (a : Fin r → K)
    (j : M.ι) :
    (letI := secModule p M; ∑ i, a i • s i).f j = ∑ i, constFn p _ (a i) * (s i).f j := by
  let _ : Module K M.Sec := secModule p M
  rw [sum_f]
  refine Finset.sum_congr rfl fun i _ => ?_
  show resG X le_top (constHom p (a i)) * (s i).f j = _
  rw [resG_constHom]

theorem lineBundle_global_sections_functionField_iff (p : X ⟶ Sp K) (M : LB X) (r : ℕ) :
    SectionsHaveFiniteDimension p M r ↔ letI := secModule p M; Nonempty ((Fin r → K) ≃ₗ[K] M.Sec) := by
  let _ : Module K M.Sec := secModule p M
  constructor
  · rintro ⟨s, hs⟩
    let Φ : (Fin r → K) →ₗ[K] M.Sec :=
      { toFun := fun a => ∑ i, a i • s i
        map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c a => by
          simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    have hΦ : Function.Bijective Φ := by
      constructor
      · intro a b hab
        obtain ⟨c, -, hc⟩ := hs (Φ a)
        have ha : ∀ j, (Φ a).f j = ∑ i, constFn p _ (a i) * (s i).f j := fun j => sum_constHom_smul_sec_apply p M s a j
        have hb : ∀ j, (Φ a).f j = ∑ i, constFn p _ (b i) * (s i).f j := fun j => by
          rw [hab]; exact sum_constHom_smul_sec_apply p M s b j
        exact (hc a ha).trans (hc b hb).symm
      · intro t
        obtain ⟨a, ha, -⟩ := hs t
        exact ⟨a, DVR.SecOps.sec_ext fun j => (sum_constHom_smul_sec_apply p M s a j).trans (ha j).symm⟩
    exact ⟨LinearEquiv.ofBijective Φ hΦ⟩
  · rintro ⟨e⟩
    set s : Fin r → M.Sec := fun i => e (fun j => if i = j then 1 else 0) with hs_def
    have key : ∀ a : Fin r → K, e a = ∑ i, a i • s i := fun a =>
      LinearMap.pi_apply_eq_sum_univ (e : (Fin r → K) →ₗ[K] M.Sec) a
    refine ⟨s, fun t => ⟨e.symm t, fun j => ?_, fun a ha => ?_⟩⟩
    · have h1 : (∑ i, e.symm t i • s i) = t := (key (e.symm t)).symm.trans (e.apply_symm_apply t)
      exact (congrArg (fun x : M.Sec => x.f j) h1).symm.trans (sum_constHom_smul_sec_apply p M s (e.symm t) j)
    · have h2 : e a = t := DVR.SecOps.sec_ext fun j => by
        rw [key a]; exact (sum_constHom_smul_sec_apply p M s a j).trans (ha j).symm
      rw [← h2, e.symm_apply_apply]

theorem sectionsHaveFiniteDimension_unique (p : X ⟶ Sp K) (M : LB X) {r r' : ℕ} (h : SectionsHaveFiniteDimension p M r) (h' : SectionsHaveFiniteDimension p M r') : r = r' := by
  obtain ⟨e⟩ := (lineBundle_global_sections_functionField_iff p M r).1 h
  obtain ⟨e'⟩ := (lineBundle_global_sections_functionField_iff p M r').1 h'
  let _ : Module K M.Sec := secModule p M
  have h2 := (e.trans e'.symm).finrank_eq
  simpa using h2

theorem sectionsHaveFiniteDimension_congr_addEquiv (p : X ⟶ Sp K) (q : Y ⟶ Sp K) {M : LB X} {N : LB Y} (E : M.Sec ≃+ N.Sec)
    (hE : ∀ (a : K) (s : M.Sec), E (constHom p a • s) = constHom q a • E s) (r : ℕ) :
    SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension q N r := by
  let _ : Module K M.Sec := secModule p M
  let _ : Module K N.Sec := secModule q N
  let E' : M.Sec ≃ₗ[K] N.Sec := E.toLinearEquiv fun a s => hE a s
  rw [lineBundle_global_sections_functionField_iff, lineBundle_global_sections_functionField_iff]
  exact ⟨fun ⟨e⟩ => ⟨e.trans E'⟩, fun ⟨e⟩ => ⟨e.trans E'.symm⟩⟩

private theorem sep_lemma' {U : X.Opens} {J : Type} (V : J → X.Opens) (hV : ∀ i, V i ≤ U) (hc : U ≤ ⨆ i, V i)
    (x y : Γ(X, U)) (h : ∀ i, DVR.rs (hV i) x = DVR.rs (hV i) y) : x = y :=
  X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hc x y h

private theorem rs_resG_global_eq_rs_resG_global {U U' V : X.Opens} (h1 : V ≤ U) (h2 : V ≤ U') (c : Γ(X, ⊤)) :
    DVR.rs h1 (resG X le_top c) = DVR.rs h2 (resG X le_top c) := by
  simp only [DVR.rs, resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

private theorem exists_sections_map_of_lbIso (p : X ⟶ Sp K) {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) :
    ∃ T : (letI := secModule p A; letI := secModule p B; B.Sec →ₗ[K] A.Sec), Function.Injective T := by
  let _ : Module K A.Sec := secModule p A
  let _ : Module K B.Sec := secModule p B
  obtain ⟨u, hu⟩ := H
  have sepA : ∀ a (x y : Γ(X, A.U a)),
      (∀ b, DVR.rs (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) x = DVR.rs inf_le_left y) → x = y :=
    fun a x y h => sep_lemma' (fun b => A.U a ⊓ B.U b) (fun b => inf_le_left) (DVR.cover_inf hB a) x y h
  have sepB : ∀ b (x y : Γ(X, B.U b)),
      (∀ a, DVR.rs (inf_le_right : A.U a ⊓ B.U b ≤ B.U b) x = DVR.rs inf_le_right y) → x = y :=
    fun b x y h => sep_lemma' (fun a => A.U a ⊓ B.U b) (fun a => inf_le_right)
      (by simpa only [inf_comm] using DVR.cover_inf (A := B) (B := A) hA b) x y h
  refine ⟨{ toFun := fun t => DVR.secOfIso t hu hA hB, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro t t'
    refine DVR.SecOps.sec_ext fun a => sepA a _ _ fun b => ?_
    show DVR.rs _ ((DVR.secOfIso (t + t') hu hA hB).f a) =
      DVR.rs _ ((DVR.secOfIso t hu hA hB).f a + (DVR.secOfIso t' hu hA hB).f a)
    have e1 := DVR.secOfIso_spec (t + t') hu hA hB a b
    have e2 := DVR.secOfIso_spec t hu hA hB a b
    have e3 := DVR.secOfIso_spec t' hu hA hB a b
    simp only [DVR.rs] at e1 e2 e3 ⊢
    rw [map_add, e1, e2, e3]
    simp only [DVR.isoCand, DVR.rs]
    rw [← mul_add, ← map_add]
    rfl
  · intro k t
    refine DVR.SecOps.sec_ext fun a => sepA a _ _ fun b => ?_
    show DVR.rs _ ((DVR.secOfIso (constHom p k • t) hu hA hB).f a) =
      DVR.rs _ (resG X le_top (constHom p k) * (DVR.secOfIso t hu hA hB).f a)
    have e1 := DVR.secOfIso_spec (constHom p k • t) hu hA hB a b
    have e2 := DVR.secOfIso_spec t hu hA hB a b
    have r1 := rs_resG_global_eq_rs_resG_global (inf_le_right : A.U a ⊓ B.U b ≤ B.U b) (inf_le_left : A.U a ⊓ B.U b ≤ A.U a)
      (constHom p k)
    have hsm : (constHom p k • t).f b = resG X le_top (constHom p k) * t.f b := rfl
    simp only [DVR.rs] at e1 e2 r1 ⊢
    rw [map_mul, e1, e2]
    simp only [DVR.isoCand, DVR.rs]
    rw [hsm, map_mul, r1]
    ring
  · intro t t' htt
    refine DVR.SecOps.sec_ext fun b => sepB b _ _ fun a => ?_
    have h3 : DVR.isoCand u t a b = DVR.isoCand u t' a b := by
      rw [← DVR.secOfIso_spec t hu hA hB a b, ← DVR.secOfIso_spec t' hu hA hB a b]
      exact congrArg (fun s => DVR.rs (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) (s.f a)) htt
    simp only [DVR.isoCand] at h3
    exact (Units.mul_right_inj _).1 h3

private theorem finiteDimensional_of_lbIso_sections {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (g : W →ₗ[K] V) (hf : Function.Injective f) (hg : Function.Injective g) (r : ℕ) :
    Nonempty ((Fin r → K) ≃ₗ[K] V) → Nonempty ((Fin r → K) ≃ₗ[K] W) := by
  rintro ⟨e⟩
  have : FiniteDimensional K V := LinearEquiv.finiteDimensional e
  have : FiniteDimensional K W := Module.Finite.of_injective g hg
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have h2 := LinearMap.finrank_le_finrank_of_injective hg
  have h3 : Module.finrank K V = r := by rw [← e.finrank_eq]; simp
  exact ⟨LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun]; omega)⟩

theorem sectionsHaveFiniteDimension_iff_of_lineBundleIso (p : X ⟶ Sp K) {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (h : LBIso M M') (r : ℕ) :
    SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension p M' r := by
  obtain ⟨T, hT⟩ := exists_sections_map_of_lbIso p hM hM' h
  obtain ⟨T', hT'⟩ := exists_sections_map_of_lbIso p hM' hM (LBIso.symm h)
  rw [lineBundle_global_sections_functionField_iff, lineBundle_global_sections_functionField_iff]
  let _ : Module K M.Sec := secModule p M
  let _ : Module K M'.Sec := secModule p M'
  exact ⟨finiteDimensional_of_lbIso_sections T' T hT' hT r, finiteDimensional_of_lbIso_sections T T' hT hT' r⟩

private theorem presheaf_map_homOfLE_map_homOfLE_apply {Z : Scheme.{0}} {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Z, U)) :
    (Z.presheaf.map (homOfLE h2).op).hom ((Z.presheaf.map (homOfLE h1).op).hom x) =
      (Z.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem presheaf_map_homOfLE_refl_apply {Z : Scheme.{0}} {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) :
    (Z.presheaf.map (homOfLE h).op).hom x = x := by
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

private theorem exists_sec_addEquiv_pull_of_bijective_app (p : X ⟶ Sp K) (M : LB X) (φ : Y ⟶ X)
    (hφ : ∀ V, Function.Bijective (φ.app V).hom) :
    ∃ E : M.Sec ≃+ (M.pull φ).Sec, ∀ (a : K) (s : M.Sec), E (constHom p a • s) = constHom (φ ≫ p) a • E s := by
  have hle : ∀ j : M.ι, φ ⁻¹ᵁ M.U j ≤ (M.pull φ).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  have hP : ∀ (s : M.Sec) (J : PUnit → M.ι),
      (secPull s φ).f J = (φ.appLE _ _ ((chartPullPull M φ).le J)).hom (s.f (J PUnit.unit)) :=
    fun s J => chartSec_f (chartPullPull M φ) s J
  let P : M.Sec →+ (M.pull φ).Sec :=
    { toFun := fun s => secPull s φ
      map_zero' := DVR.SecOps.sec_ext fun (J : PUnit → M.ι) => (hP 0 J).trans (map_zero _)
      map_add' := fun s t => DVR.SecOps.sec_ext fun (J : PUnit → M.ι) => by
        show (secPull (s + t) φ).f J = (secPull s φ).f J + (secPull t φ).f J
        exact (hP (s + t) J).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) (hP s J).symm (hP t J).symm)) }
  have inj : Function.Injective P := fun s t hst => DVR.SecOps.sec_ext fun j => by
    have h1 := congrArg (fun u : (M.pull φ).Sec => u.f (fun _ => j)) hst
    change (secPull s φ).f _ = (secPull t φ).f _ at h1
    rw [hP, hP] at h1
    apply (hφ (M.U j)).1
    have h2 := congrArg (Y.presheaf.map (homOfLE (hle j)).op).hom h1
    exact (presheaf_map_homOfLE_refl_apply _ _).symm.trans ((presheaf_map_homOfLE_map_homOfLE_apply _ _ _).symm.trans (h2.trans ((presheaf_map_homOfLE_map_homOfLE_apply _ _ _).trans (presheaf_map_homOfLE_refl_apply _ _))))
  have surj : Function.Surjective P := fun t => by
    let e := fun j : M.ι => Equiv.ofBijective _ (hφ (M.U j))
    have a1 : ∀ j x, (φ.app (M.U j)).hom ((e j).symm x) = x := fun j x => (e j).apply_symm_apply x
    let s : M.Sec :=
      { f := fun j => (e j).symm ((Y.presheaf.map (homOfLE (hle j)).op).hom (t.f (fun _ => j)))
        compat := fun i j => by
          apply (hφ (M.U i ⊓ M.U j)).1
          rw [map_mul]
          have n1 := DVR.app_rs φ (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)
            ((e i).symm ((Y.presheaf.map (homOfLE (hle i)).op).hom (t.f (fun _ => i))))
          have n2 := DVR.app_rs φ (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)
            ((e j).symm ((Y.presheaf.map (homOfLE (hle j)).op).hom (t.f (fun _ => j))))
          simp only [DVR.rs] at n1 n2
          rw [n1, n2, a1, a1, presheaf_map_homOfLE_map_homOfLE_apply, presheaf_map_homOfLE_map_homOfLE_apply]
          have hij : φ ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ (M.pull φ).U (fun _ => i) ⊓ (M.pull φ).U (fun _ => j) :=
            le_inf (((TopologicalSpace.Opens.map φ.base).monotone inf_le_left).trans (hle i))
              (((TopologicalSpace.Opens.map φ.base).monotone inf_le_right).trans (hle j))
          have tc := congrArg (Y.presheaf.map (homOfLE hij).op).hom (t.compat (fun _ => i) (fun _ => j))
          rw [map_mul, presheaf_map_homOfLE_map_homOfLE_apply, presheaf_map_homOfLE_map_homOfLE_apply] at tc
          rw [tc]
          congr 1
          simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
          unfold res pullU
          exact (presheaf_map_homOfLE_map_homOfLE_apply _ _ _).trans (presheaf_map_homOfLE_refl_apply _ _) }
    refine ⟨s, DVR.SecOps.sec_ext fun (J : PUnit → M.ι) => ?_⟩
    change (secPull s φ).f J = t.f J
    refine (hP s J).trans ?_
    change (Y.presheaf.map _).hom ((φ.app _).hom ((e (J PUnit.unit)).symm _)) = _
    rw [a1]
    exact (presheaf_map_homOfLE_map_homOfLE_apply _ _ _).trans (presheaf_map_homOfLE_refl_apply _ _)
  exact ⟨AddEquiv.ofBijective P ⟨inj, surj⟩, fun a s => DVR.SecOps.sec_ext fun (J : PUnit → M.ι) => by
    change (secPull (constHom p a • s) φ).f J = resG Y le_top (constHom (φ ≫ p) a) * (secPull s φ).f J
    refine (hP _ J).trans ?_
    refine Eq.trans ?_ (congrArg (resG Y le_top (constHom (φ ≫ p) a) * ·) (hP s J)).symm
    change (φ.appLE _ _ _).hom (resG X le_top (constHom p a) * s.f (J PUnit.unit)) = _
    refine (map_mul _ _ _).trans ?_
    congr 1
    exact (congrArg (φ.appLE _ _ _).hom (resG_constHom p _ a)).trans
      ((appLE_constFn p φ _ a).trans (resG_constHom (φ ≫ p) _ a).symm)⟩

theorem sectionsHaveFiniteDimension_iff_pull_bijective (p : X ⟶ Sp K) (M : LB X) (φ : Y ⟶ X) (hφ : ∀ V, Function.Bijective (φ.app V).hom)
    (r : ℕ) : SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension (φ ≫ p) (M.pull φ) r := by
  obtain ⟨E, hE⟩ := exists_sec_addEquiv_pull_of_bijective_app p M φ hφ
  exact sectionsHaveFiniteDimension_congr_addEquiv p (φ ≫ p) E hE r

theorem lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X), M.IsLB → (∀ r r', SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M r' → r = r') ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → (∀ r, SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M' r) ∧ ∀ e, LBIso (lbPow M e) (lbPow M' e)) ∧ (∀ a e, LBIso (lbPow (lbPow M a) e) (lbPow M (a * e))) ∧ LBIso (lbPow M 1) M ∧ (∀ (Y : Scheme.{0}) (φ : Y ⟶ X) (e : ℕ), LBIso (lbPow (M.pull φ) e) ((lbPow M e).pull φ)) ∧ ∀ (Y : Scheme.{0}) (φ : Y ≅ X) (r : ℕ), SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension (φ.hom ≫ p) (M.pull φ.hom) r := by
  intro K _ X p M hM
  refine ⟨fun r r' h h' => sectionsHaveFiniteDimension_unique p M h h', fun M' hM' hMM' =>
    ⟨fun r h => (sectionsHaveFiniteDimension_iff_of_lineBundleIso p hM hM' hMM' r).1 h, fun e => lbIso_lbPow hMM' e⟩,
    fun a e => lbIso_lbPow_lbPow hM a e, lbIso_lbPow_one hM, fun Y φ e => lbIso_lbPow_pull hM φ e,
    fun Y φ r => sectionsHaveFiniteDimension_iff_pull_bijective p M φ.hom (fun V => ConcreteCategory.bijective_of_isIso _) r⟩

end GlobalTheory.SecDim

end
