import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TendstoOfSandwich
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGlobalSectionsFunctionFieldIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def regAlg [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    (U : X.Opens) (h : genericPoint X ∈ U) : Subalgebra K X.functionField :=
  { (gen U h).rangeS with
    algebraMap_mem' := fun a => ⟨constFn p U a, (gen_constFn p U h a).trans (halg a).symm⟩ }

theorem mem_regAlg [Algebra K X.functionField] {p : X ⟶ Sp K} {halg} {U : X.Opens} {h}
    {f : X.functionField} : f ∈ regAlg p halg U h ↔ ∃ a, gen U h a = f := Iff.rfl

theorem sections_power_integral_iff_affine_cover [Algebra K X.functionField] (p : X ⟶ Sp K) (halg)
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (y : κ → X.functionField)
    (hy : ∀ i, tr N (c i) j₀ (hW i (hη i)) h₀ = y i) (e r : ℕ) :
    SectionsHaveFiniteDimension p (lbPow N e) r ↔ Module.Finite K (piece (fun i => regAlg p halg (W i) (hη i)) y e) ∧
      Module.finrank K (piece (fun i => regAlg p halg (W i) (hη i)) y e) = r := by
  refine lineBundle_global_sections_functionField_iff p halg (N := lbPow N e) (LB.isLB_linComb hN _ _) (fun _ => j₀)
    (Set.mem_iInter.2 fun _ => h₀) W (fun i _ => c i)
    (fun i _ hx => Set.mem_iInter.2 fun _ => hW i hx) hη hc _ (fun f => ?_) r
  refine forall_congr' fun i => ?_
  refine mem_regAlg.trans (exists_congr fun a => Eq.congr_right (congrArg (f * ·) ?_))
  exact ((tr_lbPow N e (fun _ => c i) (fun _ => j₀) _ _ (hW i (hη i)) h₀).trans
    (congrArg (· ^ e) (hy i))).symm

def constFF (p : X ⟶ Sp K) : K →+* X.functionField :=
  (gen ⊤ trivial).comp ((p.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem den_of_section [Algebra K Y.functionField] (p : Y ⟶ Sp K) (halg) (M : LB Y) (j₀ : M.ι) (h₀)
    {κ : Type} [Finite κ] (W : κ → Y.Opens) (c : κ → M.ι) (hW : ∀ i, W i ≤ M.U (c i))
    (hη : ∀ i, genericPoint Y ∈ W i) (haff : ∀ i, IsAffineOpen (W i)) (d : ℕ) (s : (pw M d).Sec)
    (hs : IsAffineOpen (Out.nonzeroLocus s)) (hs' : genericPoint Y ∈ Out.nonzeroLocus s) :
    Den (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀) := by
  let σ := gen _ h₀ (s.f j₀)
  have hσ : σ ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hs'
    have hk' : genericPoint Y ∈ M.U k := Y.basicOpen_le _ hk
    have h1 := (mem_basicOpen_iff hk' (s.f k)).1 hk
    exact right_ne_zero_of_mul ((gen_sec s k j₀ hk' h₀).symm.trans_ne h1)
  let u : ∀ i, Γ(Y, W i) := fun i => rs Y (hW i) (s.f (c i))
  have hu : ∀ i, gen _ (hη i) (u i) = tr M (c i) j₀ (hW i (hη i)) h₀ ^ d * σ := fun i =>
    (gen_rs _ _ _).trans ((gen_sec s (c i) j₀ (hW i (hη i)) h₀).trans
      (congrArg (· * σ) (tr_pw M d _ _ _ _)))
  have hu0 : ∀ i, gen _ (hη i) (u i) ≠ 0 := fun i => by
    rw [hu]
    exact mul_ne_zero (pow_ne_zero _ (tr_ne_zero _ _ _ _ _)) hσ
  have hD : ∀ i, Y.basicOpen (u i) ≤ Out.nonzeroLocus s := fun i =>
    (Y.basicOpen_res (s.f (c i)) (homOfLE (hW i)).op).le.trans
      (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) (c i)))
  have ev : ∀ a : Γ(Y, Out.nonzeroLocus s), ∀ᶠ n : ℕ in Filter.atTop, gen _ hs' a * σ ^ n ∈
      piece (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀)
        (d * n) := by
    intro a
    simp only [mem_piece]
    refine Filter.eventually_all.2 fun i => ?_
    filter_upwards [eventually_mul_pow (haff i) (hη i) (u i) (hu0 i) (hD i) hs' a] with n hn
    obtain ⟨b, hb⟩ := hn
    refine ⟨b, hb.trans ?_⟩
    rw [hu]
    ring
  intro t
  obtain ⟨a, b, hb, hab⟩ := exists_frac hs hs' t
  obtain ⟨n, hna, hnb⟩ := ((ev a).and (ev b)).exists
  refine ⟨d * n, _, hnb, mul_ne_zero hb (pow_ne_zero _ hσ), ?_⟩
  rw [← hab] at hna
  convert hna using 1
  ring

omit [IsIntegral Y] in
theorem exists_affine_cover [CompactSpace Y] {M : LB Y} (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → Y.Opens) (c : κ → M.ι), (∀ i, W i ≤ M.U (c i)) ∧
      (∀ i, ∃ x, x ∈ W i) ∧ (∀ i, IsAffineOpen (W i)) ∧ ∀ x, ∃ i, x ∈ W i := by
  have h : ∀ y : Y, ∃ (j : M.ι) (W : Y.Opens), IsAffineOpen W ∧ y ∈ W ∧ W ≤ M.U j := by
    intro y
    have hy : y ∈ ⨆ i, M.U i := hM.cover ▸ trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨W, hW, h1, h2⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨j, W, hW, h1, h2⟩
  choose c W h1 h2 h3 using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, h2 y⟩)
  refine ⟨t, inferInstance, fun y => W y, fun y => c y, fun y => h3 y, fun y => ⟨y, h2 y⟩,
    fun y => h1 y, fun x => ?_⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hx⟩

theorem vol_pull [CompactSpace Y] (p : Y ⟶ Sp K) (ψ : X ⟶ Y) [IsFinite ψ]
    (hψ : ψ (genericPoint X) = genericPoint Y) {D : ℕ} (hD : MapDeg ψ D) {M : LB Y} (hM : M.IsLB)
    (d : ℕ) (s : (pw M d).Sec) (hs : IsAffineOpen (Out.nonzeroLocus s))
    (hs' : genericPoint Y ∈ Out.nonzeroLocus s) {g : ℕ} {δ : ℝ} (hv : Vol p M g δ) :
    Vol (ψ ≫ p) (M.pull ψ) g (D * δ) := by
  obtain ⟨κ, _, W, c, hW, hne, haff, hc⟩ := exists_affine_cover hM
  have hη : ∀ i, genericPoint Y ∈ W i := fun i => generic_mem (hne i).choose_spec
  have hη' : ∀ i, genericPoint X ∈ ψ ⁻¹ᵁ W i := fun i => show ψ _ ∈ W i from hψ ▸ hη i
  obtain ⟨i₀, -⟩ := hc (genericPoint Y)
  letI : Algebra K Y.functionField := (constFF p).toAlgebra
  letI : Algebra K X.functionField := (constFF (ψ ≫ p)).toAlgebra
  letI : Algebra Y.functionField X.functionField := (ffMap ψ hψ).toAlgebra
  have halg : ∀ a, algebraMap K Y.functionField a = gen ⊤ trivial (constFn p ⊤ a) := fun _ => rfl
  have halg' : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn (ψ ≫ p) ⊤ a) :=
    fun _ => rfl
  have hφ : ∀ a, algebraMap Y.functionField X.functionField a = ffMap ψ hψ a := fun _ => rfl
  haveI : IsScalarTower K Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hφ, halg, halg', ffMap_gen ψ hψ ⊤ trivial trivial]
    congr 1
    unfold constFn
    rw [Scheme.Hom.app_eq_appLE]
    exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE ψ p ⊤ ⊤ ⊤ (fun _ _ => trivial) (fun _ _ => trivial))).symm
  let R := fun i => regAlg p halg (W i) (hη i)
  let R' := fun i => regAlg (ψ ≫ p) halg' (ψ ⁻¹ᵁ W i) (hη' i)
  let y := fun i => tr M (c i) (c i₀) (hW i (hη i)) (hW i₀ (hη i₀))
  have hden : Den R y := den_of_section p halg M (c i₀) _ W c hW hη haff d s hs hs'
  have H : ∀ e r, SectionsHaveFiniteDimension p (lbPow M e) r ↔
      Module.Finite K (piece R y e) ∧ Module.finrank K (piece R y e) = r :=
    sections_power_integral_iff_affine_cover p halg hM (c i₀) (hW i₀ (hη i₀)) W c hW hη hc y fun _ => rfl
  have hW' : ∀ i, ψ ⁻¹ᵁ W i ≤ (M.pull ψ).U (fun _ => c i) := fun i =>
    le_trans (fun _ hx => hW i hx) (AbLaw.le_pull M ψ (le_refl (M.U (c i))))
  have H' : ∀ e r, SectionsHaveFiniteDimension (ψ ≫ p) (lbPow (M.pull ψ) e) r ↔
      Module.Finite K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) ∧
        Module.finrank K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) = r :=
    sections_power_integral_iff_affine_cover (ψ ≫ p) halg' (N := M.pull ψ) (LB.isLB_linComb hM _ _) (fun _ => c i₀)
      (hW' i₀ (hη' i₀)) (fun i => ψ ⁻¹ᵁ W i) (fun i _ => c i) hW' hη' (fun x => hc (ψ x)) _
      fun i => tr_pull M ψ hψ _ _ _ _ (hW i (hη i)) (hW i₀ (hη i₀))
  have hR : ∀ i, ∀ a ∈ R i, algebraMap _ X.functionField a ∈ R' i := by
    rintro i _ ⟨a, rfl⟩
    exact ⟨_, (ffMap_gen ψ hψ _ _ _ a).symm⟩
  have hS : ∀ i, ∀ t : X.functionField, ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a := by
    intro i t
    obtain ⟨a, b, hb, hab⟩ := exists_frac ((haff i).preimage ψ) (hη' i) t
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb, hab⟩
  have hG : ∀ i, ∃ (n : ℕ) (v : Fin n → X.functionField), ∀ t ∈ R' i,
      ∃ w : Fin n → Y.functionField, (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • v l := by
    intro i
    letI := (ψ.app (W i)).hom.toAlgebra
    haveI : Module.Finite Γ(Y, W i) Γ(X, ψ ⁻¹ᵁ W i) := IsFinite.finite_app ψ (W i) (haff i)
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(Y, W i)) (M := Γ(X, ψ ⁻¹ᵁ W i))
    refine ⟨n, fun l => gen _ (hη' i) (v l), ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hv ▸ Submodule.mem_top : t ∈ Submodule.span Γ(Y, W i) (Set.range v))
    refine ⟨fun l => gen _ (hη i) (w l), fun l => ⟨_, rfl⟩, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ffMap_gen ψ hψ _ _ (hη' i)]
    rfl
  haveI : Module.Finite Y.functionField X.functionField := by
    obtain ⟨n, v, hv⟩ := hG i₀
    exact finite_of_frac (R' i₀) (hS i₀) v fun t ht => (hv t ht).imp fun _ h => h.2
  have hrank : Module.finrank Y.functionField X.functionField = D := by
    haveI : Nonempty (W i₀) := ⟨⟨_, hη i₀⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ W i₀) := ⟨⟨_, hη' i₀⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Y _ (haff i₀)
    haveI := functionField_isFractionRing_of_isAffineOpen X _ ((haff i₀).preimage ψ)
    letI := (ψ.app (W i₀)).hom.toAlgebra
    letI : Algebra Γ(Y, W i₀) X.functionField :=
      ((gen _ (hη' i₀)).comp (ψ.app (W i₀)).hom).toAlgebra
    haveI : IsScalarTower Γ(Y, W i₀) Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower Γ(Y, W i₀) Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => (ffMap_gen ψ hψ _ (hη i₀) (hη' i₀) a).symm
    rw [IsFractionRing.finrank_eq Γ(Y, W i₀) Y.functionField Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField]
    exact Module.finrank_eq_of_rank_eq (hD _ (haff i₀) ⟨_, hη i₀⟩)
  obtain ⟨h, hh, hlim⟩ := hv
  have hfin := fun e => ((H e _).1 (hh e)).1
  have hrk := fun e => ((H e _).1 (hh e)).2
  obtain ⟨c₁, hup⟩ := upper (R' := R') hden hG hfin
  obtain ⟨c₂, hlo⟩ := lower hden hR hS fun e => (hup e).1
  refine ⟨_, fun e => (H' e _).2 ⟨(hup e).1, rfl⟩,
    tendsto_of_sandwich h _ D g c₂ c₁ δ hlim (fun e => ?_) fun e => ?_⟩
  · rw [← hrk, ← hrank]
    exact hlo e (hfin e)
  · rw [← hrk, ← hrank]
    exact (hup e).2

end GlobalTheory.VolFin

namespace GlobalTheory

theorem vol_pull_of_isFinite : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  intro K _ _ P α D M δ hα hfin hD hM hamp hv
  haveI := polAV_isIntegral_of_isAlgClosed K P
  haveI := P.isAb.proper
  haveI : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hsurj := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  have hψ : α.left (genericPoint P.A.left) = genericPoint P.A.left := by
    have := (genericPoint_spec P.A.left).image α.left.continuous
    rw [Set.image_univ, α.left.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨d, -, n, s, hcov, hs⟩ := (Unif.relAmple_iff_veryAmpleBy K P.A M hM).1 hamp
  have hx : genericPoint P.A.left ∈ ⨆ i, Out.nonzeroLocus (s i) := hcov ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have := VolFin.vol_pull P.A.hom α.left hψ hD hM d (s i) (hs i).1 hi hv
  rwa [Over.w α] at this

end GlobalTheory
