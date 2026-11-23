import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  have h1 : (toUnit X).left = X.hom := by simp
  show (toUnit X ≫ η[G]).left = _
  rw [Over.comp_left, h1]

private theorem left_comp_comp_hom_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} (y : T ⟶ G') :
    (y.left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ x)).hom := by
  simp only [Over.mk_hom, Category.assoc, h.1.w]
  rw [← Category.assoc, Over.w]

private theorem eq_one_of_left_eq_one_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)}
    (u₀ : Over.mk (T.hom ≫ x) ⟶ G) (hu : u₀.left = (1 : T ⟶ G').left ≫ φ) : u₀ = 1 := by
  have h2 := h.2 T 1 1 u₀ u₀ hu hu
  rw [_root_.mul_one, ← hu] at h2
  have h3 : u₀ * u₀ = u₀ := Over.OverMorphism.ext h2
  simpa using h3

private theorem list_prod_left_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G')) (u₀ : Fin m → (Over.mk (T.hom ≫ x) ⟶ G)),
      (∀ i, (u₀ i).left = (u i).left ≫ φ) → (List.ofFn u₀).prod.left = (List.ofFn u).prod.left ≫ φ := by
  intro m
  induction m with
  | zero =>
    intro u u₀ _
    simp only [List.ofFn_zero, List.prod_nil]
    have e0 : (Over.homMk ((1 : T ⟶ G').left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h 1) : Over.mk (T.hom ≫ x) ⟶ G) = 1 :=
      eq_one_of_left_eq_one_comp_of_isGrpPullback h _ rfl
    rw [← e0]
    rfl
  | succ m ih =>
    intro u u₀ hu
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact h.2 T _ _ _ _ (hu 0) (ih _ _ fun i => hu i.succ)

private theorem eq_of_left_comp_eq_of_isGrpPullback' {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} {u v : T ⟶ G'}
    (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

private theorem spMap_fstHom_comp_epsR_hom (K : Type) [Field K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = 𝟙 (Sp K) := by
  have e1 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K :=
    RingHom.ext fun _ => rfl
  show Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = 𝟙 _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_id, Spec.map_id]

private theorem isLieComb_iff_eq_prodPts {K : Type} [Field K] {G' : Over (Sp K)} [GrpObj G'] {n : ℕ} (c : Fin n → K)
    (v : Fin n → (epsR K ⟶ G')) (y : epsR K ⟶ G') : IsLieComb c v y ↔ y = Chart.prodPts c v := by
  unfold IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    have e1 : u = fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i := funext fun i => Over.OverMorphism.ext (hu i)
    rw [e1]
    rfl
  · rintro rfl
    exact ⟨fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i, fun i => rfl, rfl⟩

private theorem lieMult_of_finrank_eigenSub_eq {O K : Type} [CommRing O] [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S}
    {G' : Over (Sp K)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
    {n : ℕ} {v : Fin n → (epsR K ⟶ G')} (hv : IsLieBasis v) (act : OAct O G) (act' : OAct O G')
    (ha : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (ρ : O →+* Module.End K (Fin n → K))
    (hρ : ∀ a c, Chart.prodPts (ρ a c) v = Chart.prodPts c v ≫ act'.act a) (τ : O →+* K) (N : ℕ)
    (hN : Module.finrank K (GlobalTheory.EigenSplit.eigenSub ρ τ) = N) : LieMult act x τ N := by
  have hv0 := hv
  unfold IsLieBasis at hv0
  obtain ⟨hvt, hvu⟩ := hv0
  let P : (epsR K ⟶ G') → (epsPt x ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h y)
  have hP : ∀ y, (P y).left = y.left ≫ φ := fun y => rfl
  have hU : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e1 := congrArg Over.Hom.left (eq_one_of_left_eq_one_comp_of_isGrpPullback h (T := epsR K) (P 1) rfl)
    rw [hP, isGrpPullback_one_left, isGrpPullback_one_left] at e1
    simp only [Over.mk_hom, Category.assoc] at e1
    have e2 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ t) e1
    have hf1 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) :=
      spMap_fstHom_comp_epsR_hom K
    simp only [← Category.assoc, hf1, Category.id_comp] at e2
    exact e2
  have hfstw : ∀ y : epsR K ⟶ G', (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ y.left) ≫ G'.hom = 𝟙 _ := by
    intro y
    rw [Category.assoc, Over.w, spMap_fstHom_comp_epsR_hom]
  have hηw : η[G'].left ≫ G'.hom = 𝟙 _ := by
    exact Over.w η[G']
  have htan : ∀ y : epsR K ⟶ G', IsTangent y ↔
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (P y).left = (1 : Over.mk x ⟶ G).left := by
    intro y
    unfold IsTangent
    rw [hP, isGrpPullback_one_left]
    simp only [Over.mk_hom]
    constructor
    · intro hy
      rw [← Category.assoc, hy, hU]
    · intro hy
      apply h.1.hom_ext
      · rw [Category.assoc]
        exact hy.trans hU.symm
      · exact (hfstw y).trans hηw.symm
  have heig : ∀ (y : epsR K ⟶ G') (a : O) (s : K),
      (P y ≫ act.act a).left = spMap (epsScale s) ≫ (P y).left ↔ y ≫ act'.act a = Chart.spMap (Chart.scaleD s) ≫ y := by
    intro y a s
    have e1 : (P y ≫ act.act a).left = (y ≫ act'.act a).left ≫ φ := by
      simp only [Over.comp_left, Category.assoc, hP, ha]
    rw [e1, hP]
    constructor
    · intro e2
      apply eq_of_left_comp_eq_of_isGrpPullback' h
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
    · intro e2
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
  let B := Module.finBasisOfFinrankEq K (GlobalTheory.EigenSplit.eigenSub ρ τ) hN
  let e : Fin N → (epsR K ⟶ G') := fun i => Chart.prodPts ((B i : Fin n → K)) v
  have heS : ∀ c : Fin n → K, c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ → ∀ a,
      Chart.prodPts c v ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ Chart.prodPts c v := by
    intro c hc a
    rw [← hρ, GlobalTheory.EigenSplit.mem_eigenSub.1 hc a, GlobalTheory.LieEigen.prodPts_smul]
  have hlift : ∀ w : epsPt x ⟶ G, ∃ y, P y = w := by
    intro w
    refine ⟨Over.homMk (h.1.lift w.left (epsR K).hom (Over.w w)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  have hsc : ∀ (d : K) (i : Fin N),
      (P (Chart.spMap (Chart.scaleD d) ≫ e i)).left = spMap (epsScale d) ≫ (P (e i)).left := by
    intro d i
    show (Chart.spMap (Chart.scaleD d) ≫ e i).left ≫ φ = spMap (epsScale d) ≫ (e i).left ≫ φ
    rw [Over.comp_left, Category.assoc]
    try rfl
  have hprod : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
      (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
        (List.ofFn u).prod = P (Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v) := by
    intro d u hu
    apply Over.OverMorphism.ext
    rw [hP, ← GlobalTheory.LieEigen.prodPts_prodPts hvt d fun i => (B i : Fin n → K)]
    exact list_prod_left_comp_of_isGrpPullback h (fun i => Chart.spMap (Chart.scaleD (d i)) ≫ e i) u
      (fun i => by rw [hu i, ← hsc]; rfl)
  unfold LieMult
  refine ⟨fun i => P (e i), fun i => ?_, fun w hw => ?_⟩
  · unfold IsLieEigen
    exact ⟨(htan (e i)).1 (GlobalTheory.LieEigen.isTangent_prodPts hvt _),
      fun a => (heig (e i) a (τ a)).2 (heS _ (B i).2 a)⟩
  · unfold IsLieEigen at hw
    obtain ⟨hw0, hw1⟩ := hw
    obtain ⟨y, rfl⟩ := hlift w
    have hty : IsTangent y := (htan y).2 hw0
    have hye : ∀ a, y ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ y := fun a => (heig y a (τ a)).1 (hw1 a)
    obtain ⟨c, hc, -⟩ := hvu y hty
    rw [isLieComb_iff_eq_prodPts] at hc
    subst hc
    have hcm : c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ := by
      rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      apply GlobalTheory.LieEigen.prodPts_injective hv
      show Chart.prodPts (ρ a c) v = Chart.prodPts (τ a • c) v
      rw [hρ, hye, GlobalTheory.LieEigen.prodPts_smul]
    let cc : GlobalTheory.EigenSplit.eigenSub ρ τ := ⟨c, hcm⟩
    have key : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
        (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
          (P (Chart.prodPts c v) = (List.ofFn u).prod ↔ d = B.repr cc) := by
      intro d u hu
      rw [hprod d u hu]
      constructor
      · intro hEq
        have h1 : Chart.prodPts c v = Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v :=
          eq_of_left_comp_eq_of_isGrpPullback' h (congrArg Over.Hom.left hEq)
        have h2 := GlobalTheory.LieEigen.prodPts_injective hv h1
        have h3 : cc = ∑ i, d i • B i := by
          apply Subtype.ext
          rw [Submodule.coe_sum]
          simp only [Submodule.coe_smul]
          exact h2
        rw [h3, Module.Basis.repr_sum_self]
      · intro hd
        subst hd
        have h4 := congrArg Subtype.val (B.sum_repr cc)
        rw [Submodule.coe_sum] at h4
        simp only [Submodule.coe_smul] at h4
        exact congrArg (fun t => P (Chart.prodPts t v)) h4.symm
    refine ⟨fun i => B.repr cc i, ⟨fun i => P (Chart.spMap (Chart.scaleD (B.repr cc i)) ≫ e i), fun i => hsc _ i, ?_⟩, ?_⟩
    · exact (key _ _ fun i => hsc _ i).2 rfl
    · rintro d ⟨u, hu, hEq⟩
      exact (key d u hu).1 hEq

theorem GlobalTheory.exists_lie_coordinates_lieMult_iff : ∀ (O R : Type) [CommRing O] [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR R ⟶ G)), Smooth G.hom → IsLieBasis v → ∃ M : O →+* Module.End R (Fin n → R), ∀ (K : Type) [Field K] (f : R →+* K), ∃ M' : O →+* Module.End K (Fin n → K), (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ (τ : O →+* K) (N : ℕ), LieMult act (spMap f) τ N ↔ Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = N := by
  intro O R _ _ G _ _ act n v hs hv
  obtain ⟨M, hM⟩ := GlobalTheory.LieEigen.exists_action hv act
  refine ⟨M, fun K _ f => ?_⟩
  have hpb := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange R K f G ((Over.pullback (spMap f)).obj G)
    (pullback.fst G.hom (spMap f)) hpb hs n v hv
  obtain ⟨act', hact'⟩ := GlobalTheory.DetExtend.exists_oAct_pullback (spMap f) act
  have ha : ∀ a, (act'.act a).left ≫ pullback.fst G.hom (spMap f) =
      pullback.fst G.hom (spMap f) ≫ (act.act a).left := by
    intro a
    rw [hact']
    exact pullback.lift_fst _ _ _
  obtain ⟨M', hM'⟩ := GlobalTheory.LieEigen.exists_action hv' act'
  refine ⟨M', fun a c => GlobalTheory.LieEigen.action_baseChange hpb hv' hvv ha hM hM' a c, fun τ N => ⟨fun hN => ?_, fun hN => ?_⟩⟩
  · exact GlobalTheory.LieEigen.finrank_of_lieMult hpb hv' ha hM' hN
  · exact lieMult_of_finrank_eigenSub_eq hpb hv' act act' ha M' hM' τ N hN
