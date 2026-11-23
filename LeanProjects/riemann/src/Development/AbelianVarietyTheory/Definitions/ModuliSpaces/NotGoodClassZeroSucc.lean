import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ZM.Model
open Out.Inh

def baseC (k : ℕ) (hk : k ≠ 0) : TBase ℂ k where
  ζ := ((Complex.isPrimitiveRoot_exp k hk).isUnit hk).unit
  unit := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk)
  prim := fun _ _ β => (Complex.isPrimitiveRoot_exp k hk).map_of_injective β.injective

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

def zeroObj (J : Type) (b : TBase o k) (s : S ⟶ Sp o) : TObj 0 k J b s where
  A := 𝟙_ (Over S)
  grp := (zeroPolAV S).grp
  ab := (zeroPolAV S).isAb
  dim := (zeroPolAV S).smoothDim
  L := trivLB _
  isLB := (zeroPolAV S).isLB
  rigid := (zeroPolAV S).rigid
  sym := (zeroPolAV S).sym
  ample := (zeroPolAV S).ample
  ktriv := (zeroPolAV S).ktriv
  pt := fun i => Fin.elim0 i
  torsion := fun i => Fin.elim0 i
  bij := fun _ _ _ _ _ _ => ⟨fun i => Fin.elim0 i, toUnit_unique _ _, fun _ _ => funext fun i => Fin.elim0 i⟩
  pairing := fun i => Fin.elim0 i
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance

example {g : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s) (w w' : J) (h : t.Prim w w') :
    lift (t.act w) (t.act w') ≫ μ[t.A] = 𝟙 t.A := h.1

theorem lbIso_of_g {X : Scheme.{0}} (L M : LB X) (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have h : (LB.div M L).g i j = 1 :=
    (congrArg₂ (· * ·) ((congrArg _ (hM _ _)).trans (map_one _)) ((congrArg (·⁻¹) ((congrArg _ (hL _ _)).trans
      (map_one _))).trans inv_one)).trans (_root_.mul_one _)
  exact (map_one _).trans ((congrArg₂ (· * ·) h (map_one _)).trans (_root_.mul_one _)).symm

theorem zero_prim {J : Type} (b : TBase o k) (s : S ⟶ Sp o) (w w' : J) : (zeroObj J b s).Prim w w' :=
  ⟨toUnit_unique _ _, lbIso_of_g _ _ (linComb_triv_g _ _) (linComb_triv_g _ _),
    lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)⟩

theorem zero_tmap {J : Type} (b : TBase o k) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) :
    TMap (zeroObj J b s') (zeroObj J b s) f := by
  refine ⟨f, ⟨?_, fun T x y x₀ y₀ _ _ => ?_⟩, lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _),
    fun i => Fin.elim0 i, fun j => ?_⟩
  · show IsPullback f (𝟙 S') (𝟙 S) f
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · have h1 : (x₀ * y₀).left ≫ 𝟙 S = T.hom ≫ f := Over.w (x₀ * y₀)
    have h2 : (x * y).left ≫ 𝟙 S' = T.hom := Over.w (x * y)
    exact ((Category.comp_id _).symm.trans h1).trans (congrArg (· ≫ f) ((Category.comp_id _).symm.trans h2)).symm
  · show 𝟙 S' ≫ f = f ≫ 𝟙 S
    simp

theorem zero_hasTh {J : Type} {N : ℕ} (hN : Odd N) (b : TBase o (N ^ 2)) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ S)
    (s : S ⟶ Sp o) : (zeroObj J b s).HasTh x (fun _ => 1) := by
  have hu : IsUnit (N : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  have hu' : IsUnit (N : Γ((Over.mk x).left, ⊤)) := by
    have := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  unfold TObj.HasTh
  simp only [map_one]
  exact GlobalTheory.ThetaPtDet.isThetaPt_zero S N hN hu' _

theorem zero_fromC {J : Type} (b : TBase ℂ k) :
    fromSet (RingHom.id ℂ) (fun _ => True) (zeroObj J b (spMap (RingHom.id ℂ))) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ⟨ℂ, inferInstance, 𝟙 _, ⟨p, rfl⟩, ℂ, inferInstance, RingHom.id ℂ, RingHom.id ℂ,
    RingHom.id ℂ, zeroObj J b _, zeroObj J b _, zeroObj J b _, rfl, ?_, zero_tmap _ _ _ _, zero_tmap _ _ _ _,
    zero_tmap _ _ _ _, trivial⟩
  simp [spMap]

theorem goodClass_empty {g N : ℕ} {J : Type} {b : TBase o (N ^ 2)} (em : o →+* ℂ) (Mat κ) (w w' : J) (d : ℕ) :
    GoodClass (g := g) (b := b) em (fun _ => False) Mat κ w w' d where
  iso := fun _ _ h => h.elim
  shape := fun _ h => h.elim
  fam := ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ h => h.elim⟩

theorem odd_of_thetaFam {g n N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) : Odd N := by
  obtain ⟨x, hx, -⟩ := F.pts PUnit (algebraMap o PUnit) (fun _ => 0)
    ⟨fun _ _ => Subsingleton.elim _ _, fun q hq => (hq.ne_top (Subsingleton.elim _ _)).elim⟩
  exact hx.2.1

example : ¬ Coset (g := 1) 3 9 (fun a : Ix 1 (9 ^ 2) => if a = 0 then (1 : ℚ) else 0) ⊥ := by
  intro h
  obtain ⟨c, hc⟩ := h (fun _ => 1)
  apply hc
  beta_reduce
  rw [if_neg]; · simp
  intro h0
  have h1 := congrFun h0 0
  have h2 := congrArg (ZMod.castHom (show 3 ∣ 9 ^ 2 by norm_num) (ZMod 3)) h1
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_one, map_nsmul, Pi.zero_apply, map_zero] at h2
  revert h2
  generalize (ZMod.castHom (show 3 ∣ 9 ^ 2 by norm_num) (ZMod 3)) (c 0) = z
  revert z; decide

theorem isIso_of_dim_zero (A : Over S) [GrpObj A] (h : IsAbelianScheme A) (hd : SmoothOfRelativeDimension 0 A.hom) :
    IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) := ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem lbIso_of_gen {X : Scheme.{0}} (L M : LB X) (F : X ⟶ X) (hF : F = 𝟙 X) (t : LB.Gen (L.pull F)) (ht : t.IsGen)
    (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  subst hF
  have le : ∀ p : M.ι × L.ι, M.U p.1 ⊓ L.U p.2 ≤ (L.pull (𝟙 X)).U (fun _ => p.2) :=
    fun p y hy => Set.mem_iInter.2 fun _ => hy.2
  refine ⟨⟨fun p => (res (le p) (t.s fun _ => p.2))⁻¹⟩, fun p q => ?_⟩
  have hle : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤
      (L.pull (𝟙 X)).U (fun _ => p.2) ⊓ (L.pull (𝟙 X)).U (fun _ => q.2) := inf_le_inf (le p) (le q)
  have key := congrArg (res hle) (ht (fun _ => p.2) (fun _ => q.2))
  erw [map_mul, DVR.res_res', DVR.res_res'] at key
  have aux : ∀ {G : Type} [CommGroup G] (a g b a' m g' b' : G), a = g * b → a' = a⁻¹ → m = 1 → g' = g → b' = b⁻¹ →
      a' = m * g'⁻¹ * b' := by
    rintro G _ a g b a' m g' b' rfl rfl rfl rfl rfl
    rw [_root_.one_mul, mul_inv]
  refine aux _ _ _ _ _ _ _ key ((map_inv _ _).trans (congrArg _ (DVR.res_res' _ _ _)))
    ((congrArg _ (hM _ _)).trans (map_one _)) ?_ ((map_inv _ _).trans (congrArg _ (DVR.res_res' _ _ _)))
  dsimp only [LB.pull, LB.LinComb]
  erw [Fintype.prod_unique, zpow_one, DVR.res_res']
  rfl

theorem tmap_zero {J : Type} {b : TBase o k} (s : S ⟶ Sp o) {s' : S' ⟶ Sp o} (t : TObj 0 k J b s') (f : S' ⟶ S) :
    TMap t (zeroObj J b s) f := by
  haveI := isIso_of_dim_zero t.A t.ab t.dim
  obtain ⟨r, hr⟩ := t.rigid
  have he : (eSec t.A : S' ⟶ t.A.left) ≫ t.A.hom = 𝟙 S' := Over.w η[t.A]
  have hF : t.A.hom ≫ (eSec t.A : S' ⟶ t.A.left) = 𝟙 _ := by
    rw [← cancel_mono t.A.hom, Category.assoc, he]; simp
  refine ⟨t.A.hom ≫ f, ⟨?_, fun T x y x₀ y₀ _ _ => ?_⟩,
    lbIso_of_gen _ _ _ hF _ (DVR.pullGen_isGen _ _ _ r hr t.A.hom) (linComb_triv_g _ _),
    fun i => Fin.elim0 i, fun j => ?_⟩
  · show IsPullback (t.A.hom ≫ f) t.A.hom (𝟙 S) f
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · have h1 : (x₀ * y₀).left ≫ 𝟙 S = T.hom ≫ f := Over.w (x₀ * y₀)
    exact ((Category.comp_id _).symm.trans h1).trans
      ((congrArg (· ≫ f) (Over.w (x * y))).symm.trans (Category.assoc _ _ _))
  · show (t.act j).left ≫ t.A.hom ≫ f = (t.A.hom ≫ f) ≫ 𝟙 S
    rw [← Category.assoc, Over.w (t.act j), Category.comp_id]

theorem zero_hasTh_unit {J : Type} {N : ℕ} (hN : Odd N) (b : TBase o (N ^ 2)) {R : Type} [CommRing R] (β : o →+* R)
    (x : Sp R ⟶ S) (s : S ⟶ Sp o) (v : Ix 0 (N ^ 2) → R) (c : Rˣ) (hv : ∀ a, v a = c) : (zeroObj J b s).HasTh x v := by
  obtain ⟨h1, h2, h3⟩ := zero_hasTh (J := J) hN b β x s
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  refine ⟨V, hV, th, s1, α, τ, U, s2, w,
    (show Γ((Out.overRes V).left, ⊤)ˣ from
      Units.map (V.ι.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toMonoidHom c) * u,
    a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have h := a8 i
  simp only [map_one] at h
  erw [Units.val_mul, _root_.mul_assoc, ← h, _root_.mul_one]
  simp only [hv]
  rfl

def thetaFamZero (n N : ℕ) (hN : Odd N) (J : Type) (b : TBase ℂ (N ^ 2)) :
    ThetaFam (g := 0) (J := J) (b := b) n (RingHom.id ℂ) (fun _ => True) where
  MM := Sp ℂ
  s := spMap (RingHom.id ℂ)
  qproj := by
    haveI := GlobalTheory.ProjSpace.Model.isIso_str_zero (R := ℂ)
    exact ⟨0, inv (PSpace.str ℂ 0), inferInstance, inferInstance, by simp [spMap]⟩
  flat := by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]; infer_instance
  reduced := inferInstance
  univ := zeroObj J b _
  dense := by rw [zero_fromC]; exact dense_univ
  loc := fun R _ _ β x _ => ⟨fun _ => 1, zero_hasTh hN b β x _, fun F hF => by
    have h0 : MvPolynomial.eval₂ (RingHom.id ℂ) (fun _ => 1) F = 0 := by
      simp only [thIdeal, Ideal.mem_iInf] at hF
      exact hF (zeroObj J b _) (fun _ => 1) ⟨trivial, zero_hasTh hN b (RingHom.id ℂ) _ _⟩
    have h1 := congrArg β h0
    rw [MvPolynomial.eval₂_comp_left, map_zero] at h1
    simpa [Function.comp_def] using h1, fun q hq a => ⟨0, (Ideal.ne_top_iff_one q).1 hq.ne_top⟩⟩
  pts := fun R _ β v hv => by
    haveI : Subsingleton (Ix 0 (N ^ 2)) := ⟨fun _ _ => funext fun i => Fin.elim0 i⟩
    have hu : IsUnit (v 0) := by
      by_contra hn
      obtain ⟨m, hm, hmv⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
      obtain ⟨c, hc⟩ := hv.2 m hm.isPrime 0
      exact hc (by rwa [Subsingleton.elim (0 + (N / n) • c) 0])
    refine ⟨spMap β, ⟨by simp [spMap], zero_hasTh_unit hN b β _ _ v hu.unit fun a => ?_⟩, fun y hy => ?_⟩
    · rw [Subsingleton.elim a 0]; rfl
    · simpa [spMap] using hy.1
  rep := fun S s' t _ _ => ⟨s', ⟨by simp [spMap], tmap_zero _ t _⟩, fun y hy => by simpa [spMap] using hy.1⟩
  unram := fun K _ x _ h _ _ => by simpa [spMap] using h

theorem linComb_g_one {X Y : Scheme.{0}} (M : LB X) (hg : ∀ i j, M.g i j = 1) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : (LB.LinComb M φ ε).ι) : (LB.LinComb M φ ε).g j j' = 1 :=
  Finset.prod_eq_one fun _ _ => by rw [hg, map_one]; erw [map_one]; exact one_zpow _

theorem zero_shape {J : Type} (b : TBase o k) (s : S ⟶ Sp o) (Mat κ) : (zeroObj J b s).Shape Mat κ := by
  refine fun j => ⟨fun i => Fin.elim0 i, ?_⟩
  show Out.RelAmple (𝟙_ (Over S)) (LB.LinComb (trivLB _) (K := Fin 2) ![𝟙 _, 𝟙 _] ![(κ : ℤ), -1])
  generalize hM : LB.LinComb (trivLB (𝟙_ (Over S)).left) (Y := (𝟙_ (Over S)).left) (K := Fin 2) ![𝟙 _, 𝟙 _] ![(κ : ℤ), -1] = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

example : Nonempty (ThetaFam (g := 0) (J := Unit) (b := baseC (9 ^ 2) (by norm_num)) 3 (RingHom.id ℂ) (fun _ => True)) :=
  ⟨thetaFamZero 3 9 (by decide) _ _⟩

theorem linComb_iso_triv {X X' Y : Scheme.{0}} {L : LB X'} (hL : L.IsLB) {F : X' ⟶ X} (H : LBIso L ((trivLB X).pull F))
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X')) (ε : K → ℤ) {M : LB Y} (hM : M.IsLB) (hg : ∀ i j, M.g i j = 1) :
    LBIso (LB.LinComb L ψ ε) M := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ (trivLB_isLB _) _ _) hM
    (iso_linComb ((isGen_iff w).1 hw) ψ ε) (lbIso_of_g _ _ (linComb_triv_g _ _) hg)

theorem shape_prim_of_dim_zero {J : Type} {b : TBase o k} {R : Type} [CommRing R] {s : Sp R ⟶ Sp o} (t : TObj 0 k J b s)
    (Mat κ) (w w' : J) : t.Shape Mat κ ∧ t.Prim w w' := by
  haveI := isIso_of_dim_zero t.A t.ab t.dim
  letI := t.ab.comm
  obtain ⟨φ, h, hL, -, -⟩ := tmap_zero s t (𝟙 _)
  have hL' : LBIso t.L ((trivLB (Sp R)).pull φ) := hL
  have lb : ∀ {Y : Scheme.{0}} {K : Type} [Fintype K] (ψ : K → (Y ⟶ t.A.left)) (ε : K → ℤ),
      (LB.LinComb t.L ψ ε).IsLB := fun _ _ => DVR.linComb_isLB _ t.isLB _ _
  have lb' : ((trivLB (Sp R)).pull φ).IsLB := DVR.linComb_isLB _ (trivLB_isLB _) _ _
  refine ⟨fun j => ⟨fun i => Fin.elim0 i, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := linComb_iso_triv t.isLB hL' (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1] lb'
      (linComb_triv_g _ _)
    exact relAmple_pull h.1 (trivLB_isLB _) (lb _ _) ((isGen_iff u).1 hu) ⊤ (isAffineOpen_top _) (fun _ => trivial)
      (zeroPolAV (Sp R)).ample
  · apply Over.OverMorphism.ext
    rw [← cancel_mono t.A.hom, Over.w, Over.w]
  · exact LBIso.trans (lb _ _) (trivLB_isLB _) (lb _ _)
      (linComb_iso_triv t.isLB hL' _ _ (trivLB_isLB _) fun _ _ => rfl)
      (linComb_iso_triv t.isLB hL' _ _ (trivLB_isLB _) fun _ _ => rfl).symm
  · exact LBIso.trans t.isLB lb' (lb _ _) hL' (linComb_iso_triv t.isLB hL' _ _ lb' (linComb_triv_g _ _)).symm

theorem goodClass_zero {N : ℕ} (hN : Odd N) {J : Type} (b : TBase o (N ^ 2)) (em : o →+* ℂ) (Mat κ) (w w' : J) :
    GoodClass (g := 0) (b := b) em (fun _ => True) Mat κ w w' 0 where
  iso := fun _ _ _ _ => trivial
  shape := fun t _ => shape_prim_of_dim_zero t Mat κ w w'
  fam := ⟨1, fun _ => Set.univ, fun _ _ _ => 1, fun _ => ⟨isOpen_univ, isPreconnected_univ,
      fun _ => differentiableOn_const _, fun _ _ => ⟨⟨zeroObj J b _, trivial, zero_hasTh hN b em _ _⟩,
        (Set.toFinite _).countable⟩⟩,
    fun t _ => ⟨0, 0, trivial, (GlobalTheory.hasTh_iff_of_tmap o 0 N J b _ (spMap em) (zeroObj J b _) _ (spMap em) t (𝟙 _) ℂ _ _
      (tmap_zero _ t _)).2 (zero_hasTh hN b em _ _)⟩⟩

theorem odd_of_goodClass {g N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N ^ 2) J b (spMap em) → Prop} {Mat κ} {w w' : J} {d : ℕ} (h : GoodClass em C Mat κ w w' d)
    (t) (ht : C t) : Odd N := by
  obtain ⟨r, B, θ, -, h2⟩ := h.fam
  obtain ⟨i, z, -, hz⟩ := h2 t ht
  exact hz.1

theorem nonempty_of_thetaFam {n N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {em : o →+* ℂ}
    {C : TObj 0 (N ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) (t) (ht : C t) : Nonempty F.MM := by
  have hd : Dense (fromSet em C (zeroObj J b (spMap em))) := fun p =>
    subset_closure ⟨ℂ, inferInstance, 𝟙 _, ⟨p, rfl⟩, ℂ, inferInstance, em, RingHom.id ℂ, RingHom.id ℂ, zeroObj J b _,
      zeroObj J b _, t, rfl, by simp [spMap], zero_tmap _ _ _ _, zero_tmap _ _ _ _, tmap_zero _ _ _, ht⟩
  obtain ⟨f, -, -⟩ := F.rep _ _ _ inferInstance hd
  exact ⟨f (IsLocalRing.closedPoint ℂ)⟩

theorem not_goodClass_zero_succ {N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {em : o →+* ℂ}
    {C : TObj 0 (N ^ 2) J b (spMap em) → Prop} {Mat κ} {w w' : J} {d : ℕ}
    (hne : ∀ (t : TObj 0 (N ^ 2) J b (spMap em)) v, t.HasTh (𝟙 _) v → v 0 ≠ 0) (t) (ht : C t) :
    ¬ GoodClass em C Mat κ w w' (d + 1) := by
  intro h
  haveI : Subsingleton (Ix 0 (N ^ 2)) := ⟨fun _ _ => funext fun i => Fin.elim0 i⟩
  obtain ⟨r, B, θ, h1, h2⟩ := h.fam
  obtain ⟨i, z, hz, hv⟩ := h2 t ht
  have hc := ((h1 i).2.2.2 z hz).2
  have he : {z' ∈ B i | ∃ c : ℂ, θ i z' = c • θ i z} = B i := by
    refine Set.Subset.antisymm (fun _ h => h.1) fun y hy => ⟨hy, θ i y 0 / θ i z 0, funext fun a => ?_⟩
    rw [Subsingleton.elim a 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (hne t _ hv)]
  rw [he] at hc
  have h0 := hc.measure_zero (MeasureTheory.volume : MeasureTheory.Measure (Fin (d + 1) → ℂ))
  exact ((h1 i).1.measure_pos MeasureTheory.volume ⟨z, hz⟩).ne' h0

example {g n N : ℕ} (h : n ∣ N) (c : Ix g (N ^ 2)) : n • N • (N / n) • c = 0 := by
  rw [smul_comm n N, smul_smul n, Nat.mul_div_cancel' h, smul_smul, ← sq]
  funext i
  simp

end GlobalTheory.ZM.Model
end
