import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.Height
open IsLocalRing

def ev (R : Type) [CommRing R] [IsLocalRing R] : (Sp R).presheaf.stalk (closedPoint R) →+* R :=
  (stalkClosedPointIso (CommRingCat.of R)).hom.hom

theorem isUnit_ev {R : Type} [CommRing R] [IsLocalRing R] (a : (Sp R).presheaf.stalk (closedPoint R)) :
    IsUnit (ev R a) ↔ IsUnit a :=
  MulEquiv.isUnit_map (stalkClosedPointIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

theorem ev_gs {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) (U : X.Opens)
    (h : b (closedPoint R) ∈ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) :
    ev R (gs b (closedPoint R) U f) = (b.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f := by
  rw [gs_eq b _ U h, ← germ_stalkClosedPointIso_hom]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, ev]
  congr 1
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') (closedPoint R) (Set.mem_univ _) _).symm

theorem isUnit_gs {X Y : Scheme.{0}} (b : Y ⟶ X) (y : Y) (U : X.Opens) (h : b y ∈ U) (f : Γ(X, U)) :
    IsUnit (gs b y U f) ↔ b y ∈ X.basicOpen f := by
  rw [gs_eq b _ U h, ← Y.mem_basicOpen _ y h, ← Scheme.preimage_basicOpen]
  rfl

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem integral_value (O : ValuationSubring K) {X : Scheme.{0}} (b : Sp O ⟶ X) (U : X.Opens)
    (h : b (closedPoint O) ∈ U) :
    (spMap O.subtype ≫ b) (closedPoint K) ∈ U ∧ ∀ f : Γ(X, U), ∃ a : O,
      (a : K) = ev K (gs (spMap O.subtype ≫ b) (closedPoint K) U f) ∧
        (IsUnit a ↔ b (closedPoint O) ∈ X.basicOpen f) := by
  have h1 : ⊤ ≤ b ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of O) b h).ge
  have h2 : ⊤ ≤ (spMap O.subtype ≫ b) ⁻¹ᵁ U := fun x _ => h1 (x := spMap O.subtype x) trivial
  refine ⟨h2 trivial, fun f => ⟨ev O (gs b _ U f), ?_, (isUnit_ev _).trans (isUnit_gs b _ U h f)⟩⟩
  rw [ev_gs b U h h1, ev_gs _ U (h2 trivial) h2,
    ← Scheme.Hom.appLE_comp_appLE (spMap O.subtype) b U ⊤ ⊤ h1 le_rfl]
  have h3 : (spMap O.subtype).appLE ⊤ ⊤ le_rfl = (spMap O.subtype).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

theorem ext_unique (O : ValuationSubring K) (B : Over (Sp k)) [IsSeparated B.hom] {b b' : Sp O ⟶ B.left}
    (h : spMap O.subtype ≫ b = spMap O.subtype ≫ b') : b = b' := by
  have : IsDominant (spMap O.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated B.hom (ext_of_isDominant (spMap O.subtype) ?_) _ h
  rw [← Category.assoc, h, Category.assoc]

theorem ext_exists (O : ValuationSubring K) (hO : ∀ c, algebraMap k K c ∈ O) (B : Over (Sp k))
    [IsProper B.hom] (x : Over.mk (spMap (algebraMap k K)) ⟶ B) :
    ∃ b : Sp O ⟶ B.left, spMap O.subtype ≫ b = x.left := by
  have hE : ValuativeCriterion.Existence B.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed B.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.hom).1
  obtain ⟨⟨l⟩⟩ := hE { R := O, K := K, i₁ := x.left, i₂ := spMap ((algebraMap k K).codRestrict O hO), commSq := ⟨(Over.w x).trans (by rw [← Spec.map_comp]; rfl)⟩ }
  exact ⟨l.l, l.fac_left⟩

theorem centre_finite (Pl : Places k K) (B : Over (Sp k)) [IsProper B.hom]
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) (b : ∀ i, Sp (Pl.O i) ⟶ B.left)
    (hb : ∀ i, spMap (Pl.O i).subtype ≫ b i = x.left) (U : B.left.Opens) (hU : x.left (closedPoint K) ∈ U) :
    {i | b i (closedPoint (Pl.O i)) ∉ U}.Finite := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have hx : ⊤ ≤ x.left ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of K) x.left hxV).ge
  let ψ : Γ(B.left, V) ⟶ CommRingCat.of K := x.left.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hψ : Spec.map ψ ≫ hV.fromSpec = x.left := AffinePointValues.specMap_appLE_fromSpec hV _ hx
  let c : CommRingCat.of k ⟶ Γ(B.left, V) := (Scheme.ΓSpecIso (.of k)).inv ≫ B.hom.appLE ⊤ V le_top
  have hc : c ≫ ψ = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← AffinePointValues.fromSpec_comp hV B.hom le_top, ← Category.assoc, hψ]
    exact Over.w x
  have hft : c.hom.FiniteType := (B.hom.finiteType_appLE (isAffineOpen_top _) hV le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  letI := c.hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  have hfin : ∀ a : K, {i | a ∉ Pl.O i}.Finite := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · refine (Pl.fin (Units.mk0 a ha)).subset fun i hi h0 => hi ?_
      exact (Pl.mem i (Units.mk0 a ha)).2 (le_of_eq (Eq.symm h0))
  refine (T.finite_toSet.biUnion fun a _ => hfin (ψ.hom a)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hn
  have hall : ∀ a, ψ.hom a ∈ Pl.O i := fun a => by
    have ha : a ∈ Algebra.adjoin k (T : Set Γ(B.left, V)) := hT ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a h => exact hn a h
    | algebraMap r => exact (congrArg (fun q => q.hom r) hc) ▸ Pl.const i r
    | add a a' _ _ h h' => rw [map_add]; exact add_mem h h'
    | mul a a' _ _ h h' => rw [map_mul]; exact mul_mem h h'
  have e : b i = Spec.map (CommRingCat.ofHom (ψ.hom.codRestrict (Pl.O i) hall)) ≫ hV.fromSpec := by
    refine ext_unique _ B ?_
    rw [hb, ← hψ, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine hi (hVU ?_)
  rw [e]
  exact hV.range_fromSpec.le ⟨_, rfl⟩

def ord (Pl : Places k K) (i : Pl.I) : ((Sp K).presheaf.stalk (closedPoint K))ˣ →* Multiplicative ℤ :=
  (MonoidHom.mk' (fun x : Kˣ => Multiplicative.ofAdd (Pl.v i x)) fun x y => by
    rw [Pl.v_mul, ofAdd_add]).comp (Units.map (ev K).toMonoidHom)

def od (Pl : Places k K) (i : Pl.I) (u : ((Sp K).presheaf.stalk (closedPoint K))ˣ) : ℤ := (ord Pl i u).toAdd

variable (Pl : Places k K)

theorem od_fin (u) : (Function.support fun i => od Pl i u).Finite := Pl.fin _

theorem od_sum (u) : ∑ᶠ i, od Pl i u = 0 := Pl.sum _

theorem od_mul (i u u') : od Pl i (u * u') = od Pl i u + od Pl i u' := by
  simp only [od, map_mul, toAdd_mul]

theorem od_zpow (i u) (n : ℤ) : od Pl i (u ^ n) = n * od Pl i u := by
  simp only [od, map_zpow, toAdd_zpow, smul_eq_mul]

theorem od_inv (i u) : od Pl i u⁻¹ = -od Pl i u := by
  simp only [od, map_inv, toAdd_inv]

theorem od_prod (i) {n : ℕ} (u : Fin n → _) : od Pl i (∏ m, u m) = ∑ m, od Pl i (u m) := by
  simp only [od, map_prod, toAdd_prod]

theorem od_mem (i u) : ev K u.val ∈ Pl.O i ↔ 0 ≤ od Pl i u := Pl.mem i (Units.map (ev K).toMonoidHom u)

theorem od_section (i) {X : Scheme.{0}} (b : Sp (Pl.O i) ⟶ X) (x : Sp K ⟶ X)
    (hb : spMap (Pl.O i).subtype ≫ b = x) (U : X.Opens) (h : b (closedPoint (Pl.O i)) ∈ U) (f : Γ(X, U))
    (u : ((Sp K).presheaf.stalk (closedPoint K))ˣ) (hu : gs x (closedPoint K) U f = u.val) :
    0 ≤ od Pl i u ∧ (od Pl i u = 0 ↔ b (closedPoint (Pl.O i)) ∈ X.basicOpen f) := by
  subst hb
  obtain ⟨a, ha, hi⟩ := (integral_value _ b U h).2 f
  rw [hu] at ha
  have h0 : 0 ≤ od Pl i u := (od_mem Pl i u).1 (ha ▸ a.2)
  have hm : (a : K) * ev K u⁻¹.val = 1 := by rw [ha, ← map_mul, Units.mul_inv, map_one]
  refine ⟨h0, Iff.trans ⟨fun h1 => ?_, fun h1 => ?_⟩ hi⟩
  · have h2 : ev K u⁻¹.val ∈ Pl.O i := (od_mem Pl i _).2 (by rw [od_inv, h1]; rfl)
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : Pl.O i) (Subtype.ext hm)
  · obtain ⟨a', ha'⟩ := h1.exists_right_inv
    have h3 : (a : K) * a' = 1 := congrArg Subtype.val ha'
    have h4 : ev K u⁻¹.val = a' := mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h3) (hm.trans h3.symm)
    have h2 := (od_mem Pl i u⁻¹).1 (h4 ▸ a'.2)
    rw [od_inv] at h2
    omega

theorem od_unit (i) {X : Scheme.{0}} (b : Sp (Pl.O i) ⟶ X) (x : Sp K ⟶ X)
    (hb : spMap (Pl.O i).subtype ≫ b = x) (U : X.Opens) (h : b (closedPoint (Pl.O i)) ∈ U) (f : Γ(X, U)ˣ) :
    od Pl i (gm x (closedPoint K) U f) = 0 := by
  have hx : x (closedPoint K) ∈ U := hb ▸ (integral_value _ b U h).1
  refine (od_section Pl i b x hb U h f.val _ (gs_unit x _ U hx f)).2.2 ?_
  rw [X.basicOpen_of_isUnit f.isUnit]
  exact h

theorem gs_pw {X Y : Scheme.{0}} {L : LB X} {N : ℤ} (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : x y ∈ L.U i) (hj : x y ∈ L.U j) :
    gs x y (L.U i) (s.f i) = (gm x y (L.U i ⊓ L.U j) (L.g i j) ^ N).val * gs x y (L.U j) (s.f j) := by
  have hm : x y ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (s.compat i j)).trans
    ((gs_mul x y _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res x y _ hm _))))
  exact (gs_unit x y _ hm (L.g i j ^ N)).trans (congrArg Units.val (map_zpow _ _ _))

end GlobalTheory.SS.Height

namespace GlobalTheory.SS
open IsLocalRing Height

theorem exists_height : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (Pl : Places k K) (B : Over (Sp k)), IsProper B.hom → ∀ (L : LB B.left), L.IsLB → ∃ h : (Over.mk (spMap (algebraMap k K)) ⟶ B) → ℤ, (∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (n : ℕ) (φ : Fin n → (Z ⟶ B)) (ε : Fin n → ℤ), (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) → ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0) ∧ ∀ (N : ℕ) (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Over.mk (spMap (algebraMap k K)) ⟶ B), 1 ≤ N → Set.range x.left ⊆ Out.nonzeroLocus s → 0 ≤ h x ∧ (h x = 0 → ∀ i, ∃ b : Sp (Pl.O i) ⟶ B.left, spMap (Pl.O i).subtype ≫ b = x.left ∧ Set.range b ⊆ Out.nonzeroLocus s) := by
  intro k K _ _ _ Pl B hB L hL
  choose b hb using fun (x : Over.mk (spMap (algebraMap k K)) ⟶ B) (i : Pl.I) =>
    ext_exists (Pl.O i) (Pl.const i) B x
  choose ch hch using exists_chart hL
  let j₀ : (Over.mk (spMap (algebraMap k K)) ⟶ B) → L.ι := fun x => ch (x.left (closedPoint K))
  let j : (Over.mk (spMap (algebraMap k K)) ⟶ B) → Pl.I → L.ι := fun x i => ch (b x i (closedPoint (Pl.O i)))
  let g : (Over.mk (spMap (algebraMap k K)) ⟶ B) → Pl.I → ℤ := fun x i =>
    od Pl i (gm (Y := Sp K) x.left (closedPoint K) (L.U (j x i) ⊓ L.U (j₀ x)) (L.g (j x i) (j₀ x)))
  have hj : ∀ x i, x.left (closedPoint K) ∈ L.U (j x i) := fun x i =>
    hb x i ▸ (integral_value _ (b x i) _ (hch _)).1
  have hg : ∀ x, (Function.support (g x)).Finite := fun x =>
    (centre_finite Pl B x (b x) (hb x) (L.U (j₀ x)) (hch _)).subset fun i hi => by
      by_contra hn
      exact hi (od_unit Pl i (b x i) x.left (hb x i) (L.U (j x i) ⊓ L.U (j₀ x)) ⟨hch _, not_not.1 hn⟩ _)
  refine ⟨fun x => ∑ᶠ i, g x i, ?_, ?_⟩
  · rintro Z hZ n φ ε ⟨t, ht⟩ z
    have m₀ : z.left (closedPoint K) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j₀ (z ≫ φ m)) :=
      Set.mem_iInter.2 fun m => hch _
    have key : ∀ i, ∑ m, ε m * g (z ≫ φ m) i = -od Pl i (gm (Y := Sp K) z.left (closedPoint K)
        (LB.wchart L (fun m => (φ m).left) (fun m => j₀ (z ≫ φ m))) (t.s (fun m => j₀ (z ≫ φ m)))) := by
      intro i
      obtain ⟨c, hc⟩ := ext_exists (Pl.O i) (Pl.const i) Z z
      have e : ∀ m, b (z ≫ φ m) i = c ≫ (φ m).left := fun m =>
        ext_unique _ B (by rw [hb, ← Category.assoc, hc]; rfl)
      have m₁ : c (closedPoint (Pl.O i)) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j (z ≫ φ m) i) :=
        Set.mem_iInter.2 fun m => by
          have := hch (b (z ≫ φ m) i (closedPoint (Pl.O i)))
          rw [e m] at this
          simp only [j]
          rw [e m]
          exact this
      have m₂ : z.left (closedPoint K) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j (z ≫ φ m) i) :=
        Set.mem_iInter.2 fun m => hj (z ≫ φ m) i
      have h1 := ((od_unit Pl i c z.left hc _ m₁ _).symm.trans
        (congrArg (od Pl i) (gen_trans ht (Z := Sp K) z.left (closedPoint K) m₂ m₀))).trans (od_mul Pl i _ _)
      refine eq_neg_of_add_eq_zero_left (Eq.trans ?_ h1.symm)
      congr 1
      exact ((od_prod Pl i _).trans (Finset.sum_congr rfl fun m _ => od_zpow Pl i _ _)).symm
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ (fun i m => ε m * g (z ≫ φ m) i)
      (fun m _ => (hg _).subset (Function.support_mul_subset_right _ _))]
    simp only [key]
    rw [finsum_neg_distrib, od_sum, neg_zero]
  · intro N s x hN hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hx ⟨closedPoint K, rfl⟩)
    have ha' : x.left (closedPoint K) ∈ L.U a := B.left.basicOpen_le _ ha
    obtain ⟨u, hu⟩ := (isUnit_gs (Y := Sp K) x.left _ _ ha' _).2 ha
    have h₀ := gs_pw s (Y := Sp K) x.left (closedPoint K) (hch _) ha'
    rw [← hu, ← Units.val_mul] at h₀
    generalize _ * u = u₀ at h₀
    have key : ∀ i, 0 ≤ (N : ℤ) * g x i + od Pl i u₀ ∧ ((N : ℤ) * g x i + od Pl i u₀ = 0 ↔
        b x i (closedPoint (Pl.O i)) ∈ B.left.basicOpen (s.f (j x i))) := fun i => by
      have h₁ := gs_pw s (Y := Sp K) x.left (closedPoint K) (hj x i) (hch _)
      rw [h₀, ← Units.val_mul] at h₁
      have := od_section Pl i (b x i) x.left (hb x i) _ (hch _) _ _ h₁
      rwa [od_mul, od_zpow] at this
    have f₁ : (Function.support fun i => (N : ℤ) * g x i).Finite :=
      (hg _).subset (Function.support_mul_subset_right _ _)
    have hs : ∑ᶠ i, ((N : ℤ) * g x i + od Pl i u₀) = N * ∑ᶠ i, g x i := by
      rw [finsum_add_distrib f₁ (od_fin Pl u₀), od_sum, add_zero, mul_finsum]
    have hp : 0 ≤ (N : ℤ) * ∑ᶠ i, g x i := hs ▸ finsum_nonneg fun i => (key i).1
    refine ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hN)).1 hp, fun h0 i => ⟨b x i, hb x i, ?_⟩⟩
    have h0' : ∑ᶠ i, g x i = 0 := h0
    rw [h0', mul_zero] at hs
    have hi : (N : ℤ) * g x i + od Pl i u₀ = 0 := by
      by_contra hne
      exact (finsum_pos (fun i => (key i).1) ⟨i, lt_of_le_of_ne (key i).1 (Ne.symm hne)⟩
        ((f₁.union (od_fin Pl u₀)).subset (Function.support_add _ _))).ne' hs
    have hm : b x i (closedPoint (Pl.O i)) ∈ Out.nonzeroLocus s :=
      TopologicalSpace.Opens.mem_iSup.2 ⟨_, (key i).2.1 hi⟩
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Pl.O i)) (b x i) hm).ge (x := y) trivial

end GlobalTheory.SS
