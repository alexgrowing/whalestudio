import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem hasTh_exists (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hK : (m : K) ≠ 0) :
    ∃ c : Fin ((m ^ 2) ^ (2 * P.g)) → K, HasTh P.A P.L ρ m (𝟙 (Sp K)) c ∧ (3 ≤ m → c ≠ 0) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hK' : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hK
  have hc := TorsionFieldExt.card_torsion hL P (𝟙 (Sp K)) hK'
  have hm0 : 0 < m := hm.pos
  have : Finite {y : Over.mk (𝟙 (Sp K)) ⟶ P.A // y ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  let e := (Finite.equivFinOfCardEq hc).symm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hL K P m hm hK (fun a => (e a).1) (fun a => (e a).2)
  let c : Fin ((m ^ 2) ^ (2 * P.g)) → K := fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v a)
  have hvc : v = fun a => GlobalTheory.Ex.fnOf (c a) := funext fun a =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v a)).symm
  rw [hvc] at hv
  obtain ⟨th, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ hρ m _ (fun a => (e a).1) c (fun a => (e a).2) hv
  refine ⟨c, ⟨th, fun a => (e a).1, hg, fun a b h => e.injective (Subtype.ext h), hth, fun K' _ _ i p hp => ?_⟩,
    fun h3 => ?_⟩
  · obtain ⟨y, hy, hyp⟩ := (GlobalTheory.torsion_points_field_extension hL _ P K K' i (𝟙 _)).2 _ p hK' hp
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    rw [← hyp]
    simp
  · obtain ⟨-, -, h₁, h₂⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate hL K _ P (𝟙 _) m hm hK _ (fun a => (e a).1) (fun a => (e a).2)
    exact (h₂ h3 (fun y hy => ⟨e.symm ⟨y, hy⟩, by simp⟩) 1 1 c ((h₁ c).1 hv) ((h₁ c).1 hv)).2

theorem length_eq {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {K : Type} [Field K]
    (hK : (m : K) ≠ 0) (x : Sp K ⟶ S) {θ : SecAt P.A P.L x} {N : ℕ} {pt : Fin N → (Over.mk x ⟶ P.A)} {c : Fin N → K}
    (H : ThList P.A P.L ρ m x θ pt c) : N = (m ^ 2) ^ (2 * P.g) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let i : K →+* AlgebraicClosure K := algebraMap _ _
  have hK' : ((m ^ 2 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i, map_ne_zero, Nat.cast_pow]; exact pow_ne_zero _ hK
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  rw [← TorsionFieldExt.card_torsion hL P (spMap i ≫ x) hK', ← Nat.card_fin N]
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨u ≫ pt a, by
    rw [← MonObj.comp_pow, (H.2.1 a).1, MonObj.comp_one]⟩) ⟨fun a b h => ?_, fun p => ?_⟩)
  · exact H.1 (TorsionFieldExt.comp_injective u _ (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := H.2.2 _ i p.1 p.2
    exact ⟨a, Subtype.ext (Over.OverMorphism.ext ha.symm)⟩

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    (GlobalTheory.PolBaseChange.lbIso_refl P.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)⟩

theorem symTup_two {R : Type} [CommRing R] (a b : R) : symTup ![a, b] = ![(a + b) ^ 2, a * b] := by
  funext j
  fin_cases j
  · simp only [symTup, Finset.esymm_map_val]
    simp [Finset.powersetCard_one, Fin.sum_univ_two]
  · have : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by decide
    simp only [symTup, Finset.esymm_map_val]
    simp [this]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (c ∘ σ) = symTup c := by
  funext j
  rw [symTup, symTup, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem symTup_smul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun a => t * c a) j = t ^ N.factorial * symTup c j := by
  have hd : ((j : ℕ) + 1) * (N.factorial / ((j : ℕ) + 1)) = N.factorial :=
    Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)
  have : (Finset.univ.val.map fun a => t * c a).esymm ((j : ℕ) + 1) =
      t ^ ((j : ℕ) + 1) * (Finset.univ.val.map c).esymm ((j : ℕ) + 1) := by
    rw [Finset.esymm_map_val, Finset.esymm_map_val, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hs).2]
  rw [symTup, symTup, this, mul_pow, ← pow_mul, hd]

theorem symTup_eq_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : symTup c = 0) : c = 0 := by
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := fun k hk hN => by
    have := congrFun h ⟨k - 1, by omega⟩
    simp only [symTup, Pi.zero_apply, Nat.sub_add_cancel hk] at this
    exact (pow_eq_zero_iff'.1 this).1
  funext a
  have h1 := congrArg (Polynomial.eval (-c a)) (Multiset.prod_X_add_C_eq_sum_esymm (Finset.univ.val.map c))
  have hcard : Multiset.card (Finset.univ.val.map c) = N := by simp
  have hN : 0 < N := a.pos
  rw [hcard, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero (by
    simp only [Multiset.map_map, Multiset.mem_map]
    exact ⟨a, by simp, by simp⟩), Finset.sum_eq_single 0 (fun k hk h0 => by
      rw [he k (Nat.pos_of_ne_zero h0) (by simpa [Nat.lt_succ_iff] using hk)]; simp) (by simp)] at h1
  simp only [Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.prod_zero,
    Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero, Polynomial.eval_pow, Polynomial.eval_X] at h1
  simpa [hN.ne'] using h1.symm

theorem prim_one_two : Prim (Int.castRingHom ℚ) ![(1 : ℚ), 2] := by
  refine ⟨fun a => ?_, 0, by simp, by simpa using RingHom.isIntegralElem_one _⟩
  fin_cases a
  · simpa using RingHom.isIntegralElem_one _
  · simpa using RingHom.isIntegralElem_map (Int.castRingHom ℚ) (x := 2)

theorem not_prim_two : ¬ Prim (Int.castRingHom ℚ) ![(2 : ℚ)] := by
  rintro ⟨-, a, -, h⟩
  fin_cases a
  have : IsIntegral ℤ ((2 : ℚ)⁻¹) := h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  have h2 : (2 * y : ℚ) = 1 := by rw [show (y : ℚ) = 2⁻¹ from hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    symTup (fun a => i (c a)) j = i (symTup c j) := by
  simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem thG_pull {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {y : T ⟶ P.A} {c : Γ(T.left, ⊤)}
    (H : ThG P.A P.L ρ m θ y c) : ThG P.A P.L ρ m (VVRank.pullS P.A _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hL := P.isLB
  have := P.isAb.comm
  have hp : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A)))
  obtain ⟨w, hw⟩ : LBIso P.L (P.L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS P.A _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec P.A ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec P.A t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thMap_exists (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hK : (m : K) ≠ 0) {n : ℕ} (c : Fin (n + 1) → K)
    (hc : HasTh P.A P.L ρ m (𝟙 (Sp K)) c) (h0 : c ≠ 0) :
    ∃ f : Sp K ⟶ PSpace K n, f ≫ PSpace.str K n = 𝟙 _ ∧ PCrd f (symTup c) ∧ ThMap P.A P.L ρ m (𝟙 _) f := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨j, hj⟩ := Function.ne_iff.1 fun h => h0 (symTup_eq_zero c h)
  have hv : Ideal.span (Set.range (symTup c)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) (IsUnit.mk0 _ hj)
  let f := ProjSpace.pt (RingHom.id K) (symTup c) hv
  have hf : PCrd f (symTup c) := by
    have h1 := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) (RingHom.id K) f
      (by simpa using ProjSpace.pt_str (RingHom.id K) _ hv) (symTup c)).2 ⟨hv, Category.comp_id _⟩
    have h2 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 K n) (GlobalTheory.ProjSpace.coord K n) (𝟙 _) f (symTup c)).1 h1
    rwa [Category.comp_id] at h2
  refine ⟨f, (ProjSpace.pt_str (RingHom.id K) _ hv).trans (Spec.map_id _), hf, fun F _ x c' hc' => ?_⟩
  obtain ⟨i, rfl⟩ := RepUniq.exists_spMap x
  obtain ⟨θ, pt, -, h₁, h₂, h₃⟩ := hc
  obtain ⟨θ', pt', hg, h₁', h₂', h₃'⟩ := hc'
  let β : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap i) rfl
  obtain ⟨r, hr⟩ := hg (VVRank.pullS P.A _ β θ)
  have e₁ : SecM.ofSec P.A (VVRank.pullS P.A _ β θ) = r • SecM.ofSec P.A θ' := Subtype.ext (funext hr)
  let k : F →+* AlgebraicClosure F := algebraMap _ _
  let u : Over.mk (spMap k ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) := Over.homMk (spMap k) rfl
  have hs : ∀ a, ∃ b, β ≫ pt a = pt' b := fun a => by
    obtain ⟨b, hb⟩ := h₃' _ k (u ≫ β ≫ pt a) (by
      rw [← MonObj.comp_pow, ← MonObj.comp_pow, (h₂ a).1, MonObj.comp_one, MonObj.comp_one])
    exact ⟨b, TorsionFieldExt.comp_injective u _ (Over.OverMorphism.ext hb)⟩
  choose s hs using hs
  have hsi : Function.Injective s := fun a a' h =>
    h₁ (TorsionFieldExt.comp_injective β _ ((hs a).trans ((congrArg pt' h).trans (hs a').symm)))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
    exact (IsUnit.mk0 _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK)).map _
  let r₀ : F := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom r
  have key : ∀ a, i (c a) = r₀ * c' (s a) := fun a => by
    have q₁ := thG_pull P hρ β (h₂ a)
    have q₂ := ThG.smul P.isLB e₁ (h₂' (s a))
    rw [hs] at q₁
    have q := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (ThG.unique hL P hm hun q₁ q₂)
    have e₂ : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.Ex.fnOf (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e₂] at q
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply _).symm.trans (q.trans
      ((map_mul _ _ _).trans (congrArg (r₀ * ·) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply _))))
  have hr₀ : r₀ ≠ 0 := fun h => h0 (funext fun a => by
    have := key a
    rw [h, zero_mul] at this
    exact (map_eq_zero i).1 this)
  have e₃ : symTup c' = fun j => ((Units.mk0 r₀ hr₀ ^ (n + 1).factorial)⁻¹ : Fˣ) * i (symTup c j) := funext fun j => by
    rw [← symTup_map, funext key, symTup_smul, Units.eq_inv_mul_iff_mul_eq, ← symTup_perm c' σ]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rfl
  rw [e₃]
  have hb := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB K n) hf).1 F i
  exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB K n) hb).2.1 _

theorem elliptic : ∃ (P : PolAV (Sp ℂ)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (c : Fin 81 → ℂ) (f : Sp ℂ ⟶ PSpace ℂ 80),
    P.g = 1 ∧ ρ.IsGen ∧ PolFib P.A P.L 1 (𝟙 _) ∧ HasTh P.A P.L ρ 3 (𝟙 _) c ∧ c ≠ 0 ∧ PCrd f (symTup c) ∧
      ThMap P.A P.L ρ 3 (𝟙 _) f := by
  have hΔ : IsUnit (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℂ).Δ := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  obtain ⟨P, -, -, hP, -⟩ := GlobalTheory.WeierstrassCurve.exists_polAV ℂ _ hΔ
  obtain ⟨ρ, hr⟩ := P.rigid
  have h := hasTh_exists ℂ P ρ hr 3 (by decide) (by norm_num)
  rw [hP] at h
  obtain ⟨c, hc, h0⟩ := h
  obtain ⟨f, -, hf, hf'⟩ := thMap_exists ℂ P ρ hr 3 (by decide) (by norm_num) (n := 80) c hc (h0 le_rfl)
  exact ⟨P, ρ, c, f, hP, hr, hP ▸ polFib_self P, hc, h0 le_rfl, hf, hf'⟩

theorem thMap_of_ne {K : Type} [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ)
    (hK : (m : K) ≠ 0) {n : ℕ} (hn : n + 1 ≠ (m ^ 2) ^ (2 * P.g)) (f : Sp K ⟶ PSpace K n) :
    ThMap P.A P.L ρ m (𝟙 _) f := by
  rintro F _ x c ⟨θ, pt, -, H⟩
  obtain ⟨i, rfl⟩ := RepUniq.exists_spMap x
  exact absurd (length_eq P ρ m (by rw [← map_natCast i]; exact (map_ne_zero i).2 hK) _ H) hn

theorem thList_pull {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) {m : ℕ}
    {K F : Type} [Field K] [Field F] (i : K →+* F) {x : Sp K ⟶ S} {θ : SecAt P.A P.L x} {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ P.A)} {c : Fin N → K} (H : ThList P.A P.L ρ m x θ pt c) (a : Fin N) :
    ThG P.A P.L ρ m (SecAt.pull P.A P.L θ i)
      ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ pt a) (GlobalTheory.ZH.fn (i (c a))) := by
  have q := thG_pull P hρ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) (H.2.1 a)
  have e : (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x).left.appTop.hom (GlobalTheory.ZH.fn (c a)) =
      GlobalTheory.ZH.fn (i (c a)) :=
    (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [e] at q
  exact q

theorem symAt_of_thList {K : Type} [Field K] (P : PolAV (Sp K)) {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen)
    {m : ℕ} (hm : Odd m) (hK : (m : K) ≠ 0) {θ : SecAt P.A P.L (𝟙 (Sp K))} {N : ℕ}
    {pt : Fin N → (Over.mk (𝟙 (Sp K)) ⟶ P.A)} {c : Fin N → K} (H : ThList P.A P.L ρ m _ θ pt c) :
    SymAt P.A P.L ρ m _ θ (symTup c) := by
  intro F _ i pt' c' ⟨h₁', h₂', h₃'⟩ j
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let β : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap i) rfl
  let k : F →+* AlgebraicClosure F := algebraMap _ _
  let u : Over.mk (spMap k ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) := Over.homMk (spMap k) rfl
  have hs : ∀ a, ∃ b, β ≫ pt a = pt' b := fun a => by
    obtain ⟨b, hb⟩ := h₃' _ k (u ≫ β ≫ pt a) (by
      rw [← MonObj.comp_pow, ← MonObj.comp_pow, (H.2.1 a).1, MonObj.comp_one, MonObj.comp_one])
    exact ⟨b, TorsionFieldExt.comp_injective u _ (Over.OverMorphism.ext hb)⟩
  choose s hs using hs
  have hsi : Function.Injective s := fun a a' h =>
    H.1 (TorsionFieldExt.comp_injective β _ ((hs a).trans ((congrArg pt' h).trans (hs a').symm)))
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
    exact (IsUnit.mk0 _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK)).map _
  have key : ∀ a, i (c a) = c' (s a) := fun a => by
    have q₁ := thList_pull P hρ i H a
    rw [hs] at q₁
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
      (ThG.unique hL P hm hun q₁ (h₂' (s a)))
  rw [← symTup_map, funext key, ← symTup_perm c' σ]
  rfl

theorem hasTh₂_of_hasTh {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} {m m' : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} {N N' : ℕ} {c : Fin N → K} {c' : Fin N' → K} (H : HasTh P.A P.L ρ m x c)
    (H' : HasTh P.A P.L ρ m' x c') : ∃ r : K, HasTh₂ P.A P.L ρ m m' x c fun a => r * c' a := by
  obtain ⟨θ, pt, hg, h⟩ := H
  obtain ⟨θ', pt', hg', h₁, h₂, h₃⟩ := H'
  obtain ⟨r, hr⟩ := hg' θ
  have e₁ : SecM.ofSec P.A θ = r • SecM.ofSec P.A θ' := Subtype.ext (funext hr)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, θ, pt, pt', hg, h, h₁, fun a => ?_, h₃⟩
  have q := ThG.smul P.isLB e₁ (h₂ a)
  have e₂ : GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r * c' a) =
      @id Γ(Sp K, ⊤) r * @id Γ(Sp K, ⊤) (GlobalTheory.ZH.fn (c' a)) :=
    (map_mul (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _ _).trans
      (congrArg (· * _) ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply r))
  rw [e₂]
  exact q

end GlobalTheory.UMin.Model
