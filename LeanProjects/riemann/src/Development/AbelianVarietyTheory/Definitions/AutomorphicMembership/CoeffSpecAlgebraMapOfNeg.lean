import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowLSOfNotDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

abbrev MultiRing (K : Type) [Field K] (r : ℕ) : Type :=
  Localization.Away (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)

namespace MultiRing

variable {K : Type} [Field K] {r : ℕ}

theorem prod_X_ne_zero : (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ h => by simpa using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h

theorem powers_le : Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K) ≤ nonZeroDivisors _ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors prod_X_ne_zero

instance instIsDomain : IsDomain (MultiRing K r) :=
  haveI := GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r
  IsLocalization.isDomain_localization powers_le

instance instIsIntegrallyClosed : IsIntegrallyClosed (MultiRing K r) :=
  haveI := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries K r
  haveI := GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r
  isIntegrallyClosed_of_isLocalization (MultiRing K r)
    (Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)) powers_le

instance instIsNoetherianRing : IsNoetherianRing (MultiRing K r) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)) _ inferInstance

theorem algebraMap_injective : Function.Injective (algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r)) :=
  IsLocalization.injective _ powers_le

def u (i : Fin r) : MultiRing K r := algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r) (MvPowerSeries.X i)

theorem isUnit_u (i : Fin r) : IsUnit (u i : MultiRing K r) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := MultiRing K r) (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))) h

theorem exists_mul_pow (Φ : MultiRing K r) : ∃ (n : ℕ) (f : MvPowerSeries (Fin r) K),
    Φ * (∏ i, u i) ^ n = algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r) f := by
  obtain ⟨⟨f, _, n, rfl⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)) Φ
  exact ⟨n, f, by simpa only [map_pow, map_prod, u] using h⟩

section Spec

variable (a : Fin r → ℕ) (ha : ∀ i, 1 ≤ a i)
include ha

theorem hasSubst : MvPowerSeries.HasSubst fun i => (PowerSeries.X ^ a i : PowerSeries K) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    change PowerSeries.constantCoeff (PowerSeries.X ^ a i : PowerSeries K) = 0
    simp [show a i ≠ 0 from Nat.one_le_iff_ne_zero.1 (ha i)]

def specPS : MvPowerSeries (Fin r) K →+* PowerSeries K :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst a ha)).toRingHom

theorem specPS_apply (f : MvPowerSeries (Fin r) K) :
    specPS a ha f = MvPowerSeries.subst (fun i => (PowerSeries.X ^ a i : PowerSeries K)) f :=
  MvPowerSeries.substAlgHom_apply _ f

@[simp] theorem specPS_X (i : Fin r) : specPS a ha (MvPowerSeries.X i) = (PowerSeries.X ^ a i : PowerSeries K) :=
  MvPowerSeries.substAlgHom_X _ i

@[simp] theorem specPS_C (c : K) : specPS a ha (MvPowerSeries.C c) = PowerSeries.C c :=
  (MvPowerSeries.substAlgHom (R := K) (hasSubst a ha)).commutes c

theorem finite_weight (n : ℕ) : {m : Fin r →₀ ℕ | ∑ i, a i * m i = n}.Finite :=
  (Finsupp.finite_of_nat_weight_eq a (fun i => Nat.one_le_iff_ne_zero.1 (ha i)) n).subset fun m hm => by
    rw [Set.mem_setOf_eq, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simpa only [Set.mem_setOf_eq, smul_eq_mul, mul_comm] using hm

theorem coeff_specPS (f : MvPowerSeries (Fin r) K) (n : ℕ) :
    PowerSeries.coeff n (specPS a ha f) = ∑ m ∈ (finite_weight a ha n).toFinset, MvPowerSeries.coeff m f := by
  classical
  have e : ∀ m : Fin r →₀ ℕ, (m.prod fun s k => (PowerSeries.X ^ a s : PowerSeries K) ^ k) =
      PowerSeries.X ^ ∑ i, a i * m i := fun m => by
    rw [Finsupp.prod_fintype _ _ (by simp), ← Finset.prod_pow_eq_pow_sum]
    simp only [pow_mul]
  have h := MvPowerSeries.coeff_subst (hasSubst (K := K) a ha) f (Finsupp.single () n)
  rw [specPS_apply]
  refine h.trans ?_
  have e' : ∀ m : Fin r →₀ ℕ, MvPowerSeries.coeff m f • MvPowerSeries.coeff (Finsupp.single () n)
      (m.prod fun s k => (PowerSeries.X ^ a s : PowerSeries K) ^ k) =
        if ∑ i, a i * m i = n then MvPowerSeries.coeff m f else 0 := fun m => by
    rw [e]
    change _ • PowerSeries.coeff n (PowerSeries.X ^ _ : PowerSeries K) = _
    rw [PowerSeries.coeff_X_pow]
    by_cases hm : ∑ i, a i * m i = n
    · simp [hm]
    · simp [hm, Ne.symm hm]
  rw [finsum_congr e', finsum_eq_sum_of_support_subset (s := (finite_weight a ha n).toFinset)]
  · exact Finset.sum_congr rfl fun m hm => if_pos (by simpa using hm)
  · intro m hm
    by_contra hn
    exact hm (if_neg (by simpa using hn))

def spec : MultiRing K r →+* LaurentSeries K :=
  IsLocalization.Away.lift (∏ i, MvPowerSeries.X i : MvPowerSeries (Fin r) K)
    (g := (HahnSeries.ofPowerSeries ℤ K).comp (specPS a ha)) (IsUnit.mk0 _ (by
      rw [RingHom.comp_apply, map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using fun h => absurd h PowerSeries.X_ne_zero))

@[simp] theorem spec_algebraMap (f : MvPowerSeries (Fin r) K) :
    spec a ha (algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r) f) = HahnSeries.ofPowerSeries ℤ K (specPS a ha f) :=
  IsLocalization.Away.lift_eq _ _ f

@[simp] theorem spec_u (i : Fin r) : spec a ha (u i : MultiRing K r) = HahnSeries.single (a i : ℤ) 1 := by
  rw [u, spec_algebraMap, specPS_X, HahnSeries.ofPowerSeries_X_pow]

end Spec

def ofPS (i : Fin r) : PowerSeries K →+* MvPowerSeries (Fin r) K :=
  (PowerSeries.substAlgHom (R := K) (PowerSeries.HasSubst.X i (S := K))).toRingHom

def ofLaurent (i : Fin r) : LaurentSeries K →+* MultiRing K r :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries K)
    (g := (algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r)).comp (ofPS i)) (by
      have e : ofPS i (PowerSeries.X : PowerSeries K) = MvPowerSeries.X i := PowerSeries.substAlgHom_X _
      rw [RingHom.comp_apply, e]
      exact isUnit_u i)

theorem spec_comp_ofLaurent (a : Fin r → ℕ) (ha : ∀ i, 1 ≤ a i) (i : Fin r) :
    (spec a ha).comp (ofLaurent i) = powLS (K := K) (ha i) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries K)) (RingHom.ext fun g => ?_)
  change spec a ha (ofLaurent i (algebraMap (PowerSeries K) _ g)) = powLS (ha i) (HahnSeries.ofPowerSeries ℤ K g)
  rw [ofLaurent, IsLocalization.Away.lift_eq, RingHom.comp_apply, spec_algebraMap, powLS_coe, specPS_apply, powPS_apply,
    PowerSeries.expand_apply]
  congr 1
  change MvPowerSeries.subst _ (PowerSeries.substAlgHom _ g) = _
  rw [PowerSeries.coe_substAlgHom, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (hasSubst a ha)]
  simp only [MvPowerSeries.subst_X (hasSubst (K := K) a ha)]

theorem powLS_one : powLS (K := K) (le_refl 1) = RingHom.id _ :=
  RingHom.ext fun f => HahnSeries.ext (funext fun n => by simpa using coeff_powLS_mul (le_refl 1) f n)

theorem spec_one_bijective : Function.Bijective (spec (K := K) (fun _ : Fin 1 => 1) fun _ => le_rfl) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun Φ h => ?_, fun g => ⟨ofLaurent 0 g, ?_⟩⟩
  · obtain ⟨n, f, e⟩ := exists_mul_pow Φ
    have hf : specPS (fun _ : Fin 1 => 1) (fun _ => le_rfl) f = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
      rw [← spec_algebraMap, ← e, map_mul, h, zero_mul, map_zero])
    have hf' : f = 0 := by
      ext m
      have e := coeff_specPS (fun _ : Fin 1 => 1) (fun _ => le_rfl) f (m 0)
      rw [hf, Finset.sum_eq_single_of_mem m (by simp) fun m' hm' hne =>
        absurd (Finsupp.ext fun i => by rw [Subsingleton.elim i 0]; simpa using hm') hne] at e
      simpa using e.symm
    rw [hf', map_zero] at e
    exact (mul_eq_zero.1 e).resolve_right (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => (isUnit_u i).ne_zero))
  · rw [← RingHom.comp_apply, spec_comp_ofLaurent, powLS_one, RingHom.id_apply]

def equivLaurent : MultiRing K 1 ≃+* LaurentSeries K := RingEquiv.ofBijective _ spec_one_bijective

example : spec ![2, 3] (by decide) (u 0 * u 1 : MultiRing K 2) = HahnSeries.single 5 1 := by
  rw [map_mul, spec_u, spec_u, HahnSeries.single_mul_single]
  simp

example : spec (fun _ => 1) (fun _ => le_rfl) (u 0 - u 1 : MultiRing K 2) = 0 ∧ (u 0 - u 1 : MultiRing K 2) ≠ 0 := by
  refine ⟨by rw [map_sub, spec_u, spec_u, sub_self], fun h => ?_⟩
  have := congrArg (fun Φ => (spec ![1, 2] (by decide) Φ).coeff 1) h
  simp at this

end MultiRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F) {r : ℕ}

def IsMultiArc (δ : Fin r → t.Forms) (y : Sp (MultiRing ↥F.K r) ⟶ (Y Z.i).X)
    (w : Vecs Dw (Y Z.i).t (MultiRing ↥F.K r)) : Prop :=
  (∃ (g : Z.i.c.F →+* MultiRing ↥F.K r) (yo : Sp (MultiRing ↥F.K r) ⟶ (Xo Z.i.l).XF Z.i.c),
    yo ≫ pullback.snd _ _ = spMap g ∧ yo ≫ (Y Z.i).j = y ∧ IsFrame (Y Z.i).t g y w) ∧
  ∀ (a : Fin r → ℕ) (ha : ∀ i, 1 ≤ a i), ∃ x : Sp (LaurentSeries ↥F.K) ⟶ Z.X,
    x ≫ Z.π = spMap (MultiRing.spec a ha) ≫ y ∧ IsArc t (∑ i, a i • δ i) x (w.bc (MultiRing.spec a ha))

namespace IsMultiArc

variable {t} {δ : Fin r → t.Forms} {y : Sp (MultiRing ↥F.K r) ⟶ (Y Z.i).X} {w : Vecs Dw (Y Z.i).t (MultiRing ↥F.K r)}

theorem sum_mem_dir (h : IsMultiArc t δ y w) (a : Fin r → ℕ) (ha : ∀ i, 1 ≤ a i) : ∑ i, a i • δ i ∈ t.Dir := by
  obtain ⟨_, -, h, -⟩ := h.2 a ha
  exact h

theorem pos (h : IsMultiArc t δ y w) : 0 < r := by
  haveI := t.a.nontriv
  obtain ⟨z, hz⟩ := exists_ne (0 : t.a.D₀.X)
  refine Nat.pos_of_ne_zero fun hr => ?_
  subst hr
  simpa using (h.sum_mem_dir (fun _ => 1) fun _ => le_rfl).1 z hz

end IsMultiArc

theorem exists_isFrame_of_flagAt {k : Type} [Field k] {x : Sp k ⟶ Z.X} {v : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x v) :
    ∃ (g : Z.i.c.F →+* k) (y₀ : Sp k ⟶ (Xo Z.i.l).XF Z.i.c),
      y₀ ≫ pullback.snd _ _ = spMap g ∧ y₀ ≫ (Y Z.i).j = x ≫ Z.π ∧ IsFrame (Y Z.i).t g (x ≫ Z.π) v := by
  obtain ⟨a, φ, e, hfr, -⟩ := h
  obtain ⟨g, y₀, hy, hyj⟩ := (Cht.extendSt E H Dw Xo p W Y i₀).1 Z.i _ (x ≫ Z.π) (by
    rintro _ ⟨z, rfl⟩
    have hz : x z ∈ Z.opn := by
      rw [← Z.cover, ← e]
      refine Set.mem_iUnion.2 ⟨a, ?_⟩
      rw [← (Z.U a).2.range_fromSpec]
      exact ⟨spMap φ z, rfl⟩
    exact hz)
  have e₁ : spMap (g.comp (Z.i.c.V W).subtype) = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
    rw [spMap_comp, ← hy, Category.assoc, ← (Y Z.i).j_s, ← Category.assoc, hyj, Category.assoc, Z.π_s, ← e,
      Category.assoc, Z.alg_s, ← spMap_comp, RingHom.comp_assoc]
  have e₂ : g = φ.comp (Z.alg a) :=
    IsFractionRing.ringHom_ext (A := Z.i.c.V W) fun z => RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)) z
  exact ⟨g, y₀, hy, hyj, e₂ ▸ hfr⟩

theorem IsArc.isMultiArc_single {γ : t.Forms} {x : Sp (LaurentSeries ↥F.K) ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K)} (hx : IsArc t γ x v) (i : Fin r) :
    IsMultiArc t (Pi.single i γ) (spMap (MultiRing.ofLaurent i) ≫ x ≫ Z.π) (v.bc (MultiRing.ofLaurent i)) := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hfl⟩ := id hx
  obtain ⟨g, y₀, hy, hyj, hfr⟩ := exists_isFrame_of_flagAt hfl
  refine ⟨⟨(MultiRing.ofLaurent i).comp g, spMap (MultiRing.ofLaurent i) ≫ y₀, by rw [Category.assoc, hy, spMap_comp],
    by rw [Category.assoc, hyj], GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ _ _ _ hfr⟩, fun a ha => ?_⟩
  have e : ∑ j, a j • (Pi.single i γ : Fin r → t.Forms) j = a i • γ := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, smul_zero]) (by simp), Pi.single_eq_same]
  refine ⟨spMap (powLS (ha i)) ≫ x, ?_, ?_⟩
  · rw [← MultiRing.spec_comp_ofLaurent a ha i, spMap_comp, Category.assoc, Category.assoc]
  · rw [e, Vecs.bc_bc, MultiRing.spec_comp_ofLaurent]
    exact IsArc.pow t (ha i) hx

theorem exists_isMultiArc_single (hY : (Y Z.i).N4) {γ : t.Forms} (h : γ ∈ t.Dir) (i : Fin r) :
    ∃ y w, IsMultiArc t (Pi.single i γ) y w := by
  obtain ⟨x, v, hx⟩ := exists_isArc t hY h
  exact ⟨_, _, hx.isMultiArc_single t i⟩

theorem exists_isMultiArc_one_iff (hY : (Y Z.i).N4) (δ : Fin 1 → t.Forms) :
    (∃ y w, IsMultiArc t δ y w) ↔ δ 0 ∈ t.Dir := by
  refine ⟨fun ⟨_, _, h⟩ => by simpa using h.sum_mem_dir (fun _ => 1) fun _ => le_rfl, fun h => ?_⟩
  have e : δ = Pi.single 0 (δ 0) := funext fun i => by rw [Subsingleton.elim i 0, Pi.single_eq_same]
  rw [e]
  exact exists_isMultiArc_single t hY h 0

example (hY : (Y Z.i).N4) : (∃ (δ : Fin 1 → t.Forms), ∃ y w, IsMultiArc t δ y w) ∧
    ¬ ∃ y w, IsMultiArc t (fun _ : Fin 1 => 0) y w := by
  obtain ⟨γ, hγ⟩ := t.dir_nonempty
  refine ⟨⟨fun _ => γ, (exists_isMultiArc_one_iff t hY _).2 hγ⟩, fun h => ?_⟩
  haveI := t.a.nontriv
  obtain ⟨z, hz⟩ := exists_ne (0 : t.a.D₀.X)
  simpa using ((exists_isMultiArc_one_iff t hY _).1 h).1 z hz

end GlobalTheory.LocM.FJ
