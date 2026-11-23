import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ExtLB

open IsLocalRing

variable {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]

abbrev cp (A : Type) [CommRing A] [IsLocalRing A] : Sp A := closedPoint A

theorem top_le [IsLocalRing A] (f : Sp A ⟶ X) {U : X.Opens} (h : f (cp A) ∈ U) : ⊤ ≤ f ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) f h).ge

def ev (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom).hom

def toSt (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sp A).presheaf.germ ⊤ y trivial).hom

theorem gs_eq_toSt (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (y : Sp A) (a : Γ(X, U)) :
    gs f y U a = toSt y (ev f U h a) := by
  rw [gs_eq f y U (h (Set.mem_univ y))]
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
    (Sp A).presheaf.germ ⊤ y trivial).hom a
  rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.appLE, Category.assoc]
  exact (TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE h) y (Set.mem_univ y) _).symm

theorem ev_comp (g : A →+* B) (f : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U)
    (a : Γ(X, U)) : ev (spMap g ≫ f) U h' a = g (ev f U h a) := by
  change _ = ((f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom) ≫ CommRingCat.ofHom g).hom a
  rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun q => (q ≫ (Scheme.ΓSpecIso (.of B)).hom).hom a)
    (Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h le_top).symm

theorem toSt_bijective [IsLocalRing A] : Function.Bijective (toSt (cp A)) := by
  have : toSt (cp A) = (stalkClosedPointIso (.of A)).inv.hom := by
    rw [toSt, ← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  rw [this]
  exact (stalkClosedPointIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective

theorem isUnit_toSt [IsLocalRing A] (a : A) : IsUnit (toSt (cp A) a) ↔ IsUnit a :=
  MulEquiv.isUnit_map (RingEquiv.ofBijective _ toSt_bijective)

theorem exists_lift (g : A →+* B) (hg : Function.Injective g) (x : Sp B ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (hr : ∀ a, ∃ r, g r = ev x U h a) : ∃ χ : Sp A ⟶ X, spMap g ≫ χ = x := by
  let e : A ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hg (congrArg Subtype.val hab), g.rangeRestrict_surjective⟩
  let ρ : Γ(X, U) →+* A := e.symm.toRingHom.comp ((ev x U h).codRestrict g.range hr)
  have hρ : g.comp ρ = ev x U h := RingHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply ((ev x U h).codRestrict g.range hr a))
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ hU.fromSpec, ?_⟩
  have e₁ := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e₁
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ, ev, CommRingCat.ofHom_hom, Spec.map_comp,
    Category.assoc, e₁, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

variable {L : LB X}

theorem le_chart {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

theorem le_chart' {x : Sp A ⟶ X} {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    ⊤ ≤ (𝟙 (Sp A) : Sp A ⟶ Sp A) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => h hy

def sv {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : A :=
  ev x _ (le_chart h) (s.f fun _ => i)

def gv {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) : Aˣ :=
  Units.map (ev (𝟙 (Sp A)) _ (le_chart' h)).toMonoidHom (e.s fun _ => i)

theorem isUnit_sv [IsLocalRing A] {d : ℕ} (s : H0 L d) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    IsUnit (sv s x h) ↔ x (cp A) ∈ nonzeroLocus s := by
  rw [mem_nonzeroLocus_iff_pull s x (cp A) (k := fun _ => i) (le_chart h (Set.mem_univ _)), ← isUnit_toSt]
  exact (congrArg IsUnit (gs_eq_toSt x _ (le_chart h) _ _)).to_iff.symm

theorem gs_sv {d : ℕ} (s : H0 L d) (g : A →+* B) (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    gs (spMap g ≫ x) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (s.f fun _ => i) = toSt y (g (sv s x h)) :=
  (gs_eq_toSt (spMap g ≫ x) _ (fun z _ => le_chart h (Set.mem_univ (spMap g z))) y _).trans
    (congrArg _ (ev_comp g x _ (le_chart h) _ _))

theorem gm_gv (g : A →+* B) {x : Sp A ⟶ X} (e : LB.Gen (L.pull x)) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (y : Sp B) :
    (gm (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (e.s fun _ => i)).val = toSt y (g (gv e h).val) := by
  have hm : ⊤ ≤ (spMap g ≫ 𝟙 _) ⁻¹ᵁ LB.wchart L (fun _ : PUnit => x) (fun _ => i) :=
    fun _ _ => le_chart' h (Set.mem_univ _)
  refine (gs_unit (spMap g) y (LB.wchart L (fun _ : PUnit => x) (fun _ => i)) (hm (Set.mem_univ y)) _).symm.trans ?_
  refine (congrArg (fun q => gs q y _ _) (Category.comp_id (spMap g)).symm).trans ?_
  exact (gs_eq_toSt _ _ hm _ _).trans (congrArg _ (ev_comp g (𝟙 _) _ (le_chart' h) _ _))

theorem quot_eq (hL : L.IsLB) {C : Type} [CommRing C] [IsLocalRing C] (g : A →+* C) (g' : B →+* C)
    {x : Sp A ⟶ X} {χ : Sp B ⟶ X} (hc : spMap g ≫ x = spMap g' ≫ χ) (e : LB.Gen (L.pull x)) (he : e.IsGen)
    (e' : LB.Gen (L.pull χ))
    (hv : ∀ z J, Good L z J → val (L := L) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap g) z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (spMap g') z J)
    {i i' : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (h' : ⊤ ≤ χ ⁻¹ᵁ L.U i') {d : ℕ} (s : H0 L d) :
    g (sv s x h * ((gv e h)⁻¹ ^ d).val) = g' (sv s χ h' * ((gv e' h')⁻¹ ^ d).val) := by
  have m : (spMap g ≫ x) (cp C) ∈ L.U i := h (Set.mem_univ _)
  have m' : (spMap g ≫ x) (cp C) ∈ L.U i' := by rw [hc]; exact h' (Set.mem_univ _)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL (cp C) (fun _ : PUnit => spMap g ≫ x) (fun _ => i') (fun _ _ _ => rfl)
    (fun _ => m')
  have v := hv _ J hJ
  rw [val_of (L := L) (φ := fun _ : PUnit => x) e _ _ J (fun _ => i') (fun _ => hJi PUnit.unit),
    val_of (L := L) (φ := fun _ : PUnit => χ) e' _ _ J (fun _ => i') (fun _ => hc ▸ hJi PUnit.unit),
    gen_trans (L := L) (φ := fun _ : PUnit => x) he (spMap g) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m), trF, Fintype.prod_unique, zpow_one] at v
  have v' := congrArg Units.val v
  rw [Units.val_mul, gm_gv g e h, gm_gv g' e' h'] at v'
  have w := sec_trans s (spMap g ≫ x) (cp C) (j := fun _ => i') (j' := fun _ => i)
      (Set.mem_iInter.2 fun _ => m') (Set.mem_iInter.2 fun _ => m)
  rw [trF, Fintype.prod_unique, zpow_natCast, Category.comp_id, gs_sv s g x h, Units.val_pow_eq_pow_val] at w
  have w' := gs_sv s g' χ h' (cp C)
  rw [← hc, w] at w'
  apply toSt_bijective.1
  have u : toSt (cp C) (g (gv e h).val) * toSt (cp C) (g (gv e h)⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have u' : toSt (cp C) (g' (gv e' h').val) * toSt (cp C) (g' (gv e' h')⁻¹.val) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  simp only [map_mul, map_pow, Units.val_pow_eq_pow_val]
  rw [← w', mul_comm (_ ^ d), _root_.mul_assoc, ← mul_pow]
  congr 2
  rw [← v'] at u'
  linear_combination (-toSt (cp C) (g (gv e h)⁻¹.val)) * u' + ((gm (spMap g ≫ x) (cp C) _ (L.g i' i)).val *
    toSt (cp C) (g' (gv e' h')⁻¹.val)) * u

theorem exists_sv_eq [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) [IsLocalRing A] {d : ℕ} (s : H0 L d)
    (x : Sp A ⟶ X) {i : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U i) (hs : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (d * m)), sv t x h = sv s x h ^ m * ev x _ hs a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL d s).1 a
  refine ⟨m, t, toSt_bijective.1 ?_⟩
  have e := congrArg (x.stalkMap (cp A)).hom (ht (x (cp A)) (fun _ => i) (hs (Set.mem_univ _)) (h (Set.mem_univ _)))
  rw [map_mul, map_pow] at e
  have k : ∀ (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(X, U)),
      (x.stalkMap (cp A)).hom (gs (𝟙 X) (x (cp A)) U b) = toSt (cp A) (ev x U hU b) := fun U hU b =>
    (gs_stalkMap x (cp A) U (hU (Set.mem_univ _)) b).symm.trans (gs_eq_toSt x U hU _ b)
  rw [map_mul, map_pow]
  exact (k _ (le_chart h) _).symm.trans (e.trans (congrArg₂ (· * ·) (congrArg (· ^ m) (k _ (le_chart h) _)) (k _ hs _)))

theorem exists_eq_of_traits {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CharZero R] (q : FractionRing R)
    (H : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ w : W, gam q = algebraMap W _ w) : ∃ r : R, algebraMap R _ r = q := by
  refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV h1 _ => ?_
  let W := AdicCompletion (maximalIdeal V) V
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : R →+* W := (algebraMap V W).comp ((algebraMap R (FractionRing R)).codRestrict V h1)
  let gam : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := V) inj
  have hg : ∀ v : V, gam v = algebraMap W _ (algebraMap V W v) := fun v => IsFractionRing.lift_algebraMap inj v
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr V).comp
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := H W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ gam
    (fun r => hg ⟨_, h1 r⟩)
  by_contra hq
  have hq0 : q ≠ 0 := fun h => hq (h ▸ V.zero_mem)
  have hi : q⁻¹ ∈ V := (V.mem_or_inv_mem q).resolve_left hq
  have hu : IsUnit (algebraMap V W ⟨_, hi⟩) := IsUnit.of_mul_eq_one w (IsFractionRing.injective W (FractionRing W) (by
    rw [map_mul, ← hg, ← hw, ← map_mul, map_one]
    exact (congrArg gam (inv_mul_cancel₀ hq0)).trans (map_one _)))
  obtain ⟨b, hb⟩ := ((isUnit_map_iff (algebraMap V W) _).1 hu).exists_right_inv
  have : q⁻¹ * b = 1 := congrArg Subtype.val hb
  have e : (b : FractionRing R) = q := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hq (e ▸ b.2)

theorem exists_extension : ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z] (AA : LB Z), AA.IsLB → (∀ z : Z, ∃ (d : ℕ) (s : H0 AA d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp (FractionRing R) ⟶ Z) (e : LB.Gen (AA.pull x)), e.IsGen → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∃ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ ∧ ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J) → ∃ χ : Sp R ⟶ Z, jK R ≫ χ = x := by
  intro Z _ _ AA hL amp R _ _ _ _ _ _ x e he H
  by_cases hR : IsField R
  · obtain ⟨d, s, -, hz, hs⟩ := amp (x (cp _))
    refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hz) fun a => ?_
    exact (IsField.localization_map_bijective (M := nonZeroDivisors R) zero_notMem_nonZeroDivisors hR).2 _
  obtain ⟨i, hi⟩ := exists_chart hL (x (cp _))
  have h := top_le x hi
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
      ∃ z : Z, ∀ (d : ℕ) (s : H0 AA d), ∃ w : W, gam (sv s x h * ((gv e h)⁻¹ ^ d).val) = algebraMap W _ w ∧
        (z ∈ nonzeroLocus s → IsUnit w) := by
    intro W _ _ _ hW φ gam hg
    obtain ⟨χ, hc, e', -, hv⟩ := H W hW φ gam hg
    obtain ⟨i', hi'⟩ := exists_chart hL (χ (cp _))
    exact ⟨χ (cp _), fun d s => ⟨_, quot_eq hL gam (algebraMap W _) hc e he e' hv h (top_le χ hi') s,
      fun hz => ((isUnit_sv s χ _).2 hz).mul (Units.isUnit _)⟩⟩
  have int : ∀ (d : ℕ) (s : H0 AA d), ∃ r : R, algebraMap R _ r = sv s x h * ((gv e h)⁻¹ ^ d).val := fun d s =>
    exists_eq_of_traits _ fun W _ _ _ hW φ gam hg => by
      obtain ⟨z, hz⟩ := key W hW φ gam hg
      exact (hz d s).imp fun _ => And.left
  obtain ⟨W, _, _, _, _, φ, hφ, _⟩ := exists_complete_discreteValuationRing_dominating R hR
  have inj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  have hg : ∀ r, IsFractionRing.lift (K := FractionRing R) inj (algebraMap R _ r) = algebraMap W _ (φ r) :=
    fun r => IsFractionRing.lift_algebraMap inj r
  obtain ⟨z, hz⟩ := key W ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩ φ _ hg
  obtain ⟨d, s, -, hzs, hs⟩ := amp z
  obtain ⟨w, hw, hu⟩ := hz d s
  obtain ⟨r, hr⟩ := int d s
  rw [← hr, hg] at hw
  have hru : IsUnit r := (isUnit_map_iff φ r).1 (IsFractionRing.injective W _ hw ▸ hu hzs)
  have hx : x (cp _) ∈ nonzeroLocus s :=
    (isUnit_sv s x h).1 (isUnit_of_mul_isUnit_left (hr ▸ hru.map (algebraMap R (FractionRing R))))
  refine exists_lift _ (IsFractionRing.injective R _) x hs (top_le x hx) fun a => ?_
  obtain ⟨m, t, ht⟩ := exists_sv_eq hL s x h (top_le x hx) a
  obtain ⟨r', hr'⟩ := int _ t
  obtain ⟨u, rfl⟩ := hru
  refine ⟨r' * (u⁻¹ ^ m).val, ?_⟩
  rw [map_mul, hr', ht, pow_mul, Units.val_pow_eq_pow_val _ m, mul_right_comm (_ ^ m), ← mul_pow, ← hr, ← map_pow,
    mul_right_comm, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
    Units.val_one, map_one, _root_.one_mul]

end GlobalTheory.ExtLB
