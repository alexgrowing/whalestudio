import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClearSecB

theorem exists_app_eq_of_local {X Y : Scheme.{0}} (h : Y ⟶ X) (hinj : ∀ W : X.Opens, Function.Injective (h.app W).hom)
    (W : X.Opens) (f : Γ(Y, h ⁻¹ᵁ W))
    (hf : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ ∃ a : Γ(X, V),
      (h.app V).hom a = (Y.presheaf.map (homOfLE (fun _ hy => hV hy : h ⁻¹ᵁ V ≤ h ⁻¹ᵁ W)).op).hom f) :
    ∃ a : Γ(X, W), (h.app W).hom a = f := by
  choose V hV hxV a ha using hf
  have gp : ∀ (U : X.Opens) (c : Γ(X, U)) (y : Y), h y ∈ U → gs (𝟙 Y) y (h ⁻¹ᵁ U) ((h.app U).hom c) = gs h y U c :=
    fun U c y hy => (gs_pull (𝟙 Y) h y U hy c).trans (by rw [Category.id_comp])
  have gx : ∀ x (hx : x ∈ W) (y : Y), h y ∈ V x hx → gs h y (V x hx) (a x hx) = gs (𝟙 Y) y (h ⁻¹ᵁ W) f := by
    intro x hx y hy
    have hy' : (𝟙 Y) y ∈ h ⁻¹ᵁ V x hx := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha x hx)).trans (gs_res (𝟙 Y) y _ hy' _))
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : W => V x.1 x.2) W (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV x hx⟩) (fun x => a x.1 x.2) (fun x x' => hinj _ (fn_ext
      fun y hy => by
        have hy' : h y ∈ V x.1 x.2 ⊓ V x'.1 x'.2 := hy
        exact (gp _ _ y hy').trans ((gs_res h y _ hy' _).trans ((gx _ _ y hy'.1).trans ((gx _ _ y hy'.2).symm.trans
          ((gs_res h y _ hy' _).symm.trans (gp _ _ y hy').symm))))))
  refine ⟨s, fn_ext fun y hy => ?_⟩
  have hy' : h y ∈ W := hy
  exact (gp _ _ y hy').trans ((gs_res h y (hV _ hy') (hxV _ hy') s).symm.trans
    ((congrArg (gs h y _) (hs ⟨h y, hy'⟩)).trans (gx _ _ y (hxV _ hy'))))

theorem exists_mul_eq_app {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (V : Q.P.A.left.Opens)
    (hV : IsAffineOpen V) (f : Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)) :
    ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, V), ((DegPre.prB Q (FractionRing R)).left.app V).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) * f := by
  have eT : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have H0 := (IsPullback.of_hasPullback (TF (R := R) (FractionRing R)).hom Q.P.A.hom).flip
  have H : IsPullback (DegPre.prB Q (FractionRing R)).left (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom)
      Q.P.A.hom (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (CommRingCat.of (FractionRing R))))) :=
    IsPullback.of_iso H0 (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; exact eT)
  have hloc := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := CommRingCat.of R) (L := CommRingCat.of (FractionRing R))
    (nonZeroDivisors R) H hV
  letI := ((DegPre.prB Q (FractionRing R)).left.app V).hom.toAlgebra
  obtain ⟨⟨a, _, r, hr, rfl⟩, e⟩ := IsLocalization.surj
    ((nonZeroDivisors (CommRingCat.of R)).map (GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom) f
  refine ⟨r, nonZeroDivisors.ne_zero hr, a, ?_⟩
  have e2 : algebraMap Γ(Q.P.A.left, V) Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)
      ((GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom r) =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) := by
    show ((DegPre.prB Q (FractionRing R)).left.app V).hom _ = _
    rw [GlobalTheory.QCoh.Qcqs.app_baseRingHom, ← GlobalTheory.QCoh.Qcqs.baseRingHom_res _ (le_top : _ ≤ ⊤), GlobalTheory.QCoh.Qcqs.baseRingHom_top,
      Over.w]
    rfl
  rw [e2] at e
  exact e.symm.trans (mul_comm _ _)

theorem exists_clear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))), ∃ r : R, r ≠ 0 ∧ ∃ σ : Q.SecB k β, ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J = gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J := by
  intro R _ _ _ Q k β s
  classical
  set p := (DegPre.prB Q (FractionRing R)).left with hp
  have hφ : ∀ i, DegPre.famφ Q (FractionRing R) β i = p ≫ Q.famφB β i := ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq Q _ β
  have hw : ∀ j, LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j = p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := by
    intro j
    have e : DegPre.famφ Q (FractionRing R) β = fun k => p ≫ Q.famφB β k := funext hφ
    rw [e]
    ext y
    simp [LB.wchart]
  have inj : ∀ W, Function.Injective (p.app W).hom := fun W => GlobalTheory.IntegralExpansion.prB_app_injective Q W
  have hpw : p ≫ Q.P.A.hom = (DegPre.BF Q (FractionRing R)).hom := Over.w _
  have gp : ∀ (U : Q.P.A.left.Opens) (a : Γ(Q.P.A.left, U)) (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ U →
      gs (𝟙 _) y (p ⁻¹ᵁ U) ((p.app U).hom a) = gs p y U a := fun U a y h =>
    (gs_pull (𝟙 _) p y U h a).trans (by rw [Category.id_comp])
  have gsc : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c : R),
      gs p y ⊤ (Out.scal Q.P.A.hom c) = gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) := fun y c =>
    (gs_pull p Q.P.A.hom y ⊤ trivial _).trans ((by rw [hpw, Category.id_comp] :
      gs (p ≫ Q.P.A.hom) y ⊤ _ = gs (𝟙 _ ≫ (DegPre.BF Q (FractionRing R)).hom) y ⊤ _).trans
        (gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom y ⊤ trivial _).symm)
  have gmul : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c c' : R),
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (c * c')) =
        gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) * gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c') :=
    fun y c c' => by rw [← gs_mul _ y ⊤ trivial]; simp only [Out.scal, map_mul]
  have htr : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (i j : Fin 4 → Q.P.L.ι),
      trF (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k) (𝟙 _) y i j =
        trF (Q.famφB β) (DegPre.famε k) p y i j := fun y i j => by
    simp only [trF, hφ, Category.id_comp]
  have : IsProper Q.P.A.hom := Q.P.isAb.proper
  have : CompactSpace Q.P.A.left := QuasiCompact.compactSpace_of_compactSpace Q.P.A.hom
  have hb : ∀ b : Q.P.A.left, ∃ j : Fin 4 → Q.P.L.ι, ∃ V : Q.P.A.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      V ≤ LB.wchart Q.P.L (Q.famφB β) j := by
    intro b
    choose i hi using fun k : Fin 4 => exists_chart Q.P.isLB (Q.famφB β k b)
    have hb : b ∈ LB.wchart Q.P.L (Q.famφB β) i := Set.mem_iInter.2 hi
    obtain ⟨V, hV, hbV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Q.P.A.left.isBasis_affineOpens) hb
    exact ⟨i, V, hV, hbV, hle⟩
  choose jb Vb hVa hbV hVle using hb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun b => (Vb b : Set Q.P.A.left)) (fun b => (Vb b).isOpen)
    (fun b _ => Set.mem_iUnion.2 ⟨b, hbV b⟩)
  have hA : ∀ b, ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, Vb b), (p.app (Vb b)).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (le_trans (show p ⁻¹ᵁ Vb b ≤ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (jb b) from
          fun _ hy => hVle b hy) (hw (jb b)).ge)).op).hom (s.f (jb b)) :=
    fun b => exists_mul_eq_app Q (Vb b) (hVa b) _
  choose rb hrb ab hab using hA
  have hAg : ∀ b (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ Vb b → gs p y (Vb b) (ab b) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (rb b)) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b)) (s.f (jb b)) := by
    intro b y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ Vb b := hy
    have e := congrArg (gs (𝟙 _) y (p ⁻¹ᵁ Vb b)) (hab b)
    exact (gp _ _ y hy).symm.trans (e.trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  set r := ∏ b ∈ t, rb b with hr_def
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hrb b

  have hlift : ∀ j, ∃ a : Γ(Q.P.A.left, LB.wchart Q.P.L (Q.famφB β) j), (p.app _).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (hw j).ge).op).hom (s.f j) := by
    intro j
    refine exists_app_eq_of_local p inj _ _ fun x hx => ?_
    obtain ⟨b, hbt, hxb⟩ : ∃ b ∈ t, x ∈ Vb b := by simpa using ht (Set.mem_univ x)
    have le1 : Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j ≤ (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U j ⊓
        (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U (jb b) := le_inf inf_le_right (inf_le_left.trans (hVle b))
    refine ⟨Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j, inf_le_right, ⟨hxb, hx⟩,
      resTop _ (Out.scal Q.P.A.hom (∏ b' ∈ t.erase b, rb b')) *
        (Q.P.A.left.presheaf.map (homOfLE inf_le_left).op).hom (ab b) *
        (Q.P.A.left.presheaf.map (homOfLE le1).op).hom
          ((LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).g j (jb b)).val, ?_⟩
    refine fn_ext fun y hy => ?_
    have hpy : p y ∈ Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    have hyb : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b) := (hw (jb b)).ge (hVle b hpy.1)
    have hy1 : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hpy.2
    refine ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_mul p y _ hpy _ _).trans
      (congrArg₂ (· * ·) ((gs_res p y le_top hpy _).trans (gsc y _)) ((gs_res p y inf_le_left hpy _).trans
        (hAg b y hpy.1)))) ((gs_res p y le1 hpy _).trans ((gs_unit p y _ (le1 hpy) _).trans
          (congrArg Units.val (gm_linComb _ _ _ p y j (jb b) hpy.2 (hVle b hpy.1)))))))).trans
      (Eq.trans ?_ ((gs_res (𝟙 _) y _ hy _).trans ((gs_mul _ y _ hy1 _ _).trans (congrArg₂ (· * ·)
        (gs_res _ y le_top hy1 _) ((gs_res _ y _ hy1 _).trans (sec_trans s (𝟙 _) y hyj hyb))))).symm)
    rw [htr, hr_def, ← Finset.mul_prod_erase t rb hbt, gmul]
    simp only [trF]
    ring
  choose σf hσf using hlift
  have hσg : ∀ j (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ LB.wchart Q.P.L (Q.famφB β) j → gs p y _ (σf j) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j) (s.f j) := by
    intro j y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 _) y _) (hσf j)).trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  refine ⟨r, hr, ⟨σf, fun i j => inj _ (fn_ext fun y hy => ?_)⟩, fun Z x z J hJ => ?_⟩
  · have hpy : p y ∈ LB.wchart Q.P.L (Q.famφB β) i ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyi : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) i := (hw i).ge hpy.1
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    refine ((gp _ _ y hpy).trans ((gs_res p y _ hpy _).trans (hσg i y hpy.1))).trans (Eq.trans ?_
      ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_unit p y _ hpy _).trans
        (congrArg Units.val (gm_linComb _ _ _ p y i j hpy.1 hpy.2))) ((gs_res p y _ hpy _).trans
          (hσg j y hpy.2))))).symm)
    rw [sec_trans s (𝟙 _) y hyi hyj]
    simp only [trF, hφ, Category.id_comp]
    ring
  · have hj0 := hJ.mem (Q.famφB β) (x ≫ p)
    have hxz : x z ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (fun k => J ((x ≫ p) ≫ Q.famφB β k)) := hj0
    rw [sval_of s x z J (fun k => J ((x ≫ p) ≫ Q.famφB β k)) (fun k => by rw [hφ, Category.assoc])]
    show gs (x ≫ p) z _ (σf _) = _
    refine ((gs_pull x p z _ hj0 _).symm.trans ((congrArg (gs x z _) (hσf _)).trans ((gs_mul x z _ hxz _ _).trans
      (congrArg₂ (· * ·) (gs_res x z le_top hxz _) (gs_res x z _ hxz _))))).trans ?_
    exact congrArg (· * _) (gs_pull x _ z ⊤ trivial _)

end GlobalTheory.ClearSecB
