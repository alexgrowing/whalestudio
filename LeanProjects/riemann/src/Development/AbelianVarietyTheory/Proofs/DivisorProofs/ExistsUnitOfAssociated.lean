import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymExtend

open GlobalTheory.CechPic TopologicalSpace

section Cl

variable {X Y Z : Scheme.{0}} {L M : LB X}

open Classical in

def cl (s : L.Sec) (r : Z ⟶ X) (z : Z) : Associates (Z.presheaf.stalk z) :=
  if h : ∃ a, r z ∈ L.U a then Associates.mk (gs r z (L.U h.choose) (s.f h.choose)) else 0

theorem gs_trans (s : L.Sec) (r : Z ⟶ X) (z : Z) {a b : L.ι} (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gs r z (L.U a) (s.f a) = (gm r z _ (L.g a b)).val * gs r z (L.U b) (s.f b) := by
  have hm : r z ∈ L.U a ⊓ L.U b := ⟨ha, hb⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat a b)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem mk_unit_mul {A : Type} [CommRing A] (u : Aˣ) (a : A) : Associates.mk (u.val * a) = Associates.mk a :=
  Associates.mk_eq_mk_iff_associated.2 (associated_unit_mul_left a u u.isUnit)

theorem cl_eq (s : L.Sec) (r : Z ⟶ X) (z : Z) {a : L.ι} (ha : r z ∈ L.U a) :
    cl s r z = Associates.mk (gs r z (L.U a) (s.f a)) := by
  have h : ∃ a, r z ∈ L.U a := ⟨a, ha⟩
  rw [cl, dif_pos h, gs_trans s r z h.choose_spec ha, mk_unit_mul]

theorem gs_pow (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem exists_move (hL : L.IsLB) (hM : M.IsLB) (e : cls L hL = cls M hM) (s : L.Sec) :
    ∃ t : M.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), cl t r z = cl s r z := by
  obtain ⟨u, hu⟩ := (cls_eq_iff hM hL).1 e.symm
  refine ⟨DVR.secOfIso s hu hM hL, fun Z r z => ?_⟩
  obtain ⟨a, ha⟩ := exists_chart hM (r z)
  obtain ⟨b, hb⟩ := exists_chart hL (r z)
  rw [cl_eq _ r z ha, cl_eq _ r z hb, DVR.ps_gs_secOfIso u s hu hM hL a b r z ⟨ha, hb⟩, mk_unit_mul]

abbrev pp (L : LB X) (φ : Y ⟶ X) (n : ℕ) : LB Y := LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => (n : ℤ))

theorem isLB_pp (hL : L.IsLB) (φ : Y ⟶ X) (n : ℕ) : (pp L φ n).IsLB := LB.isLB_linComb hL _ _

theorem cls_pp (hL : L.IsLB) (φ : Y ⟶ X) (n : ℕ) : cls _ (isLB_pp hL φ n) = n • pull φ (cls L hL) := by
  rw [cls_linComb hL]; simp

theorem exists_pp (hL : L.IsLB) (φ : Y ⟶ X) (n : ℕ) (s : L.Sec) :
    ∃ t : (pp L φ n).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), cl t r z = cl s (r ≫ φ) z ^ n := by
  have val : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι), r z ∈ (pp L φ n).U j →
      gs r z ((pp L φ n).U j) ((Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit)).op).hom
        ((φ.app (L.U (j PUnit.unit))).hom (s.f (j PUnit.unit) ^ n))) =
        gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) ^ n := fun Z r z j hj =>
    (gs_res r z _ hj _).trans ((gs_pull r φ z _ (Set.mem_iInter.1 hj PUnit.unit) _).trans
      (gs_pow _ z _ (Set.mem_iInter.1 hj PUnit.unit) _ n))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit)).op).hom
        ((φ.app (L.U (j PUnit.unit))).hom (s.f (j PUnit.unit) ^ n)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z => ?_⟩
  · refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (val _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (val _ (𝟙 Y) y j' hy.2)).symm)
    rw [gs_trans s (𝟙 Y ≫ φ) y (Set.mem_iInter.1 hy.1 PUnit.unit) (Set.mem_iInter.1 hy.2 PUnit.unit), mul_pow]
    simp
  · obtain ⟨a, ha⟩ := exists_chart hL (φ (r z))
    have hj : r z ∈ (pp L φ n).U (fun _ => a) := Set.mem_iInter.2 fun _ => ha
    rw [cl_eq _ r z hj, cl_eq s (r ≫ φ) z ha, ← Associates.mk_pow]
    exact congrArg Associates.mk (val Z r z _ hj)

theorem exists_scale (hL : L.IsLB) (c : Γ(X, ⊤)) (s : L.Sec) :
    ∃ t : L.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), cl t r z = Associates.mk (gs r z ⊤ c) * cl s r z := by
  have val : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (a : L.ι), r z ∈ L.U a →
      gs r z (L.U a) ((X.presheaf.map (homOfLE (le_top : L.U a ≤ ⊤)).op).hom c * s.f a) =
        gs r z ⊤ c * gs r z (L.U a) (s.f a) := fun Z r z a ha =>
    (gs_mul r z _ ha _ _).trans (congrArg (· * _) (gs_res r z _ ha _))
  refine ⟨⟨fun a => (X.presheaf.map (homOfLE (le_top : L.U a ≤ ⊤)).op).hom c * s.f a,
    fun a b => fn_ext fun y hy => ?_⟩, fun Z r z => ?_⟩
  · rw [gs_res (𝟙 X) y _ hy, gs_mul (𝟙 X) y _ hy, gs_res (𝟙 X) y _ hy, gs_unit (𝟙 X) y _ hy, val _ _ _ a hy.1,
      val _ _ _ b hy.2, gs_trans s (𝟙 X) y hy.1 hy.2, mul_left_comm]
  · obtain ⟨a, ha⟩ := exists_chart hL (r z)
    rw [cl_eq _ r z ha, cl_eq _ r z ha, Associates.mk_mul_mk]
    exact congrArg Associates.mk (val Z r z a ha)

theorem gs_ne_zero [IsIntegral X] {W : X.Opens} {a : Γ(X, W)} (ha : a ≠ 0) (x : X) (hx : x ∈ W) :
    gs (𝟙 X) x W a ≠ 0 := fun e => ha (germ_injective_of_isIntegral X x hx
      (((gs_eq (𝟙 X) x W hx a).symm.trans e).trans (map_zero _).symm))

theorem cl_ne_zero [IsIntegral X] (hL : L.IsLB) (s : L.Sec) (hs : ∃ i, s.f i ≠ 0) (x : X) : cl s (𝟙 X) x ≠ 0 := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨a, ha⟩ := exists_chart hL x
  have hne : ((L.U i : Set X)).Nonempty := by
    by_contra hn
    have e : L.U i = ⊥ := Opens.ext (Set.not_nonempty_iff_eq_empty.1 hn)
    have : Subsingleton Γ(X, L.U i) := by rw [e]; infer_instance
    exact hi (Subsingleton.elim _ _)
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (L.U i).isOpen (L.U a).isOpen hne ⟨x, ha⟩
  rw [cl_eq s (𝟙 X) x ha, Ne, Associates.mk_eq_zero]
  refine gs_ne_zero (fun e => gs_ne_zero hi y hy.1 ?_) x ha
  rw [gs_trans s (𝟙 X) y hy.1 hy.2, e, gs_eq (𝟙 X) y _ hy.2, map_zero, map_zero, MulZeroClass.mul_zero]

theorem exists_ne_zero_of_cl (hL : L.IsLB) (s : L.Sec) (r : Z ⟶ X) (z : Z) (h : cl s r z ≠ 0) : ∃ i, s.f i ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_chart hL (r z)
  refine ⟨a, fun e => h ?_⟩
  rw [cl_eq s r z ha, e, gs_eq r z _ ha, map_zero, map_zero]
  rfl

theorem cl_ne_zero_of_flat [IsIntegral X] (hL : L.IsLB) (s : L.Sec) (hs : ∃ i, s.f i ≠ 0) (r : Z ⟶ X) [Flat r]
    (z : Z) : cl s r z ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_chart hL (r z)
  have h := cl_ne_zero hL s hs (r z)
  rw [cl_eq s (𝟙 X) (r z) ha, Ne, Associates.mk_eq_zero] at h
  rw [cl_eq s r z ha, Ne, Associates.mk_eq_zero, gs_stalkMap r z _ ha]
  intro e
  exact h (zero_dvd_iff.1 (dvd_descend r z (by rw [e, map_zero])))

theorem exists_mul_of_dvd [IsIntegral X] (W : X.Opens) (a b : Γ(X, W)) (hb : ∀ x ∈ W, gs (𝟙 X) x W b ≠ 0)
    (h : ∀ x ∈ W, gs (𝟙 X) x W b ∣ gs (𝟙 X) x W a) : ∃ w : Γ(X, W), a = w * b := by
  have loc : ∀ x : W, ∃ V : X.Opens, x.1 ∈ V ∧ V ≤ W ∧ ∃ w : Γ(X, V), ∀ y ∈ V,
      gs (𝟙 X) y W a = gs (𝟙 X) y V w * gs (𝟙 X) y W b := by
    intro x
    obtain ⟨c, hc⟩ := h x.1 x.2
    obtain ⟨V, hV, w, rfl⟩ := X.presheaf.germ_exist c
    have hx : x.1 ∈ V ⊓ W := ⟨hV, x.2⟩
    refine ⟨V ⊓ W, hx, inf_le_right, (X.presheaf.map (homOfLE inf_le_left).op).hom w, fun y hy => ?_⟩
    have e : (X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op).hom a =
        (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op).hom w *
          (X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op).hom b := by
      apply germ_injective_of_isIntegral X x.1 hx
      refine (gs_eq (𝟙 X) x.1 _ hx _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X) x.1 _ hx _))
      refine (gs_res (𝟙 X) x.1 inf_le_right hx a).trans (hc.trans ((mul_comm _ _).trans (Eq.symm ?_)))
      exact (gs_mul (𝟙 X) x.1 _ hx _ _).trans (congrArg₂ (· * ·)
        ((gs_res (𝟙 X) x.1 inf_le_left hx w).trans (gs_eq (𝟙 X) x.1 V hV w)) (gs_res (𝟙 X) x.1 inf_le_right hx b))
    have := congrArg (gs (𝟙 X) y (V ⊓ W)) e
    rwa [gs_mul _ _ _ hy, gs_res (𝟙 X) y inf_le_right hy, gs_res (𝟙 X) y inf_le_right hy] at this
  choose V hxV hVW w hw using loc
  obtain ⟨u, hu, -⟩ := X.sheaf.existsUnique_gluing' V W (fun x => homOfLE (hVW x))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxV _⟩) w (fun x x' => fn_ext (V := V x ⊓ V x') fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hVW x hy.1)) ((hw x y hy.1).symm.trans (hw x' y hy.2)))
  refine ⟨u, fn_ext fun y hy => ?_⟩
  refine (hw ⟨y, hy⟩ y (hxV _)).trans (Eq.trans (congrArg (· * _) ?_) (gs_mul (𝟙 X) y W hy u b).symm)
  exact (congrArg (gs (𝟙 X) y _) (hu ⟨y, hy⟩)).symm.trans (gs_res (𝟙 X) y (hVW ⟨y, hy⟩) (hxV ⟨y, hy⟩) u)

theorem exists_unit_of_associated [IsIntegral X] (W : X.Opens) (a b : Γ(X, W)) (hb : ∀ x ∈ W, gs (𝟙 X) x W b ≠ 0)
    (h : ∀ x ∈ W, Associated (gs (𝟙 X) x W a) (gs (𝟙 X) x W b)) : ∃ w : Γ(X, W)ˣ, a = w * b := by
  obtain ⟨w, hw⟩ := exists_mul_of_dvd W a b hb fun x hx => (h x hx).symm.dvd
  obtain ⟨w', hw'⟩ := exists_mul_of_dvd W b a (fun x hx => (h x hx).ne_zero_iff.2 (hb x hx)) fun x hx => (h x hx).dvd
  have e : w' * w = 1 := fn_ext fun x hx => by
    apply mul_right_cancel₀ (hb x hx)
    rw [← gs_mul _ _ _ hx, ← gs_mul _ _ _ hx, _root_.mul_assoc, ← hw, ← hw', _root_.one_mul]
  exact ⟨⟨w, w', (mul_comm _ _).trans e, e⟩, hw⟩

end Cl

section Generic

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

theorem isUnit_gs_scal {Z : Scheme.{0}} (r : Z ⟶ pullback G.hom (jK R)) (z : Z) {t : R} (ht : t ≠ 0) :
    IsUnit (gs (r ≫ pullback.fst G.hom (jK R) ≫ G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t)) := by
  rw [pullback.condition, ← Category.assoc, ← gs_pull _ (jK R) z ⊤ trivial, gs_eq _ z _ (by trivial)]
  refine (IsUnit.map _ (IsUnit.map _ ?_))
  have e := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  refine (show _ = _ from e) ▸ ?_
  exact IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (IsUnit.mk0 (algebraMap R (FractionRing R) t)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ht))

theorem exists_ext [QuasiCompact G.hom] [IsSeparated G.hom] {M : LB G.left} (hM : M.IsLB)
    {N : LB (pullback G.hom (jK R))} (hN : N.IsLB) (e : cls N hN = pull (pullback.fst G.hom (jK R)) (cls M hM))
    (s : N.Sec) : ∃ σ : M.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK R)) (z : Z),
      cl σ (r ≫ pullback.fst G.hom (jK R)) z = cl s r z := by
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨s', hs'⟩ := exists_move hN (isLB_pp hM (pullback.fst G.hom (jK R) ≫ 𝟙 _) 1)
    (by rw [cls_pp, e, one_smul, Category.comp_id]) s
  obtain ⟨t, ht, σ', hσ'⟩ := GlobalTheory.TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) hM (fun _ : PUnit => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) s'
  obtain ⟨σ, hσ⟩ := exists_move (isLB_pp hM (𝟙 _) 1) hM (by rw [cls_pp, one_smul, pull_id]) σ'
  refine ⟨σ, fun Z r z => ?_⟩
  obtain ⟨a, ha⟩ := exists_chart (isLB_pp hM (pullback.fst G.hom (jK R) ≫ 𝟙 _) 1) (r z)
  have ha' : (r ≫ pullback.fst G.hom (jK R)) z ∈ (pp M (𝟙 _) 1).U a :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 ha k
  rw [hσ, ← hs', cl_eq σ' _ z ha', cl_eq s' r z ha]
  obtain ⟨u, hu⟩ := isUnit_gs_scal G r z (nonZeroDivisors.ne_zero ht)
  exact (congrArg Associates.mk ((hσ' Z r z a ha).trans (congrArg (· * _) hu.symm))).trans (mk_unit_mul _ _)

theorem gs_scal' {S : Type} [CommRing S] {X Z : Scheme.{0}} (p : X ⟶ Sp S) (r : Z ⟶ X) (z : Z) (t : S) :
    gs r z ⊤ (scal p t) = GlobalTheory.TwistLoc.gc (r ≫ p) z t := gs_pull r p z ⊤ trivial _

theorem exists_scalars [Flat G.hom] [IsIntegral (pullback G.hom (jK R))]
    (hK : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom) {N : LB G.left} (hN : N.IsLB) (s t : N.Sec)
    (ht : ∀ y, cl t (pullback.fst G.hom (jK R)) y ≠ 0)
    (hst : ∀ y, cl s (pullback.fst G.hom (jK R)) y = cl t (pullback.fst G.hom (jK R)) y) :
    ∃ r r' : R, r ≠ 0 ∧ r' ≠ 0 ∧ ∀ x : G.left, Associates.mk (GlobalTheory.TwistLoc.gc G.hom x r') * cl s (𝟙 _) x =
      Associates.mk (GlobalTheory.TwistLoc.gc G.hom x r) * cl t (𝟙 _) x := by
  have hpb := pullback.condition (f := G.hom) (g := jK R)
  have hinj := GlobalTheory.ExpInt.generic_app_injective G
  generalize pullback.snd G.hom (jK R) = q at hK hpb
  generalize pullback.fst G.hom (jK R) = j at ht hst hpb hinj
  generalize pullback G.hom (jK R) = Y at *
  have pl : ∀ (U : G.left.Opens) (f : Γ(G.left, U)) (y : Y), j y ∈ U →
      gs (𝟙 Y) y (j ⁻¹ᵁ U) ((j.app U).hom f) = gs j y U f := fun U f y hy =>
    (gs_pull (𝟙 Y) j y U hy f).trans (by rw [Category.id_comp])
  have ht' : ∀ a y, j y ∈ N.U a → gs j y (N.U a) (t.f a) ≠ 0 := fun a y hy e =>
    ht y (by rw [cl_eq t j y hy, e]; rfl)
  have loc : ∀ a, ∃ w : Γ(Y, j ⁻¹ᵁ N.U a), ∀ y, j y ∈ N.U a →
      gs j y (N.U a) (s.f a) = gs (𝟙 Y) y (j ⁻¹ᵁ N.U a) w * gs j y (N.U a) (t.f a) := by
    intro a
    obtain ⟨w, hw⟩ := exists_mul_of_dvd (j ⁻¹ᵁ N.U a) ((j.app _).hom (s.f a)) ((j.app _).hom (t.f a))
      (fun y hy => by rw [pl _ _ y hy]; exact ht' a y hy) (fun y hy => by
        rw [pl _ _ y hy, pl _ _ y hy]
        exact (Associates.mk_eq_mk_iff_associated.1
          ((cl_eq s j y hy).symm.trans ((hst y).trans (cl_eq t j y hy)))).symm.dvd)
    refine ⟨w, fun y hy => ?_⟩
    rw [← pl _ _ y hy, ← pl _ _ y hy, hw, gs_mul (𝟙 Y) y (j ⁻¹ᵁ N.U a) hy]
  choose w hw using loc
  obtain ⟨u, hu, -⟩ := Y.sheaf.existsUnique_gluing' (fun a => j ⁻¹ᵁ N.U a) ⊤ (fun a => homOfLE le_top)
    (fun y _ => Opens.mem_iSup.2 (exists_chart hN (j y))) w
    (fun a b => fn_ext (V := j ⁻¹ᵁ N.U a ⊓ j ⁻¹ᵁ N.U b) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      refine mul_right_cancel₀ (ht' a y hy.1) ((hw a y hy.1).symm.trans ?_)
      rw [gs_trans s j y hy.1 hy.2, gs_trans t j y hy.1 hy.2, hw b y hy.2, mul_left_comm])
  have hu' : ∀ a y, j y ∈ N.U a → gs j y (N.U a) (s.f a) = gs (𝟙 Y) y ⊤ u * gs j y (N.U a) (t.f a) :=
    fun a y hy => (hw a y hy).trans (congrArg (· * _) ((congrArg (gs (𝟙 Y) y _) (hu a)).symm.trans
      (gs_res (𝟙 Y) y (le_top : j ⁻¹ᵁ N.U a ≤ ⊤) hy u)))
  obtain ⟨k, hk⟩ := hK u
  obtain ⟨⟨r, r', hr'⟩, hκ⟩ := IsLocalization.surj (nonZeroDivisors R)
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k)
  have hc : ∀ (y : Y) (a : R), gs j y ⊤ (scal G.hom a) =
      GlobalTheory.TwistLoc.gc (𝟙 Y ≫ q) y (algebraMap R (FractionRing R) a) := fun y a => by
    rw [gs_scal', hpb, Category.id_comp, GlobalTheory.TwistLoc.gc, GlobalTheory.TwistLoc.gc, ← gs_pull q (jK R) y ⊤ trivial]
    exact congrArg (gs q y ⊤) (congrArg (fun f => f.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  have hrel : ∀ y : Y, gs (𝟙 Y) y ⊤ u * gs j y ⊤ (scal G.hom r') = gs j y ⊤ (scal G.hom r) := fun y => by
    rw [hc, hc, ← hκ, GlobalTheory.TwistLoc.gc_mul, ← gs_scal' q (𝟙 Y) y ((Scheme.ΓSpecIso _).hom.hom k), ← hk]
    congr 2
    rw [scal, Iso.hom_inv_id_apply]
  have key : ∀ a, (G.left.presheaf.map (homOfLE (le_top : N.U a ≤ ⊤)).op).hom (scal G.hom r') * s.f a =
      (G.left.presheaf.map (homOfLE (le_top : N.U a ≤ ⊤)).op).hom (scal G.hom r) * t.f a := fun a =>
    hinj (N.U a) (fn_ext fun y hy => by
      rw [pl _ _ y hy, pl _ _ y hy, gs_mul j y _ hy, gs_mul j y _ hy, gs_res j y _ hy, gs_res j y _ hy, hu' a y hy,
        ← hrel]
      ring)
  refine ⟨r, r', ?_, nonZeroDivisors.ne_zero hr', fun x => ?_⟩
  · rintro rfl
    have hk0 : k = 0 := by
      have h0 : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k = 0 := by
        rw [map_zero] at hκ
        exact (mul_eq_zero.1 hκ).resolve_right ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
          (nonZeroDivisors.ne_zero hr'))
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) k]
      exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom h0).trans (map_zero _)
    obtain ⟨y⟩ : Nonempty Y := inferInstance
    obtain ⟨a, ha⟩ := exists_chart hN (j y)
    apply ht y
    rw [← hst, cl_eq s j y ha, hu' a y ha, ← hk, hk0, map_zero, gs_eq (𝟙 Y) y ⊤ trivial, map_zero, map_zero,
      MulZeroClass.zero_mul]
    rfl
  · obtain ⟨a, ha⟩ := exists_chart hN x
    have := congrArg (gs (𝟙 G.left) x (N.U a)) (key a)
    rw [gs_mul _ x _ ha, gs_mul _ x _ ha, gs_res _ x _ ha, gs_res _ x _ ha, gs_scal', gs_scal',
      Category.id_comp] at this
    rw [cl_eq s (𝟙 _) x ha, cl_eq t (𝟙 _) x ha, Associates.mk_mul_mk, Associates.mk_mul_mk, this]

end Generic

theorem exists_sec_sq_of_double : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom → ∀ (Lθ : LB (pullback G.hom (jK R))) (hθ : Lθ.IsLB) (θ : Lθ.Sec), (∃ i, θ.f i ≠ 0) → ∀ (L2 : LB G.left) (h2 : L2.IsLB), 2 • GlobalTheory.CechPic.cls Lθ hθ = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) (GlobalTheory.CechPic.cls L2 h2) → ∀ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left → GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls Lθ hθ) = 4 • GlobalTheory.CechPic.cls Lθ hθ → ∃ h : L2.Sec, (∀ j i, ∃ w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G.hom (jK R), pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G.hom (jK R)).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j))) ∧ (∀ (x' : G.left) (k : L2.ι), ((𝟙 G) ^ 2 : G ⟶ G).left x' ∈ L2.U k → gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) ≠ 0 ∧ ∃ (u : (G.left.presheaf.stalk x')ˣ) (g : G.left.presheaf.stalk x'), gs ((𝟙 G) ^ 2 : G ⟶ G).left x' (L2.U k) (h.f k) = u * g ^ 2) := by
  intro R _ _ _ hA G _ _ hG hK Lθ hθ θ hne L2 h2 e2 φ hφ e4
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : IsNoetherianRing R := hA.1
  haveI : Smooth G.hom := hG.smooth
  haveI : IsSeparated G.hom := hG.separated
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : IsIntegral (pullback G.hom (jK R)) := GlobalTheory.isIntegral_pullback_of_smooth G.hom (jK R)
  haveI : Flat (jK R) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R)))
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG 2 two_ne_zero).1
  generalize ((𝟙 G) ^ 2 : G ⟶ G) = f at hφ hfl ⊢
  obtain ⟨θ₂, hθ₂⟩ := exists_pp hθ (𝟙 _) 2 θ
  obtain ⟨h₀, hh₀⟩ := exists_ext G h2 (isLB_pp hθ (𝟙 _) 2) (by rw [cls_pp hθ, pull_id, e2]) θ₂
  obtain ⟨θφ, hθφ⟩ := exists_pp hθ φ 1 θ
  have hM := isLB_pp h2 (𝟙 _) 2
  obtain ⟨σ, hσ⟩ := exists_ext G hM (isLB_pp hθ φ 1)
    (by rw [cls_pp hθ, cls_pp h2, pull_id, map_nsmul, ← e2, e4, one_smul, smul_smul]; rfl) θφ
  obtain ⟨t, ht⟩ := exists_pp hM (𝟙 _) 2 σ
  obtain ⟨s₀, hs₀⟩ := exists_pp h2 f.left 1 h₀
  have hN := isLB_pp hM (𝟙 _) 2
  have hN₀ := isLB_pp h2 f.left 1
  have hiso := GlobalTheory.Mum.lbIso_of_generic_local R G (η[G]).left (Over.w η[G]) _ _ hN₀ hN
    ((cls_eq_iff (LB.isLB_pull hN₀ _) (LB.isLB_pull hN _)).1 (by
      rw [cls_pull hN₀, cls_pull hN, cls_pp hM, cls_pp h2, cls_pp h2, pull_id, pull_id, one_smul, ← pull_comp, ← hφ,
        pull_comp, map_nsmul, map_nsmul, ← e2, map_nsmul, e4, smul_smul, smul_smul, smul_smul]
      rfl))
  obtain ⟨s, hs⟩ := exists_move hN₀ hN ((cls_eq_iff _ _).2 hiso) s₀
  have hθ0 := cl_ne_zero hθ θ hne
  have hh₀' : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK R)) (z : Z),
      cl h₀ (r ≫ pullback.fst G.hom (jK R)) z = cl θ r z ^ 2 := fun Z r z => by
    rw [hh₀, hθ₂, Category.comp_id]
  have ht' : ∀ y, cl t (pullback.fst G.hom (jK R)) y = cl θ φ y ^ 2 := fun y => by
    have := hσ _ (𝟙 _) y
    rw [hθφ, Category.id_comp, Category.id_comp, pow_one] at this
    rw [ht, Category.comp_id, this]
  obtain ⟨y₀⟩ : Nonempty (pullback G.hom (jK R) : Scheme.{0}) := inferInstance
  have hφ0 : ∀ y, cl θ φ y ≠ 0 := fun y e =>
    cl_ne_zero_of_flat h2 h₀ (exists_ne_zero_of_cl h2 h₀ _ y₀ (by rw [hh₀' _ (𝟙 _)]; exact pow_ne_zero _ (hθ0 y₀)))
      (pullback.fst G.hom (jK R) ≫ f.left) y (by rw [← hφ, hh₀', e, zero_pow two_ne_zero])
  obtain ⟨r, r', hr, hr', hrr⟩ := exists_scalars G hK hN s t (fun y => by rw [ht']; exact pow_ne_zero _ (hφ0 y))
    (fun y => by rw [ht', hs, hs₀, pow_one, ← hφ, hh₀'])
  obtain ⟨h, hh⟩ := exists_scale h2 (scal G.hom (r * r')) h₀
  have hgen : ∀ y, cl h (𝟙 _ ≫ pullback.fst G.hom (jK R)) y = cl θ (𝟙 _) y ^ 2 := fun y => by
    rw [hh, hh₀', gs_scal', Category.assoc]
    obtain ⟨u, hu⟩ := isUnit_gs_scal G (𝟙 _) y (mul_ne_zero hr hr')
    rw [GlobalTheory.TwistLoc.gc, ← hu, Associates.mk_eq_one.2 u.isUnit, _root_.one_mul]
  refine ⟨h, fun j i => ?_, fun x k hx => ?_⟩
  · have hb : ∀ y ∈ pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i,
        Associates.mk (gs (𝟙 _) y _ (((pullback G.hom (jK R)).presheaf.map (homOfLE (inf_le_left :
          pullback.fst G.hom (jK R) ⁻¹ᵁ L2.U j ⊓ Lθ.U i ≤ _)).op).hom
            (((pullback.fst G.hom (jK R)).app (L2.U j)).hom (h.f j)))) = cl θ (𝟙 _) y ^ 2 := fun y hy => by
      rw [gs_res _ y _ hy, gs_pull _ _ y _ hy.1, ← hgen]
      exact (cl_eq h (𝟙 _ ≫ pullback.fst G.hom (jK R)) y hy.1).symm
    refine exists_unit_of_associated _ _ _ (fun y hy e => pow_ne_zero 2 (hθ0 y) ?_) (fun y hy => ?_)
    · rw [← hb y hy, e]; rfl
    · rw [← Associates.mk_eq_mk_iff_associated, hb y hy, gs_pow _ y _ hy, gs_res _ y _ hy, cl_eq θ _ y hy.2,
        Associates.mk_pow]
  · have e : cl h f.left x = (Associates.mk (GlobalTheory.TwistLoc.gc G.hom x r) * cl σ (𝟙 _) x) ^ 2 := by
      have e₁ := hrr x
      rw [hs, hs₀, ht, Category.id_comp, Category.id_comp, pow_one] at e₁
      rw [hh, gs_scal', Over.w f, GlobalTheory.TwistLoc.gc_mul, ← Associates.mk_mul_mk, _root_.mul_assoc, e₁, ← _root_.mul_assoc, ← sq,
        mul_pow]
    rw [cl_eq h f.left x hx] at e
    refine ⟨fun e0 => ?_, ?_⟩
    · refine cl_ne_zero_of_flat h2 h (exists_ne_zero_of_cl h2 h _ y₀ (by rw [hgen]; exact pow_ne_zero _ (hθ0 y₀)))
        f.left x ?_
      rw [cl_eq h f.left x hx, e0]
      rfl
    · obtain ⟨g, hg⟩ := Associates.mk_surjective (Associates.mk (GlobalTheory.TwistLoc.gc G.hom x r) * cl σ (𝟙 _) x)
      rw [← hg, ← Associates.mk_pow, Associates.mk_eq_mk_iff_associated] at e
      obtain ⟨u, hu⟩ := e.symm
      exact ⟨u, g, by rw [← hu, mul_comm]⟩

end GlobalTheory.SymExtend
