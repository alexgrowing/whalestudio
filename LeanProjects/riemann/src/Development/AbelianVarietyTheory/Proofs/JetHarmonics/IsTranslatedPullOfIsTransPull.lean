import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.EndomorphismPullbackRigid
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT IsNormEnd)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PtTie GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid

namespace GlobalTheory.TransPullCompare

variable {X : Scheme.{0}} {A : Over X}

abbrev TwoGen (L : LB A.left) {T : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, f.left] ![a, -b])

def Rel {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ} (α : TwoGen L m a b)
    (w : LB.Iso (PullPow L f b) (PowOver L a T)) : Prop :=
  m = f ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (j : Fin 2 → L.ι),
    r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
    gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j) =
      gm r z ((LB.div (PowOver L a T) (PullPow L f b)).U (fun _ => j 0, fun _ => j 1)) (w.s (fun _ => j 0, fun _ => j 1))

section Basic
variable {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ}

theorem mem_div_iff (j : Fin 2 → L.ι) (y : (T ⊗ A).left) :
    y ∈ (LB.div (PowOver L a T) (PullPow L f b)).U (fun _ => j 0, fun _ => j 1) ↔
      y ∈ LB.wchart L ![(snd T A).left, f.left] j :=
  ⟨fun h => Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [Set.mem_iInter.1 h.1 0, Set.mem_iInter.1 h.2 0],
    fun h => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h 1⟩⟩

theorem exists_rel_gen (h : m = f) (w : LB.Iso (PullPow L f b) (PowOver L a T)) : ∃ α : TwoGen L m a b, Rel α w := by
  subst h
  exact ⟨⟨fun j => res (fun y hy => (mem_div_iff j y).2 hy) (w.s (fun _ => j 0, fun _ => j 1))⟩, rfl,
    fun Z r z j hj => gm_res r z _ hj _⟩

theorem exists_rel_iso (h : m = f) (α : TwoGen L m a b) : ∃ w : LB.Iso (PullPow L f b) (PowOver L a T), Rel α w := by
  subst h
  have le : ∀ p : (Fin 1 → L.ι) × (Fin 1 → L.ι), (LB.div (PowOver L a T) (PullPow L m b)).U p ≤
      LB.wchart L ![(snd T A).left, m.left] ![p.1 0, p.2 0] := fun p y hy => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0]
  refine ⟨⟨fun p => res (le p) (α.s ![p.1 0, p.2 0])⟩, rfl, fun Z r z j hj => ?_⟩
  refine Eq.trans ?_ (gm_res r z _ ((mem_div_iff j _).2 hj) _).symm
  have e : ∀ j' : Fin 2 → L.ι, j = j' → gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j) =
      gm r z (LB.wchart L ![(snd T A).left, m.left] j') (α.s j') := by rintro _ rfl; rfl
  exact e _ (by funext k; fin_cases k <;> rfl)

theorem gm_div_two {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (j j' : Fin 2 → L.ι)
    (hj : r z ∈ LB.wchart L ![(snd T A).left, f.left] j) (hj' : r z ∈ LB.wchart L ![(snd T A).left, f.left] j') :
    gm r z _ ((LB.div (PowOver L a T) (PullPow L f b)).g (fun _ => j 0, fun _ => j 1) (fun _ => j' 0, fun _ => j' 1)) =
      trF ![(snd T A).left, f.left] ![a, -b] r z j j' := by
  have h := (mem_div_iff (a := a) (b := b) j _).2 hj
  have h' := (mem_div_iff (a := a) (b := b) j' _).2 hj'
  refine (gm_div (PullPow L f b) (PowOver L a T) r z (fun _ => j 0, fun _ => j 1) (fun _ => j' 0, fun _ => j' 1)
    ⟨h, h'⟩).trans ?_
  refine (congrArg₂ (· * ·) (gm_linComb L _ _ r z _ _ h.1 h'.1)
    (congrArg (·⁻¹) (gm_linComb L _ _ r z _ _ h.2 h'.2))).trans ?_
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]

theorem Rel.isGen_iff {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)} (h : Rel α w) :
    α.IsGen ↔ w.IsGen := by
  obtain ⟨rfl, H⟩ := h
  constructor
  · rintro hα ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    obtain ⟨j, rfl, rfl⟩ : ∃ j : Fin 2 → L.ι, p₁ = (fun _ => j 0) ∧ p₂ = fun _ => j 1 :=
      ⟨![p₁ 0, p₂ 0], funext fun k => congrArg p₁ (Subsingleton.elim _ _),
        funext fun k => congrArg p₂ (Subsingleton.elim _ _)⟩
    obtain ⟨j', rfl, rfl⟩ : ∃ j : Fin 2 → L.ι, q₁ = (fun _ => j 0) ∧ q₂ = fun _ => j 1 :=
      ⟨![q₁ 0, q₂ 0], funext fun k => congrArg q₁ (Subsingleton.elim _ _),
        funext fun k => congrArg q₂ (Subsingleton.elim _ _)⟩
    refine unit_ext fun y hy => ?_
    have hj := (mem_div_iff j y).1 hy.1
    have hj' := (mem_div_iff j' y).1 hy.2
    refine ((gm_res _ y _ hy _).trans (H _ _ y j hj).symm).trans ((gen_trans hα _ y hj hj').trans ?_)
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div_two _ y j j' hj hj')
      ((gm_res _ y _ hy _).trans (H _ _ y j' hj').symm))).symm
  · intro hw
    refine isGen_of_gm _ fun y j j' hj hj' => ?_
    have hy : (𝟙 (T ⊗ A).left : _ ⟶ _) y ∈ (LB.div (PowOver L a T) (PullPow L m b)).U (fun _ => j 0, fun _ => j 1) ⊓
        (LB.div (PowOver L a T) (PullPow L m b)).U (fun _ => j' 0, fun _ => j' 1) :=
      ⟨(mem_div_iff j y).2 hj, (mem_div_iff j' y).2 hj'⟩
    refine (H _ _ y j hj).trans ((gm_res _ y _ hy _).symm.trans ((congrArg (gm _ y _) (hw _ _)).trans ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div_two _ y j j' hj hj')
      ((gm_res _ y _ hy _).trans (H _ _ y j' hj').symm))

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (c : Γ(Y, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom c) = gs r z U c :=
  (gs_res (𝟙 Z) z h trivial ((r.app U).hom c)).trans ((gs_pull (𝟙 Z) r z U (h trivial) c).trans
    (by rw [Category.id_comp]))

theorem gm_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (c : Γ(Y, U)ˣ) :
    gm (𝟙 Z) z ⊤ (Units.map (r.appLE U ⊤ h).hom.toMonoidHom c) = gm r z U c :=
  Units.ext ((gs_unit (𝟙 Z) z ⊤ trivial _).symm.trans ((gs_appLE r U h z c.val).trans (gs_unit r z U (h trivial) c)))

theorem gs_stalk {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ Y') (z : Z) (U : Y'.Opens) (h : q (r z) ∈ U)
    (c : Γ(Y', U)) : (r.stalkMap z).hom (gs q (r z) U c) = gs (r ≫ q) z U c := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

abbrev stU {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (r z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (r.stalkMap z).hom.toMonoidHom

theorem gm_stalk {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ Y') (z : Z) (U : Y'.Opens) (h : q (r z) ∈ U)
    (c : Γ(Y', U)ˣ) : stU r z (gm q (r z) U c) = gm (r ≫ q) z U c :=
  Units.ext ((congrArg (r.stalkMap z).hom (gs_unit q (r z) U h c).symm).trans ((gs_stalk r q z U h c.val).trans
    (gs_unit (r ≫ q) z U h c)))

theorem exists_loc {W : Over X} (z : W.left) {J : (W.left ⟶ A.left) → L.ι} (hJ : Good L z J) {K : Type} [Fintype K]
    (x : K → (W ⟶ A)) : ∃ (W' : Over X) (p : W' ⟶ W) (z' : W'.left), p.left z' = z ∧
      Function.Injective (p.left.stalkMap z').hom ∧ ∀ k, Lands L (p ≫ x k) (J (x k).left) := by
  let V : W.left.Opens := LB.wchart L (fun k => (x k).left) (fun k => J (x k).left)
  have hz : z ∈ V := Set.mem_iInter.2 fun k => hJ _
  refine ⟨overRes V, overResι V, ⟨z, hz⟩, rfl, ?_, fun k y _ => Set.mem_iInter.1 y.2 k⟩
  have hi : ∀ y : V.toScheme, IsIso (V.ι.stalkMap y) := fun y => inferInstance
  have := hi ⟨z, hz⟩
  exact (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap ⟨z, hz⟩)).1

def tr (L : LB A.left) {W : Over X} (v : W ⟶ A) (z : W.left) (i : L.ι) (J : (W.left ⟶ A.left) → L.ι) :
    (W.left.presheaf.stalk z)ˣ := gm v.left z (L.U i ⊓ L.U (J v.left)) (L.g i (J v.left))

variable {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)}

theorem lift_left_snd {W : Over X} (t : W ⟶ T) (v : W ⟶ A) : (lift t v).left ≫ (snd T A).left = v.left := by
  rw [← Over.comp_left, lift_snd]

theorem Rel.germ_isoVal (h : Rel α w) (hα : α.IsGen) {W : Over X} (t : W ⟶ T) (v u : W ⟶ A) (hu : lift t v ≫ f = u)
    (i j : L.ι) (hi : Lands L v i) (hj : Lands L u j) (z : W.left) {J} (hJ : Good L z J) :
    gm (𝟙 _) z ⊤ (isoVal w t v u hu i j hi hj) = tr L v z i J ^ a * tr L u z j J ^ (-b) * val α (lift t v).left z J := by
  obtain ⟨rfl, H⟩ := h
  have hm : (lift t v).left z ∈ LB.wchart L ![(snd T A).left, m.left] ![i, j] := (mem_div_iff (a := a) (b := b) _ _).1
    ⟨Lands.le_wchart (lift_snd t v) hi trivial, Lands.le_wchart hu hj trivial⟩
  refine ((gm_appLE _ _ _ z _).trans (H _ _ z ![i, j] hm).symm).trans
    ((gen_trans hα _ z hm (hJ.mem _ _)).trans (congrArg (· * _) ?_))
  subst hu
  exact (Fin.prod_univ_two _).trans (congrArg₂ (· * ·)
    (congrArg (fun q => gm q z (L.U i ⊓ L.U (J q)) (L.g i (J q)) ^ a) (lift_left_snd t v)) rfl)

theorem Rel.stalk_val (h : Rel α w) {W W' : Over X} (p : W' ⟶ W) (z : W'.left) {J} (hJ : Good L (p.left z) J)
    (t : W ⟶ T) (v u : W ⟶ A) (hu : lift t v ≫ f = u) {t' : W' ⟶ T} {v' u' : W' ⟶ A} (ht : p ≫ t = t') (hv : p ≫ v = v')
    (hu' : lift t' v' ≫ f = u') (hi : Lands L v' (J v.left)) (hj : Lands L u' (J u.left)) :
    stU p.left z (val α (lift t v).left (p.left z) J) = gm (𝟙 _) z ⊤ (isoVal w t' v' u' hu' _ _ hi hj) := by
  obtain ⟨rfl, H⟩ := h
  subst ht hv hu
  have hm : (lift (p ≫ t) (p ≫ v)).left z ∈ LB.wchart L ![(snd T A).left, m.left] ![J v.left, J (lift t v ≫ m).left] :=
    (mem_div_iff (a := a) (b := b) _ _).1
      ⟨Lands.le_wchart (lift_snd _ _) hi trivial, Lands.le_wchart hu' hj trivial⟩
  refine Eq.trans ?_ ((gm_appLE _ _ _ z _).trans (H _ _ z _ hm).symm).symm
  rw [val_of α _ _ J ![J v.left, J (lift t v ≫ m).left] (fun k => by
    fin_cases k
    exacts [congrArg J (lift_left_snd t v), rfl])]
  rw [← comp_lift] at hm ⊢
  exact gm_stalk p.left _ z _ hm _

theorem germ_secVal {k : ℤ} (s : LB.Sec (PowOver L k T)) {W : Over X} (t : W ⟶ T) (v : W ⟶ A) (i : L.ι)
    (hi : Lands L v i) (z : W.left) {J} (hJ : Good L z J) :
    gs (𝟙 _) z ⊤ (secVal s t v i hi) = (tr L v z i J ^ k).val * sval s (lift t v).left z J := by
  refine (gs_appLE _ _ _ z _).trans ((sec_trans s _ z (Lands.le_wchart (lift_snd t v) hi trivial)
    (hJ.mem _ _)).trans (congrArg (fun u : (W.left.presheaf.stalk z)ˣ => u.val * _) ?_))
  simp only [trF, tr, Fin.prod_univ_one]
  rw [lift_left_snd]

theorem stalk_sval {k : ℤ} (s : LB.Sec (PowOver L k T)) {W W' : Over X} (p : W' ⟶ W) (z : W'.left)
    {J : (W.left ⟶ A.left) → L.ι}
    (t : W ⟶ T) (v : W ⟶ A) {t' : W' ⟶ T} {v' : W' ⟶ A} (ht : p ≫ t = t') (hv : p ≫ v = v')
    (hi : Lands L v' (J v.left)) :
    (p.left.stalkMap z).hom (sval s (lift t v).left (p.left z) J) = gs (𝟙 _) z ⊤ (secVal s t' v' _ hi) := by
  subst ht hv
  have hm := Lands.le_wchart (lift_snd (p ≫ t) (p ≫ v)) hi (show z ∈ (⊤ : W'.left.Opens) from trivial)
  refine Eq.trans ?_ (gs_appLE _ _ _ z _).symm
  rw [sval_of s _ _ J (fun _ => J v.left) (fun k => congrArg J (lift_left_snd t v))]
  rw [← comp_lift] at hm ⊢
  exact gs_stalk p.left _ z _ hm _

end Basic

section Compare
variable {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ}
  {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)}

theorem id_left_eq (T A : Over X) : 𝟙 (T ⊗ A).left = (lift (fst T A) (snd T A)).left := by
  rw [lift_fst_snd, Over.id_left]

theorem some_good (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose J hJ using fun χ : Z ⟶ A.left => exists_chart hL (χ z)
  exact ⟨J, hJ⟩

theorem stU_inj {Y Z : Scheme.{0}} {r : Z ⟶ Y} {z : Z} (h : Function.Injective (r.stalkMap z).hom) :
    Function.Injective (stU r z) := Units.map_injective h

theorem Rel.twist_iff [GrpObj A] (hL : L.IsLB) (h : Rel α w) (hα : α.IsGen) (s : LB.Sec (LPow A L b T))
    (s' : LB.Sec (LPow A L a T)) :
    IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s s' ↔ Carries w s s' := by
  obtain rfl := h.1
  have e : ∀ {W : Over X} (t : W ⟶ T) (v : W ⟶ A),
      (lift t v).left ≫ (lift (fst T A) m).left = (lift t (lift t v ≫ m)).left := fun t v => by
    rw [← Over.comp_left, comp_lift, lift_fst]
  constructor
  · intro H W t v i j hi hj
    refine fn_ext fun z _ => ?_
    obtain ⟨J, hJ⟩ := some_good hL z
    have k := twist_val H (lift t v).left z hJ
    rw [e] at k
    refine (germ_secVal s' t v i hi z hJ).trans (Eq.trans ?_ ((gs_mul _ z ⊤ trivial _ _).trans (congrArg₂ (· * ·)
      ((gs_unit _ z ⊤ trivial _).trans (congrArg Units.val (h.germ_isoVal hα t v _ rfl i j hi hj z hJ)))
      (germ_secVal s t _ j hj z hJ))).symm)
    refine (congrArg _ k).trans ?_
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _ (tr L _ z j J ^ b),
      inv_mul_cancel_right]
  · intro H
    refine VVRank.isTwistPull_of_sv A hL hα fun y J hJ => ?_
    obtain ⟨W, p, z, rfl, inj, hl⟩ := exists_loc (W := T ⊗ A) y hJ ![snd T A, lift (fst T A) (snd T A) ≫ m]
    have e' : lift (p ≫ fst T A) (p ≫ snd T A) ≫ m = p ≫ lift (fst T A) (snd T A) ≫ m := by
      rw [← comp_lift, Category.assoc]
    have hj : Lands L (lift (p ≫ fst T A) (p ≫ snd T A) ≫ m) (J (lift (fst T A) (snd T A) ≫ m).left) := e' ▸ hl 1
    have k := congrArg (gs (𝟙 _) z ⊤) (H W (p ≫ fst T A) (p ≫ snd T A) _ _ (hl 0) hj)
    rw [id_left_eq, e]
    apply inj
    refine (stalk_sval s' p z _ _ rfl rfl (hl 0)).trans (k.trans ((gs_mul _ z ⊤ trivial _ _).trans
      (Eq.trans ?_ (map_mul _ _ _).symm)))
    exact congrArg₂ (· * ·) ((gs_unit _ z ⊤ trivial _).trans
      (congrArg Units.val (h.stalk_val p z hJ _ _ _ rfl rfl rfl rfl (hl 0) hj)).symm)
      (stalk_sval s p z _ _ rfl e'.symm hj).symm

end Compare

section Grp
variable [GrpObj A] [IsCommMonObj A]

theorem translPt_eq_transl {T : Over X} (b : T ⟶ A) : translPt A b = transl b :=
  (translPt_eq b).trans (_root_.mul_comm _ _)

theorem lift_translT {T W : Over X} (b : T ⟶ A) (t : W ⟶ T) (v : W ⟶ A) :
    (lift t v).left ≫ (translT A b).left = (lift t (v * (t ≫ b))).left := by
  rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.lift_transl, _root_.mul_comm]

theorem lift_negT {T W : Over X} (t : W ⟶ T) (v : W ⟶ A) :
    (lift t v).left ≫ (negT A T).left = (lift t v⁻¹).left := by
  rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc, Hom.inv_def]

variable {L : LB A.left} {T : Over X} {k : ℤ}

theorem pow_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) {U : Lift L k θ.pt} (h : Rel (m := translPt A θ.pt) θ.φ U)
    {N : ℕ} (hN : 0 < N) (hb : θ.pt ^ N = 1) :
    LB.Gen.Corr L _ _ _ _ (powGen A L k θ N) (LB.oneGen L) ↔ PowEqOne U N := by
  have e : ∀ {W : Over X} (t : W ⟶ T) (v : W ⟶ A) (z : W.left) {J}, Good L z J →
      val (powGen A L k θ N) (lift t v).left z J = ∏ i ∈ Finset.range N,
        val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (lift t (v * (t ≫ θ.pt) ^ i)).left z J := fun t v z J hJ => by
    rw [ThetaPullback.val_powGen θ N _ hJ, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [lift_translT, MonObj.comp_pow]
  constructor
  · intro H W t v c hc hc0
    refine unit_ext fun z _ => ?_
    obtain ⟨J, hJ⟩ := some_good hL z
    have k₀ := (e t v z hJ).symm.trans ((val_corr hJ H _).trans (val_one _))
    rw [map_prod, map_one]
    refine (Finset.prod_congr rfl fun i _ => h.germ_isoVal θ.isGen t _ _ _ _ _ _ _ z hJ).trans ?_
    rw [Finset.prod_mul_distrib, k₀, _root_.mul_one]
    have tel := Finset.prod_range_div' (fun i => tr L (v * (t ≫ θ.pt) ^ i) z (c i) J ^ k) N
    simp only [zpow_neg, ← div_eq_mul_inv]
    rw [tel, hc0, ← MonObj.comp_pow θ.pt N t, hb, MonObj.comp_one, pow_zero, div_self']
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    rw [val_one, id_left_eq, e _ _ _ hJ]
    obtain ⟨W, p, z, rfl, inj, hl⟩ := exists_loc (W := T ⊗ A) y hJ
      (fun i : Fin N => snd T A * (fst T A ≫ θ.pt) ^ (i : ℕ))
    have hb' : (fst T A ≫ θ.pt) ^ N = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
    have e' : ∀ i : ℕ, p ≫ (snd T A * (fst T A ≫ θ.pt) ^ i) = (p ≫ snd T A) * ((p ≫ fst T A) ≫ θ.pt) ^ i := fun i => by
      rw [MonObj.comp_mul, MonObj.comp_pow, Category.assoc]
    have hc : ∀ i : ℕ, Lands L ((p ≫ snd T A) * ((p ≫ fst T A) ≫ θ.pt) ^ i)
        (J (snd T A * (fst T A ≫ θ.pt) ^ i).left) := fun i => by
      rw [← e', pow_eq_pow_mod i hb']
      exact hl ⟨i % N, Nat.mod_lt _ hN⟩
    have k₀ := congrArg (gm (𝟙 _) z ⊤) (H W (p ≫ fst T A) (p ≫ snd T A) _ hc (by rw [hb', pow_zero]))
    apply stU_inj inj
    rw [map_prod, map_one] at k₀ ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) k₀
    exact h.stalk_val p z hJ _ _ _ (by rw [IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.lift_transl, pow_succ, _root_.mul_assoc]) rfl (e' i) _ _ _

def SymVal (θ : ThetaGrp A L k T) (ν : TwoGen L (snd T A ≫ ι[A]) k k) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (z : W.left) (J), Good L z J →
    val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t v).left z J *
      val ν (lift t (v * (t ≫ θ.pt))).left z J *
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (lift t (v * (t ≫ θ.pt))⁻¹).left z J = val ν (lift t v).left z J

theorem symVal_iff_corr (hL : L.IsLB) (θ : ThetaGrp A L k T) (ν : TwoGen L (snd T A ≫ ι[A]) k k) :
    LB.Gen.Corr L _ _ _ _ (symGen A L k θ ν) (LB.oneGen L) ↔ SymVal θ ν := by
  constructor
  · intro H W t v z J hJ
    have k₀ := (ThetaPullback.val_symGen θ ν (lift t (v * (t ≫ θ.pt))).left hJ).symm.trans
      ((val_corr hJ H _).trans (val_one _))
    rw [lift_translT, lift_negT, GrpObj.comp_inv, mul_inv_cancel_right, ← _root_.mul_assoc] at k₀
    exact mul_inv_eq_one.1 k₀
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    have k₀ := H _ (fst T A) (snd T A * (fst T A ≫ θ.pt)⁻¹) y J hJ
    rw [inv_mul_cancel_right] at k₀
    rw [val_one, id_left_eq, ThetaPullback.val_symGen θ ν _ hJ, lift_translT, lift_negT, GrpObj.comp_inv,
      ← _root_.mul_assoc]
    exact mul_inv_eq_one.2 k₀

theorem symVal_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) {U : Lift L k θ.pt} (h : Rel (m := translPt A θ.pt) θ.φ U)
    {ν : TwoGen L (snd T A ≫ ι[A]) k k} {I : LB.Iso (PullPow L (snd T A ≫ ι[A]) k) (PowOver L k T)} (h' : Rel ν I)
    (hν : ν.IsGen) : SymVal θ ν ↔ IsSymmetricLift I U := by
  constructor
  · intro H W t v i j l m hi hj hl hm
    refine unit_ext fun z _ => ?_
    obtain ⟨J, hJ⟩ := some_good hL z
    rw [map_mul, map_mul, h.germ_isoVal θ.isGen t _ _ _ _ _ _ _ z hJ, h.germ_isoVal θ.isGen t _ _ _ _ _ _ _ z hJ,
      h'.germ_isoVal hν t _ _ _ _ _ _ _ z hJ, h'.germ_isoVal hν t _ _ _ _ _ _ _ z hJ, ← H W t v z J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module
  · intro H W t v y J hJ
    obtain ⟨W', p, z, rfl, inj, hl⟩ := exists_loc y hJ ![v, v * (t ≫ θ.pt), (v * (t ≫ θ.pt))⁻¹, v⁻¹]
    have e₁ : p ≫ (v * (t ≫ θ.pt)) = (p ≫ v) * ((p ≫ t) ≫ θ.pt) := by rw [MonObj.comp_mul, Category.assoc]
    have e₂ : p ≫ (v * (t ≫ θ.pt))⁻¹ = ((p ≫ v) * ((p ≫ t) ≫ θ.pt))⁻¹ := by rw [GrpObj.comp_inv, e₁]
    have e₃ : p ≫ v⁻¹ = (p ≫ v)⁻¹ := GrpObj.comp_inv _ _
    have k₀ := congrArg (gm (𝟙 _) z ⊤) (H W' (p ≫ t) (p ≫ v) (J v.left) (J (v * (t ≫ θ.pt)).left)
      (J (v * (t ≫ θ.pt))⁻¹.left) (J v⁻¹.left) (hl 0) (e₁ ▸ hl 1) (e₂ ▸ hl 2) (e₃ ▸ hl 3))
    apply stU_inj inj
    rw [map_mul, map_mul] at k₀ ⊢
    refine Eq.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_) (k₀.trans (Eq.symm ?_))
    · exact h.stalk_val p z hJ _ _ _ (IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.lift_transl _ _ _) rfl rfl _ _ _
    · exact h'.stalk_val p z hJ _ _ _ (lift_neg _ _) rfl e₁ _ _ _
    · exact h.stalk_val p z hJ _ _ _
        (by rw [IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.lift_transl, mul_inv_rev, mul_comm (t ≫ θ.pt)⁻¹, inv_mul_cancel_right]) rfl e₂ _ _ _
    · exact h'.stalk_val p z hJ _ _ _ (lift_neg _ _) rfl rfl _ _ _

end Grp

section Norm
variable [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def rho (W : Over X) (z : W.left) (J : (W.left ⟶ A.left) → L.L.ι) : (W.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (toUnit W).left z J

theorem germ_rigVal (W : Over X) (i : L.L.ι) (hi : Lands L.L (1 : W ⟶ A) i) (z : W.left) {J} (hJ : Good L.L z J) :
    gm (𝟙 _) z ⊤ (rigVal L W i hi) = tr L.L (1 : W ⟶ A) z i J * rho L W z J := by
  refine (gm_appLE _ _ _ z _).trans ((gen_trans (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rigGen
    (toUnit W).left z (Set.mem_iInter.2 fun _ => hi trivial) (hJ.mem _ _)).trans (congrArg (· * _) ?_))
  rw [trF, Fintype.prod_unique, zpow_one]
  rfl

theorem stalk_rho {W W' : Over X} (p : W' ⟶ W) (z : W'.left) {J} (hJ : Good L.L (p.left z) J)
    (hi : Lands L.L (1 : W' ⟶ A) (J (1 : W ⟶ A).left)) :
    stU p.left z (rho L W (p.left z) J) = gm (𝟙 _) z ⊤ (rigVal L W' _ hi) := by
  refine Eq.trans ?_ (gm_appLE _ _ _ z _).symm
  rw [toUnit_unique (toUnit W') (p ≫ toUnit W)]
  exact gm_stalk p.left _ z _ (hJ.mem (fun _ : PUnit => eSec A) (toUnit W).left) _

def NormVal {T : Over X} {m : T ⊗ A ⟶ A} {a b : ℤ} (α : TwoGen L.L m a b) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (z : W.left) (J), Good L.L z J →
    val α (lift t (1 : W ⟶ A)).left z J = rho L W z J ^ a * rho L W z J ^ (-b)

variable {L}

theorem Rel.norm_iff {φ : A ⟶ A} [IsMonHom φ] {T : Over X} {a b : ℤ} {α : TwoGen L.L (snd T A ≫ φ) a b}
    {w : LB.Iso (PullPow L.L (snd T A ≫ φ) b) (PowOver L.L a T)} (h : Rel α w) (hα : α.IsGen) :
    NormVal L α ↔ IsNormalisedIso L φ a b T w := by
  have hL := L.isLB
  constructor
  · refine fun H => ⟨h.isGen_iff.1 hα, fun W t i j hi hj => unit_ext fun z _ => ?_⟩
    obtain ⟨J, hJ⟩ := some_good hL z
    rw [map_mul, map_zpow, map_zpow, h.germ_isoVal hα t _ _ _ _ _ _ _ z hJ, germ_rigVal L W i hi z hJ,
      germ_rigVal L W j hj z hJ, H W t z J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module
  · rintro ⟨-, H⟩ W t y J hJ
    obtain ⟨W', p, z, rfl, inj, hl⟩ := exists_loc y hJ (fun _ : Unit => (1 : W ⟶ A))
    have hi : Lands L.L (1 : W' ⟶ A) (J (1 : W ⟶ A).left) := MonObj.comp_one (M := A) p ▸ hl ()
    have k₀ := congrArg (gm (𝟙 _) z ⊤) (H W' (p ≫ t) _ _ hi hi)
    apply stU_inj inj
    rw [map_mul, map_zpow, map_zpow] at k₀ ⊢
    rw [h.stalk_val p z hJ t 1 1 (origin_comp t φ) rfl (MonObj.comp_one p) (origin_comp _ φ) hi hi, stalk_rho L p z hJ hi,
      k₀, zpow_neg, mul_inv_cancel_right]

theorem isNormEnd_iff {φ : A ⟶ A} {a b : ℤ}
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) :
    IsNormEnd A L φ a b α₀ ↔ ∀ (W : Over X) (z : W.left) (J), Good L.L z J →
      val α₀ (1 : W ⟶ A).left z J = rho L W z J ^ a * rho L W z J ^ (-b) := by
  have p : ∀ (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over X)).left) (y : Z) (J), val (rigPow A L.L L.rig k) r y J =
    val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig r y J ^ k := fun k _ _ _ _ => map_zpow _ _ _
  constructor
  · intro H W z J hJ
    have k₀ := val_corr hJ H (toUnit W).left
    rw [val_pull hJ, val_mul hJ, p, p] at k₀
    exact k₀
  · intro H
    refine corr_of_val L.isLB fun y J hJ => ?_
    rw [val_pull hJ, val_mul hJ, p, p]
    have k₀ := H (𝟙_ (Over X)) y J hJ
    rw [rho, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _)] at k₀
    exact k₀

theorem exists_pull_gen {M : LB A.left} (hM : M.IsLB) {φ : A ⟶ A} {a b : ℤ}
    (α₀ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα₀ : α₀.IsGen) (T : Over X) :
    ∃ α : TwoGen M (snd T A ≫ φ) a b, α.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good M z J →
      val α r z J = val α₀ (r ≫ (snd T A).left) z J := by
  obtain ⟨α, hα, hv⟩ := exists_gen hM (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen M ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left) (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_norm_gen (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen) :
    ∃ α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]), α₀.IsGen ∧ IsNormEnd A L φ a b α₀ := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  refine ⟨α₀, hα₀, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem exists_norm_neg {T : Over X} {k : ℤ} (ν : TwoGen L.L (snd T A ≫ ι[A]) k k) (hν : ν.IsGen) :
    ∃ ν' : TwoGen L.L (snd T A ≫ ι[A]) k k, ν'.IsGen ∧ ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (z : W.left) (J),
      Good L.L z J → val ν' (lift t v).left z J = val ν (lift t v).left z J * (val ν (lift t (1 : W ⟶ A)).left z J)⁻¹ := by
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) 1
  have e₁ : n.left ≫ (snd T A ≫ ι[A]).left = n.left ≫ (snd T A).left := by
    rw [← Over.comp_left, ← Over.comp_left, origin_comp, lift_snd]
  obtain ⟨ν', hν', hv⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε' := ![k, -k])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁]
      rw [← zpow_add, neg_neg, neg_add_cancel, zpow_zero, _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ ν (LB.invGen L.L _ _ (LB.pullGen L.L _ _ ν n.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hν (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _)))
  refine ⟨ν', hν', fun W t v z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]

end Norm

section Main
variable [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isSymTranslate_iff (N : ℕ) {T : Over X} (b : T ⟶ A) (s s' : LB.Sec (LPow A L.L (N : ℤ) T)) :
    IsSymTranslate L N b s s' ↔ Odd N ∧ IsSymAct A L N b s s' := by
  have hL := L.isLB
  constructor
  · rintro ⟨hN, hb, I, U, ⟨hI, -⟩, hU, hs, hp, hc⟩
    obtain ⟨α, h⟩ := exists_rel_gen (translPt_eq_transl b) U
    obtain ⟨ν, h'⟩ := exists_rel_gen rfl I
    have hα := h.isGen_iff.2 hU
    have hν := h'.isGen_iff.2 hI
    let θ : ThetaGrp A L.L N T := ⟨b, α, hα⟩
    exact ⟨hN, hb, θ, ⟨rfl, (pow_iff hL θ h hN.pos hb).2 hp, ν, hν,
      (symVal_iff_corr hL θ ν).2 ((symVal_iff hL θ h h' hν).2 hs)⟩, (h.twist_iff hL hα s s').2 hc⟩
  · rintro ⟨hN, hb, θ, ⟨rfl, hp, ν, hν, hs⟩, hc⟩
    obtain ⟨U, h⟩ := exists_rel_iso (translPt_eq_transl θ.pt) θ.φ
    obtain ⟨ν', hν', hv⟩ := exists_norm_neg (L := L) ν hν
    obtain ⟨I, h'⟩ := exists_rel_iso rfl ν'
    refine ⟨hN, hb, I, U, (h'.norm_iff hν').1 fun W t z J hJ => ?_, h.isGen_iff.1 θ.isGen,
      (symVal_iff hL θ h h' hν').1 fun W t v z J hJ => ?_, (pow_iff hL θ h hN.pos hb).1 hp,
      (h.twist_iff hL θ.isGen s s').1 hc⟩
    · rw [hv W t 1 z J hJ, mul_inv_cancel, zpow_neg, mul_inv_cancel]
    · rw [hv W t _ z J hJ, hv W t _ z J hJ, ← (symVal_iff_corr hL θ ν).1 hs W t v z J hJ, ← _root_.mul_assoc,
        mul_right_comm]

theorem isNormPull_iff_gen (φ : A ⟶ A) (a b : ℤ) {T : Over X} (s : LB.Sec (LPow A L.L b T))
    (s' : LB.Sec (LPow A L.L a T)) : IsNormPull A L φ a b s s' ↔
      ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (α : TwoGen L.L (snd T A ≫ φ) a b),
        α₀.IsGen ∧ IsNormEnd A L φ a b α₀ ∧ α.IsGen ∧
        (∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (z : W.left) (J), Good L.L z J →
          val α (lift t v).left z J = val α₀ v.left z J) ∧
        IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α s s' := by
  have hL := L.isLB
  constructor
  · rintro ⟨α₀, α, h₀, n₀, c, tw⟩
    obtain ⟨α', hα', hv⟩ := exists_pull_gen hL α₀ h₀ T
    refine ⟨α₀, α', h₀, n₀, hα', fun W t v z J hJ => by rw [hv _ _ z J hJ, lift_left_snd],
      VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans ?_⟩
    rw [val_corr hJ c, val_pull hJ, hv _ _ y J hJ]
  · rintro ⟨α₀, α, h₀, n₀, -, hv, tw⟩
    refine ⟨α₀, α, h₀, n₀, corr_of_val hL fun y J hJ => ?_, tw⟩
    rw [val_pull hJ, Category.id_comp, id_left_eq, hv _ _ _ y J hJ]

def ComesFrom {M : LB A.left} {φ : A ⟶ A} {a b : ℤ} {T : Over X}
    (w₀ : LB.Iso (PullPow M (snd (𝟙_ (Over X)) A ≫ φ) b) (PowOver M a (𝟙_ (Over X))))
    (w : LB.Iso (PullPow M (snd T A ≫ φ) b) (PowOver M a T)) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (i j : M.ι) (hi : Lands M v i) (hj : Lands M (v ≫ φ) j),
    isoVal w t v _ (lift_snd_assoc _ _ _) i j hi hj = isoVal w₀ (toUnit W) v _ (lift_snd_assoc _ _ _) i j hi hj

theorem isNormPull_iff_comesFrom (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) {T : Over X} (s : LB.Sec (LPow A L.L b T))
    (s' : LB.Sec (LPow A L.L a T)) : IsNormPull A L φ a b s s' ↔
      ∃ (w₀ : LB.Iso (PullPow L.L (snd (𝟙_ (Over X)) A ≫ φ) b) (PowOver L.L a (𝟙_ (Over X))))
        (w : LB.Iso (PullPow L.L (snd T A ≫ φ) b) (PowOver L.L a T)),
        IsNormalisedIso L φ a b _ w₀ ∧ ComesFrom w₀ w ∧ IsNormalisedIso L φ a b T w ∧ Carries w s s' := by
  have hL := L.isLB
  rw [isNormPull_iff_gen]
  constructor
  · rintro ⟨α₀, α, h₀, n₀, hα, hv, tw⟩
    obtain ⟨α₁, hα₁, hv₁⟩ := exists_pull_gen hL α₀ h₀ (𝟙_ (Over X))
    obtain ⟨w₀, r₀⟩ := exists_rel_iso rfl α₁
    obtain ⟨w, r⟩ := exists_rel_iso rfl α
    rw [isNormEnd_iff] at n₀
    refine ⟨w₀, w, (r₀.norm_iff hα₁).1 fun W t z J hJ => ?_, fun W t v i j hi hj => unit_ext fun z _ => ?_,
      (r.norm_iff hα).1 fun W t z J hJ => ?_, (r.twist_iff hL hα s s').1 tw⟩
    · rw [hv₁ _ _ z J hJ, lift_left_snd, n₀ W z J hJ]
    · obtain ⟨J, hJ⟩ := some_good hL z
      rw [r.germ_isoVal hα _ _ _ _ _ _ _ _ z hJ, r₀.germ_isoVal hα₁ _ _ _ _ _ _ _ _ z hJ, hv _ _ _ z J hJ,
        hv₁ _ _ z J hJ, lift_left_snd]
    · rw [hv _ _ _ z J hJ, n₀ W z J hJ]
  · rintro ⟨w₀, w, n₀, hc, n, c⟩
    obtain ⟨α₁, r₀⟩ := exists_rel_gen rfl w₀
    obtain ⟨α, r⟩ := exists_rel_gen rfl w
    have hα₁ := r₀.isGen_iff.2 n₀.1
    have hα := r.isGen_iff.2 n.1
    let q : A ⟶ 𝟙_ (Over X) ⊗ A := lift (toUnit A) (𝟙 A)
    obtain ⟨α₀, h₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
      (fun U _ f => by
        refine (prod_two q _ _ a (-b) f).trans ?_
        rw [lift_snd, lift_snd_assoc, Category.id_comp, Fin.prod_univ_two]; rfl)
      (LB.pullGen L.L _ _ α₁ q.left) (DVR.pullGen_isGen _ _ _ _ hα₁ _)
    have hv : ∀ (W : Over X) (v : W ⟶ A) (z : W.left) (J), Good L.L z J →
        val α₀ v.left z J = val α₁ (lift (toUnit W) v).left z J := fun W v z J hJ => by
      rw [hv₀ _ _ z J hJ, val_pull hJ, ← Over.comp_left, comp_lift, comp_toUnit, Category.comp_id]
    refine ⟨α₀, α, h₀, (isNormEnd_iff α₀).2 fun W z J hJ => ?_, hα, fun W t v y J hJ => ?_,
      (r.twist_iff hL hα s s').2 c⟩
    · rw [hv W 1 z J hJ, (r₀.norm_iff hα₁).2 n₀ W _ z J hJ]
    · rw [hv W v y J hJ]
      obtain ⟨W', p, z, rfl, inj, hl⟩ := exists_loc y hJ ![v, v ≫ φ]
      have hj : Lands L.L ((p ≫ v) ≫ φ) (J (v ≫ φ).left) := (Category.assoc p v φ).symm ▸ hl 1
      apply stU_inj inj
      exact (r.stalk_val p z hJ t v _ (lift_snd_assoc _ _ _) rfl rfl (lift_snd_assoc _ _ _) (hl 0) hj).trans
        ((congrArg _ (hc W' (p ≫ t) (p ≫ v) _ _ (hl 0) hj)).trans
          (r₀.stalk_val p z hJ _ v _ (lift_snd_assoc _ _ _) (comp_toUnit p) rfl (lift_snd_assoc _ _ _) (hl 0) hj).symm)

theorem isEndPull_of_isNormPull (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) {T : Over X} {s : LB.Sec (LPow A L.L b T)}
    {s' : LB.Sec (LPow A L.L a T)} (h : IsNormPull A L φ a b s s') : IsEndPull L φ a b s s' := by
  obtain ⟨-, w, -, -, n, c⟩ := (isNormPull_iff_comesFrom L φ a b s s').1 h
  exact ⟨w, n, c⟩

theorem isEndPull_iff_base (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) (s : LB.Sec (LPow A L.L b (𝟙_ (Over X))))
    (s' : LB.Sec (LPow A L.L a (𝟙_ (Over X)))) : IsEndPull L φ a b s s' ↔ IsNormPull A L φ a b s s' := by
  refine ⟨fun ⟨w, n, c⟩ => (isNormPull_iff_comesFrom L φ a b s s').2 ⟨w, w, n, fun W t v i j hi hj => ?_, n, c⟩,
    isEndPull_of_isNormPull L φ a b⟩
  obtain rfl := toUnit_unique t (toUnit W)
  rfl

theorem isEndPull_iff (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) {T : Over X}
    (hp : Function.Surjective (fst T A).left.appTop.hom)
    (hβ : ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]), β.IsGen)
    (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)) :
    IsEndPull L φ a b s s' ↔ IsNormPull A L φ a b s s' := by
  have hL := L.isLB
  refine ⟨fun ⟨w, n, c⟩ => ?_, isEndPull_of_isNormPull L φ a b⟩
  obtain ⟨β, hβ⟩ := hβ
  obtain ⟨α₀, h₀, n₀⟩ := exists_norm_gen φ a b β hβ
  obtain ⟨α', hα', hv⟩ := exists_pull_gen hL α₀ h₀ T
  obtain ⟨α, r⟩ := exists_rel_gen rfl w
  have hα := r.isGen_iff.2 n.1
  refine (isNormPull_iff_gen L φ a b s s').2 ⟨α₀, α, h₀, n₀, hα, fun W t v z J hJ => ?_, (r.twist_iff hL hα s s').2 c⟩
  rw [gen_unique hL (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    (congrArg (fun q => q.left) (lift_fst _ _ : lift (𝟙 T) (1 : T ⟶ A) ≫ _ = _)) hp hα hα' (fun y I hI => by
      rw [(r.norm_iff hα).2 n T _ y I hI, hv _ _ y I hI, lift_left_snd, (isNormEnd_iff α₀).1 n₀ T y I hI]) _ _ z J hJ,
    hv _ _ z J hJ, lift_left_snd]

theorem isTranslatedPull_of_isTransPull (φ : A ⟶ A) [IsMonHom φ] {N : ℕ} (hN : Odd N) {T : Over X} (b : T ⟶ A)
    {s : LB.Sec (LPow A L.L 1 T)} {hh : LB.Sec (LPow A L.L (N : ℤ) T)} (h : IsTransPull A L φ N s b hh) :
    IsTranslatedPull L φ N b s hh := by
  obtain ⟨h₁, p, q⟩ := h
  exact ⟨h₁, isEndPull_of_isNormPull L φ _ _ p, (isSymTranslate_iff L N b h₁ hh).2 ⟨hN, q⟩⟩

theorem isTranslatedPull_iff (φ : A ⟶ A) [IsMonHom φ] (N : ℕ) {T : Over X}
    (hp : Function.Surjective (fst T A).left.appTop.hom)
    (hβ : ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(N : ℤ), -1]), β.IsGen) (b : T ⟶ A)
    (s : LB.Sec (LPow A L.L 1 T)) (hh : LB.Sec (LPow A L.L (N : ℤ) T)) :
    IsTranslatedPull L φ N b s hh ↔ Odd N ∧ IsTransPull A L φ N s b hh :=
  ⟨fun ⟨h₁, p, q⟩ => have q' := (isSymTranslate_iff L N b h₁ hh).1 q
    ⟨q'.1, h₁, (isEndPull_iff L φ _ _ hp hβ s h₁).1 p, q'.2⟩,
    fun h => isTranslatedPull_of_isTransPull L φ h.1 b h.2⟩

theorem typings_equiv (hA : IsAbelianScheme A) (φ : A ⟶ A) [IsMonHom φ] (T : Over X) :
    (∀ a b : ℤ, (∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]), β.IsGen) →
      ∀ (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)),
        IsEndPull L φ a b s s' ↔ IsNormPull A L φ a b s s') ∧
    (∀ (N : ℕ) (b : T ⟶ A) (s s' : LB.Sec (LPow A L.L (N : ℤ) T)),
      IsSymTranslate L N b s s' ↔ Odd N ∧ IsSymAct A L N b s s') ∧
    ∀ N : ℕ, (∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(N : ℤ), -1]), β.IsGen) →
      ∀ (b : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T)) (hh : LB.Sec (LPow A L.L (N : ℤ) T)),
        IsTranslatedPull L φ N b s hh ↔ Odd N ∧ IsTransPull A L φ N s b hh :=
  have hp := surj_fst SemiRigid.globalFns hA T
  ⟨fun a b => isEndPull_iff L φ a b hp, fun N b => isSymTranslate_iff L N b, fun N => isTranslatedPull_iff L φ N hp⟩

end Main

theorem isTranslatedPull_iff_univ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (α : 𝓞 E) (N : ℕ) (hN : Odd N) (hα : α * H.bar α = (N : 𝓞 E)) (T : Over Xo.X)
    (b : T ⟶ Xo.univ.t.G) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T))
    (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) T)) :
    haveI := Xo.univ.t.act.hom α
    IsTranslatedPull Xo.univ.t.PP (Xo.univ.t.act.act α) N b s hh ↔
      IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  letI := H.starRing
  have := Xo.univ.t.act.hom α
  have : IsMonHom (Xo.univ.t.act.toRingAct.act α) := this
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 α N hα (Xo.univ.t.adj α)
    Xo.univ.t.prim 1
  rw [Nat.one_mul] at h
  exact ((typings_equiv Xo.univ.t.PP (ObjDim.isAbelianScheme Xo.univ) _ T).2.2 N
    (h.gen Xo.univ.t.PP.isLB (K' := Fin 2) _ _ rfl) b s hh).trans (and_iff_right hN)

end GlobalTheory.TransPullCompare
