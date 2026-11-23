import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

namespace GlobalTheory.TorusTangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

section Val

variable {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}

theorem valR_spMap (ρ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR (spMap ρ ≫ x) U f = ρ (valR x U f) := by
  have hx' : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U := fun p _ => hx (x := spMap ρ p) trivial
  have h3 : (spMap ρ).appLE ⊤ ⊤ le_rfl = (spMap ρ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [valR, valR, dif_pos hx, dif_pos hx', ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x U ⊤ ⊤ hx le_rfl, h3]
  exact congrArg (fun q => q.hom ((x.appLE U ⊤ hx).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))

theorem isUnit_valR (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : IsUnit (valR x U f.val) := by
  rw [valR, dif_pos hx]
  exact (f.isUnit.map _).map _

theorem gm_spMap (ρ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp B) (f : Γ(X, U)ˣ) :
    (gm (spMap ρ ≫ x) z U f).val = toStkA z (ρ (valR x U f.val)) := by
  rw [← valR_spMap ρ x U hx]
  exact (toStkA_valR _ U z (fun p _ => hx (x := spMap ρ p) trivial) f).symm

theorem valR_id_top (c : Γ(Sp A, ⊤)) : valR (𝟙 (Sp A)) ⊤ c = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c := by
  have h : (𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  rw [valR, dif_pos (show ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ ⊤ from le_top)]
  show (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top).hom _) = _
  rw [h]; rfl

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem spMap_comp {C : Type} [CommRing C] (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem fst_inl : spMap (TrivSqZeroExt.fstHom A A A).toRingHom ≫ spMap (algebraMap A (DualNumber A)) = 𝟙 _ := by
  rw [spMap_comp]
  have : (TrivSqZeroExt.fstHom A A A).toRingHom.comp (algebraMap A (DualNumber A)) = RingHom.id A := by
    ext a; simp
  rw [this]; exact Spec.map_id _

def constU (ρ : A →+* B) (z : Sp B) : Subgroup ((Sp B).presheaf.stalk z)ˣ where
  carrier := {w | ∃ g : Aˣ, w.val = toStkA z (ρ g.val)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨g, hg⟩ ⟨g', hg'⟩
    exact ⟨g * g', by rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hg, hg']⟩
  inv_mem' := by
    rintro a ⟨g, hg⟩
    refine ⟨g⁻¹, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]

theorem gm_mem_constU [IsLocalRing B] (ρ : A →+* B) (σ : B →+* A) (hσ : spMap σ ≫ spMap ρ = 𝟙 _) {ψ : Sp B ⟶ X}
    {x : Sp A ⟶ X} (e : ψ = spMap ρ ≫ x) (U : X.Opens) (h : ψ (cpt B) ∈ U) (f : Γ(X, U)ˣ) :
    gm ψ (cpt B) U f ∈ constU ρ (cpt B) := by
  subst e
  have ht := (top_le_iff_cpt _ U).2 h
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have : (spMap σ ≫ spMap ρ ≫ x) p ∈ U := ht (x := spMap σ p) trivial
    rwa [← Category.assoc, hσ, Category.id_comp] at this
  exact ⟨(isUnit_valR x U hx f).unit, gm_spMap _ x U hx _ f⟩

theorem dlog_of_constU [IsLocalRing (DualNumber A)] {w : _}
    (hw : w ∈ constU (algebraMap A (DualNumber A)) (cpt (DualNumber A))) {u v : DualNumber A}
    (e : toStkA (cpt _) u = w.val * toStkA (cpt _) v) (a : A) : u.snd = u.fst * a ↔ v.snd = v.fst * a := by
  obtain ⟨g, hg⟩ := hw
  rw [hg, ← map_mul] at e
  obtain rfl := toStkA_injective e
  simp [TrivSqZeroExt.algebraMap_eq_inl, _root_.mul_assoc]

theorem gm_linCombIso {Y Z : Scheme.{0}} {L M : LB X} {K : Type} [Fintype K] (w : LB.Iso L M) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → M.ι) (q : K → L.ι) (h : r z ∈ LB.wchart M φ p ⊓ LB.wchart L φ q) :
    gm r z (LB.wchart M φ p ⊓ LB.wchart L φ q) ((LB.linCombIso w φ ε).s (p, q)) =
      ∏ k, gm (r ≫ φ k) z (M.U (p k) ⊓ L.U (q k)) (w.s (p k, q k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ h _).trans
    (gm_pull r (φ k) z (M.U (p k) ⊓ L.U (q k)) ⟨Set.mem_iInter.1 h.1 k, Set.mem_iInter.1 h.2 k⟩ _)

end Val

section Char

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R} {T : Over (Spec (CommRingCat.of R))}

def HasVal {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t r z J = gm r z ⊤ c

theorem formEq_zero (χ : D.X) :
    FormEq (K' := PEmpty) (Out.DegPre.gtφT D T (Out.DegPre.zeroT D T) χ) Out.DegPre.gtε PEmpty.elim PEmpty.elim := by
  intro U _ h
  rw [Fin.prod_univ_four]
  show h (Out.DegPre.cT D T χ * 1).left ^ (-1 : ℤ) * h (Out.DegPre.cT D T χ).left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp

theorem val_cubAtT {y : T.left} {J} (hJ : Good D.P.L y J) (x x' : T ⟶ D.P.A) :
    val (Out.DegPre.cubAtT D T x x' (Out.DegPre.zeroT D T)) (𝟙 _) y J = 1 := by
  have := val_cub D.cub (𝟙 T) hJ x x' 1
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at this
  exact this.trans ((isCub_cubV D.cub hJ).face₃ _ _)

theorem exists_hasVal (g : Out.GtPt D T) (hb : g.b = Out.DegPre.zeroT D T) (χ : D.X) : ∃ c, HasVal (g.s χ) c := by
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain rfl : b = _ := hb
  obtain ⟨t, -, ht⟩ := exists_gen D.P.isLB (formEq_zero χ) (s χ) (hs χ)
  have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => (ht Z r z J hJ).symm.trans ?_⟩
  exact (val_of t r z J PEmpty.elim (fun k => k.elim)).trans (gm_res r z le trivial _).symm

theorem exists_pt (c : D.X → Γ(T.left, ⊤)ˣ) (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') :
    ∃ g : Out.GtPt D T, g.b = Out.DegPre.zeroT D T ∧ ∀ χ, HasVal (g.s χ) (c χ) := by
  have c0 : c 0 = 1 := mul_eq_left.1 ((hc 0 0).symm.trans (by rw [add_zero]))
  have ex : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφT D T (Out.DegPre.zeroT D T) χ) Out.DegPre.gtε),
      t.IsGen ∧ HasVal t (c χ) := fun χ => by
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K := PEmpty) (φ := PEmpty.elim) (ε := PEmpty.elim)
      (fun U _ h => (formEq_zero χ U h).symm) ⟨fun j => res le_top (c χ)⟩ (isGen_of_gm _ fun y i j hi hj =>
        (gm_res _ y _ hi _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (gm_res _ y _ hj _)).trans
          (_root_.one_mul _))))
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (gm_res r z le_top (hJ.mem _ r) _)⟩
  choose s hs hv using ex
  refine ⟨⟨_, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, c0, map_one, val_one]
  · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (val_cubAtT hJ _ _)).trans ?_
    rw [hv _ _ _ y J hJ, hv _ _ _ y J hJ, hc, map_mul, _root_.mul_one]

theorem ext_of_hasVal {g g' : Out.GtPt D T} (hb : g.b = g'.b) (c : D.X → Γ(T.left, ⊤)ˣ) (h : ∀ χ, HasVal (g.s χ) (c χ))
    (h' : ∀ χ, HasVal (g'.s χ) (c χ)) : g = g' := by
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain ⟨b', s', hs', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => by
    have : (s χ).s = (s' χ).s := funext fun j => unit_ext fun y hy => by
      choose I hI using fun ψ : T.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ y)
      exact (gen_trans (hs χ) (𝟙 _) y hy (Good.mem hI _ _)).trans ((congrArg _ ((h χ _ _ y I hI).trans
        (h' χ _ _ y I hI).symm)).trans (gen_trans (hs' χ) (𝟙 _) y hy (Good.mem hI _ _)).symm)
    cases h₁ : s χ; cases h₂ : s' χ
    rw [h₁, h₂] at this
    congr
  rfl

theorem zeroT_left : (Out.DegPre.zeroT D T).left = T.hom ≫ eSec D.P.A := rfl

theorem gtφT_const (χ : D.X) (k : Fin 4) :
    ∃ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, Out.DegPre.gtφT D T (Out.DegPre.zeroT D T) χ k = T.hom ≫ x := by
  fin_cases k
  · refine ⟨(D.c χ).left, ?_⟩
    show (Out.DegPre.cT D T χ * 1).left = _
    rw [_root_.mul_one]; rfl
  · exact ⟨(D.c χ).left, rfl⟩
  · exact ⟨_, zeroT_left⟩
  · exact ⟨_, zeroT_left⟩

end Char

section Dual

variable {A : Type} [CommRing A] [IsDomain A] {D : Out.DegPre A}

def Dlog (ν : Out.GtPt D (epsR A)) (x : D.X) (a : A) : Prop :=
  ∀ j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR A) ν.b x) j →
    TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) =
      TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * a

variable [IsLocalRing (DualNumber A)]

theorem dlog_iff (ν : Out.GtPt D (epsR A)) (hb : ν.b = Out.DegPre.zeroT D (epsR A)) (x : D.X) {J}
    (hJ : Good D.P.L (Z := Sp (DualNumber A)) (cpt _) J) {u : DualNumber A}
    (e : (val (ν.s x) (𝟙 (Sp (DualNumber A))) (cpt _) J).val = toStkA (cpt _) u) (a : A) :
    Dlog ν x a ↔ u.snd = u.fst * a := by
  have key : ∀ j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR A) ν.b x) j →
      (TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) =
        TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * a ↔ u.snd = u.fst * a) := by
    intro j hj
    have m := hJ.mem (Out.DegPre.gtφT D (epsR A) ν.b x) (𝟙 (Sp (DualNumber A)))
    have t := gen_trans (ν.isGen x) (𝟙 (Sp (DualNumber A))) (cpt _) (hj trivial) m
    refine dlog_of_constU (w := trF (Out.DegPre.gtφT D (epsR A) ν.b x) Out.DegPre.gtε (𝟙 (Sp (DualNumber A))) (cpt _) j _)
      (Subgroup.prod_mem _ fun k _ => Subgroup.zpow_mem _ ?_ _)
      ((toStkA_valR (𝟙 (Sp (DualNumber A))) (LB.wchart D.P.L (Out.DegPre.gtφT D (epsR A) ν.b x) j) _ hj _).trans ((congrArg Units.val t).trans
        ((Units.val_mul _ _).trans (congrArg _ e)))) a
    obtain ⟨x₀, h₀⟩ := gtφT_const (D := D) (T := epsR A) x k
    exact gm_mem_constU _ _ fst_inl (x := x₀) ((Category.id_comp _).trans (by rw [hb]; exact h₀))
      (D.P.L.U (j k) ⊓ D.P.L.U (J (𝟙 (Sp (DualNumber A)) ≫ Out.DegPre.gtφT D (epsR A) ν.b x k)))
      ⟨Set.mem_iInter.1 (hj trivial) k, Set.mem_iInter.1 m k⟩ _
  refine ⟨fun h => ?_, fun h j hj => (key j hj).2 h⟩
  have m : ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR A) ν.b x) _ :=
    (top_le_iff_cpt (𝟙 (Sp (DualNumber A))) _).2 (hJ.mem (Out.DegPre.gtφT D (epsR A) ν.b x) (𝟙 (Sp (DualNumber A))))
  exact (key _ m).1 (h _ m)

omit [IsLocalRing (DualNumber A)] in
theorem exists_good' {Z : Scheme.{0}} (z : Z) : ∃ J, Good D.P.L z J := by
  choose I hI using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  exact ⟨I, hI⟩

theorem dlog_iff_hasVal (ν : Out.GtPt D (epsR A)) (hb : ν.b = Out.DegPre.zeroT D (epsR A)) (x : D.X)
    {c : Γ(Sp (DualNumber A), ⊤)ˣ} (hc : HasVal (ν.s x) c) (a : A) :
    Dlog ν x a ↔ (valR (𝟙 _) ⊤ c.val).snd = (valR (𝟙 _) ⊤ c.val).fst * a := by
  obtain ⟨J, hJ⟩ := exists_good' (D := D) (cpt (DualNumber A))
  exact dlog_iff ν hb x hJ ((congrArg Units.val (hc _ _ _ J hJ)).trans (toStkA_valR _ _ _ le_top _).symm) a

omit [IsLocalRing (DualNumber A)] in
theorem hasVal_spMap {ν : Out.GtPt D (epsR A)} {x : D.X} {c : Γ(Sp (DualNumber A), ⊤)ˣ} (hc : HasVal (ν.s x) c)
    {B : Type} [CommRing B] (ρ : DualNumber A →+* B) {z : Sp B} {J} (hJ : Good D.P.L z J) :
    (val (LB.pullGen D.P.L _ _ (ν.s x) (spMap ρ)) (𝟙 _) z J).val = toStkA z (ρ (valR (𝟙 _) ⊤ c.val)) := by
  rw [val_pull hJ, hc _ _ _ J hJ, Category.id_comp, ← gm_spMap ρ (𝟙 _) ⊤ le_top z c, Category.comp_id]

omit [IsLocalRing (DualNumber A)] in
theorem fst_of_tan [IsLocalRing A] {ν : Out.GtPt D (epsR A)} (h : GtTanR ν) {x : D.X} {c : Γ(Sp (DualNumber A), ⊤)ˣ}
    (hc : HasVal (ν.s x) c) : (valR (𝟙 _) ⊤ c.val).fst = 1 := by
  obtain ⟨g₀, h₀, h₁⟩ := h
  obtain ⟨J, hJ⟩ := exists_good' (D := D) (cpt A)
  have a := (val_corr hJ (h₁.2 x) (𝟙 _)).symm.trans ((val_corr hJ (h₀.2 x) (𝟙 _)).trans (val_one _))
  have b := hasVal_spMap hc (TrivSqZeroExt.fstHom A A A).toRingHom hJ
  exact toStkA_injective (b.symm.trans ((congrArg Units.val a).trans (map_one _).symm))

def oneAdd (a : A) : Γ(Sp (DualNumber A), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv.hom.toMonoidHom
    ⟨1 + TrivSqZeroExt.inr a, 1 - TrivSqZeroExt.inr a, by ext <;> simp, by ext <;> simp⟩

omit [IsDomain A] [IsLocalRing (DualNumber A)] in
theorem oneAdd_add (a b : A) : oneAdd (a + b) = oneAdd a * oneAdd b := by
  rw [oneAdd, oneAdd, oneAdd, ← map_mul]
  congr 1
  ext <;> simp [add_comm]

omit [IsDomain A] [IsLocalRing (DualNumber A)] in
theorem valR_oneAdd (a : A) : valR (𝟙 _) ⊤ (oneAdd a).val = 1 + TrivSqZeroExt.inr a :=
  (valR_id_top _).trans ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv_hom_id_apply _)

theorem existsUnique_tan [IsLocalRing A] (φ : D.X →+ A) : ∃! ν : Out.GtPt D (epsR A),
    GtTanR ν ∧ ν.b = Out.DegPre.zeroT D (epsR A) ∧ ∀ x, Dlog ν x (φ x) := by
  obtain ⟨ν, hb, hv⟩ := exists_pt (D := D) (T := epsR A) (fun x => oneAdd (φ x)) fun x y => by
    rw [map_add, oneAdd_add]
  refine ⟨ν, ⟨?_, hb, fun x => (dlog_iff_hasVal ν hb x (hv x) _).2 (by rw [valR_oneAdd]; simp)⟩, ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := exists_pt (D := D) (T := Over.mk (𝟙 (Sp A))) (fun _ => 1) fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, zeroT_left, zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (hasVal_spMap (hv x) (TrivSqZeroExt.fstHom A A A).toRingHom hJ).symm))
      rw [valR_oneAdd, map_one]
      simp
  · rintro ν' ⟨ht, hb', hd⟩
    refine ext_of_hasVal (hb'.trans hb.symm) _ (fun x => ?_) hv
    obtain ⟨c, hc⟩ := exists_hasVal ν' hb' x
    have h₁ := fst_of_tan ht hc
    have h₂ := (dlog_iff_hasVal ν' hb' x hc _).1 (hd x)
    have : c = oneAdd (φ x) := by
      apply Units.ext
      apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).commRingCatIsoToRingEquiv.injective
      refine (valR_id_top _).symm.trans (Eq.trans ?_ (valR_id_top _))
      rw [valR_oneAdd]
      rw [h₁] at h₂
      ext
      · rw [h₁]; simp
      · rw [h₂]; simp
    exact this ▸ hc

theorem dlog_smul (φ : D.X →+ A) (s : A) {ν ν' : Out.GtPt D (epsR A)} (hb : ν.b = Out.DegPre.zeroT D (epsR A))
    (hd : ∀ x, Dlog ν x (φ x)) (h : GtComb ![s] ![ν] ν') :
    ν'.b = Out.DegPre.zeroT D (epsR A) ∧ ∀ x, Dlog ν' x ((s • φ) x) := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have hu₀ : Out.GtPt.IsPull (spMap (epsScaleR s)) ν (u 0) := hu 0
  have ha₀ : Out.GtPt.IsAdd (p 0) (u 0) (p (Fin.last 1)) := ha 0
  have ub : (u 0).b = Out.DegPre.zeroT D (epsR A) := Over.OverMorphism.ext (by
    rw [hu₀.1, hb, zeroT_left, ← Category.assoc]
    refine congrArg (· ≫ eSec D.P.A) ((spMap_comp _ _).trans (congrArg spMap ?_))
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  have pb : (p (Fin.last 1)).b = Out.DegPre.zeroT D (epsR A) := by
    rw [ha₀.1, h₀.1, ub]
    exact _root_.mul_one (1 : epsR A ⟶ D.P.A)
  refine ⟨pb, fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_hasVal ν hb x
  obtain ⟨J, hJ⟩ := exists_good' (D := D) (cpt (DualNumber A))
  have e₁ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (ha₀.2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
  have e₂ : val (Out.DegPre.cubAtT D (epsR A) (Out.DegPre.cT D (epsR A) x) (p 0).b (u 0).b) (𝟙 (Sp (DualNumber A)))
      (cpt (DualNumber A)) J = 1 := by
    rw [ub]; exact val_cubAtT hJ _ _
  have e₃ := (val_corr hJ (h₀.2 x) (𝟙 _)).trans (val_one _)
  have e₄ := (congrArg Units.val (val_corr hJ (hu₀.2 x) (𝟙 _))).trans (hasVal_spMap hc (epsScaleR s) hJ)
  have e₅ := (_root_.mul_one _).symm.trans ((congrArg₂ (· * ·) rfl e₂).symm.trans (e₁.trans
    ((congrArg₂ (· * ·) e₃ rfl).trans (_root_.one_mul _))))
  refine (dlog_iff _ pb x hJ ((congrArg Units.val e₅).trans e₄) _).2 ?_
  have := (dlog_iff_hasVal ν hb x hc _).1 (hd x)
  simp [epsScaleR, this, mul_left_comm]

end Dual

section BaseChange

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {D : Out.DegPre A} {D₁ : Out.DegPre A'}
  {f : A →+* A'}

theorem b_zero_of_letBC (p : Out.IsPullDeg f D D₁) {ν : Out.GtPt D (epsR A)} {ν₁ : Out.GtPt D₁ (epsR A')}
    (hb : ν.b = Out.DegPre.zeroT D (epsR A)) (h : LetBC p ν ν₁) : ν₁.b = Out.DegPre.zeroT D₁ (epsR A') := by
  rw [← cancel_mono p.e.hom]
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h.1, hb, zeroT_left, zeroT_left, Category.assoc,
      p.he, ← Category.assoc, ← Category.assoc]
    refine congrArg (· ≫ eSec D.P.A) ((spMap_comp _ _).trans ((congrArg spMap ?_).trans (spMap_comp _ _).symm))
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (Over.w (ν₁.b ≫ p.e.hom)).trans (Over.w (Out.DegPre.zeroT D₁ (epsR A') ≫ p.e.hom)).symm

theorem dlog_of_letBC [IsLocalRing (DualNumber A)] [IsLocalRing (DualNumber A')] (p : Out.IsPullDeg f D D₁)
    {ν : Out.GtPt D (epsR A)} {ν₁ : Out.GtPt D₁ (epsR A')} (hb : ν.b = Out.DegPre.zeroT D (epsR A)) (h : LetBC p ν ν₁)
    (x : D₁.X) (a : A) (hd : Dlog ν (p.xe x) a) : Dlog ν₁ x (f a) := by
  intro j hj
  have hb₁ := b_zero_of_letBC p hb h
  obtain ⟨hψ, H⟩ := h.2 x
  choose i hi using fun k => exists_chart D.P.isLB
    (Out.DegPre.gtφT D (epsR A) ν.b (p.xe x) k (cpt (DualNumber A)))
  have m : ⊤ ≤ (𝟙 (Sp (DualNumber A))) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR A) ν.b (p.xe x)) i :=
    (top_le_iff_cpt (𝟙 (Sp (DualNumber A))) _).2 (Set.mem_iInter.2 hi)
  have mk : ∀ k, Out.DegPre.gtφT D₁ (epsR A') ν₁.b x k (cpt (DualNumber A')) ∈
      (D.P.L.pull (prj p)).U (fun _ => i k) := fun k => mem_pull.2 (by
    have : (spMap (dualMap f) ≫ Out.DegPre.gtφT D (epsR A) ν.b (p.xe x) k) (cpt (DualNumber A')) ∈ D.P.L.U (i k) :=
      Set.mem_iInter.1 (m (x := spMap (dualMap f) (cpt (DualNumber A'))) trivial) k
    rw [← hψ k] at this
    exact this)
  have mz : (𝟙 (Sp (DualNumber A')) : _ ⟶ _) (cpt (DualNumber A')) ∈
      LB.wchart (D.P.L.pull (prj p)) (Out.DegPre.gtφT D₁ (epsR A') ν₁.b x) (fun k _ => i k) ⊓
        LB.wchart D₁.P.L (Out.DegPre.gtφT D₁ (epsR A') ν₁.b x) j := ⟨Set.mem_iInter.2 mk, hj trivial⟩
  have e := congrArg (gm (𝟙 (Sp (DualNumber A'))) (cpt (DualNumber A')) _) (H (fun k _ => i k, j))
  have e₁ := ((gm_res _ _ _ mz _).trans ((gm_res _ _ _ mz.1 _).trans
    (gm_pull _ _ _ _ (m (x := spMap (dualMap f) (cpt (DualNumber A'))) trivial) _))).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linCombIso p.w _ _ _ _ _ _ mz) (gm_res _ _ _ mz _))))
  have e₂ := gm_spMap (dualMap f) (𝟙 _) _ m (cpt (DualNumber A')) ((ν.s (p.xe x)).s i)
  rw [Category.comp_id, ← Category.id_comp (spMap (dualMap f))] at e₂
  have e₃ := toStkA_valR (𝟙 (Sp (DualNumber A'))) (LB.wchart D₁.P.L (Out.DegPre.gtφT D₁ (epsR A') ν₁.b x) j)
    (cpt (DualNumber A')) hj ((ν₁.s x).s j)
  refine (dlog_of_constU ?_ (e₂.symm.trans ((congrArg Units.val e₁).trans ((Units.val_mul _ _).trans
    (congrArg _ e₃.symm)))) (f a)).1 ?_
  · refine Subgroup.prod_mem _ fun k _ => Subgroup.zpow_mem _ ?_ _
    have mk' : Out.DegPre.gtφT D₁ (epsR A') ν₁.b x k (cpt (DualNumber A')) ∈
      (D.P.L.pull (prj p)).U (fun _ => i k) ⊓ D₁.P.L.U (j k) := ⟨mk k, Set.mem_iInter.1 (hj trivial) k⟩
    obtain ⟨x₀, h₀⟩ := gtφT_const (D := D₁) (T := epsR A') x k
    exact gm_mem_constU _ _ fst_inl (x := x₀) ((Category.id_comp _).trans (by rw [hb₁]; exact h₀))
      ((D.P.L.pull (prj p)).U (fun _ => i k) ⊓ D₁.P.L.U (j k)) mk' _
  · have := congrArg f (hd i m)
    rw [map_mul] at this
    simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, zero_add, add_zero]
    exact this

end BaseChange

theorem main : Out.GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (D₀ : Out.DegPre A), (∀ φ : D₀.X →+ A, ∃! ν : Out.GtPt D₀ (epsR A), GtTanR ν ∧ ν.b = Out.DegPre.zeroT D₀ (epsR A) ∧ (∀ (x : D₀.X) j, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR A) ν.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * φ x)) ∧ (∀ (φ : D₀.X →+ A) (s : A) (ν ν' : Out.GtPt D₀ (epsR A)), GtTanR ν → ν.b = Out.DegPre.zeroT D₀ (epsR A) → (∀ (x : D₀.X) j, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR A) ν.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * φ x) → GtComb ![s] ![ν] ν' → ν'.b = Out.DegPre.zeroT D₀ (epsR A) ∧ (∀ (x : D₀.X) j, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR A) ν'.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν'.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν'.s x).s j).val) * (s • φ) x)) ∧ ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] (D₁ : Out.DegPre A') (f : A →+* A') (p : Out.IsPullDeg f D₀ D₁) (φ : D₀.X →+ A) (ν : Out.GtPt D₀ (epsR A)) (ν₁ : Out.GtPt D₁ (epsR A')), ν.b = Out.DegPre.zeroT D₀ (epsR A) → (∀ (x : D₀.X) j, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR A) ν.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A) (𝟙 _) _ ((ν.s x).s j).val) * φ x) → LetBC p ν ν₁ → ν₁.b = Out.DegPre.zeroT D₁ (epsR A') ∧ (∀ (x : D₁.X) j, ⊤ ≤ LB.wchart D₁.P.L (Out.DegPre.gtφT D₁ (epsR A') ν₁.b x) j → TrivSqZeroExt.snd (valR (A := DualNumber A') (𝟙 _) _ ((ν₁.s x).s j).val) = TrivSqZeroExt.fst (valR (A := DualNumber A') (𝟙 _) _ ((ν₁.s x).s j).val) * (fun x => f (φ (p.xe x))) x) := by
  intro _ A _ _ _ D₀
  have := isLocalRing_dual A
  refine ⟨fun φ => existsUnique_tan φ, fun φ s ν ν' _ hb hd h => dlog_smul φ s hb hd h, ?_⟩
  intro A' _ _ _ D₁ f p φ ν ν₁ hb hd h
  have := isLocalRing_dual A'
  exact ⟨b_zero_of_letBC p hb h, fun x => dlog_of_letBC p hb h x _ (hd _)⟩

end GlobalTheory.TorusTangent
