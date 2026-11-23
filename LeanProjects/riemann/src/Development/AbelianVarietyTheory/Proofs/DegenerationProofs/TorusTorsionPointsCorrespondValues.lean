import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.GtValues

section Pt
variable {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_pt (hM : M.IsLB) {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp F ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {y : Sp F} {J}
    (hJ : Good M y J) (e : val t (𝟙 _) y J = val t' (𝟙 _) y J) : LB.Gen.Corr M _ _ _ _ t t' :=
  corr_of_val hM fun y' I hI => by
    have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    obtain rfl := Subsingleton.elim y y'
    exact (gen_trans ht (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).trans ((congrArg₂ (· * ·)
      (hF.trF (𝟙 _) y (fun ψ => I (𝟙 _ ≫ ψ)) fun ψ => J (𝟙 _ ≫ ψ)) e).trans
      (gen_trans ht' (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).symm)

theorem toStk_surj (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

theorem exists_gen_val (hM : M.IsLB) (φ : K → (Sp F ⟶ X)) (ε : K → ℤ) {y : Sp F} {J} (hJ : Good M y J)
    (u : ((Sp F).presheaf.stalk y)ˣ) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) y J = u := by
  have all : ∀ w : Sp F, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_mem (𝟙 (Sp F)) _ y).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun j w hw => ⟨hw, all w⟩
  obtain ⟨f, hf⟩ := toStk_surj y u.val
  have f0 : f ≠ 0 := fun h => Units.ne_zero _ (hf.symm.trans (by rw [h, map_zero]))
  let c : Γ(Sp F, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 f f0)
  have hc : gm (𝟙 (Sp F)) y ⊤ c = u := Units.ext ((gm_val (𝟙 _) y ⊤ trivial c).trans hf)
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) * res le_top c⟩
  have v : ∀ (w : Sp F) j, w ∈ LB.wchart M φ j → gm (𝟙 (Sp F)) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * gm (𝟙 (Sp F)) w ⊤ c := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      (gm_res _ w le_top h c))
  refine ⟨t, isGen_of_gm _ fun w j j' h h' => ?_, (v y _ (all y)).trans ?_⟩
  · refine (v w j h).trans (Eq.trans ?_ (congrArg _ (v w j' h')).symm)
    rw [← trF_trans hM _ ε (𝟙 _) w h h' (all w), _root_.mul_assoc]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) y (all y) (all y) (all y)), _root_.one_mul, hc]

end Pt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
section OneGauge
variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J)
include hJ

theorem exists_gt_pt (b : TF (R := R) F ⟶ D.P.A) (v : D.X → ((TF (R := R) F).left.presheaf.stalk y)ˣ) (m₀ : v 0 = 1)
    (m : ∀ χ χ', v (χ + χ') * th D y J (cP D _ χ) (cP D _ χ') b = v χ * v χ') :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ, val (g.s χ) (𝟙 _) y J = v χ := by
  choose s hs hv using fun χ => exists_gen_val D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_pt D.P.isLB (fun U _ h => ?_) (hs 0) (fun i j => (map_one _).trans ((congrArg₂ (· * ·)
    (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ ((hv 0).trans (m₀.trans (val_one _).symm)),
    fun χ χ' => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAt hJ _ _ _))).trans ((m χ χ').trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl, hv⟩
  · rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_gt b _ h) (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem gt_ext {g g' : GtPtF D F} (hb : g.b = g'.b) (hv : ∀ χ, val (g.s χ) (𝟙 _) y J = val (g'.s χ) (𝟙 _) y J) :
    g = g' := by
  obtain ⟨b, s, hs, z, m⟩ := g
  obtain ⟨b', s', hs', z', m'⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => by
    have e : (s χ).s = (s' χ).s := funext fun j => unit_ext fun w hw => by
      have : Subsingleton (TF (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
      obtain rfl := Subsingleton.elim y w
      exact (gen_trans (hs χ) (𝟙 _) y hw (hJ.mem _ _)).trans ((congrArg _ (hv χ)).trans
        (gen_trans (hs' χ) (𝟙 _) y hw (hJ.mem _ _)).symm)
    exact congrArg LB.Gen.mk e
  rfl

theorem isZero_pt (g : GtPtF D F) : g.IsZero ↔ g.b = 1 ∧ ∀ χ, val (g.s χ) (𝟙 _) y J = 1 := by
  refine ⟨fun h => ⟨h.1, fun χ => ((isZero_iff g).1 h).2 χ y J hJ⟩, fun ⟨hb, hv⟩ => ⟨hb, fun χ =>
    corr_pt D.P.isLB (fun U _ h => ?_) (g.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
    ((hv χ).trans (val_one _).symm)⟩⟩
  show ∏ i, h (DegPre.gtφ D F g.b χ i) ^ DegPre.gtε i = _
  rw [prod_gt, hb, _root_.mul_one]; simp

theorem isAdd_pt (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ,
    val (g''.s χ) (𝟙 _) y J * th D y J (cP D _ χ) g.b g'.b = val (g.s χ) (𝟙 _) y J * val (g'.s χ) (𝟙 _) y J := by
  refine ⟨fun h => ⟨h.1, fun χ => ((isAdd_iff _ _ _).1 h).2 χ y J hJ⟩, fun ⟨e, hv⟩ => ⟨e, fun χ =>
    corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).trans ((hv χ).trans
        (val_mul hJ _ _ _).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_gt g''.b χ h)
    (prod_cub (cP D _ χ) g.b g'.b h)).trans (Eq.trans ?_
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt g.b χ h) (prod_gt g'.b χ h)).symm)
  rw [e, _root_.mul_assoc (cP D _ χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem isIota_pt (z : D.X) (g : GtPtF D F) : GtPtF.IsIota z g ↔ g.b = cP D _ z ∧ ∀ χ,
    val (g.s χ) (𝟙 _) y J = val (D.tau z χ) (𝟙 _ ≫ jFK (R := R) F) y J := by
  refine ⟨fun h => ⟨h.1, fun χ => ((isIota_iff _ _).1 h).2 χ y J hJ⟩, fun ⟨e, hv⟩ => ⟨e, fun χ =>
    corr_pt D.P.isLB (fun U _ h => ?_) (g.isGen χ) (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
        (invGen_isGen _ _ _ _ (D.psi_gen _))) (invGen_isGen _ _ _ _ (D.psi_gen _)))
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _))) _) hJ
      ((hv χ).trans (val_pull hJ _ _ _).symm)⟩⟩
  have a : ∀ x, jFK (R := R) F ≫ ptK (D.c x) = (cP D (TF (R := R) F) x).left := fun x => (Category.assoc _ _ _).symm
  have a₀ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
    (Category.assoc _ _ _).symm
  rw [prod_gt, e]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a, a₀, cPoint_add, neg_neg, zpow_neg,
    zpow_one, mul_comm (cP D _ z)]
  ac_rfl

end OneGauge

def toStkU (y : Sp F) : Fˣ →* ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom

theorem toStkU_bijective (y : Sp F) : Function.Bijective (toStkU y) := by
  refine ⟨fun a b h => Units.ext ((toStk y).injective (congrArg Units.val h)), fun u => ?_⟩
  obtain ⟨f, hf⟩ := toStk_surj y u.val
  exact ⟨Units.mk0 f fun h => u.ne_zero (hf.symm.trans (by rw [h, map_zero])), Units.ext hf⟩

theorem toStk_vF {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {y : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L y J) :
    toStk y (vF t r J) = (val t r y J).val := toStk_valF r _ y (hJ.mem φ r) _

theorem eq_vF_iff {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {y : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L y J) (u : Fˣ) :
    (u : F) = vF t r J ↔ toStkU y u = val t r y J := by
  rw [← (toStk y).injective.eq_iff, toStk_vF t r hJ, ← Units.val_inj]; rfl

variable {N : NumD F} (ν : NumOf D F N) (y : Sp F)

theorem good : Good D.P.L y ν.J := fun ψ => (top_le_iff_mem ψ _ y).1 (ν.good ψ)

theorem theta_eq (a b c : N.A) :
    toStkU y (N.θ a b c) = th D (T := TF (R := R) F) y ν.J (ν.eA a) (ν.eA b) (ν.eA c) :=
  (eq_vF_iff (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t _ (good ν y) _).1 (ν.θ_eq a b c)

theorem tau_eq (a b : N.X) :
    toStkU y (N.τ a b) = val (D.tau (ν.eX a) (ν.eX b)) (𝟙 _ ≫ jFK (R := R) F) y ν.J := by
  have hJ := good ν y
  have p : ∀ χ, toStkU y (N.ψ χ) = val (D.psi (ν.eX χ)) (jFK (R := R) F) y ν.J * val D.rigK (jFK (R := R) F) y ν.J :=
    fun χ => Units.ext (by
      refine (congrArg (toStk y) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (toStk_vF _ _ hJ)
        ((toStk_vF _ _ hJ).trans (congrArg Units.val ?_))))
      exact (val_pull (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) hJ D.rig (toUnit (TK R)).left
        (jFK (R := R) F)).symm)
  rw [Category.id_comp]
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))).symm
  rw [NumD.τ, map_div, map_div, p, p, p, map_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem pt_iff (g : GtPtF D F) (c : N.Gt) :
    ν.Pt g c ↔ ν.eA c.b = g.b ∧ ∀ χ, toStkU y (c.s χ) = val (g.s (ν.eX χ)) (𝟙 _) y ν.J :=
  and_congr Iff.rfl (forall_congr' fun _ => eq_vF_iff _ _ (good ν y) _)

theorem c_eq (χ : N.X) : ν.eA (N.c χ) = cP D _ (ν.eX χ) := ν.c_eq χ

omit y in

theorem exists_val (g : GtPtF D F) : ∃ c, ν.Pt g c := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  choose s hs using fun χ => (toStkU_bijective y).2 (val (g.s (ν.eX χ)) (𝟙 _) y ν.J)
  refine ⟨⟨ν.eA.symm g.b, s, fun χ χ' => (toStkU_bijective y).1 ?_⟩, (pt_iff ν y _ _).2 ⟨ν.eA.apply_symm_apply _, hs⟩⟩
  have e := gt_mul (𝟙 (TF (R := R) F)) (good ν y) g (ν.eX χ) (ν.eX χ')
  rw [Category.id_comp] at e
  rw [map_mul, map_mul, hs, hs, hs, theta_eq ν y, c_eq, c_eq, ν.eA.apply_symm_apply, map_add]
  exact e

omit y in

theorem val_unique {g : GtPtF D F} {c c' : N.Gt} (h : ν.Pt g c) (h' : ν.Pt g c') : c = c' :=
  NumD.Gt.ext (ν.eA.injective (h.1.trans h'.1.symm)) (funext fun χ => Units.ext ((h.2 χ).trans (h'.2 χ).symm))

omit y in

theorem exists_pt (c : N.Gt) : ∃ g, ν.Pt g c := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  obtain ⟨g, hb, hv⟩ := exists_gt_pt (D := D) (F := F) (good ν y) (ν.eA c.b) (fun χ => toStkU y (c.s (ν.eX.symm χ)))
    (by rw [map_zero, NumD.Gt.s_zero]; exact map_one _) (fun χ χ' => by
      have e := congrArg (toStkU y) (c.mult (ν.eX.symm χ) (ν.eX.symm χ'))
      rw [map_mul, map_mul, theta_eq ν y, c_eq, c_eq, ν.eX.apply_symm_apply, ν.eX.apply_symm_apply, ← map_add] at e
      exact e)
  exact ⟨g, (pt_iff ν y _ _).2 ⟨hb.symm, fun χ => ((hv _).trans (by rw [ν.eX.symm_apply_apply])).symm⟩⟩

omit y in

theorem pt_unique {g g' : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (h' : ν.Pt g' c) : g = g' := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
  obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
  refine gt_ext (good ν y) (a.symm.trans a') fun χ => ?_
  obtain ⟨χ, rfl⟩ := ν.eX.surjective χ
  exact (b χ).symm.trans (b' χ)

omit y in

theorem isZero_val {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) : g.IsZero ↔ c = 1 := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
  rw [isZero_pt (good ν y), NumD.Gt.ext_iff, funext_iff, ν.eX.surjective.forall]
  refine and_congr ?_ (forall_congr' fun χ => ?_)
  · rw [← a]; exact ν.eA.map_eq_one_iff
  · exact (Eq.congr (b χ).symm (map_one (toStkU y)).symm).trans (toStkU_bijective y).1.eq_iff

omit y in

theorem isAdd_val {g g' g'' : GtPtF D F} {c c' c'' : N.Gt} (h : ν.Pt g c) (h' : ν.Pt g' c') (h'' : ν.Pt g'' c'') :
    GtPtF.IsAdd g g' g'' ↔ c'' = c * c' := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
  obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
  obtain ⟨a'', b''⟩ := (pt_iff ν y _ _).1 h''
  rw [isAdd_pt (good ν y), NumD.Gt.ext_iff, funext_iff, ν.eX.surjective.forall]
  refine and_congr ?_ (forall_congr' fun χ => ?_)
  · rw [← a, ← a', ← a'', ← map_mul]; exact ν.eA.injective.eq_iff
  · have t := theta_eq ν y (N.c χ) c.b c'.b
    rw [c_eq, a, a'] at t
    rw [NumD.Gt.mul_s, eq_div_iff_mul_eq', ← (toStkU_bijective y).1.eq_iff, map_mul, map_mul, b, b', b'', t]

omit y in

theorem isIota_val {z : N.X} {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) : GtPtF.IsIota (ν.eX z) g ↔ c = N.io z := by
  let y : Sp F := (⊥ : PrimeSpectrum F)
  obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
  rw [isIota_pt (good ν y), NumD.Gt.ext_iff, funext_iff, ν.eX.surjective.forall]
  refine and_congr ?_ (forall_congr' fun χ => ?_)
  · rw [← a, ← c_eq]; exact ν.eA.injective.eq_iff
  · exact (Eq.congr (b χ).symm (tau_eq ν y z χ).symm).trans (toStkU_bijective y).1.eq_iff

omit y in

theorem isNsmul_val (k : ℕ) {g g' : GtPtF D F} {c c' : N.Gt} (h : ν.Pt g c) (h' : ν.Pt g' c') :
    GtPtF.IsNsmul k g g' ↔ c' = c ^ k := by
  constructor
  · rintro ⟨gs, g₀, st, rfl⟩
    choose cs hcs using fun i => exists_val ν (gs i)
    have : ∀ (i : ℕ) (hi : i < k + 1), cs ⟨i, hi⟩ = c ^ i := fun i hi => by
      induction i with
      | zero => exact ((isZero_val ν (hcs _)).1 g₀).trans (pow_zero c).symm
      | succ i ih =>
        exact ((isAdd_val ν (hcs _) h (hcs _)).1 (st ⟨i, by omega⟩)).trans (by rw [pow_succ, ← ih (by omega)]; rfl)
    exact (val_unique ν h' (hcs _)).trans (this k (Nat.lt_succ_self k))
  · rintro rfl
    choose gs hgs using fun i : ℕ => exists_pt ν (c ^ i)
    exact ⟨fun i => gs i, (isZero_val ν (hgs 0)).2 (pow_zero c),
      fun i => (isAdd_val ν (hgs i) h (hgs (i + 1))).2 (pow_succ c i), pt_unique ν (hgs k) h'⟩

theorem points_correspond : BrGtSt := by
  intro R _ _ D _ _ F _ _ _ N ν
  refine ⟨fun g => ?_, fun c => ?_, fun _ _ _ _ _ _ => isAdd_val ν, fun _ _ _ => isIota_val ν, fun k => ⟨fun p => ?_, fun q => ?_,
    fun p p' q q' h h' => ?_⟩⟩
  · obtain ⟨c, h⟩ := exists_val ν g
    exact ⟨c, h, fun _ h' => val_unique ν h' h⟩
  · obtain ⟨g, h⟩ := exists_pt ν c
    exact ⟨g, h, fun _ h' => pt_unique ν h' h⟩
  · obtain ⟨c, hc⟩ := exists_val ν p.g
    obtain ⟨g', hn, hi⟩ := p.eq
    obtain ⟨c', hc'⟩ := exists_val ν g'
    rw [← ν.eX.apply_symm_apply p.y] at hi
    refine ⟨⟨(Multiplicative.ofAdd (ν.eX.symm p.y), c),
      ((isNsmul_val ν k hc hc').1 hn).symm.trans ((isIota_val ν hc').1 hi)⟩, ⟨ν.eX.apply_symm_apply _, hc⟩, fun q hq => ?_⟩
    exact Subtype.ext (Prod.ext (ν.eX.eq_symm_apply.2 hq.1) (val_unique ν hq.2 hc))
  · obtain ⟨g, hg⟩ := exists_pt ν q.1.2
    obtain ⟨g', hg'⟩ := exists_pt ν (q.1.2 ^ k)
    exact ⟨⟨ν.eX q.1.1.toAdd, g, g', (isNsmul_val ν k hg hg').2 rfl, (isIota_val ν hg').2 q.2⟩, rfl, hg⟩
  · refine ν.eX.surjective.exists.trans (exists_congr fun z => and_congr ?_ ?_)
    · rw [← h.1, ← h'.1, ← map_nsmul, ← map_add]; exact ν.eX.injective.eq_iff
    · obtain ⟨g, hg⟩ := exists_pt ν (N.io z)
      refine ⟨fun ⟨g', hi, ha⟩ => ?_, fun e => ⟨g, (isIota_val ν hg).2 rfl, (isAdd_val ν h.2 hg h'.2).2 e⟩⟩
      obtain ⟨c', hc'⟩ := exists_val ν g'
      rw [← (isIota_val ν hc').1 hi]
      exact (isAdd_val ν h.2 hc' h'.2).1 ha

end GlobalTheory.Ex.GtValues
end
