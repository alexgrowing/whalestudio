import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFamRead

section
variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_eq_unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (W : (Spec (CommRingCat.of (FractionRing R))).Opens) (hW : W = ⊤)
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), W)ˣ) :
    gm r z W a = GlobalTheory.ThFam.unitAt r z (Units.map (DVR.GC.evalTop W hW).toMonoidHom a) := by
  subst hW
  apply Units.ext
  rw [gm_val r z ⊤ trivial]
  have e : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  simp only [GlobalTheory.ThFam.unitAt, DVR.GC.evalTop, Units.coe_map, RingHom.comp_apply, e,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Iso.hom_inv_id_apply]
  rfl

theorem gm_jK_eq_unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (b : Γ(Spec (CommRingCat.of R), W)ˣ) :
    gm (r ≫ jK R) z W b = GlobalTheory.ThFam.unitAt r z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom (Units.map (DVR.GC.evalTop W hW).toMonoidHom b)) := by
  have hW' : jK R ⁻¹ᵁ W = ⊤ := by subst hW; rfl
  rw [← gm_pull r (jK R) z W (by rw [hW]; trivial) b, gm_eq_unitAt r z _ hW']
  congr 1
  apply Units.ext
  exact DVR.GC.evalTop_specMap (algebraMap R (FractionRing R)) W hW hW' b.val

theorem commGroup_mul_eq_mul_mul_div {G : Type} [CommGroup G] (T A B : G) : T * A = A * B⁻¹ * (T * B) := by
  rw [_root_.mul_comm T B, ← _root_.mul_assoc, inv_mul_cancel_right, _root_.mul_comm]

variable [IsLocalRing R] (D : DegPre R)

def ch (χ : D.X) : PUnit → D.P.L.ι :=
  (DVR.exists_chart_top D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose

theorem ch_top (χ : D.X) : LB.wchart D.P.L (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (ch D χ) = ⊤ :=
  (DVR.exists_chart_top D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose_spec

def gen (χ : D.X) : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (fun _ => -1)) :=
  (DVR.exists_gen_of_local D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose

theorem gen_isGen (χ : D.X) : (gen D χ).IsGen :=
  (DVR.exists_gen_of_local D.P.L D.P.isLB (fun _ : PUnit => GlobalTheory.ThFam.ptR D χ) (fun _ => (-1 : ℤ))).choose_spec

theorem xK_eq (χ : D.X) : D.xK χ = jK R ≫ GlobalTheory.ThFam.ptR D χ := by
  simp [ptK, GlobalTheory.ThFam.ptR]

theorem chK_top (χ : D.X) : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (ch D χ) = ⊤ := by
  refine eq_top_iff.2 fun y _ => Set.mem_iInter.2 fun k => ?_
  have h1 := (ch_top D χ).ge (show jK R y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  have h2 := Set.mem_iInter.1 h1 k
  rw [← DegPre.xK, xK_eq]
  exact h2

def kap (χ : D.X) : (FractionRing R)ˣ :=
  Units.map (DVR.GC.evalTop _ (chK_top D χ)).toMonoidHom ((D.psi χ).s (ch D χ)) *
    (Units.map (algebraMap R (FractionRing R)).toMonoidHom
      (Units.map (DVR.GC.evalTop _ (ch_top D χ)).toMonoidHom ((gen D χ).s (ch D χ))))⁻¹

theorem reads' (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val (D.psi χ) r z J = GlobalTheory.ThFam.unitAt r z (kap D χ) * val (gen D χ) (r ≫ jK R) z J := by
  have hx : r ≫ D.xK χ = (r ≫ jK R) ≫ GlobalTheory.ThFam.ptR D χ := by rw [xK_eq, Category.assoc]
  have m1 := hJ.mem (K := PUnit) (fun _ => D.xK χ) r
  have m0 : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (ch D χ) := by rw [chK_top]; trivial
  have t1 := gen_trans (D.psi_gen χ) r z m1 m0
  have m1' := hJ.mem (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (r ≫ jK R)
  have m0' : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (ch D χ) := by
    rw [ch_top]; trivial
  have t2 := gen_trans (gen_isGen D χ) (r ≫ jK R) z m1' m0'
  have htr : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) (ch D χ) =
      trF (L := D.P.L) (K := PUnit) (fun _ => GlobalTheory.ThFam.ptR D χ) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ GlobalTheory.ThFam.ptR D χ)) (ch D χ) := by
    simp only [trF]
    rw [hx]
  show gm r z _ _ = _ * gm (r ≫ jK R) z _ _
  rw [t1, t2, htr]
  erw [gm_eq_unitAt r z _ (chK_top D χ), gm_jK_eq_unitAt r z _ (ch_top D χ)]
  rw [kap, map_mul, map_inv]
  exact commGroup_mul_eq_mul_mul_div _ _ _

theorem reads : GlobalTheory.ThFam.Reads D (kap D) := ⟨gen D, gen_isGen D, reads' D⟩

end

end GlobalTheory.ThFamRead

namespace GlobalTheory.ThFamRead

section
variable {R : Type} [CommRing R] [IsDomain R]

theorem unitAt_inj (z : (TK R).left) :
    Function.Injective (GlobalTheory.ThFam.unitAt (R := R) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z) := fun a b h =>
  Units.ext (RingHom.injective _ (congrArg Units.val h))

theorem toGen_unit (z : (TK R).left) (u : Rˣ) :
    Units.map (GlobalTheory.BetaAdd.toGen z).toMonoidHom u = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  have h := gm_jK_eq_unitAt (R := R) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z ⊤ rfl
    (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)
  have e1 : Units.map (DVR.GC.evalTop (⊤ : (Spec (CommRingCat.of R)).Opens) rfl).toMonoidHom
      (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u) = u := by
    apply Units.ext
    have e : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, DVR.GC.evalTop, GlobalTheory.BetaAdd.toOpen_top,
      RingHom.comp_apply, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply, Iso.inv_hom_id_apply]
  rw [e1, Category.id_comp] at h
  rw [← h]
  apply Units.ext
  show GlobalTheory.BetaAdd.toGen z u = _
  rw [GlobalTheory.BetaAdd.toGen_eq]
  exact gs_unit (jK R) z ⊤ trivial (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)

theorem mem_intU {z : (TK R).left} {x : ((TK R).left.presheaf.stalk z)ˣ} (hx : x ∈ GlobalTheory.BetaAdd.intU z) :
    ∃ u : Rˣ, x = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨u, toGen_unit z u⟩

variable [IsLocalRing R] (D : DegPre R)

theorem ptR_eq (χ : D.X) : GlobalTheory.ThFam.ptR D χ = (D.c χ).left := by
  simp [GlobalTheory.ThFam.ptR]

theorem psi_val {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (hI : ∀ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ D.P.L.U (J (jK R ≫ x)))
    (χ : D.X) : ∃ u : Rˣ, val (D.psi χ) (𝟙 _) z J = GlobalTheory.ThFam.unitAt (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z
      (kap D χ * Units.map (algebraMap R (FractionRing R)).toMonoidHom u) := by
  have h1 := reads' D χ (TK R).left (𝟙 (TK R).left) z J hJ
  have hm := GlobalTheory.BetaAdd.val_mem (z := z) hI (gen D χ) (𝟙 _) (fun _ => by rw [Category.id_comp]; exact Over.w _)
    ((𝟙 (TK R).left) ≫ jK R) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨u, hu⟩ := mem_intU hm
  exact ⟨u, h1.trans (by rw [hu, map_mul]; rfl)⟩

theorem ne0 (u : Rˣ) : algebraMap R (FractionRing R) (u : R) ≠ 0 :=
  (u.isUnit.map (algebraMap R (FractionRing R))).ne_zero

theorem even (hE : D.PsiEven) (χ : D.X) : ∃ u : Rˣ, ((kap D (-χ) : (FractionRing R)ˣ) : FractionRing R) =
    (kap D χ : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := ⟨IsLocalRing.closedPoint (FractionRing R)⟩
  obtain ⟨J, hJ, hI⟩ := GlobalTheory.BetaAdd.exists_good_int D z
  have e := (val_mul hJ _ _ (𝟙 _)).symm.trans (val_corr hJ (hE χ) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨u1, h1⟩ := psi_val D hJ hI (-χ)
  obtain ⟨u2, h2⟩ := psi_val D hJ hI χ
  obtain ⟨u3, h3⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem hI D.sym (GlobalTheory.ThFam.ptR D χ)
    (fun k => by fin_cases k <;> simp [Over.w]) (𝟙 (TK R).left ≫ D.xK χ) (by rw [Category.id_comp, xK_eq]))
  rw [h1, h2, h3, ← map_mul] at e
  have e' := congrArg Units.val (unitAt_inj z e)
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at e'
  refine ⟨u2 * u1⁻¹ * u3⁻¹, ?_⟩
  simp only [Units.val_mul, map_mul, map_units_inv]
  have n1 := ne0 u1
  have n3 := ne0 u3
  field_simp
  linear_combination e'

theorem tau_val {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (x y : D.X) :
    val (D.tau x y) (𝟙 _) z J = val (D.psi (x + y)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
      (val (D.psi y) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem cube (hB : D.TauBimult) (a a' b : D.X) : ∃ u : Rˣ,
    ((kap D (a + a' + b) * kap D a * kap D a' * kap D b : (FractionRing R)ˣ) : FractionRing R) =
      ((kap D (a + a') * kap D (a + b) * kap D (a' + b) : (FractionRing R)ˣ) : FractionRing R) *
        algebraMap R (FractionRing R) (u : R) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := ⟨IsLocalRing.closedPoint (FractionRing R)⟩
  obtain ⟨J, hJ, hI⟩ := GlobalTheory.BetaAdd.exists_good_int D z
  have e := (val_mul hJ _ _ (𝟙 _)).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [tau_val D hJ, tau_val D hJ, tau_val D hJ] at e
  have hc := val_pull hJ D.cub.t (D.pt3 a a' b) (𝟙 (TK R).left)
  erw [hc] at e
  have hr : val D.rigK (𝟙 (TK R).left) z J = val D.rig (𝟙 (TK R).left ≫ (toUnit (TK R)).left) z J := val_pull hJ _ _ _
  obtain ⟨ur, hur⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem (z := z) hI D.rig (𝟙 _)
    (fun _ => by rw [Category.id_comp]; exact Over.w _) (𝟙 (TK R).left ≫ (toUnit (TK R)).left)
    (by rw [Category.id_comp, Category.comp_id]; simpa using Over.w (toUnit (TK R))))
  obtain ⟨uc, huc⟩ := mem_intU (GlobalTheory.BetaAdd.val_mem (z := z) hI D.cub.t
    (lift (D.c a) (lift (D.c a') (D.c b))).left
    (fun k => (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w _))) (𝟙 (TK R).left ≫ D.pt3 a a' b)
    (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]))
  obtain ⟨u1, h1⟩ := psi_val D hJ hI (a + a' + b)
  obtain ⟨u2, h2⟩ := psi_val D hJ hI (a + a')
  obtain ⟨u3, h3⟩ := psi_val D hJ hI b
  obtain ⟨u4, h4⟩ := psi_val D hJ hI (a + b)
  obtain ⟨u5, h5⟩ := psi_val D hJ hI a
  obtain ⟨u6, h6⟩ := psi_val D hJ hI (a' + b)
  obtain ⟨u7, h7⟩ := psi_val D hJ hI a'
  rw [hr, hur, huc, h1, h2, h3, h4, h5, h6, h7] at e
  simp only [← map_inv, ← map_mul] at e
  have e' := congrArg Units.val (unitAt_inj z e)
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, map_units_inv] at e'
  clear h1 h2 h3 h4 h5 h6 h7 hr hur huc hc e hI hJ
  refine ⟨u2 * u4 * u6 * (u1 * u5 * u7 * u3 * ur * uc)⁻¹, ?_⟩
  simp only [Units.val_mul, map_mul, map_units_inv]
  have := ne0 u1; have := ne0 u2; have := ne0 u3; have := ne0 u4; have := ne0 u5; have := ne0 u6; have := ne0 u7
  have := ne0 ur; have := ne0 uc
  have := (kap D (a + a' + b)).ne_zero; have := (kap D (a + a')).ne_zero; have := (kap D b).ne_zero
  have := (kap D (a + b)).ne_zero; have := (kap D a).ne_zero; have := (kap D (a' + b)).ne_zero
  have := (kap D a').ne_zero
  field_simp at e' ⊢
  linear_combination e'

theorem psiIn_mem (I : Ideal R) (χ : D.X) (h : D.PsiIn χ I) :
    ∃ s ∈ I, ((kap D χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := by
  have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (ch D χ PUnit.unit) := by
    intro y _
    have h1 := Set.mem_iInter.1
      ((ch_top D χ).ge (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) PUnit.unit
    rw [ptR_eq] at h1
    exact h1
  have hh : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (ch D χ) :=
    fun y _ => (chK_top D χ).ge trivial
  obtain ⟨r, hr, e⟩ := h (ch D χ) ⊤ (isAffineOpen_top _) hle hh
  obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ GlobalTheory.BetaAdd.toOpen_bij.2).1 hr
  have key : DVR.GC.evalTop _ (chK_top D χ) ((D.psi χ).s (ch D χ)).val = algebraMap R (FractionRing R) s := by
    have e0 : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    calc DVR.GC.evalTop _ (chK_top D χ) ((D.psi χ).s (ch D χ)).val
        = DVR.GC.evalTop (jK R ⁻¹ᵁ ⊤) rfl
            (((Spec (CommRingCat.of (FractionRing R))).presheaf.map (homOfLE hh).op).hom ((D.psi χ).s (ch D χ)).val) :=
          (DVR.GC.evalTop_res hh (chK_top D χ) rfl _).symm
      _ = DVR.GC.evalTop (jK R ⁻¹ᵁ ⊤) rfl (((jK R).app ⊤).hom (DegPre.toOpen ⊤ s)) := congrArg _ e.symm
      _ = algebraMap R (FractionRing R) (DVR.GC.evalTop ⊤ rfl (DegPre.toOpen ⊤ s)) :=
          DVR.GC.evalTop_specMap (algebraMap R (FractionRing R)) ⊤ rfl rfl _
      _ = algebraMap R (FractionRing R) s := by
          congr 1
          simp only [DVR.GC.evalTop, GlobalTheory.BetaAdd.toOpen_top, RingHom.comp_apply, e0, CategoryTheory.Functor.map_id,
            CommRingCat.hom_id, RingHom.id_apply, Iso.inv_hom_id_apply]
  refine ⟨s * ((Units.map (DVR.GC.evalTop _ (ch_top D χ)).toMonoidHom ((gen D χ).s (ch D χ)))⁻¹ : Rˣ),
    I.mul_mem_right _ hs, ?_⟩
  simp only [kap, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_units_inv,
    Units.val_inv_eq_inv_val, key]
  exact congrArg (· * _) key

end

theorem exists_reading : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  intro R _ _ _ _ D
  refine ⟨kap D.toPre, reads D.toPre, even D.toPre D.psi_even, cube D.toPre D.tau_bimult,
    fun a ha => psiIn_mem D.toPre _ a (D.psi_pos a ha), fun n => (D.psi_tendsto n).subset ?_⟩
  intro χ hχ h
  exact hχ (psiIn_mem D.toPre _ χ h)

end GlobalTheory.ThFamRead
