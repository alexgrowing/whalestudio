import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SepPoints

section Fibres

variable {X Y : Scheme.{0}}

def MeetsFibres (f : X ⟶ Y) (D : X.Opens) : Prop := ∀ p : Y, ∃ x ∈ D, f x = p

theorem isIrreducible_fibre (f : X ⟶ Y) [GeometricallyIrreducible f] (p : Y) :
    IsIrreducible (f ⁻¹' {p}) := by
  rw [← f.range_fiberι, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι p).continuous.continuousOn

theorem MeetsFibres.inf {f : X ⟶ Y} [GeometricallyIrreducible f] {D D' : X.Opens}
    (h : MeetsFibres f D) (h' : MeetsFibres f D') : MeetsFibres f (D ⊓ D') := by
  intro p
  obtain ⟨x, hx, e⟩ := h p
  obtain ⟨x', hx', e'⟩ := h' p
  obtain ⟨y, hy, h₁, h₂⟩ := (isIrreducible_fibre f p).2 D D' D.2 D'.2 ⟨x, e, hx⟩ ⟨x', e', hx'⟩
  exact ⟨y, ⟨h₁, h₂⟩, hy⟩

theorem isLeftRegular_germ {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [GeometricallyIntegral f] {D : X.Opens}
    (hD : MeetsFibres f D) (V : X.Opens) (a : Γ(X, V)) (ha : D ⊓ V ≤ X.basicOpen a) (x : X)
    (hx : x ∈ V) : IsLeftRegular (gs (𝟙 X) x V a) := by
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V) (x := x) hx
  have hUV : U ≤ V := hUV
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  let _ : Algebra R Γ(X, U) := φ.hom.toAlgebra
  have hflat : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have : Module.Flat R Γ(X, U) := (HasRingHomProperty.Spec_iff (P := @Flat)).1 hflat
  have hf : ∀ p, IsIntegral (f.fiber p) := fun p => inferInstance
  let a' : Γ(X, U) := (X.presheaf.map (homOfLE hUV).op).hom a
  have reg : IsRegular a' := by
    refine isRegular_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun b hb => ?_)
    refine eq_zero_of_flat_of_forall_fiber (A := R) (B := Γ(X, U)) (L := Γ(X, U))
      (fun p _ => haveI := hf p; ThickeningClosed.noZeroDivisors_fiber f hU.fromSpec hφ p) fun q _ => ?_
    obtain ⟨z, hz, hzp⟩ := hD (f (hU.fromSpec q))
    obtain ⟨y, hy, hyU, hyD⟩ := (isIrreducible_fibre f (f (hU.fromSpec q))).2 U D U.2 D.2
      ⟨hU.fromSpec q, rfl, (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨q, rfl⟩⟩ ⟨z, hzp, hz⟩
    have hya : y ∈ X.basicOpen a' := by
      rw [Scheme.basicOpen_res]
      exact ⟨hyU, ha ⟨hyD, hUV hyU⟩⟩
    obtain ⟨q', rfl⟩ := (Set.ext_iff.1 hU.range_fromSpec y).2 hyU
    have hq' : a' ∉ q'.asIdeal := (SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen a') q').1 hya
    refine ⟨q', ?_, (@localizedModule_mk_one_eq_zero_iff _ _ _ _ _ _ q'.2 _).2 ⟨a', hq', hb⟩⟩
    have h1 : (hU.fromSpec ≫ f) q' = (hU.fromSpec ≫ f) q := hy
    rw [← hφ] at h1
    exact congrArg PrimeSpectrum.asIdeal h1
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
    IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h := Module.Flat.isSMulRegular_of_isRegular (M := X.presheaf.stalk x) reg
  rw [← gs_res (𝟙 X) x hUV hxU, gs_eq _ x U hxU]
  exact h

theorem exists_quotient (W : X.Opens) (f g : Γ(X, W))
    (hg : ∀ x ∈ W, IsLeftRegular (gs (𝟙 X) x W g))
    (h : ∀ x ∈ W, gs (𝟙 X) x W g ∣ gs (𝟙 X) x W f) :
    ∃ q : Γ(X, W), ∀ x ∈ W, gs (𝟙 X) x W f = gs (𝟙 X) x W g * gs (𝟙 X) x W q := by
  have loc : ∀ x : W, ∃ (U : X.Opens) (_ : U ≤ W) (_ : x.1 ∈ U) (q : Γ(X, U)),
      ∀ y ∈ U, gs (𝟙 X) y W f = gs (𝟙 X) y W g * gs (𝟙 X) y U q := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := h x hx
    obtain ⟨U, hU, q, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
    have e : gs (𝟙 X) x (W ⊓ U) ((X.presheaf.map (homOfLE inf_le_left).op).hom f) =
        gs (𝟙 X) x (W ⊓ U) ((X.presheaf.map (homOfLE inf_le_left).op).hom g *
          (X.presheaf.map (homOfLE inf_le_right).op).hom q) := by
      rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_res _ x _ hm, ht, gs_eq _ x U hU]
      rfl
    rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
    obtain ⟨U', hU', i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : U' ≤ W ⊓ U := i₁.le
    refine ⟨U', le.trans inf_le_left, hU',
      (X.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom q, fun y hy => ?_⟩
    have e'' := congrArg (gs (𝟙 X) y U') e'
    have k := (gs_res (𝟙 X) y le hy _).symm.trans (e''.trans (gs_res (𝟙 X) y le hy _))
    have hy' : (𝟙 X : X ⟶ X) y ∈ W ⊓ U := le hy
    have k' : gs (𝟙 X) y (W ⊓ U) ((X.presheaf.map (homOfLE inf_le_left).op).hom f) =
        gs (𝟙 X) y (W ⊓ U) ((X.presheaf.map (homOfLE inf_le_left).op).hom g *
          (X.presheaf.map (homOfLE inf_le_right).op).hom q) := k
    rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at k'
    rw [k', gs_res _ y _ hy]
  choose U hU hx q hq using loc
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U W (fun i => homOfLE (hU i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) q (fun i j => fn_ext (V := U i ⊓ U j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((hg y (hU i hy.1)
        ((hq i y hy.1).symm.trans (hq j y hy.2))).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun y hy => (hq ⟨y, hy⟩ y (hx _)).trans (congrArg _ ?_)⟩
  exact (congrArg (gs (𝟙 X) y _) (hs ⟨y, hy⟩)).symm.trans (gs_res (𝟙 X) y (hU ⟨y, hy⟩) (hx _) s)

theorem exists_gen_of_associated {L : LB X} (hL : L.IsLB) (φ : Fin 2 → (Y ⟶ X))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => φ 0) (fun _ => 1)))
    (s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => φ 1) (fun _ => 1)))
    (hreg : ∀ y J, Good L y J → IsLeftRegular (sval s' (𝟙 Y) y J))
    (hdvd : ∀ y J, Good L y J →
      sval s (𝟙 Y) y J ∣ sval s' (𝟙 Y) y J ∧ sval s' (𝟙 Y) y J ∣ sval s (𝟙 Y) y J) :
    ∃ t : LB.Gen (LB.LinComb L φ ![1, -1]), t.IsGen := by
  have hass : ∀ y J, Good L y J → Associated (sval s (𝟙 Y) y J) (sval s' (𝟙 Y) y J) := by
    intro y J hJ
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := hdvd y J hJ
    have e : w * u = 1 := hreg y J hJ (by
      show _ * _ = _ * _
      rw [← _root_.mul_assoc, ← hw, ← hu, _root_.mul_one])
    exact ⟨⟨u, w, (mul_comm _ _).trans e, e⟩, hu.symm⟩
  have l₀ : ∀ j : Fin 2 → L.ι, LB.wchart L φ j ≤ LB.wchart L (fun _ : Fin 1 => φ 0) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L φ j ≤ LB.wchart L (fun _ : Fin 1 => φ 1) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have loc : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L φ j →
      IsLeftRegular (gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => φ 1) (fun _ => j 1)) (s'.f fun _ => j 1)) ∧
      Associated (gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => φ 1) (fun _ => j 1)) (s'.f fun _ => j 1))
        (gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => φ 0) (fun _ => j 0)) (s.f fun _ => j 0)) := by
    intro j y hy
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have e₀ := sec_trans s (𝟙 Y) y (l₀ j hy) (Good.mem hI _ (𝟙 Y))
    have e₁ := sec_trans s' (𝟙 Y) y (l₁ j hy) (Good.mem hI _ (𝟙 Y))
    rw [e₀, e₁]
    exact ⟨(Units.isRegular _).left.mul (hreg y I hI), (associated_unit_mul_left _ _ (Units.isUnit _)).trans
      ((hass y I hI).symm.trans (associated_unit_mul_left _ _ (Units.isUnit _)).symm)⟩
  choose q hq using fun j : Fin 2 → L.ι => exists_quotient (LB.wchart L φ j)
    ((Y.presheaf.map (homOfLE (l₀ j)).op).hom (s.f fun _ => j 0))
    ((Y.presheaf.map (homOfLE (l₁ j)).op).hom (s'.f fun _ => j 1))
    (fun y hy => (congrArg IsLeftRegular (gs_res (𝟙 Y) y (l₁ j) hy _)).mpr (loc j y hy).1)
    (fun y hy => (congrArg₂ (· ∣ ·) (gs_res (𝟙 Y) y (l₁ j) hy _)
      (gs_res (𝟙 Y) y (l₀ j) hy _)).mpr (loc j y hy).2.dvd)
  have hq' : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L φ j →
      gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => φ 0) (fun _ => j 0)) (s.f fun _ => j 0) =
      gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => φ 1) (fun _ => j 1)) (s'.f fun _ => j 1) *
        gs (𝟙 Y) y (LB.wchart L φ j) (q j) := fun j y hy =>
    (gs_res (𝟙 Y) y (l₀ j) hy _).symm.trans ((hq j y hy).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 Y) y (l₁ j) hy _) rfl))
  have hu : ∀ j, IsUnit (q j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨u, hu⟩ := (loc j y hy).2
    have e := (loc j y hy).1 ((hq' j y hy).symm.trans hu.symm)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (fn_ext fun y hy => ?_)⟩
  refine (gs_res (𝟙 Y) y inf_le_left hy (q i)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y i j hy.1 hy.2)))
      (gs_res (𝟙 Y) y inf_le_right hy (q j)))).symm)
  apply (loc i y hy.1).1
  have e₀ := sec_trans s (𝟙 Y) y (l₀ i hy.1) (l₀ j hy.2)
  have e₁ := sec_trans s' (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  refine ((hq' i y hy.1).symm.trans (e₀.trans (congrArg _ (hq' j y hy.2)))).trans
    (Eq.trans ?_ (congrArg₂ (· * ·) e₁.symm rfl))
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    zpow_one, zpow_neg, Units.val_mul]
  have alg : ∀ {R : Type} [CommRing R] (u w : Rˣ) (a b : R),
      u.val * (a * b) = w.val * a * (u.val * (w⁻¹).val * b) := fun u w a b => by
    linear_combination (-(u.val * a * b)) * w.mul_inv
  exact alg _ _ _ _

end Fibres

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem exists_gen_cube_pow (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S}
    (a b z : T ⟶ G) (k : ℕ) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 8) ![(a * b ^ k * z).left, (a * b ^ k).left, (a * z).left,
        a.left, (b * z).left, b.left, z.left, (1 : T ⟶ G).left] ![1, -1, -1, 1, -k, k, k, -k]),
      u.IsGen := by
  induction k with
  | zero =>
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a * b ^ 0 * z).left, (a * b ^ 0).left, (a * z).left,
        a.left, (b * z).left, b.left, z.left, (1 : T ⟶ G).left])
      (ε' := ![1, -1, -1, 1, -(0 : ℕ), (0 : ℕ), (0 : ℕ), -(0 : ℕ)])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen L (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm)
    exact ⟨u, hu⟩
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨u', hu', -⟩ := exists_gen hL (φ' := ![(a * b ^ (k + 1) * z).left, (a * b ^ (k + 1)).left,
        (a * z).left, a.left, (b * z).left, b.left, z.left, (1 : T ⟶ G).left])
      (ε' := ![1, -1, -1, 1, -(k + 1 : ℕ), (k + 1 : ℕ), (k + 1 : ℕ), -(k + 1 : ℕ)]) (fun U _ h => by
        refine ((Fintype.prod_sum_type _).trans
          (congrArg₂ (· * ·) rfl (prod_cub (a * b ^ k) b z h))).trans ?_
        rw [pow_succ b, ← _root_.mul_assoc a]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
        module)
      (LB.mulGen L _ _ _ _ u (LB.pullGen L (thφ G (x3 G)) thε t (lift (a * b ^ k) (lift b z)).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ ht _))
    exact ⟨u', hu'⟩

theorem exists_gen_three (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S}
    (a b c z : T ⟶ G) (m : ℕ) (hc : a * b ^ m * c = 1) (i : Fin 4 → L.ι)
    (hi : ∀ k (y : T.left),
      (![a.left, b.left, c.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 4)
      ![z.left, (a * z).left, (b * z).left, (c * z).left] ![m + 2, -1, -m, -1]),
      u.IsGen := by
  obtain ⟨w, hw⟩ := AbSquare.exists_gen_of_mem_chart hL _ ![-1, -m, -1, m + 2] i hi
  obtain ⟨n, hn⟩ := exists_gen_cube_pow hL t ht a b z m
  obtain ⟨u, hu, -⟩ := exists_gen hL
    (φ' := ![z.left, (a * z).left, (b * z).left, (c * z).left])
    (ε' := ![m + 2, -1, -m, -1]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (a * b ^ m) c z h))).trans ?_
      rw [hc, _root_.one_mul z]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ w n)
      (LB.pullGen L (thφ G (x3 G)) thε t (lift (a * b ^ m) (lift c z)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hn)
      (DVR.pullGen_isGen _ _ _ _ ht _))
  exact ⟨u, hu⟩

variable {B : Over S} (θ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => (snd B G).left) (fun _ => 1)))

omit [GrpObj G] [IsCommMonObj G] in

theorem exists_sec_at (hL : L.IsLB) {T : Over S} (v : T ⟶ B) (w : T ⟶ G) :
    ∃ s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => w.left) (fun _ => 1)),
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L z J →
        sval s ρ.left z J = sval θ (lift (ρ ≫ v) (ρ ≫ w)).left z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : Fin 1 => w.left) (ε' := fun _ => 1)
    (fun U _ h => by rw [← Over.comp_left, lift_snd]) (pullSec θ (lift v w).left)
  refine ⟨s, fun T' ρ z J hJ => (hs _ _ z J hJ).trans ((sval_pullSec _ _ _ _ hJ).trans ?_)⟩
  rw [← Over.comp_left, comp_lift]

theorem exists_sec_three (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S}
    (v : T ⟶ B) (a b c : T ⟶ G) (m : ℕ) (hc : a * b ^ m * c = 1) (i : Fin 4 → L.ι)
    (hi : ∀ k (y : T.left),
      (![a.left, b.left, c.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => (snd T G).left) (fun _ => ((m + 2 : ℕ) : ℤ))),
      ∀ (w : T ⟶ G) (z : T.left) (J), Good L z J →
        Associated (sval s (ptSecT G w).left z J)
          (sval θ (lift v (a * w)).left z J * sval θ (lift v (b * w)).left z J ^ m *
            sval θ (lift v (c * w)).left z J) := by
  obtain ⟨u, hu⟩ := exists_gen_three hL t ht (fst T G ≫ a) (fst T G ≫ b) (fst T G ≫ c) (snd T G) m
    (by rw [← MonObj.comp_pow, ← MonObj.comp_mul, ← MonObj.comp_mul, hc, MonObj.comp_one]) i (by
    intro k y
    have := hi k ((fst T G).left y)
    fin_cases k
    · exact this
    · exact this
    · exact this
    · rw [← MonObj.comp_one (fst T G)]; exact this)
  obtain ⟨sa, ha⟩ := exists_sec_at θ hL (fst T G ≫ v) ((fst T G ≫ a) * snd T G)
  obtain ⟨sb, hb⟩ := exists_sec_at θ hL (fst T G ≫ v) ((fst T G ≫ b) * snd T G)
  obtain ⟨sc, hc'⟩ := exists_sec_at θ hL (fst T G ≫ v) ((fst T G ≫ c) * snd T G)
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T G).left)
    (ε' := fun _ => ((m + 2 : ℕ) : ℤ)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)) rfl)).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (mulSec (mulSec (mulSec sa (powSec fun _ : Fin m => sb)) sc) (genSec u hu))
  refine ⟨s, fun w z J hJ => ?_⟩
  have e : ∀ d : T ⟶ G, lift (ptSecT G w ≫ fst T G ≫ v) (ptSecT G w ≫ ((fst T G ≫ d) * snd T G)) =
      lift v (d * w) := fun d => by
    rw [MonObj.comp_mul, ptSecT, lift_fst_assoc, lift_fst_assoc, lift_snd, Category.id_comp,
      Category.id_comp]
  rw [hs _ _ z J hJ, sval_mulSec _ _ _ _ hJ, sval_mulSec _ _ _ _ hJ, sval_mulSec _ _ _ _ hJ,
    sval_powSec _ _ _ hJ, sval_genSec _ _ _ _ hJ, ha _ _ z J hJ, hb _ _ z J hJ, hc' _ _ z J hJ, e, e, e,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact associated_mul_unit_left _ _ (Units.isUnit _)

theorem meetsFibres_transl {D : (B ⊗ G).left.Opens} (hD : MeetsFibres (fst B G).left D) {T : Over S}
    (v : T ⟶ B) (e : T ⟶ G) (f : G ⟶ G) [Surjective f.left] :
    MeetsFibres (fst T G).left
      ((lift (fst T G ≫ v) ((fst T G ≫ e) * (snd T G ≫ f))).left ⁻¹ᵁ D) := by
  intro p
  obtain ⟨d, hd, hdp⟩ := hD (v.left p)
  have pb : IsPullback (fst T G).left (v ▷ G).left v.left (fst B G).left := by
    refine (IsPullback.of_right (h₁₁ := (v ▷ G).left) (v₁₁ := pullback.fst T.hom G.hom)
      (h₂₁ := v.left) (v₁₂ := pullback.fst B.hom G.hom) ?_ (Over.whiskerRight_left_fst v)
      (IsPullback.of_hasPullback B.hom G.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T.hom G.hom).flip
  obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.exists_preimage_of_isPullback pb p d hdp.symm
  let τ : T ⊗ G ⟶ T ⊗ G := lift (fst T G) ((fst T G ≫ e⁻¹) * snd T G)
  obtain ⟨g, hg⟩ := f.left.surjective ((τ ≫ snd T G).left z₁)
  have pb' : IsPullback (snd T G).left (T ◁ f).left f.left (snd T G).left := by
    refine (IsPullback.of_right (h₁₁ := (T ◁ f).left) (v₁₁ := pullback.snd T.hom G.hom)
      (h₂₁ := f.left) (v₁₂ := pullback.snd T.hom G.hom) ?_ (Over.whiskerLeft_left_snd f)
      (IsPullback.of_hasPullback T.hom G.hom)).flip
    rw [Over.whiskerLeft_left_fst, Over.w]
    exact IsPullback.of_hasPullback T.hom G.hom
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback pb' g (τ.left z₁) hg
  let σ : T ⊗ G ⟶ T ⊗ G := lift (fst T G) ((fst T G ≫ e) * snd T G)
  have h₁ : τ ≫ σ = 𝟙 _ := by
    ext
    · simp [τ, σ]
    · simp [τ, σ, MonObj.comp_mul, GrpObj.comp_inv]
  have h₂ : lift (fst T G ≫ v) ((fst T G ≫ e) * (snd T G ≫ f)) = T ◁ f ≫ σ ≫ v ▷ G := by
    ext
    · simp [σ]
    · simp [σ, MonObj.comp_mul]
  refine ⟨z, ?_, ?_⟩
  · rw [h₂]
    show (v ▷ G).left (σ.left ((T ◁ f).left z)) ∈ D
    rw [hz, show σ.left (τ.left z₁) = z₁ from congrArg (fun q => q.left z₁) h₁, hz₁']
    exact hd
  · have h₃ : (fst T G).left z = (fst T G).left ((T ◁ f).left z) :=
      congrArg (fun q => q.left z) (whiskerLeft_fst T f).symm
    have h₄ : (fst T G).left (τ.left z₁) = (fst T G).left z₁ :=
      congrArg (fun q : T ⊗ G ⟶ T => q.left z₁) (lift_fst _ _)
    rw [h₃, hz, h₄, hz₁]

theorem associated_sval_comp {X Y Z Z' : Scheme.{0}} {M : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z')
    {J : (Z ⟶ X) → M.ι} {J' : (Z' ⟶ X) → M.ι} (hJ : Good M (ρ z) J) (hJ' : Good M z J') :
    Associated (sval s (ρ ≫ r) z J') ((ρ.stalkMap z).hom (sval s r (ρ z) J)) := by
  have hm := hJ.mem φ r
  have e : gs (ρ ≫ r) z _ (s.f fun k => J (r ≫ φ k)) = (ρ.stalkMap z).hom (sval s r (ρ z) J) :=
    (gs_pull ρ r z _ hm _).symm.trans ((gs_stalkMap ρ z _ hm _).trans (congrArg _
      ((gs_pull (𝟙 Z) r (ρ z) _ hm _).trans (by rw [Category.id_comp]; rfl))))
  have e' := sec_trans s (ρ ≫ r) z (hJ'.mem φ (ρ ≫ r)) hm
  exact (Associated.of_eq (e'.trans (congrArg _ e))).trans
    (associated_unit_mul_left _ _ (Units.isUnit _))

def SameGerms (L : LB G.left) (n : ℕ) {T : Over S} (x y : T ⟶ G) : Prop :=
  ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T)
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => (snd T' G).left) (fun _ => (n : ℤ))))
    (z : T'.left) (J), Good L z J →
      Associated (sval s (ptSecT G (h ≫ x)).left z J) (sval s (ptSecT G (h ≫ y)).left z J)

omit [GrpObj G] [IsCommMonObj G] in
theorem SameGerms.comp {n : ℕ} {T T' : Over S} {x y : T ⟶ G} (H : SameGerms L n x y) (g : T' ⟶ T) :
    SameGerms L n (g ≫ x) (g ≫ y) := by
  intro T'' _ h s z J hJ
  have := H T'' (h ≫ g) s z J hJ
  rwa [Category.assoc, Category.assoc] at this

omit [GrpObj G] [IsCommMonObj G] in
theorem SameGerms.symm {n : ℕ} {T : Over S} {x y : T ⟶ G} (H : SameGerms L n x y) :
    SameGerms L n y x := fun T' _ h s z J hJ => (H T' h s z J hJ).symm

theorem dvd_of_sameGerms [Flat G.hom] [GeometricallyIntegral G.hom] (hL : L.IsLB)
    (t : LB.Gen (Theta G L)) (ht : t.IsGen) (hD : MeetsFibres (fst B G).left (nonzeroLocus θ))
    (m : ℕ) [Surjective (mulA G m).left] {X : Over S} (v : X ⟶ B) (x y a : X ⟶ G)
    (H : SameGerms L (m + 2) x y) (q : X.left) (J) (hJ : Good L q J) :
    sval θ (lift v (a * y)).left q J ∣ sval θ (lift v (a * x)).left q J := by
  have : Flat (fst X G).left := inferInstanceAs (Flat (pullback.fst X.hom G.hom))
  have : GeometricallyIntegral (fst X G).left :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst X.hom G.hom))
  have : Surjective (𝟙 G : G ⟶ G).left := inferInstanceAs (Surjective (𝟙 G.left))
  have : IsIso (GrpObj.inv : G ⟶ G).left := inferInstanceAs (IsIso ((Over.forget S).map GrpObj.inv))
  have : Surjective (mulA G m)⁻¹.left :=
    inferInstanceAs (Surjective ((mulA G m).left ≫ (GrpObj.inv : G ⟶ G).left))
  let c : X ⊗ G ⟶ G := ((fst X G ≫ a) * snd X G ^ m)⁻¹
  obtain ⟨w, ⟨h₁, h₂⟩, rfl⟩ := ((meetsFibres_transl hD v x (𝟙 G)).inf
    (meetsFibres_transl hD v (x * a⁻¹) (mulA G m)⁻¹)) q
  let χ : Fin 4 → ((X ⊗ G).left ⟶ G.left) :=
    ![(fst X G ≫ a).left, (snd X G).left, c.left, (1 : X ⊗ G ⟶ G).left]
  choose i hi using fun k => exists_chart hL (χ k w)
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := (X ⊗ G).left)
    (U := LB.wchart L χ i) (x := w) (Set.mem_iInter.2 hi)
  let κ : overRes (T := X ⊗ G) V ⟶ X ⊗ G := overResι V
  have : IsAffine (overRes (T := X ⊗ G) V).left := hV
  obtain ⟨s, hs⟩ := exists_sec_three θ hL t ht (κ ≫ fst X G ≫ v) (κ ≫ fst X G ≫ a) (κ ≫ snd X G)
    (κ ≫ c) m (by
      rw [← MonObj.comp_pow, ← MonObj.comp_mul, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one])
    i (fun k z => by
      have := Set.mem_iInter.1 (hle z.2) k
      fin_cases k
      · exact this
      · exact this
      · exact this
      · rw [← MonObj.comp_one κ]; exact this)
  let z : (overRes (T := X ⊗ G) V).left := ⟨w, hwV⟩
  choose I hI using fun ψ : (overRes (T := X ⊗ G) V).left ⟶ G.left => exists_chart hL (ψ z)
  have key := (hs _ z I hI).symm.trans ((H _ (κ ≫ fst X G) s z I hI).trans (hs _ z I hI))
  have unit : ∀ (d : X ⊗ G ⟶ G) (d' : overRes (T := X ⊗ G) V ⟶ G), d' = κ ≫ d →
      (lift (fst X G ≫ v) d).left w ∈ nonzeroLocus θ →
      IsUnit (sval θ (lift (κ ≫ fst X G ≫ v) d').left z I) := by
    rintro d _ rfl hd
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hd
    rw [← comp_lift]
    exact isUnit_sval θ _ z hI k hk
  have u₁ := unit _ ((κ ≫ snd X G) * ((κ ≫ fst X G) ≫ x)) (by
    rw [MonObj.comp_mul, Category.comp_id, Category.assoc, mul_comm]) h₁
  have u₂ := unit _ ((κ ≫ c) * ((κ ≫ fst X G) ≫ x)) (by
    rw [Category.assoc, ← MonObj.comp_mul]
    congr 1
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, Category.comp_id, mul_inv]
    ac_rfl) h₂
  have dv := ((u₁.pow m).dvd_mul_right).1 ((u₂.dvd_mul_right).1
    (((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans key.symm.dvd))
  have e : ∀ p : X ⟶ G, (lift (κ ≫ fst X G ≫ v) ((κ ≫ fst X G ≫ a) * ((κ ≫ fst X G) ≫ p))).left =
      (κ ≫ fst X G).left ≫ (lift v (a * p)).left := fun p => by
    rw [← Over.comp_left, comp_lift, MonObj.comp_mul]
    simp only [Category.assoc]
  rw [e, e] at dv
  have : Flat (κ ≫ fst X G).left := inferInstanceAs (Flat (V.ι ≫ (fst X G).left))
  exact dvd_descend (κ ≫ fst X G).left z
    (((associated_sval_comp θ _ (κ ≫ fst X G).left z hJ hI).symm.dvd.trans dv).trans
      (associated_sval_comp θ _ (κ ≫ fst X G).left z hJ hI).dvd)

theorem eq_of_sameGerms [Smooth G.hom] [GeometricallyIntegral G.hom] (hL : L.IsLB) (hK : KTriv G L)
    (t : LB.Gen (Theta G L)) (ht : t.IsGen) (hD : MeetsFibres (fst B G).left (nonzeroLocus θ))
    (m : ℕ) [Surjective (mulA G m).left] (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Spec (CommRingCat.of R) ⟶ S) (v : Over.mk b ⟶ B) (x y : Over.mk b ⟶ G)
    (H : SameGerms L (m + 2) x y) : x = y := by
  let T : Over S := Over.mk b
  let φ : Fin 2 → ((T ⊗ G).left ⟶ G.left) :=
    ![(lift (fst T G ≫ (x * y⁻¹)) (snd T G) ≫ μ[G]).left, (snd T G).left]
  let a : T ⊗ G ⟶ G := (fst T G ≫ y)⁻¹ * snd T G
  have e₀ : a * (fst T G ≫ x) = (fst T G ≫ (x * y⁻¹)) * snd T G := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]; simp only [a]; ac_rfl
  have e₁ : a * (fst T G ≫ y) = snd T G := by
    rw [mul_comm, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  obtain ⟨s, hs⟩ := exists_sec_at θ hL (fst T G ≫ v) ((fst T G ≫ (x * y⁻¹)) * snd T G)
  obtain ⟨s', hs'⟩ := exists_sec_at θ hL (fst T G ≫ v) (snd T G)
  have : Flat (fst T G).left := inferInstanceAs (Flat (pullback.fst T.hom G.hom))
  have : GeometricallyIntegral (fst T G).left :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst T.hom G.hom))
  have : IsLocallyNoetherian T.left := inferInstanceAs (IsLocallyNoetherian (Spec (.of R)))
  have : IsLocallyNoetherian (T ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst T.hom G.hom)
  have : Surjective (𝟙 G : G ⟶ G).left := inferInstanceAs (Surjective (𝟙 G.left))
  have hm := meetsFibres_transl hD v 1 (𝟙 G)
  rw [MonObj.comp_one, _root_.one_mul, Category.comp_id] at hm
  obtain ⟨c, hc⟩ := exists_gen_of_associated hL φ s s' (fun z J hJ => by
      refine isLeftRegular_germ (fst T G).left hm _ _ (fun w hw => ?_) z (hJ.mem _ (𝟙 _))
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hw.1
      choose I hI using fun ψ : (T ⊗ G).left ⟶ G.left => exists_chart hL (ψ w)
      have u := isUnit_sval θ _ w hI k hk
      have e := hs' _ (𝟙 _) w I hI
      rw [Category.id_comp, Category.id_comp] at e
      have e' := (germ_eq_sval s' w hI _ hw.2).trans (congrArg _ e)
      exact ((T ⊗ G).left.mem_basicOpen _ w hw.2).2
        ((congrArg IsUnit e').mpr ((Units.isUnit _).mul u)))
    (fun z J hJ => by
      have e := hs _ (𝟙 _) z J hJ
      have e' := hs' _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at e e'
      have d := dvd_of_sameGerms θ hL t ht hD m (fst T G ≫ v) _ _ a (H.comp (fst T G)) z J hJ
      have d' := dvd_of_sameGerms θ hL t ht hD m (fst T G ≫ v) _ _ a (H.comp (fst T G)).symm z J hJ
      rw [e₀, e₁, ← e, ← e'] at d d'
      exact ⟨d', d⟩)
  refine mul_inv_eq_one.1 (hK R b (x * y⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  exact gen_chartPull (chartPullOut L φ _ _ _ fun k => rfl) _ (DVR.pullGen_isGen _ _ _ _ hc _)

theorem associated_of_isValueAt {n : ℤ} {T : Over S} (s : LB.Sec (LPow G L n T)) (w : T ⟶ G)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n)))
    (c : Γ(T.left, ⊤)) (h : IsValueAt G L n s w τ c) (z : T.left) (J) (hJ : Good L z J) :
    Associated (sval (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => n) s (ptSecT G w).left z J)
      (gs (𝟙 T.left) z ⊤ c) := by
  have e : (ptSecT G w).left ≫ (snd T G).left = w.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  let j : Fin 1 → L.ι := fun _ => J ((ptSecT G w).left ≫ (snd T G).left)
  have hz : z ∈ LB.wchart L (fun _ : Fin 1 => w.left) j := Set.mem_iInter.2 fun _ => by
    have := hJ ((ptSecT G w).left ≫ (snd T G).left)
    exact (congrArg (fun q => q z ∈ L.U (j 0)) e).mp this
  have e₁ := ((gs_res (𝟙 _) z _ hz _).trans (gs_pull (𝟙 _) (ptSecT G w).left z _
    (val_le G L w j hz) _)).symm.trans ((congrArg (gs (𝟙 T.left) z _) (h j)).trans
      ((gs_mul (𝟙 _) z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_res (𝟙 _) z le_top hz c) (gs_unit (𝟙 _) z _ hz _))))
  rw [Category.id_comp] at e₁
  exact (Associated.of_eq e₁).trans (associated_mul_unit_left _ _ (Units.isUnit _))

theorem exists_isValueAt (hL : L.IsLB) {n : ℤ} {T : Over S} (s : LB.Sec (LPow G L n T)) (w : T ⟶ G)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n)))
    (hτ : τ.IsGen) : ∃ c, IsValueAt G L n s w τ c :=
  (EvVal.existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover L hL _ _)
    (EvVal.pullSec L (fun _ : Fin 1 => (snd T G).left) (fun _ => n) (ptSecT G w).left
      (fun _ => w.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le G L w) s) τ hτ).exists

end Group

theorem exists_sec_meetsFibres (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (P : PolAV S) [GeometricallyIntegral P.A.hom] (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ θ : LB.Sec (LB.LinComb P.L
        (fun _ : Fin 1 => (snd (overRes (T := baseOver S) V) P.A).left) (fun _ => 1)),
      MeetsFibres (fst (overRes (T := baseOver S) V) P.A).left (nonzeroLocus θ) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl p
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  refine ⟨V, hV, b i₀, fun q => ?_⟩
  let B := overRes (T := baseOver S) V
  let K : Type := B.left.residueField q
  let t : Spec (CommRingCat.of K) ⟶ B.left := B.left.fromSpecResidueField q
  let b' : Fin (1 ^ P.g) → LB.Sec (LPow P.A P.L (1 : ℕ) (baseAt t)) := fun i =>
    EvVal.pullSec P.L (fun _ : Fin 1 => (snd B P.A).left) (fun _ => ((1 : ℕ) : ℤ))
      (homAt t ▷ P.A).left (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg (fun q => q.left) (whiskerRight_snd (homAt t) P.A))
      (chart_le_res P.A P.L (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (1 : ℕ)) (b i)
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := (hb K t b' fun i j => rfl).1.ne_zero i₀
  have : IsIntegral (baseAt t ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral K _
  obtain ⟨j, hj⟩ : ∃ j, (b' i₀).f j ≠ 0 := by
    by_contra hn
    exact hne (Subtype.ext (funext fun j => not_not.1 fun h => hn ⟨j, h⟩))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (baseAt t ⊗ P.A).left.basicOpen ((b' i₀).f j) := by
    by_contra hn
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim))
  refine ⟨(homAt t ▷ P.A).left z, Opens.mem_iSup.2 ⟨j, ?_⟩, ?_⟩
  · have h := (SetLike.ext_iff.1 (Scheme.basicOpen_res _ _ _) z).1 hz
    exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen (homAt t ▷ P.A).left ((b i₀).f j)) z).2 h.2
  · have h : (fst B P.A).left ((homAt t ▷ P.A).left z) = t ((fst (baseAt t) P.A).left z) :=
      congrArg (fun q => q.left z) (whiskerRight_fst (homAt t) P.A)
    exact h.trans (Scheme.fromSpecResidueField_apply q _)

theorem eq_of_forall_value_eq : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → SecBaseChangeSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 3 ≤ n → ∀ (T : Over S) [IsLocallyNoetherian T.left] (x y : T ⟶ P.A) (τx : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (τy : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => y.left) (fun _ => (n : ℤ)))), τx.IsGen → τy.IsGen → (∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T) (s : LB.Sec (LPow P.A P.L n T')) (vx vy : Γ(T'.left, ⊤)), IsValueAt P.A P.L n s (h ≫ x) (LB.pullGen P.L _ _ τx h.left) vx → IsValueAt P.A P.L n s (h ≫ y) (LB.pullGen P.L _ _ τy h.left) vy → vx = vy) → x = y := by
  intro hGI hC hS hM S _ P n hn T _ x y τx τy hx hy H
  have := P.isAb.comm
  have := P.isAb.smooth
  have := hGI _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  obtain ⟨t, ht⟩ := hC S P P.L P.isLB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have := (hM S P m (by omega)).2.2.1
  have hG : SameGerms P.L (m + 2) x y := by
    intro T' _ h s z J hJ
    obtain ⟨vx, hvx⟩ := exists_isValueAt P.isLB s (h ≫ x) (LB.pullGen P.L _ _ τx h.left)
      (DVR.pullGen_isGen _ _ _ _ hx _)
    obtain ⟨vy, hvy⟩ := exists_isValueAt P.isLB s (h ≫ y) (LB.pullGen P.L _ _ τy h.left)
      (DVR.pullGen_isGen _ _ _ _ hy _)
    obtain rfl := H T' h s vx vy hvx hvy
    exact (associated_of_isValueAt s _ _ _ hvx z J hJ).trans
      (associated_of_isValueAt s _ _ _ hvy z J hJ).symm
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)
  obtain ⟨V, hV, θ, hθ⟩ := exists_sec_meetsFibres hS P (T.hom p)
  obtain ⟨U, hU, hp, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T.left) (U := T.hom ⁻¹ᵁ V)
    (x := p) hV
  refine ⟨U, hp, ?_⟩
  have : IsNoetherianRing Γ(T.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let g : Over.mk (Y := Spec (CommRingCat.of Γ(T.left, U))) (hU.fromSpec ≫ T.hom) ⟶ T :=
    Over.homMk hU.fromSpec rfl
  let v : Over.mk (Y := Spec (CommRingCat.of Γ(T.left, U))) (hU.fromSpec ≫ T.hom) ⟶
      overRes (T := baseOver S) V :=
    Over.homMk (IsOpenImmersion.lift V.ι (hU.fromSpec ≫ T.hom) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨q, rfl⟩)))
      ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac _ _ _))
  have e := congrArg (fun q => q.left)
    (eq_of_sameGerms θ P.isLB P.ktriv t ht hθ m _ _ v _ _ (hG.comp g))
  have e' : hU.fromSpec ≫ x.left = hU.fromSpec ≫ y.left := e
  rw [← hU.isoSpec_inv_ι, Category.assoc, Category.assoc, cancel_epi] at e'
  exact e'

end GlobalTheory.SepPoints
