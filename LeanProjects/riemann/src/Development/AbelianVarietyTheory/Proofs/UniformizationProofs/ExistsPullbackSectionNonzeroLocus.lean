import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_pullback_section_nonzero_locus {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (n : ℕ) (θ : H0 L n) :
    ∃ θ' : H0 (L.pull F) n, ∀ y : X', y ∈ nonzeroLocus θ' ↔ F y ∈ nonzeroLocus θ := by
  have hL' := pull_isLB hL F
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  have hP := linComb_isLB L hL (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))
  have hP' := linComb_isLB (L.pull F) hL' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => (n : ℤ))
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin 1 => 𝟙 X) (fun _ => (n : ℤ)) F _
    fun _ => (Category.id_comp F).trans (Category.comp_id F).symm)
    (iso_linComb hw (fun _ : Fin 1 => 𝟙 X') (fun _ => (n : ℤ)))
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hP hP' θ
  refine ⟨s', fun y => ?_⟩
  refine (mem_nonzeroLocus _ y).trans
    (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (F y)).symm)
  · obtain ⟨j, hj⟩ := exists_chart hP (F y)
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp, gs_stalkMap F y _ hj] at e
    exact ⟨j, hj, (isUnit_map_iff (F.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
  · obtain ⟨k, hk⟩ := exists_chart hP' y
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at e
    exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap F y _ hj _).symm.trans e)).mp (u.map _))⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

noncomputable def transl (x : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ x)

theorem comp_transl (x : 𝟙_ (Over S) ⟶ A) {T : Over S} (y : T ⟶ A) : y ≫ transl x = y * (toUnit T ≫ x) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem toUnit_mul_self {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) (T : Over S) :
    (toUnit T ≫ x) * (toUnit T ≫ x) = 1 := by
  rw [← MonObj.comp_mul, hx, MonObj.comp_one]

theorem transl_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) : transl x ≫ transl x = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]

theorem inv_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) :
    (GrpObj.inv : A ⟶ A) ≫ transl x = transl x ≫ (GrpObj.inv : A ⟶ A) := by
  rw [comp_transl, ← Hom.inv_def, transl, mul_inv, inv_eq_of_mul_eq_one_right (toUnit_mul_self hx A), Hom.inv_def,
    Category.id_comp]

theorem exists_restrict {X Y : Scheme.{0}} (p : X ⟶ Y) (h : X ⟶ X) (e : h ≫ p = p) (V : Y.Opens) :
    ∃ n : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme, n ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ h :=
  ⟨IsOpenImmersion.lift _ ((p ⁻¹ᵁ V).ι ≫ h) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y.1 ∈ V) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩

theorem sym_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (h : Sym A L) :
    Sym A (L.pull (transl x).left) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := exists_restrict A.hom (transl x).left (Over.w _) U
  refine ⟨U, hU, _, LBxP.isGen_pullAlong L (transl x).left n _ _ _ (fun k => ?_) t ht⟩
  fin_cases k
  · show (_ ≫ _) ≫ _ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    exact congrArg (fun q => _ ≫ q.left) (inv_transl hx)
  · exact hn.symm

theorem kTriv_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (hL : L.IsLB) (h : KTriv A L) :
    KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x))) V
  have k₂ : T ◁ transl x ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_transl hx, Category.comp_id]
  have k₃ : T ◁ transl x ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

theorem exists_translate : ∀ (K : Type) [Field K] (A : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ _ ⟶ A.A), x * x = 1 →
    ∀ θ : H0 A.L 1, ∃ (A' : PolAV (Spec (CommRingCat.of K))) (e : A'.A ≅ A.A) (θ' : H0 A'.L 1), IsMonHom e.hom ∧
      A'.g = A.g ∧ ∀ a : A'.A.left, a ∈ nonzeroLocus θ' ↔ (e.hom * (toUnit _ ≫ x)).left a ∈ nonzeroLocus θ := by
  intro K _ A x hx θ
  have hL' := pull_isLB A.isLB (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  have e : (transl x).left ≫ (transl x).left = 𝟙 _ := congrArg (fun q => q.left) (transl_transl hx)
  have : IsIso (transl x).left := ⟨⟨(transl x).left, e, e⟩⟩
  have hp : IsPullback (transl x).left A.A.hom A.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  obtain ⟨θ', hθ'⟩ := exists_pullback_section_nonzero_locus A.isLB (transl x).left 1 θ
  exact ⟨{ A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := A.L.pull (transl x).left, isLB := hL'
           rigid := exists_gen_of_local (V := K) _ hL' (K := PUnit) (fun _ => eSec A.A) (fun _ => 1)
           sym := sym_transl hx A.sym
           ample := relAmple_pull hp A.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample
           ktriv := kTriv_transl hx A.isLB A.ktriv },
    Iso.refl _, θ', inferInstanceAs (IsMonHom (𝟙 _)), rfl, hθ'⟩

end GlobalTheory.PolTranslate
