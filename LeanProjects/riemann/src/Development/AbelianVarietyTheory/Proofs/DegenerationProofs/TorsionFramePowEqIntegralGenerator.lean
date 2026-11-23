import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.TorsFrameInt

section Pt

variable {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_eq (hM : M.IsLB) {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp F ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ ε φ' ε') {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) {y : Sp F} {J} (hJ : Good M y J) (e : val t (𝟙 _) y J = val t' (𝟙 _) y J) :
    LB.Gen.Corr M _ _ _ _ t t' :=
  corr_of_val hM fun y' I hI => by
    have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    obtain rfl := Subsingleton.elim y y'
    exact (gen_trans ht (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).trans ((congrArg₂ (· * ·)
      (hF.trF (𝟙 _) y (fun ψ => I (𝟙 _ ≫ ψ)) fun ψ => J (𝟙 _ ≫ ψ)) e).trans
      (gen_trans ht' (𝟙 _) y (hI.mem _ _) (hJ.mem _ _)).symm)

theorem toStk_surjective (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

noncomputable def scale {Y : Scheme.{0}} {N : LB Y} (t : LB.Gen N) (c : Γ(Y, ⊤)ˣ) : LB.Gen N :=
  ⟨fun i => res le_top c * t.s i⟩

theorem gm_scale {Y Z : Scheme.{0}} {N : LB Y} (t : LB.Gen N) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) (i : N.ι)
    (h : r z ∈ N.U i) : gm r z (N.U i) ((scale t c).s i) = gm r z ⊤ c * gm r z (N.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top h c) rfl)

theorem scale_isGen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (c : Γ(Y, ⊤)ˣ) : (scale t c).IsGen :=
  isGen_of_gm _ fun y j j' hj hj' =>
    (gm_scale t c (𝟙 Y) y j hj).trans ((congrArg _ (gen_trans ht (𝟙 Y) y hj hj')).trans ((mul_left_comm _ _ _).trans
      (congrArg _ (gm_scale t c (𝟙 Y) y j' hj').symm)))

noncomputable def constU (u : F) (hu : u ≠ 0) : Γ(Sp F, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 u hu)

theorem gm_constU (u : F) (hu : u ≠ 0) (z : Sp F) : (gm (𝟙 (Sp F)) z ⊤ (constU u hu)).val = toStk z u := by
  rw [gm_val (𝟙 _) z ⊤ trivial]; rfl

end Pt

section Bundles

variable {X H Y Z : Scheme.{0}} {L : LB X} {M : LB H} {K : Type} [Fintype K]

noncomputable def wv {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ H) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gw w r z (J (r ≫ ψ)) (fun _ => J' (r ≫ f))

theorem exists_move (hL : L.IsLB) (hM : M.IsLB) {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) (φX : K → (X ⟶ X)) (φY : K → (Y ⟶ Y)) (φH : K → (H ⟶ H)) (ε : K → ℤ)
    (h₁ : ∀ k, φY k ≫ ψ = ψ ≫ φX k) (h₂ : ∀ k, φY k ≫ f = f ≫ φH k)
    (α : LB.Gen (LB.LinComb L φX ε)) (hα : α.IsGen) :
    ∃ a : LB.Gen (LB.LinComb M (fun k => f ≫ φH k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good M z J' →
        val α (r ≫ ψ) z J = (∏ k, wv w (r ≫ φY k) z J J' ^ ε k) * val a r z J' := by
  obtain ⟨b, hb, H⟩ := H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα
  have le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      have : (f ≫ φH k) y ∈ M.U (j k) := Set.mem_iInter.1 hy k
      rw [← h₂ k] at this; exact this)
  refine ⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z J J' hJ hJ' => ?_⟩
  · refine (gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))
    refine (gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc, h₂]
  · have m := hJ'.mem (fun k => f ≫ φH k) r
    have e := H Z r z (fun k => J ((r ≫ ψ) ≫ φX k)) (fun k _ => J' (r ≫ f ≫ φH k)) (fun k => by
      have := hJ ((r ≫ ψ) ≫ φX k)
      rw [Category.assoc, ← h₁ k] at this
      rw [Category.assoc, ← h₁ k]; exact this) (fun k => Set.mem_iInter.1 (le _ m) k)
    refine e.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ z _ m _).symm)
    rw [wv, Category.assoc, Category.assoc, Category.assoc, h₁, h₂]

theorem exists_gen_of_chart (hM : M.IsLB) (φ : K → (Y ⟶ H)) (ε : K → ℤ) (j₀ : K → M.ι)
    (h : ∀ y, y ∈ LB.wchart M φ j₀) : ∃ ρ : LB.Gen (LB.LinComb M φ ε), ρ.IsGen := by
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j y hy => ⟨hy, h y⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  exact ((gm_res _ y _ hj _).trans (gm_linComb M φ ε (𝟙 Y) y j j₀ hj (h y))).trans
    ((trF_trans hM φ ε (𝟙 Y) y hj hj' (h y)).symm.trans (congrArg _
      ((gm_res _ y _ hj' _).trans (gm_linComb M φ ε (𝟙 Y) y j' j₀ hj' (h y))).symm))

theorem ratio_indep {B B' : Scheme.{0}} {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) {e : B ⟶ X} {e' : B' ⟶ H} {a : LB.Gen (L.pull e)} {a' : LB.Gen (M.pull e')} (ha : a.IsGen)
    (ha' : a'.IsGen) (r : Z ⟶ Y) (t : Z ⟶ B) (t' : Z ⟶ B') (h : r ≫ ψ = t ≫ e) (h' : r ≫ f = t' ≫ e') (z : Z)
    {J J' I I'} (hJ : Good L z J) (hJ' : Good M z J') (hI : Good L z I) (hI' : Good M z I') :
    val a t z J * (wv w r z J J' * val a' t' z J')⁻¹ = val a t z I * (wv w r z I I' * val a' t' z I')⁻¹ := by
  have e₁ : val a t z J = _ * val a t z I := gen_trans ha t z (hJ.mem _ t) (hI.mem _ t)
  have e₂ : val a' t' z J' = _ * val a' t' z I' := gen_trans ha' t' z (hJ'.mem _ t') (hI'.mem _ t')
  have e₃ : wv w r z J J' = _ * wv w r z I I' := (isGen_iff w).1 hw Z r z _ _ _ _ (hJ (r ≫ ψ)) (hI (r ≫ ψ))
    (mem_pull.2 (hJ' (r ≫ f))) (mem_pull.2 (hI' (r ≫ f)))
  rw [gm_pull_g M f r z _ _ (mem_pull.2 (hJ' (r ≫ f))) (mem_pull.2 (hI' (r ≫ f))), h, h'] at e₃
  rw [trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Bundles

section Dvr

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X H : Scheme.{0}} {M : LB H}
  {K : Type} [Fintype K]

noncomputable def intU (V : Type) [CommRing V] [IsDomain V] :
    Subgroup ((Sp (FractionRing V)).presheaf.stalk (cpt (FractionRing V)))ˣ :=
  (Units.map ((toStkA (cpt (FractionRing V))).comp (algebraMap V (FractionRing V))).toMonoidHom).range

theorem exists_unit_gm {A C : Type} [CommRing A] [CommRing C] (σ : A →+* C) (z : Sp C) {Y : Scheme.{0}} (g : Sp A ⟶ Y)
    (U : Y.Opens) (ht : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) :
    ∃ v : Aˣ, toStkA z (σ v.val) = (gm (spMap σ ≫ g) z U a).val := by
  have hu : IsUnit (valR g U a.val) := by
    rw [GlobalTheory.Points.valR_eq g _ ht]; exact (Units.isUnit _).map _
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, ← GlobalTheory.Points.valR_spMap_comp σ g U ht a.val]
  exact toStkA_valR (spMap σ ≫ g) U z (fun y _ => ht (show spMap σ y ∈ (⊤ : (Sp A).Opens) from trivial)) a

theorem mem_intU {V : Type} [CommRing V] [IsDomain V] {u} : u ∈ intU V ↔
    ∃ v : Vˣ, toStkA (cpt (FractionRing V)) (algebraMap V (FractionRing V) v.val) = u.val :=
  exists_congr fun _ => Units.ext_iff

omit [IsDiscreteValuationRing V] in
theorem gm_mem_intU {Y : Scheme.{0}} (g : Sp V ⟶ Y) (U : Y.Opens) (ht : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) :
    gm (jK V ≫ g) (cpt _) U a ∈ intU V :=
  mem_intU.2 (exists_unit_gm (algebraMap V (FractionRing V)) _ g U ht a)

omit [IsDiscreteValuationRing V] in
theorem val_mem_intU {Y : Scheme.{0}} {φ : K → (Y ⟶ H)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb M φ ε)) (g : Sp V ⟶ Y)
    (r : Sp (FractionRing V) ⟶ Y) (hr : r = jK V ≫ g) (J : (Sp (FractionRing V) ⟶ H) → M.ι)
    (h : ∀ k, ⊤ ≤ (g ≫ φ k) ⁻¹ᵁ M.U (J (r ≫ φ k))) : val c r (cpt _) J ∈ intU V := by
  subst hr
  exact gm_mem_intU g (LB.wchart M φ (fun k => J ((jK V ≫ g) ≫ φ k)))
    (fun y hy => Set.mem_iInter.2 fun k => h k hy) _

theorem exists_extend (hM : M.IsLB) (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p)
    (he : e ≫ p = 𝟙 _) (eK : Sp (FractionRing V) ⟶ pullback p (jK V)) (h₁ : eK ≫ pullback.fst p (jK V) = jK V ≫ e)
    (h₂ : eK ≫ pullback.snd p (jK V) = 𝟙 _) (φ : K → (H ⟶ H)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb M (fun k => pullback.fst p (jK V) ≫ φ k) ε)) (ha : a.IsGen)
    (ρ : LB.Gen (LB.LinComb M (fun k => e ≫ φ k) ε)) (hρ : ρ.IsGen) {J} (hJ : Good M (cpt (FractionRing V)) J) :
    ∃ c : LB.Gen (LB.LinComb M φ ε), ∀ x : Sp (FractionRing V) ⟶ pullback p (jK V),
      x ≫ pullback.snd p (jK V) = 𝟙 _ →
      val c (x ≫ pullback.fst p (jK V)) (cpt _) J * val a eK (cpt _) J = val a x (cpt _) J * val ρ (jK V) (cpt _) J := by
  obtain ⟨u, hu⟩ := toStk_surjective (cpt (FractionRing V)) (val ρ (jK V) (cpt _) J * (val a eK (cpt _) J)⁻¹).val
  have u0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact Units.ne_zero _ hu.symm
  have hs' : gm (𝟙 _) (cpt (FractionRing V)) ⊤ (constU u u0) = _ := Units.ext ((gm_constU u u0 _).trans hu)
  let t := scale a (pullU (pullback.snd p (jK V)) ⊤ (constU u u0))
  have ht : t.IsGen := scale_isGen a ha _
  have hv : ∀ x : Sp (FractionRing V) ⟶ pullback p (jK V), x ≫ pullback.snd p (jK V) = 𝟙 _ →
      val t x (cpt _) J = val ρ (jK V) (cpt _) J * (val a eK (cpt _) J)⁻¹ * val a x (cpt _) J := fun x hx => by
    refine (gm_scale a _ x _ _ (hJ.mem _ x)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (gm_pull x (pullback.snd p (jK V)) _ ⊤ trivial _).trans ?_
    rw [hx]; exact hs'
  obtain ⟨c, ⟨-, hc⟩, -⟩ := GlobalTheory.GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hg he eK h₁ M hM K φ ε
    t ρ ht hρ (corr_of_val_eq hM (fun U _ k => Finset.prod_congr rfl fun i _ => by
        show k (eK ≫ pullback.fst p (jK V) ≫ φ i) ^ _ = k (jK V ≫ e ≫ φ i) ^ _
        rw [← Category.assoc, h₁, Category.assoc])
      (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ hρ _) hJ (by
        rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
        exact (hv eK h₂).trans (inv_mul_cancel_right _ _)))
  refine ⟨c, fun x hx => ?_⟩
  have : val c (x ≫ pullback.fst p (jK V)) (cpt _) J = val t x (cpt _) J :=
    (val_pull hJ c _ x).symm.trans (congrArg (fun q => val q x (cpt _) J) hc)
  rw [this, hv x hx, mul_right_comm, inv_mul_cancel_right, mul_comm]

end Dvr

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem left_mulA {T : Over S} (x : T ⟶ G) (n : ℕ) : x.left ≫ (mulA G n).left = (x ^ n).left := by
  rw [← Over.comp_left]
  exact congrArg _ ((map_pow (preHom x) (𝟙 G) n).trans (congrArg (· ^ n) (Category.comp_id x)))

theorem mulA_comm (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  refine e.trans ((left_mulA _ n).symm.trans ?_)
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := rfl

theorem one_comm (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (baseOver S')))
  have e' : (𝟙 S' ≫ η[G'].left) ≫ φ = (𝟙 S' ≫ f) ≫ η[G].left := e
  rwa [Category.id_comp, Category.id_comp] at e'

theorem one_mulA (n : ℕ) : η[G].left ≫ (mulA G n).left = η[G].left := by
  have e := left_mulA (1 : baseOver S ⟶ G) n
  rw [one_pow] at e
  have e' : (𝟙 S ≫ η[G].left) ≫ _ = 𝟙 S ≫ η[G].left := e
  rwa [Category.id_comp] at e'

end Grp

theorem frame_values {S : Scheme.{0}} (P : PolAV S) {rig : LB.Gen (P.L.pull (eSec P.A))} {n : ℕ} {z : baseOver S ⟶ P.A}
    {τ} (H : IsTorsFrame P rig n z τ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (y : Z) J, Good P.L y J →
        val α (t ≫ eSec P.A) y J = val rig t y J ^ ((n : ℤ) ^ 2) * (val rig t y J)⁻¹ ∧
        val (Y := (baseOver S).left) τ t y J ^ ((n : ℤ) ^ 2) = val α (t ≫ z.left) y J * val rig t y J := by
  obtain ⟨-, -, α, hα, hn, hc⟩ := H
  refine ⟨α, hα, fun Z t y J hJ => ⟨?_, ?_⟩⟩
  · have q := val_corr hJ hn t
    rw [val_pull hJ, val_mul hJ, val_inv] at q
    exact q.trans (congrArg (· * _) (map_zpow _ _ _))
  · have q := val_corr hJ hc t
    rw [val_mul hJ, val_pull hJ] at q
    refine Eq.trans (map_zpow _ _ _).symm (q.trans (congrArg (_ * ·) ?_))
    have hy := hJ.mem (fun _ : Fin 1 => (baseOver S).hom ≫ eSec P.A) t
    refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res _ y _ hy _).trans ?_))
    refine (gm_pull t (baseOver S).hom y (LB.wchart P.L (fun _ : PUnit => eSec P.A)
      (fun _ => J (t ≫ (baseOver S).hom ≫ eSec P.A))) (rigT_le P.A P.L _ hy) _).trans ?_
    refine Eq.trans (val_of rig (t ≫ (baseOver S).hom) y J _ (fun _ => by rw [Category.assoc])).symm ?_
    exact congrArg (fun q => val rig q y J) (Category.comp_id t)

theorem key_algebra {U : Type} [CommGroup U] (N : ℤ) (τ ax ae r l we wx m tx te c ρ : U)
    (h₁ : r * (we * m)⁻¹ = l) (h₂ : ae = r ^ N * r⁻¹) (h₃ : τ ^ N = ax * r)
    (h₄ : ax = wx ^ N * we ^ (-1 : ℤ) * tx) (h₅ : ae = we ^ N * we ^ (-1 : ℤ) * te) (h₆ : c * te = tx * ρ) :
    τ ^ N = (l * wx) ^ N * (m ^ N * c * ρ⁻¹) := by
  apply Additive.ofMul.injective
  replace h₁ := congrArg Additive.ofMul h₁
  replace h₂ := congrArg Additive.ofMul h₂
  replace h₃ := congrArg Additive.ofMul h₃
  replace h₄ := congrArg Additive.ofMul h₄
  replace h₅ := congrArg Additive.ofMul h₅
  replace h₆ := congrArg Additive.ofMul h₆
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  linear_combination (norm := module) h₃ + h₄ - h₆ - h₅ + h₂ + N • h₁

theorem core {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X H B : Scheme.{0}} {L : LB X} {M : LB H}
    (hL : L.IsLB) (hM : M.IsLB) (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p)
    [IsSeparated p] (he : e ≫ p = 𝟙 _) (eK : Sp (FractionRing V) ⟶ pullback p (jK V))
    (h₁ : eK ≫ pullback.fst p (jK V) = jK V ≫ e) (h₂ : eK ≫ pullback.snd p (jK V) = 𝟙 _)
    (eA : B ⟶ X) (t : Sp (FractionRing V) ⟶ B) (ψ : pullback p (jK V) ⟶ X) (h₃ : eK ≫ ψ = t ≫ eA)
    (nG : H ⟶ H) (nK : pullback p (jK V) ⟶ pullback p (jK V)) (nA : X ⟶ X) (hp : nG ≫ p = p)
    (c₁ : nK ≫ ψ = ψ ≫ nA) (c₂ : nK ≫ pullback.fst p (jK V) = pullback.fst p (jK V) ≫ nG) (c₃ : eK ≫ nK = eK)
    (c₄ : e ≫ nG = e)
    (w : LB.Iso (M.pull (pullback.fst p (jK V))) (L.pull ψ)) (hw : w.IsGen)
    (rig : LB.Gen (L.pull eA)) (hrig : rig.IsGen) (rigM : LB.Gen (M.pull e)) (hrigM : rigM.IsGen) (N : ℤ) :
    ∃ l : ((Sp (FractionRing V)).presheaf.stalk (cpt (FractionRing V)))ˣ,
      ∀ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nA] ![N, -1])), α.IsGen →
      ∀ (h : Sp V ⟶ H) (x : Sp (FractionRing V) ⟶ pullback p (jK V)), h ≫ p = 𝟙 _ →
        x ≫ pullback.fst p (jK V) = jK V ≫ h → x ≫ pullback.snd p (jK V) = 𝟙 _ → x ≫ nK = eK →
        ∀ (i : M.ι), ⊤ ≤ h ⁻¹ᵁ M.U i → ∀ J, Good L (cpt (FractionRing V)) J → ∀ τ,
        val α (t ≫ eA) (cpt _) J = val rig t (cpt _) J ^ N * (val rig t (cpt _) J)⁻¹ →
        τ ^ N = val α (x ≫ ψ) (cpt _) J * val rig t (cpt _) J →
        ∃ v ∈ intU V, τ ^ N = (l * gw w x (cpt _) (J (x ≫ ψ)) (fun _ => i)) ^ N * v := by
  choose I hI using fun χ : Sp (FractionRing V) ⟶ X => exists_chart hL (χ (cpt _))
  choose I' hI' using fun χ : Sp (FractionRing V) ⟶ H => exists_chart hM (χ (cpt _))
  refine ⟨val rig t _ I * (wv w eK _ I I' * val rigM (jK V) _ I')⁻¹,
    fun α hα h x hh x₁ x₂ x₃ i hi J hJ τ a₁ a₂ => ?_⟩
  have : IsDominant (jK V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have ext : ∀ a b : Sp V ⟶ H, a ≫ p = 𝟙 _ → b ≫ p = 𝟙 _ → jK V ≫ a = jK V ≫ b → a = b := fun a b ha hb hab =>
    ext_of_isDominant_of_isSeparated p (ha.trans hb.symm) (jK V) hab
  have hn : h ≫ nG = e := ext _ _ (by rw [Category.assoc, hp, hh]) he (by
    rw [← Category.assoc, ← x₁, Category.assoc, ← c₂, ← Category.assoc, x₃, h₁])
  obtain ⟨j₀, hj₀, hji⟩ : ∃ j₀, ⊤ ≤ e ⁻¹ᵁ M.U j₀ ∧ (h = e → i = j₀) := by
    by_cases hhe : h = e
    · exact ⟨i, hhe ▸ hi, fun _ => rfl⟩
    · obtain ⟨j, hj⟩ := exists_chart hM (e (cpt V))
      exact ⟨j, (top_le_iff_cpt e _).2 hj, fun q => absurd q hhe⟩
  obtain ⟨J', hJ', hv⟩ := exists_good M hM (cpt (FractionRing V)) (K := Bool)
    (fun b => cond b (jK V ≫ h) (jK V ≫ e)) (fun b => cond b i j₀) (by
      rintro (_ | _) (_ | _) q
      exacts [rfl, (hji (ext _ _ hh he q.symm)).symm, hji (ext _ _ hh he q), rfl]) (by
      rintro (_ | _)
      exacts [hj₀ (show jK V _ ∈ (⊤ : (Sp V).Opens) from trivial), hi (show jK V _ ∈ (⊤ : (Sp V).Opens) from trivial)])
  have v₁ : J' (jK V ≫ h) = i := hv true
  have v₂ : J' (jK V ≫ e) = j₀ := hv false
  obtain ⟨a, ha, hav⟩ := exists_move hL hM w hw ![𝟙 X, nA] ![𝟙 _, nK] ![𝟙 H, nG] ![N, -1]
    (fun k => by fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁])
    (fun k => by fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]) α hα
  have ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nG] k = e := fun k => by fin_cases k; exacts [Category.comp_id _, c₄]
  obtain ⟨ρ, hρ⟩ := exists_gen_of_chart hM (fun k : Fin 2 => e ≫ ![𝟙 H, nG] k) ![N, -1] (fun _ => j₀)
    (fun y => Set.mem_iInter.2 fun k => by
      show (e ≫ ![𝟙 H, nG] k) y ∈ M.U j₀
      rw [ee]; exact hj₀ trivial)
  obtain ⟨c, hc⟩ := exists_extend hM p e hs hg he eK h₁ h₂ _ _ a ha ρ hρ hJ'
  have b₁ := ratio_indep w hw hrig hrigM eK t (jK V) h₃ h₁ _ hJ hJ' hI hI'
  have b₄ := hav _ x _ J J' hJ hJ'
  have b₅ := hav _ eK _ J J' hJ hJ'
  rw [Fin.prod_univ_two] at b₄ b₅
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, x₃, c₃] at b₄ b₅
  rw [h₃] at b₅
  have b := key_algebra N τ _ _ _ _ _ _ _ _ _ _ _ b₁ a₁ a₂ b₄ b₅ (hc x x₂)
  rw [show wv w x _ J J' = gw w x _ (J (x ≫ ψ)) (fun _ => i) by rw [wv, x₁, v₁], x₁] at b
  refine ⟨_, mul_mem (mul_mem (zpow_mem ?_ _) ?_) (inv_mem ?_), b⟩
  · exact val_mem_intU rigM (𝟙 _) _ (Category.comp_id _).symm J' fun _ => by rw [Category.id_comp, v₂]; exact hj₀
  · refine val_mem_intU c h _ rfl J' fun k => ?_
    fin_cases k
    · show ⊤ ≤ (h ≫ 𝟙 _) ⁻¹ᵁ M.U (J' ((jK V ≫ h) ≫ 𝟙 _))
      rw [Category.comp_id, Category.comp_id, v₁]; exact hi
    · show ⊤ ≤ (h ≫ nG) ⁻¹ᵁ M.U (J' ((jK V ≫ h) ≫ nG))
      rw [Category.assoc, hn, v₂]; exact hj₀
  · exact val_mem_intU ρ (𝟙 _) _ (Category.comp_id _).symm J' fun k => by
      rw [Category.id_comp, ee, v₂]; exact hj₀

theorem torsFrame_pow_eq : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (M : RigLB G) (B : Scheme.{0}) (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (t : Sp (FractionRing V) ⟶ B) (ψ : pullback G.hom (jK V) ⟶ P.A.left), IsGrpPullback ((Over.pullback (jK V)).obj G) P.A t ψ → ∀ (w : LB.Iso (M.L.pull (pullback.fst G.hom (jK V))) (P.L.pull ψ)), w.IsGen → ∀ n : ℕ, ∃ lam : FractionRing V, lam ≠ 0 ∧ ∀ (z : baseOver B ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver B).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))), IsTorsFrame P rig n z τ → ∀ (h : baseOver (Sp V) ⟶ G) (x : Sp (FractionRing V) ⟶ pullback G.hom (jK V)), x ≫ pullback.fst G.hom (jK V) = jK V ≫ h.left → x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → x ≫ ψ = t ≫ z.left → ∀ (i : M.L.ι) (k : P.L.ι), ⊤ ≤ h.left ⁻¹ᵁ M.L.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ P.L.U k → ∃ v : Vˣ, valR (X := (baseOver B).left) t _ (τ.s (fun _ => k)).val ^ (n ^ 2) = (lam * valR x _ (w.s (fun _ => k, fun _ => i)).val) ^ (n ^ 2) * algebraMap V (FractionRing V) v := by
  intro V _ _ _ G _ _ hG M B P rig hrig t ψ gp w hw n
  have := hG.smooth
  have := hG.geomConnected
  have := hG.separated
  have gq := isGrpPullback_pullback G (jK V)
  let eK : Sp (FractionRing V) ⟶ pullback G.hom (jK V) := η[(Over.pullback (jK V)).obj G].left
  have h₃ : eK ≫ ψ = t ≫ eSec P.A := one_comm gp
  have h₂ : eK ≫ pullback.snd G.hom (jK V) = 𝟙 _ := Over.w η[(Over.pullback (jK V)).obj G]
  obtain ⟨l, H⟩ := core P.isLB M.isLB G.hom (eSec G) hG.smooth (GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G)
    (Over.w η[G]) eK (one_comm gq) h₂ (eSec P.A) t ψ h₃ (mulA G n).left (mulA ((Over.pullback (jK V)).obj G) n).left
    (mulA P.A n).left (Over.w _) (mulA_comm gp n) (mulA_comm gq n) (one_mulA n) (one_mulA n) w hw rig hrig M.rig
    M.rigGen ((n : ℤ) ^ 2)
  obtain ⟨lam, hl⟩ := toStk_surjective (cpt (FractionRing V)) l.val
  refine ⟨lam, fun q => ?_, fun z τ hτ h x x₁ x₂ x₃ i k hi hk => ?_⟩
  · rw [q, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  obtain ⟨α, hα, hv⟩ := frame_values P hτ
  obtain ⟨J, hJ, hJk⟩ := exists_good P.L P.isLB (cpt (FractionRing V)) (K := PUnit) (fun _ => x ≫ ψ) (fun _ => k)
    (fun _ _ _ => rfl) (fun _ => hk trivial)
  have e₀ : J (x ≫ ψ) = k := hJk PUnit.unit
  obtain ⟨a₁, a₂⟩ := hv _ t _ J hJ
  have xn : x ≫ (mulA ((Over.pullback (jK V)).obj G) n).left = eK := by
    refine gp.1.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (mulA_comm gp n)).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₃).trans ((Category.assoc _ _ _).trans ?_))
      refine (congrArg (t ≫ ·) ((left_mulA z n).trans ?_)).trans h₃.symm
      rw [hτ.1]
      exact Category.id_comp _
    · exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (Over.w _)).trans (x₂.trans h₂.symm))
  obtain ⟨u, hu, e⟩ := H α hα h.left x (Over.w h) x₁ x₂ xn i hi J hJ _ a₁ (by rw [x₃]; exact a₂)
  obtain ⟨v, hv⟩ := mem_intU.1 hu
  refine ⟨v, toStkA_injective ?_⟩
  have m₁ : ⊤ ≤ t ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) := fun y hy => Set.mem_iInter.2 fun _ => by
    have := hk hy
    rw [x₃] at this; exact this
  have m₂ : ⊤ ≤ x ⁻¹ᵁ ((P.L.pull ψ).U (fun _ => k) ⊓ (M.L.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
    fun y hy => ⟨mem_pull.2 (hk hy), mem_pull.2 (by
      have : (jK V ≫ h.left) y ∈ M.L.U i := hi (show jK V y ∈ (⊤ : (Sp V).Opens) from trivial)
      rw [← x₁] at this; exact this)⟩
  have s₁ := toStkA_valR t _ (cpt _) m₁ (τ.s fun _ => k)
  have s₂ := toStkA_valR x _ (cpt _) m₂ (w.s (fun _ => k, fun _ => i))
  rw [val_of τ t _ J (fun _ => k) (fun _ => by rw [← e₀, x₃]), e₀, ← Nat.cast_pow, zpow_natCast, zpow_natCast] at e
  rw [map_mul, map_pow, map_pow, map_mul, hv]
  refine (congrArg (· ^ (n ^ 2)) s₁).trans ((congrArg Units.val e).trans ?_)
  exact congrArg (· ^ (n ^ 2) * u.val) (congrArg₂ (· * ·) hl s₂).symm

end GlobalTheory.TorsFrameInt
