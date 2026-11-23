import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.GraphSystem
open GlobalTheory.CechPic GlobalTheory.EndOnTorsion GlobalTheory.AmpleSpan

variable {X Y Z : Scheme.{0}}

theorem mem_subring_of_local_inverse {W V : Y.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (le : V ≤ W)
    (S : Subring Γ(Y, V)) (hS : ∀ a, resG Y le a ∈ S)
    (loc : ∀ y ∈ W, ∃ (O : Y.Opens) (t : Γ(Y, O)) (u : Γ(Y, V)), y ∈ O ∧ u ∈ S ∧
      (∀ z ∈ W, z ∈ Y.basicOpen t → z ∈ V) ∧ ∀ z ∈ V, z ∈ O → gs (𝟙 Y) z _ u * gs (𝟙 Y) z _ t = 1)
    (b : Γ(Y, V)) : b ∈ S := by
  have key : ∀ y ∈ W, ∃ h : Γ(Y, W), y ∈ Y.basicOpen h ∧ ∃ n, resG Y le h ^ n * b ∈ S := fun y hy => by
    obtain ⟨O, t, u, hyO, hu, h1, h2⟩ := loc y hy
    obtain ⟨h, hle, hyh⟩ := hW.exists_basicOpen_le (V := O) ⟨y, hyO⟩ hy
    refine ⟨h, hyh, ?_⟩
    have hhW : Y.basicOpen h ≤ W := Y.basicOpen_le h
    haveI := hW.isLocalization_basicOpen h
    obtain ⟨l, a₀, ha₀⟩ := IsLocalization.Away.surj h (resG Y hle t)
    have ha₀' : resG Y hle t * resG Y hhW h ^ l = resG Y hhW a₀ := ha₀
    have g₀ : ∀ z ∈ Y.basicOpen h, gs (𝟙 Y) z _ t * gs (𝟙 Y) z _ h ^ l = gs (𝟙 Y) z _ a₀ := fun z hz => by
      have e := congrArg (gs (𝟙 Y) z _) ha₀'
      rwa [gs_mul _ z _ hz, LBGerm.gs_pow _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz] at e
    have hc : Y.basicOpen (h * a₀) ≤ V := fun z hz => by
      rw [Y.basicOpen_mul] at hz
      refine h1 z (hhW hz.1) ((isUnit_gs_iff (𝟙 Y) z _ (hle hz.1) t).1 ?_)
      exact isUnit_of_mul_isUnit_left ((g₀ z hz.1).symm ▸ (isUnit_gs_iff (𝟙 Y) z _ (hhW hz.1) a₀).2 hz.2)
    have hc' : ∀ z ∈ V, z ∈ Y.basicOpen h → z ∈ Y.basicOpen (h * a₀) := fun z hz hzh => by
      rw [Y.basicOpen_mul]
      refine ⟨hzh, (isUnit_gs_iff (𝟙 Y) z _ (hhW hzh) a₀).1 ?_⟩
      rw [← g₀ z hzh]
      exact (IsUnit.of_mul_eq_one_right _ (h2 z hz (hle hzh))).mul
        (((isUnit_gs_iff (𝟙 Y) z _ (hhW hzh) h).2 hzh).pow l)
    have hcW : Y.basicOpen (h * a₀) ≤ W := Y.basicOpen_le _
    haveI := hW.isLocalization_basicOpen (h * a₀)
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (h * a₀) (resG Y hc b)
    have ha' : resG Y hc b * resG Y hcW (h * a₀) ^ m = resG Y hcW a := ha
    obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hV
      (resG Y le h ^ (m + l * m) * b - resG Y le a * u ^ m) (resG Y le h) (fn_ext fun z hz => by
        have hz' : z ∈ V ⊓ Y.basicOpen h := (Y.basicOpen_res h (homOfLE le).op).le hz
        have hzc := hc' z hz'.1 hz'.2
        have e := congrArg (gs (𝟙 Y) z _) ha'
        rw [gs_mul _ z _ hzc, LBGerm.gs_pow _ z _ hzc, gs_res _ z _ hzc, gs_res _ z _ hzc, gs_res _ z _ hzc,
          gs_mul _ z _ (le hz'.1), ← g₀ z hz'.2] at e
        refine (gs_res (𝟙 Y) z (Y.basicOpen_le _) hz _).trans (Eq.trans ?_ (LBGerm.gs_zero _ z _ hz).symm)
        rw [gs_sub' _ z _ hz'.1, gs_mul _ z _ hz'.1, gs_mul _ z _ hz'.1, LBGerm.gs_pow _ z _ hz'.1,
          LBGerm.gs_pow _ z _ hz'.1, gs_res _ z _ hz'.1, gs_res _ z _ hz'.1, ← e]
        have e2 := congrArg (· ^ m) (h2 z hz'.1 (hle hz'.2))
        simp only [mul_pow, one_pow] at e2
        simp only [mul_pow, pow_add, pow_mul]
        linear_combination (-(gs (𝟙 Y) z _ h ^ m * (gs (𝟙 Y) z _ h ^ l) ^ m * gs (𝟙 Y) z _ b)) * e2)
    refine ⟨k + (m + l * m), ?_⟩
    have : resG Y le h ^ (k + (m + l * m)) * b = resG Y le h ^ k * (resG Y le a * u ^ m) := by
      rw [pow_add]; linear_combination hk
    rw [this]
    exact S.mul_mem (S.pow_mem (hS h) k) (S.mul_mem (hS a) (S.pow_mem hu m))
  letI : Algebra Γ(Y, W) Γ(Y, V) := (resG Y le).toAlgebra
  let N : Submodule Γ(Y, W) Γ(Y, V) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c x hx => S.mul_mem (hS c) hx }
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N {h | ∃ n, resG Y le h ^ n * b ∈ S} ?_ b ?_
  · rw [← hW.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨h, hyh, hn⟩ := key y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨h, hn⟩, hyh⟩
  · rintro ⟨h, n, hn⟩
    refine ⟨n, ?_⟩
    rw [← map_pow] at hn
    exact hn

theorem secCoord_tens {A B : LB Y} {σ₁ σ₂ : Type} {s : σ₁ → A.Sec} {t : σ₂ → B.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ Y} {v₁ : σ₁ → R} {v₂ : σ₂ → R} (h₁ : SecCoord A s x v₁) (h₂ : SecCoord B t x v₂) :
    SecCoord (tens A B) (fun i : σ₁ × σ₂ => tensSec (s i.1) (t i.2)) x (fun i => v₁ i.1 * v₂ i.2) := by
  obtain ⟨τ₁, g₁, h₁⟩ := h₁
  obtain ⟨τ₂, g₂, h₂⟩ := h₂
  have l₁ : ∀ J, ((tens A B).pull x).U J ≤ (A.pull x).U (fun _ => (J PUnit.unit).1) :=
    fun J y hy => mem_pull.2 (mem_pull.1 hy).1
  have l₂ : ∀ J, ((tens A B).pull x).U J ≤ (B.pull x).U (fun _ => (J PUnit.unit).2) :=
    fun J y hy => mem_pull.2 (mem_pull.1 hy).2
  have gen : ∀ {C : LB Y} {τ : (C.pull x).Gen}, τ.IsGen → ∀ (y : Sp R) j j', x y ∈ C.U j → x y ∈ C.U j' →
      gm (𝟙 _) y _ (τ.s fun _ => j) = gm x y _ (C.g j j') * gm (𝟙 _) y _ (τ.s fun _ => j') := by
    intro C τ g y j j' hj hj'
    have e := (isGen_iff_germ τ).1 g y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
    have e' := gm_pull_g C x (𝟙 _) y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
    rw [Category.id_comp] at e'
    exact e.trans (congrArg (· * _) e')
  have val : ∀ {C : LB Y} (τ : (C.pull x).Gen) (w : C.Sec) (a : R) j (y : Sp R) (hy : x y ∈ C.U j),
      (x.appLE _ _ (RepBC.pull_le C x fun _ => j)).hom (w.f j) =
        resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
          (show Γ(Sp R, (C.pull x).U fun _ => j) from (τ.s fun _ => j).val) →
      gs x y _ (w.f j) = SegreCoord.ev y a * (gm (𝟙 _) y _ (τ.s fun _ => j)).val := by
    intro C τ w a j y hy h
    have hy' : y ∈ (C.pull x).U (fun _ => j) := mem_pull.2 hy
    have := congrArg (gs (𝟙 _) y _) h
    refine (SegreCoord.gs_appLE x y _ hy' _).symm.trans (this.trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) ?_ ?_)))
    · exact (gs_res _ y _ hy' _).trans (SegreCoord.ev_eq y _).symm
    · exact gs_unit _ y _ hy' _
  refine SegreCoord.secCoord_mk (fun J => resG _ (l₁ J) (τ₁.s _).val * resG _ (l₂ J) (τ₂.s _).val)
    (fun y j => (gm (𝟙 _) y _ (τ₁.s fun _ => j.1)).val * (gm (𝟙 _) y _ (τ₂.s fun _ => j.2)).val)
    (fun J y hy => ?_) (fun y j _ => (Units.isUnit _).mul (Units.isUnit _)) (fun y j j' hj hj' => ?_)
    (fun y j i hj => ?_)
  · exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans (gs_unit _ y _ (l₁ J hy) _)) ((gs_res _ y _ hy _).trans (gs_unit _ y _ (l₂ J hy) _)))
  · rw [gen g₁ y j.1 j'.1 hj.1 hj'.1, gen g₂ y j.2 j'.2 hj.2 hj'.2, gm_tens A B x y j j' hj hj']
    simp only [Units.val_mul]
    ring
  · have e : gs x y _ ((tensSec (s i.1) (t i.2)).f j) = gs x y _ ((s i.1).f j.1) * gs x y _ ((t i.2).f j.2) :=
      (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
    rw [e, val τ₁ _ _ _ y hj.1 (h₁ i.1 (fun _ => j.1) _), val τ₂ _ _ _ y hj.2 (h₂ i.2 (fun _ => j.2) _), map_mul]
    ring

theorem nonzeroLocus_pull (M : LB X) (f : Y ⟶ X) (s : M.Sec) :
    Out.nonzeroLocus (RepBC.secPull M f s) = f ⁻¹ᵁ Out.nonzeroLocus s := by
  refine nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y k hk => ?_
  · obtain ⟨j, hj⟩ := exists_chart_of_mem s hy
    exact ⟨fun _ => j, mem_pull.2 hj⟩
  · have e : gs (𝟙 Y) y _ ((RepBC.secPull M f s).f k) = gs f y _ (s.f (k PUnit.unit)) :=
      SegreCoord.gs_appLE f y _ hk _
    rw [e]
    exact (mem_nonzeroLocus_iff_gs s f y (mem_pull.1 hk)).symm

theorem exists_secCoord_local {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec) {R : Type} [CommRing R]
    [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ := exists_chart hM (x (IsLocalRing.closedPoint R))
  refine SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : x ⁻¹ᵁ M.U k = ⊤ := (IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ M.U k)).1 hk
  exact this.ge (show y ∈ (⊤ : (Sp R).Opens) from trivial)

section Product
variable {X₁ X₂ : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)

def prodSec (s : M₁.Sec) (t : M₂.Sec) : (tens (M₁.pull a₁) (M₂.pull a₂)).Sec :=
  tensSec (RepBC.secPull M₁ a₁ s) (RepBC.secPull M₂ a₂ t)

theorem nonzeroLocus_prodSec (s : M₁.Sec) (t : M₂.Sec) :
    Out.nonzeroLocus (prodSec a₁ a₂ s t) = a₁ ⁻¹ᵁ Out.nonzeroLocus s ⊓ a₂ ⁻¹ᵁ Out.nonzeroLocus t := by
  rw [prodSec, nonzeroLocus_tensSec, nonzeroLocus_pull, nonzeroLocus_pull]

theorem gs_prodSec (s : M₁.Sec) (t : M₂.Sec) (y : Y) {j : M₁.ι} {k : M₂.ι} (hj : a₁ y ∈ M₁.U j) (hk : a₂ y ∈ M₂.U k) :
    gs (𝟙 Y) y _ ((prodSec a₁ a₂ s t).f (fun _ => j, fun _ => k)) = gs a₁ y _ (s.f j) * gs a₂ y _ (t.f k) := by
  have h : y ∈ (tens (M₁.pull a₁) (M₂.pull a₂)).U (fun _ => j, fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  exact (gs_mul _ y _ h _ _).trans (congrArg₂ (· * ·)
    ((gs_res _ y _ h _).trans (SegreCoord.gs_appLE a₁ y _ h.1 _))
    ((gs_res _ y _ h _).trans (SegreCoord.gs_appLE a₂ y _ h.2 _)))

theorem secCoord_prod {σ₁ σ₂ : Type} {th₁ : σ₁ → M₁.Sec} {th₂ : σ₂ → M₂.Sec} {R : Type} [CommRing R]
    {y : Sp R ⟶ Y} {v₁ : σ₁ → R} {v₂ : σ₂ → R} (h₁ : SecCoord M₁ th₁ (y ≫ a₁) v₁) (h₂ : SecCoord M₂ th₂ (y ≫ a₂) v₂) :
    SecCoord (tens (M₁.pull a₁) (M₂.pull a₂)) (fun i : σ₁ × σ₂ => prodSec a₁ a₂ (th₁ i.1) (th₂ i.2)) y
      (fun i => v₁ i.1 * v₂ i.2) :=
  secCoord_tens ((RepBC.secCoord_pull M₁ th₁ a₁ y v₁).2 h₁) ((RepBC.secCoord_pull M₂ th₂ a₂ y v₂).2 h₂)

theorem graphIdeal_eq {K σ₁ σ₂ : Type} [CommRing K] (s : Y ⟶ Sp K) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) :
    graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ = idealOf s (tens (M₁.pull a₁) (M₂.pull a₂))
      (fun i : σ₁ × σ₂ => prodSec a₁ a₂ (th₁ i.1) (th₂ i.2)) (𝟙 Y) := by
  ext F
  simp only [graphIdeal, idealOf, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · rintro h R _ β y v ⟨hy, hv⟩
    refine eq_zero_of_localization _ fun J hJ => ?_
    let φ := algebraMap R (Localization.AtPrime J)
    obtain ⟨v₁, e₁⟩ := exists_secCoord_local h₁ th₁ ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, e₂⟩ := exists_secCoord_local h₂ th₂ ((spMap φ ≫ y) ≫ a₂)
    obtain ⟨u, hu⟩ := Coord.unique (isLB_tens (pull_isLB h₁ a₁) (pull_isLB h₂ a₂)) (secCoord_prod a₁ a₂ e₁ e₂)
      (Coord.baseChange hv φ)
    have := h _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨by rw [Category.assoc, hy, ← spMap_comp], Coord.scale e₁ u, e₂⟩
    refine Eq.trans ?_ this
    refine (MvPolynomial.map_eval₂Hom β v φ F).trans ?_
    congr 2
    funext i
    rw [hu, _root_.mul_assoc]
  · rintro h R _ β y v₁ v₂ ⟨hy, e₁, e₂⟩
    exact h R _ β y _ ⟨hy, secCoord_prod a₁ a₂ e₁ e₂⟩

theorem vAmp_prod {K σ₁ σ₂ : Type} [Field K] {p₁ : X₁ ⟶ Sp K} {p₂ : X₂ ⟶ Sp K} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    {th₁ : σ₁ → M₁.Sec} {th₂ : σ₂ → M₂.Sec} (V₁ : VAmp p₁ M₁ th₁) (V₂ : VAmp p₂ M₂ th₂) [IsClosedImmersion a₁] :
    VAmp (a₁ ≫ p₁) (tens (M₁.pull a₁) (M₂.pull a₂)) (fun i : σ₁ × σ₂ => prodSec a₁ a₂ (th₁ i.1) (th₂ i.2)) := by
  obtain ⟨c₁, V₁⟩ := V₁
  obtain ⟨c₂, V₂⟩ := V₂
  choose f₁ r₁ q₁ g₁ using V₁
  choose f₂ r₂ q₂ g₂ using V₂
  have q₁' : ∀ i j, IsRatio (th₁ j) (th₁ i) (r₁ i j) := q₁
  have q₂' : ∀ i j, IsRatio (th₂ j) (th₂ i) (r₂ i j) := q₂
  have o₁ : ∀ i, r₁ i i = 1 := fun i => (q₁' i i).unique fun k => by rw [map_one, _root_.one_mul]
  have o₂ : ∀ i, r₂ i i = 1 := fun i => (q₂' i i).unique fun k => by rw [map_one, _root_.one_mul]
  have m₁ : ∀ x, ∃ i, x ∈ Out.nonzeroLocus (th₁ i) := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [c₁]; trivial)
  have m₂ : ∀ x, ∃ i, x ∈ Out.nonzeroLocus (th₂ i) := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [c₂]; trivial)
  refine ⟨top_le_iff.1 fun y _ => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := m₁ (a₁ y)
    obtain ⟨i', hi'⟩ := m₂ (a₂ y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), (nonzeroLocus_prodSec a₁ a₂ _ _).ge ⟨hi, hi'⟩⟩
  rintro ⟨i, i'⟩
  have eV := nonzeroLocus_prodSec a₁ a₂ (th₁ i) (th₂ i')
  have hW : IsAffineOpen (a₁ ⁻¹ᵁ Out.nonzeroLocus (th₁ i)) := (f₁ i).preimage a₁
  have hV : IsAffineOpen (Out.nonzeroLocus (prodSec a₁ a₂ (th₁ i) (th₂ i'))) := by
    rw [eV, inf_comm, ← nonzeroLocus_pull M₂]
    exact isAffineOpen_nonzeroLocus_inf (pull_isLB h₂ a₂) _ hW
  have l₁ := eV.le.trans inf_le_left
  have l₂ := eV.le.trans inf_le_right
  let r : σ₁ × σ₂ → Γ(Y, Out.nonzeroLocus (prodSec a₁ a₂ (th₁ i) (th₂ i'))) := fun j =>
    (a₁.appLE _ _ l₁).hom (r₁ i j.1) * (a₂.appLE _ _ l₂).hom (r₂ i' j.2)
  refine ⟨hV, r, fun j => isRatio_of_gs (s := prodSec a₁ a₂ (th₁ j.1) (th₂ j.2)) fun y hy => ?_, fun f => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart h₁ (a₁ y)
    obtain ⟨k', hk'⟩ := exists_chart h₂ (a₂ y)
    refine ⟨(fun _ => k, fun _ => k'), ⟨mem_pull.2 hk, mem_pull.2 hk'⟩, ?_⟩
    rw [gs_prodSec a₁ a₂ _ _ y hk hk', gs_prodSec a₁ a₂ _ _ y hk hk', gs_mul _ y _ hy,
      SegreCoord.gs_appLE a₁ y _ hy, SegreCoord.gs_appLE a₂ y _ hy, (q₁' i j.1).gs a₁ y (l₁ hy) hk,
      (q₂' i' j.2).gs a₂ y (l₂ hy) hk']
    ring
  let c : K →+* Γ(Y, Out.nonzeroLocus (prodSec a₁ a₂ (th₁ i) (th₂ i'))) :=
    RingHom.comp ((a₁ ≫ p₁).appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let S := (MvPolynomial.eval₂Hom c r).range
  have hr : ∀ j, r j ∈ S := fun j => ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  refine Exists.imp (fun F hF => Eq.symm hF)
    (RingHom.mem_range.1 (mem_subring_of_local_inverse hW hV l₁ S (fun a => ?_) (fun y _ => ?_) f))
  · obtain ⟨a, rfl⟩ := a₁.app_surjective _ (f₁ i) a
    obtain ⟨F, rfl⟩ := g₁ i a
    change (a₁.appLE _ _ l₁).hom _ ∈ S
    rw [MvPolynomial.eval₂_comp_left]
    refine MvPolynomial.eval₂_mem (fun d _ => ?_) fun j => ?_
    · exact ⟨MvPolynomial.C (MvPolynomial.coeff d F), (MvPolynomial.eval₂Hom_C _ _ _).trans
        (RepBC.appLE_appLE a₁ p₁ (U := ⊤) le_top l₁ le_top
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (MvPolynomial.coeff d F))).symm⟩
    · have := hr (j, i')
      simpa only [r, o₂, map_one, _root_.mul_one, Function.comp_apply] using this
  · obtain ⟨k, hk⟩ := m₂ (a₂ y)
    refine ⟨a₂ ⁻¹ᵁ Out.nonzeroLocus (th₂ k), (a₂.appLE _ _ le_rfl).hom (r₂ k i'), (a₂.appLE _ _ l₂).hom (r₂ i' k),
      hk, ?_, fun z hz hz' => eV.ge ⟨hz, ?_⟩, fun z hz hz' => ?_⟩
    · have := hr (i, k)
      simpa only [r, o₁, map_one, _root_.one_mul] using this
    · have hzk := Y.basicOpen_le _ hz'
      have e := (isUnit_gs_iff (𝟙 Y) z _ hzk _).2 hz'
      rw [SegreCoord.gs_appLE a₂ z _ hzk, isUnit_gs_iff a₂ z _ hzk, (q₂' k i').basicOpen] at e
      exact e.2
    · obtain ⟨l, hl⟩ := exists_chart h₂ (a₂ z)
      rw [SegreCoord.gs_appLE a₂ z _ hz, SegreCoord.gs_appLE a₂ z _ hz']
      refine ((mem_nonzeroLocus_iff_gs (th₂ k) a₂ z hl).1 hz').mul_right_cancel ?_
      rw [_root_.mul_assoc, ← (q₂' k i').gs a₂ z hz' hl, ← (q₂' i' k).gs a₂ z (l₂ hz) hl, _root_.one_mul]

end Product

theorem exists_product_system : ∀ (K σ₁ σ₂ : Type) [Field K] [Finite σ₁] [Finite σ₂] (Y X₁ X₂ : Scheme.{0}) (s : Y ⟶ Sp K) (p₁ : X₁ ⟶ Sp K) (p₂ : X₂ ⟶ Sp K) (M₁ : LB X₁) (M₂ : LB X₂) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂), M₁.IsLB → M₂.IsLB → VAmp p₁ M₁ th₁ → VAmp p₂ M₂ th₂ → IsClosedImmersion a₁ → a₁ ≫ p₁ = s → a₂ ≫ p₂ = s → ∃ (M : LB Y) (th : σ₁ × σ₂ → M.Sec), M.IsLB ∧ VAmp s M th ∧ LBIso (LB.div M (M₁.pull a₁)) (M₂.pull a₂) ∧ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ = idealOf s M th (𝟙 Y) ∧ (∀ (R : Type) [CommRing R] (y : Sp R ⟶ Y) v₁ v₂, SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord M th y (fun i => v₁ i.1 * v₂ i.2)) ∧ ∀ i i' : σ₁ × σ₂, (∀ j, (th₁ i.1).f j = (th₁ i'.1).f j) → (∀ j, (th₂ i.2).f j = (th₂ i'.2).f j) → ∀ j, (th i).f j = (th i').f j := by
  intro K σ₁ σ₂ _ _ _ Y X₁ X₂ s p₁ p₂ M₁ M₂ th₁ th₂ a₁ a₂ h₁ h₂ V₁ V₂ _ e₁ _
  have k₁ := pull_isLB h₁ a₁
  have k₂ := pull_isLB h₂ a₂
  have k := isLB_tens k₁ k₂
  refine ⟨_, fun i => prodSec a₁ a₂ (th₁ i.1) (th₂ i.2), k, e₁ ▸ vAmp_prod a₁ a₂ h₁ h₂ V₁ V₂, ?_,
    graphIdeal_eq a₁ a₂ s h₁ h₂ th₁ th₂, fun R _ y v₁ v₂ => secCoord_prod a₁ a₂, fun i i' u₁ u₂ j => ?_⟩
  · rw [← cls_eq_iff (LB.isLB_div k k₁) k₂, cls_div k k₁, cls_tens k₁ k₂, add_sub_cancel_left]
  · show resG Y _ ((a₁.appLE _ _ _).hom ((th₁ i.1).f _)) * resG Y _ ((a₂.appLE _ _ _).hom ((th₂ i.2).f _)) =
      resG Y _ ((a₁.appLE _ _ _).hom ((th₁ i'.1).f _)) * resG Y _ ((a₂.appLE _ _ _).hom ((th₂ i'.2).f _))
    rw [u₁, u₂]

end GlobalTheory.ZV.GraphSystem
end
