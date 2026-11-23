import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace MapToProj

open MvPolynomial TopologicalSpace SecRingIso LBGerm

variable {R : Type} [CommRing R] {X X' Y Z : Scheme.{0}} {H : LB X} {H' : LB X'} {n : ℕ}
  {s : Fin (n + 1) → H.Sec} {s' : Fin (n + 1) → H'.Sec}

theorem exists_isRatioFamily (s : Fin (n + 1) → H.Sec) (i : Fin (n + 1)) : ∃ r, IsRatioFamily s i r := by
  choose r hr using fun j => exists_quot (s j) (s i) _ le_rfl
  refine ⟨r, fun j k => fn_ext fun y hy => ?_⟩
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hr j y k hy.1 hy.2, mul_comm]

theorem ratio_gs {i : Fin (n + 1)} {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (φ : Z ⟶ X) (z : Z) (hy : φ z ∈ nonzeroLocus (s i)) {k : H.ι} (hk : φ z ∈ H.U k) (j : Fin (n + 1)) :
    gs φ z _ ((s j).f k) = gs φ z _ (r j) * gs φ z _ ((s i).f k) := by
  have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hy, hk⟩
  have e := congrArg (gs φ z _) (hr j k)
  rwa [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (φ : Z ⟶ X) (z : Z) (U : X.Opens) (h : φ z ∈ U) (c : R) :
    gs φ z U (cst f U c) =
      gs (𝟙 Z) z ⊤ ((φ ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e := gs_pull (𝟙 Z) φ z ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  exact (gs_res φ z le_top h _).trans e.symm

theorem ker_le (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R))
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i))
    (hv : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d) (i : Fin (n + 1))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (h' : IsRatioFamily s' i r') :
    RingHom.ker (eval₂Hom (cst f _) (r i)) ≤ RingHom.ker (eval₂Hom (cst f' _) r') := by
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  obtain ⟨e, F, hF, G, hG⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    rw [eq_add_of_sub_eq hG, map_add, hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose m hm using hn
  have hx : MvPolynomial.X i ^ Finset.univ.sup m * F ∈ vanishingForms f s (Finset.univ.sup m + e) := by
    refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i _).mul hF) fun j => ?_
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hm j, mul_zero]
  have e₂ := h'.eval_eq_zero f' (hv _ hx)
  rw [eq_add_of_sub_eq hG, map_mul, map_pow, map_add, map_mul, map_sub, map_one, eval₂Hom_X', h'.self_eq_one] at e₂
  simpa using e₂

def Propor (s : Fin (n + 1) → H.Sec) (s' : Fin (n + 1) → H'.Sec) (φ : Z ⟶ X) (ψ : Z ⟶ X') : Prop :=
  ∀ z : Z, (∀ a, φ z ∈ nonzeroLocus (s a) ↔ ψ z ∈ nonzeroLocus (s' a)) ∧
    ∀ a b k k', φ z ∈ H.U k → ψ z ∈ H'.U k' →
      gs φ z _ ((s a).f k) * gs ψ z _ ((s' b).f k') = gs φ z _ ((s b).f k) * gs ψ z _ ((s' a).f k')

theorem Propor.comp {φ : Z ⟶ X} {ψ : Z ⟶ X'} (h : Propor s s' φ ψ) (r : Y ⟶ Z) : Propor s s' (r ≫ φ) (r ≫ ψ) :=
  fun y => ⟨(h (r y)).1, fun a b j j' hj hj' => by
    rw [gs_comp r φ y _ hj, gs_comp r φ y _ hj, gs_comp r ψ y _ hj', gs_comp r ψ y _ hj', ← map_mul, ← map_mul]
    exact congrArg _ ((h (r y)).2 a b j j' hj hj')⟩

theorem Propor.of_local {φ : Z ⟶ X} {ψ : Z ⟶ X'}
    (h : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ Propor s s' (U.ι ≫ φ) (U.ι ≫ ψ)) : Propor s s' φ ψ := fun z => by
  obtain ⟨U, hz, H⟩ := h z
  obtain ⟨y, rfl⟩ : ∃ y : U.toScheme, U.ι y = z := ⟨⟨z, hz⟩, rfl⟩
  refine ⟨(H y).1, fun a b j j' hj hj' => ?_⟩
  have e := (H y).2 a b j j' hj hj'
  rw [gs_comp U.ι φ y _ hj, gs_comp U.ι φ y _ hj, gs_comp U.ι ψ y _ hj', gs_comp U.ι ψ y _ hj',
    ← map_mul, ← map_mul] at e
  exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y)).1 e

theorem Propor.unique (f : X ⟶ Spec (CommRingCat.of R)) {φ₁ φ₂ : Z ⟶ X} {ψ : Z ⟶ X'} (h₁ : Propor s s' φ₁ ψ)
    (h₂ : Propor s s' φ₂ ψ) (e : φ₁ ≫ f = φ₂ ≫ f) {i : Fin (n + 1)} (ha : IsAffineOpen (nonzeroLocus (s i)))
    {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (hs : Function.Surjective (eval₂Hom (cst f _) r)) (hψ : ∀ z, ψ z ∈ nonzeroLocus (s' i)) : φ₁ = φ₂ := by
  have m₁ := fun z => ((h₁ z).1 i).2 (hψ z)
  have m₂ := fun z => ((h₂ z).1 i).2 (hψ z)
  refine hom_ext_affine ha m₁ m₂ fun g z => ?_
  obtain ⟨p, rfl⟩ := hs g
  obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hψ z)
  have key : ∀ χ : Z ⟶ X, Propor s s' χ ψ → ∀ j,
      gs χ z _ (r j) * gs ψ z _ ((s' i).f k') = gs ψ z _ ((s' j).f k') := fun χ hχ j => by
    have m := ((hχ z).1 i).2 (hψ z)
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus m
    refine ((mem_nonzeroLocus_iff_pull _ χ z hk).1 m).mul_left_cancel ?_
    rw [← (hχ z).2 j i k k' hk hk', ratio_gs hr χ z m hk j]
    ring
  induction p using MvPolynomial.induction_on with
  | C a => rw [eval₂Hom_C, gs_cst f _ z _ (m₁ z), gs_cst f _ z _ (m₂ z), e]
  | add p q hp hq => rw [map_add, gs_add _ z _ (m₁ z), gs_add _ z _ (m₂ z), hp, hq]
  | mul_X p j hp =>
    rw [map_mul, gs_mul _ z _ (m₁ z), gs_mul _ z _ (m₂ z), hp, eval₂Hom_X']
    exact congrArg _ (((mem_nonzeroLocus_iff_pull _ ψ z hk').1 (hψ z)).mul_right_cancel
      ((key _ h₁ j).trans (key _ h₂ j).symm))

theorem exists_local (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R)) {i : Fin (n + 1)}
    (ha : IsAffineOpen (nonzeroLocus (s i))) {r : Fin (n + 1) → Γ(X, nonzeroLocus (s i))}
    (hr : IsRatioFamily s i r) (hs : Function.Surjective (eval₂Hom (cst f _) r))
    {r' : Fin (n + 1) → Γ(X', nonzeroLocus (s' i))} (hr' : IsRatioFamily s' i r')
    (hk : RingHom.ker (eval₂Hom (cst f _) r) ≤ RingHom.ker (eval₂Hom (cst f' _) r')) :
    ∃ φ : (nonzeroLocus (s' i)).toScheme ⟶ X, φ ≫ f = (nonzeroLocus (s' i)).ι ≫ f' ∧
      Propor s s' φ (nonzeroLocus (s' i)).ι := by
  obtain ⟨φ, hφ, hg⟩ := exists_hom_of_ringHom ha (nonzeroLocus (s' i))
    ((eval₂Hom (cst f _) r).liftOfSurjective hs ⟨_, hk⟩)
  have hp : ∀ p z, gs φ z _ (eval₂Hom (cst f _) r p) =
      gs (nonzeroLocus (s' i)).ι z _ (eval₂Hom (cst f' _) r' p) := fun p z => by
    rw [hg, RingHom.liftOfSurjective_comp_apply]
  have hz : ∀ z : (nonzeroLocus (s' i)).toScheme, (nonzeroLocus (s' i)).ι z ∈ nonzeroLocus (s' i) := fun z => z.2
  refine ⟨φ, hom_ext_spec fun c z => ?_, fun z => ?_⟩
  · have e := hp (C c) z
    rwa [eval₂Hom_C, eval₂Hom_C, gs_cst f _ z _ (hφ z), gs_cst f' _ z _ (hz z)] at e
  · have e : ∀ j, gs φ z _ (r j) = gs (nonzeroLocus (s' i)).ι z _ (r' j) := fun j => by
      have e := hp (MvPolynomial.X j) z
      rwa [eval₂Hom_X', eval₂Hom_X'] at e
    refine ⟨fun a => ?_, fun a b k k' hk hk' => ?_⟩
    · obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (hφ z)
      obtain ⟨k', hk'⟩ := exists_chart_of_mem_nonzeroLocus (hz z)
      rw [mem_nonzeroLocus_iff_pull _ φ z hk, mem_nonzeroLocus_iff_pull _ _ z hk', ratio_gs hr φ z (hφ z) hk a,
        ratio_gs hr' _ z (hz z) hk' a, IsUnit.mul_iff, IsUnit.mul_iff, e,
        and_iff_left ((mem_nonzeroLocus_iff_pull _ φ z hk).1 (hφ z)),
        and_iff_left ((mem_nonzeroLocus_iff_pull _ _ z hk').1 (hz z))]
    · rw [ratio_gs hr φ z (hφ z) hk a, ratio_gs hr φ z (hφ z) hk b, ratio_gs hr' _ z (hz z) hk' a,
        ratio_gs hr' _ z (hz z) hk' b, e, e]
      ring

theorem exists_unit {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) (k : H.ι)
    (k' : H'.ι) : ∃ u : Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ, ∀ j z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gm (𝟙 X') z _ u).val * gs (𝟙 X') z _ ((s' j).f k') := by
  let V : X'.Opens := (H.pull φ).U (fun _ => k) ⊓ H'.U k'
  let W : Fin (n + 1) → X'.Opens := fun i => V ⊓ nonzeroLocus (s' i)
  have l₁ : ∀ i, W i ≤ φ ⁻¹ᵁ H.U k := fun i x hx => mem_pull.1 hx.1.1
  have l₂ : ∀ i, W i ≤ H'.U k' := fun i x hx => hx.1.2
  have un : ∀ i y, y ∈ W i → IsUnit (gs (𝟙 X') y _ ((s' i).f k')) := fun i y hy =>
    (mem_nonzeroLocus_iff_isUnit _ (l₂ i hy)).1 hy.2
  have hu : ∀ i, IsUnit (resG X' (l₂ i) ((s' i).f k')) := fun i =>
    X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := un i y hy
      rw [← gs_res (𝟙 X') y (l₂ i) hy, gs_eq _ y _ hy] at this
      exact this
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(X', W i), ∀ j (y : X') i, y ∈ W i →
      gs φ y _ ((s j).f k) = gs (𝟙 X') y _ (v i) * gs (𝟙 X') y _ ((s' j).f k') := by
    refine ⟨fun i => resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val, fun j y i hy => ?_⟩
    have e : gs (𝟙 X') y _ (resG X' (l₁ i) ((φ.app _).hom ((s i).f k)) * ((hu i).unit⁻¹).val) *
        gs (𝟙 X') y _ ((s' i).f k') = gs φ y _ ((s i).f k) := by
      rw [← gs_res (𝟙 X') y (l₂ i) hy ((s' i).f k'), ← gs_mul _ y _ hy, _root_.mul_assoc, (hu i).val_inv_mul,
        _root_.mul_one, gs_res _ y _ hy, gs_pull (𝟙 X') φ y _ (l₁ i hy), Category.id_comp]
    refine (un i y hy).mul_right_cancel ?_
    rw [(h y).2 j i k k' (l₁ i hy) (l₂ i hy), ← e]
    ring
  have cov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    exact ⟨i, hy, hi⟩
  obtain ⟨c, hc', -⟩ := DVR.sec_glue V W (fun _ => inf_le_left) (fun y hy => Opens.mem_iSup.2 (cov y hy)) v
    (fun a b => fn_ext fun y hy => by
      rw [gs_res _ y _ hy, gs_res _ y _ hy]
      exact (un a y hy.1).mul_right_cancel ((hv a y a hy.1).symm.trans (hv a y b hy.2)))
  have hcv : ∀ j y, y ∈ V → gs φ y _ ((s j).f k) = gs (𝟙 X') y V c * gs (𝟙 X') y _ ((s' j).f k') :=
    fun j y hy => by
      obtain ⟨i, hi⟩ := cov y hy
      rw [hv j y i hi, ← hc' i, gs_res _ y _ hi]
  have uc : IsUnit c := X'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨i, hi⟩ := cov y hy
    have := (mem_nonzeroLocus_iff_pull _ φ y (l₁ i hi)).1 (((h y).1 i).2 hi.2)
    rw [hcv i y hy] at this
    have := isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at this
    exact this
  refine ⟨uc.unit, fun j z hk hk' => ?_⟩
  have hz : z ∈ V := ⟨mem_pull.2 hk, hk'⟩
  rw [← gs_unit _ z V hz]
  exact hcv j z hz

theorem exists_iso {φ : X' ⟶ X} (h : Propor s s' φ (𝟙 X')) (hc : ⨆ i, nonzeroLocus (s' i) = ⊤) :
    ∃ w : LB.Iso H' (H.pull φ), w.IsGen ∧ ∀ j z k k', φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ ((s j).f k) = (gw w (𝟙 X') z k k').val * gs (𝟙 X') z _ ((s' j).f k') := by
  choose u hu using fun k k' => exists_unit h hc k k'
  refine ⟨⟨fun p => u (p.1 PUnit.unit) p.2⟩, ?_, fun j z k k' hk hk' => hu k k' j z hk hk'⟩
  rintro ⟨J, k⟩ ⟨J', k'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have this : gm (𝟙 X') x _ (u (J PUnit.unit) k) = gm (𝟙 X' ≫ φ) x _ (H.g (J PUnit.unit) (J' PUnit.unit)) *
      (gm (𝟙 X') x _ (H'.g k k'))⁻¹ * gm (𝟙 X') x _ (u (J' PUnit.unit) k') := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    have e := hu _ k i x hj hx.1.2
    rw [gs_compat (s i) φ x hj hj', gs_compat (s' i) (𝟙 X') x hx.1.2 hx.2.2, hu _ k' i x hj' hx.2.2,
      ← _root_.mul_assoc, ← _root_.mul_assoc] at e
    have e' := ((mem_nonzeroLocus_iff_isUnit _ hx.2.2).1 hi).mul_right_cancel e
    rw [Category.id_comp, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact Units.ext e'.symm
  rw [← gm_div_g (𝟙 X') x _ _ k k' hj hj' hx.1.2 hx.2.2] at this
  exact (gm_res _ x _ hx _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

end MapToProj

open MapToProj in

theorem exists_hom_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → (⨆ i, nonzeroLocus (s' i) = ⊤) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f') ((H').U k)) (fun j => (s' j).f k) (F) = 0)) → ∃ (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), φ ≫ f = f' ∧ w.IsGen ∧ (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) := by
  intro R _ X f H n s _ ⟨hc, hs⟩ X' f' H' s' _ hc' hv
  choose ha r hr hsur using hs
  have hv' : ∀ d, vanishingForms f s d ⊆ vanishingForms f' s' d := fun d F hF => ⟨hF.1, hv d F hF.1 hF.2⟩
  choose r' hr' using exists_isRatioFamily s'
  choose φ hf hφ using fun i => exists_local f f' (ha i) (hr i) (hsur i) (hr' i) (ker_le f f' hc ha r hr hv' i (hr' i))
  let 𝒰 := X'.openCoverOfIsOpenCover (fun i => nonzeroLocus (s' i)) hc'
  have hcomp : ∀ i j : Fin (n + 1), pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ φ i =
      pullback.snd _ _ ≫ φ j := fun i j =>
    ((hφ i).comp _).unique f (by rw [pullback.condition]; exact (hφ j).comp _)
      (by rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]) (ha i) (hr i) (hsur i)
      fun z => (pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι z).2
  have hΦ : ∀ i : Fin (n + 1), (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms φ hcomp = φ i :=
    fun i => 𝒰.ι_glueMorphisms φ hcomp i
  have hP : Propor s s' (𝒰.glueMorphisms φ hcomp) (𝟙 X') := Propor.of_local fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc'.ge (Set.mem_univ x))
    exact ⟨_, hi, by rw [hΦ, Category.comp_id]; exact hφ i⟩
  obtain ⟨w, hw, H⟩ := exists_iso hP hc'
  refine ⟨_, w, 𝒰.hom_ext _ _ fun i => ?_, hw, H⟩
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (hΦ i))).trans (hf i)

end GlobalTheory
