import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

namespace GlobalTheory

namespace FibreDeriv

variable {g : ℕ} {X Y : Scheme.{0}}

def jet (w : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : DualNumber ℂ :=
  TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 w)

theorem fst_jet (w : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : (jet w F).fst = F 0 := by simp [jet]

theorem snd_jet (w : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : (jet w F).snd = fderiv ℂ F 0 w := by simp [jet]

theorem jet_congr (w : Fin g → ℂ) {F F' : (Fin g → ℂ) → ℂ} (h : F =ᶠ[𝓝 0] F') : jet w F = jet w F' := by
  rw [jet, jet, h.fderiv_eq, h.eq_of_nhds]

theorem jet_const (w : Fin g → ℂ) (a : ℂ) : jet w (fun _ => a) = algebraMap ℂ (DualNumber ℂ) a := by
  ext <;> simp [fst_jet, snd_jet, TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_add (w : Fin g → ℂ) {F F' : (Fin g → ℂ) → ℂ} (h : DifferentiableAt ℂ F 0) (h' : DifferentiableAt ℂ F' 0) :
    jet w (fun z => F z + F' z) = jet w F + jet w F' := by
  ext <;> simp [fst_jet, snd_jet, fderiv_fun_add h h']

theorem jet_neg (w : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : jet w (fun z => - F z) = - jet w F := by
  ext <;> simp [fst_jet, snd_jet, fderiv_fun_neg]

theorem jet_mul (w : Fin g → ℂ) {F F' : (Fin g → ℂ) → ℂ} (h : DifferentiableAt ℂ F 0) (h' : DifferentiableAt ℂ F' 0) :
    jet w (fun z => F z * F' z) = jet w F * jet w F' := by
  ext
  · simp [fst_jet]
  · simp [fst_jet, snd_jet, fderiv_fun_mul h h', mul_comm]

def evEps (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : Γ(X, U) →+* DualNumber ℂ :=
  (v.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom

theorem evEps_appLE (v : Sp (DualNumber ℂ) ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evEps v V hV ((φ.appLE U V e).hom f) = evEps (v ≫ φ) U hU f := by
  simp only [evEps, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem evEps_res (v : Sp (DualNumber ℂ) ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V)
    (hU : ⊤ ≤ v ⁻¹ᵁ U) : evEps v V hV (resG X h f) = evEps v U hU f := by
  simp only [evEps, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  change (v.appLE V ⊤ hV).hom ((X.presheaf.map (homOfLE h).op).hom f) = _
  rw [← CommRingCat.comp_apply (X.presheaf.map _), Scheme.Hom.map_appLE]

theorem fst_evEps (v : Sp (DualNumber ℂ) ⟶ X) (x : Sp ℂ ⟶ X)
    (hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    (evEps v U h f).fst = valAt' x U f := by
  subst hx
  rw [← valAt'_appLE _ v U ⊤ h f le_top, valAt'_eq_valAt _ le_top]
  have := congrArg (fun k => k.hom ((v.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this.symm

theorem evEps_spMap (a : Γ(Sp ℂ, ⊤)) (h) :
    evEps (spMap (algebraMap ℂ (DualNumber ℂ))) ⊤ h a =
      algebraMap ℂ (DualNumber ℂ) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom a) := by
  have := congrArg (fun k => k.hom a)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this

theorem top_le_preimage_eps (v : Sp (DualNumber ℂ) ⟶ X) (x : Sp ℂ ⟶ X)
    (hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  subst hx
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro q
    have : q ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
      intro b hb
      have hb' : b.fst = 0 := hb
      refine q.2.mem_of_pow_mem 2 ?_
      have : b ^ 2 = 0 := by
        ext <;> simp [pow_two, hb']
      rw [this]
      exact zero_mem _
    exact this
  obtain ⟨q, rfl⟩ := hs p
  exact h (Set.mem_univ q)

theorem isDerivAt0_iff (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 e w v ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
      ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), evEps v U h f = jet w (fun z => valAt' (e z) U f) := by
  refine and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_
  refine ⟨fun H => TrivSqZeroExt.ext ?_ ?_, fun H => ?_⟩
  · rw [fst_jet, fst_evEps v _ h0]
  · rw [snd_jet]; exact H
  · rw [← snd_jet, ← H]; rfl

theorem isDerivAt0_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (H : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at H ⊢
  refine ⟨by rw [← Category.assoc, H.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := by rwa [Scheme.Hom.comp_preimage] at h
  rw [← evEps_appLE v φ U (φ ⁻¹ᵁ U) le_rfl f h' h, H.2, ← Scheme.Hom.app_eq_appLE]
  simp only [valAt'_comp]

theorem isDerivAt0_of_affine {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0) {V : X.Opens} (hV : IsAffineOpen V)
    (hv : ⊤ ≤ v ⁻¹ᵁ V)
    (H : ∀ a : Γ(X, V), DifferentiableAt ℂ (fun z => valAt' (e z) V a) 0 ∧
      evEps v V hv a = jet w (fun z => valAt' (e z) V a)) : IsDerivAt0 e w v := by
  rw [isDerivAt0_iff]
  refine ⟨h0, fun U hU f => ?_⟩
  obtain ⟨h, hhU, hh₀⟩ := hV.exists_basicOpen_le (V := U)
    ⟨_, (top_le_preimage_iff_mem _ U).1 ((top_le_preimage_eps v _ h0 U).1 hU)⟩
    ((top_le_preimage_iff_mem _ V).1 ((top_le_preimage_eps v _ h0 V).1 hv))
  have hD₀ : ⊤ ≤ e 0 ⁻¹ᵁ X.basicOpen h := (top_le_preimage_iff_mem _ _).2 hh₀
  have hDv : ⊤ ≤ v ⁻¹ᵁ X.basicOpen h := (top_le_preimage_eps v _ h0 _).2 hD₀
  have hn₀ : valAt' (e 0) V h ≠ 0 := (top_le_preimage_basicOpen_iff _ V h).1 hD₀
  have hev : ∀ᶠ z in 𝓝 0, ⊤ ≤ e z ⁻¹ᵁ X.basicOpen h := by
    filter_upwards [(H h).1.continuousAt.eventually_ne hn₀] with z hz
    exact (top_le_preimage_basicOpen_iff _ V h).2 hz
  have hloc := hV.isLocalization_basicOpen h
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers h) (resG X hhU f)
  have ha' : resG X hhU f * resG X (X.basicOpen_le h) (h ^ n) = resG X (X.basicOpen_le h) a := ha
  have hb₀ : valAt' (e 0) V (h ^ n) ≠ 0 := by
    rw [valAt'_pow _ (top_le_preimage_mono _ (X.basicOpen_le h) hD₀)]
    exact pow_ne_zero n hn₀
  have hmul : (fun z => valAt' (e z) U f * valAt' (e z) V (h ^ n)) =ᶠ[𝓝 0] fun z => valAt' (e z) V a := by
    filter_upwards [hev] with z hz
    rw [← valAt'_res _ hhU f hz, ← valAt'_res _ (X.basicOpen_le h) (h ^ n) hz, ← valAt'_mul, ha', valAt'_res _ _ _ hz]
  have hf : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 := by
    refine ((H a).1.mul ((H (h ^ n)).1.inv hb₀)).congr_of_eventuallyEq ?_
    filter_upwards [hmul, (H (h ^ n)).1.continuousAt.eventually_ne hb₀] with z h1 h2
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [eq_mul_inv_iff_mul_eq₀ h2]
    exact h1
  have hu : IsUnit (jet w fun z => valAt' (e z) V (h ^ n)) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_jet]
    exact hb₀.isUnit
  refine hu.mul_right_cancel ?_
  rw [← jet_mul w hf (H _).1, jet_congr w hmul, ← (H a).2, ← (H _).2, ← evEps_res v hhU f hDv hU,
    ← evEps_res v (X.basicOpen_le h) _ hDv hv, ← evEps_res v (X.basicOpen_le h) a hDv hv, ← map_mul, ha']

theorem isDerivAt0_of_isPullback {Z : Scheme.{0}} {φ : Y ⟶ Z} {s : Y ⟶ Sp ℂ} {p : Z ⟶ X} {y : Sp ℂ ⟶ X}
    (H : IsPullback φ s p y) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hs : ∀ z, e z ≫ s = 𝟙 _)
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ))) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  rw [isDerivAt0_iff] at hd
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := by
    refine H.hom_ext (by rw [Category.assoc, hd.1]) ?_
    rw [Category.assoc, hv, hs, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  obtain ⟨S, hS, hyS, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyS' : ⊤ ≤ y ⁻¹ᵁ S := (top_le_preimage_iff_mem y S).2 hyS
  have hey : (e 0 ≫ φ) ≫ p = y := by rw [Category.assoc, H.w, ← Category.assoc, hs, Category.id_comp]
  obtain ⟨U, hU, hxU, hUS⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := p ⁻¹ᵁ S)
    (x := (e 0 ≫ φ) (default : PrimeSpectrum ℂ))
    ((top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ p S).1 (hey.symm ▸ hyS')))
  have hUS' : U ≤ p ⁻¹ᵁ S := hUS
  have hVdef : φ ⁻¹ᵁ U = φ ⁻¹ᵁ U ⊓ s ⁻¹ᵁ ⊤ := by simp
  have hV : IsAffineOpen (φ ⁻¹ᵁ U) := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU
    have : IsAffine _ := hS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS (isAffineOpen_top _) hU)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hU₀ : ⊤ ≤ (e 0 ≫ φ) ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hV₀ : ⊤ ≤ e 0 ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_comp _ φ U).1 hU₀
  have hVv : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_eps v _ h0 _).2 hV₀
  have hUv : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
  have hN := (hol U 0).1.mem_nhds (x := 0) ⟨trivial, hU₀⟩
  have hev : ∀ᶠ z in 𝓝 0, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    filter_upwards [hN] with z hz using (top_le_preimage_comp _ φ U).1 hz.2
  have hconst : ∀ (a : Γ(Y, φ ⁻¹ᵁ U)) (c : ℂ), (∀ z, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) → valAt' (e z) _ a = c) →
      evEps v _ hVv a = algebraMap ℂ _ c → DifferentiableAt ℂ (fun z => valAt' (e z) _ a) 0 ∧
      evEps v _ hVv a = jet w (fun z => valAt' (e z) _ a) := fun a c h1 h2 => by
    have h3 : (fun z => valAt' (e z) _ a) =ᶠ[𝓝 0] fun _ => c := hev.mono h1
    exact ⟨(differentiableAt_const c).congr_of_eventuallyEq h3, by rw [jet_congr w h3, jet_const, h2]⟩
  refine isDerivAt0_of_affine h0 hV hVv fun a => ?_
  have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have h3 : (fun z => valAt' (e z) _ ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b)) =ᶠ[𝓝 0]
          fun z => valAt' (e z ≫ φ) U b := hev.mono fun z hz => valAt'_appLE _ _ _ _ _ _ hz
      exact ⟨((hol U b).2.differentiableAt hN).congr_of_eventuallyEq h3,
        by rw [jet_congr w h3, ← hd.2 U hUv b, evEps_appLE]⟩
    · refine hconst _ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom b) (fun z hz => ?_) ?_
      · rw [valAt'_appLE _ _ _ _ _ _ hz, hs]
        have := valAt'_id_top ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom b)
        simpa using this
      · rw [evEps_appLE v s ⊤ _ _ b hVv le_top]
        have := evEps_spMap b le_top
        rw [← this]
        congr 1
        congr 1
  | zero => exact hconst _ 0 (fun z _ => valAt'_zero _ _) (by simp)
  | one => exact hconst _ 1 (fun z hz => valAt'_one _ hz) (by simp)
  | add x y _ _ hx hy =>
    simp only [valAt'_add]
    exact ⟨hx.1.add hy.1, by rw [jet_add w hx.1 hy.1, map_add, hx.2, hy.2]⟩
  | neg x _ hx =>
    simp only [valAt'_neg]
    exact ⟨hx.1.neg, by rw [jet_neg w, map_neg, hx.2]⟩
  | mul x y _ _ hx hy =>
    simp only [valAt'_mul]
    exact ⟨hx.1.mul hy.1, by rw [jet_mul w hx.1 hy.1, map_mul, hx.2, hy.2]⟩

end FibreDeriv

open FibreDeriv in

theorem isDerivAt0_fibre :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Y : Scheme.{0}) (φ : Y ⟶ G.left) (s : Y ⟶ Sp ℂ) (e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)), IsPullback φ s G.hom y → (∀ z, e₁ z ≫ φ = (e z).left ∧ e₁ z ≫ s = 𝟙 _) → IsHolTo Set.univ (fun z => (e z).left) → ((∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ((∀ w, ∃! v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧ IsDerivAt0 e₁ w v) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e₁ 0 → ∃! w, IsDerivAt0 e₁ w v) := by
  intro X G y g e Y φ s e₁ H he hol hd
  have hee : (fun z => (e z).left) = fun z => e₁ z ≫ φ := funext fun z => (he z).1.symm
  have hs : ∀ z, e₁ z ≫ s = 𝟙 _ := fun z => (he z).2
  have key : ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Y), v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
      (IsDerivAt0 e₁ w v ↔ IsDerivAt0 (fun z => (e z).left) w (v ≫ φ)) := fun w v hv => by
    constructor
    · intro h
      have := isDerivAt0_comp h φ
      rw [← hee] at this
      exact this
    · intro h
      refine isDerivAt0_of_isPullback H hs ?_ hv ?_
      · rw [← hee]; exact hol
      · rw [← hee]; exact h
  have hw : ∀ v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
      (v ≫ φ) ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y := fun v hv => by
    rw [Category.assoc, H.w, ← Category.assoc, hv]
  refine ⟨fun w => ?_, fun v hv h0 => ?_⟩
  · obtain ⟨u, hu, huniq⟩ := hd.1 w
    have huw : u.left ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y := Over.w u
    refine ⟨H.lift u.left _ huw, ⟨H.lift_snd _ _ _, (key w _ (H.lift_snd _ _ _)).2 ?_⟩, fun v hv => ?_⟩
    · rw [H.lift_fst]; exact hu
    · have h1 := huniq (Over.homMk (v ≫ φ) (hw v hv.1)) ((key w v hv.1).1 hv.2)
      refine H.hom_ext ?_ (by rw [H.lift_snd, hv.1])
      rw [H.lift_fst, ← h1]
      rfl
  · have h1 := hd.2 (Over.homMk (v ≫ φ) (hw v hv)) (by
      change _ ≫ v ≫ φ = _
      rw [← Category.assoc, h0, (he 0).1])
    simp only [key _ v hv]
    exact h1

end GlobalTheory
