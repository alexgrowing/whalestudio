import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AppLEBasicOpenIsStandardSmooth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualElements
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

open GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

variable {R C D : Type} [CommRing R] [CommRing C] [CommRing D]

theorem surj_fstC (q : Sp (DualNumber C)) :
    ∃ p : Sp C, spMap (TrivSqZeroExt.fstHom C C C).toRingHom p = q := by
  refine ⟨PrimeSpectrum.comap (algebraMap C (DualNumber C)) q, ?_⟩
  show PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom
    (PrimeSpectrum.comap (algebraMap C (DualNumber C)) q) = q
  apply PrimeSpectrum.ext
  ext x
  have hn : TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
    have h2 : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd = 0 := by simp
    have : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
      rw [h2]; exact zero_mem _
    exact (q.isPrime.mem_or_mem this).elim id id
  have hx : x = algebraMap C (DualNumber C) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  show algebraMap C (DualNumber C) x.fst ∈ q.asIdeal ↔ x ∈ q.asIdeal
  constructor
  · intro h; rw [hx]; exact add_mem h hn
  · intro h
    have : algebraMap C (DualNumber C) x.fst = x - TrivSqZeroExt.inr x.snd := eq_sub_of_add_eq hx.symm
    rw [this]; exact sub_mem h hn

theorem le_dual {X : Scheme.{0}} {v : Sp (DualNumber C) ⟶ X} {x : Sp C ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v = x) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro q _
  obtain ⟨p, rfl⟩ := surj_fstC q
  subst h
  have h1 := hx (Set.mem_univ p)
  change (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v) p ∈ U at h1
  change v _ ∈ U
  rwa [Scheme.Hom.comp_apply] at h1

theorem spMap_comp' (β : R →+* C) (κ : C →+* D) : spMap (κ.comp β) = spMap κ ≫ spMap β := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp (β : R →+* C) (κ : C →+* D) : dualMap (κ.comp β) = (dualMap κ).comp (dualMap β) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

variable (G : Over (Sp R)) [GrpObj G]

abbrev ptU (β : R →+* C) : Sp C ⟶ G.left := spMap β ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left

variable {G} {E : Type} [AddCommGroup E] [Module R E]

abbrev ptV (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) : Sp (DualNumber C) ⟶ G.left :=
  spMap (dualMap β) ≫ (M.pt w).left

theorem ptU_over (β : R →+* C) : ptU G β ≫ G.hom = spMap β := by
  have e : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 (Sp R) := Over.w _
  rw [Category.assoc, e, Category.comp_id]

theorem ptV_over (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) :
    ptV M β w ≫ G.hom = spMap ((algebraMap C (DualNumber C)).comp β) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id, ← spMap_comp']
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

theorem ptV_fst (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) :
    spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ ptV M β w = ptU G β := by
  rw [ptU, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap β x) = β (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem one_left_comp (β : R →+* C) (θ : C →+* ℂ) :
    (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left = spMap θ ≫ ptU G β := by
  rw [one_left_spMap, spMap_comp', Category.assoc]

theorem le_one_left (β : R →+* C) (θ : C →+* ℂ) {V : G.left.Opens} (h : ⊤ ≤ ptU G β ⁻¹ᵁ V) :
    ⊤ ≤ (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left ⁻¹ᵁ V := by
  rw [one_left_comp]
  exact fun p _ => h (x := spMap θ p) trivial

theorem val_one_left (β : R →+* C) (θ : C →+* ℂ) {V : G.left.Opens} (h : ⊤ ≤ ptU G β ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    valAt' (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left V f = θ (valR (ptU G β) V f) := by
  rw [one_left_comp, valAt'_eq_valR, valR_spMap _ _ _ h]

theorem snd_val_comp (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (θ : C →+* ℂ) (w : E) {V : G.left.Opens}
    (h : ⊤ ≤ ptV M β w ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    TrivSqZeroExt.snd (valR (spMap (dualMap (θ.comp β)) ≫ (M.pt w).left) V f) =
      θ (TrivSqZeroExt.snd (valR (ptV M β w) V f)) := by
  rw [dualMap_comp, spMap_comp', Category.assoc, valR_spMap _ _ _ h]
  simp [dualMap]

theorem fst_val (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) {V : G.left.Opens}
    (h : ⊤ ≤ ptV M β w ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    TrivSqZeroExt.fst (valR (ptV M β w) V f) = valR (ptU G β) V f := by
  have := valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom (ptV M β w) V h f
  rw [ptV_fst] at this
  exact this.symm

theorem exists_lift (r : R) (θ : R →+* ℂ) (h : θ r ≠ 0) :
    ∃ θ' : Localization.Away r →+* ℂ, θ'.comp (algebraMap R (Localization.Away r)) = θ :=
  ⟨IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h), IsLocalization.Away.lift_comp r _⟩

theorem res_cst {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (cst p U a) = cst p V a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

theorem isStandardSmooth_basicOpen {X : Scheme.{0}} (p : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U)
    (h : (cst p U).IsStandardSmooth) (s : Γ(X, U)) : (cst p (X.basicOpen s)).IsStandardSmooth := by
  have := hU.isLocalization_basicOpen s
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen s)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
  have h2 := RingHom.IsStandardSmooth.comp (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 0 _ h1) h
  have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen s)).comp (cst p U) = cst p (X.basicOpen s) :=
    RingHom.ext fun a => res_cst p (X.basicOpen_le s) a
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

open GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

theorem exists_coords : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (ρ : R), IsAffineOpen V ∧ φ ρ ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    (∀ θ : R →+* ℂ, θ ρ ≠ 0 → ⊤ ≤ (1 : Over.mk (spMap θ) ⟶ G).left ⁻¹ᵁ V ∧ (∀ c, valAt' (1 : Over.mk (spMap θ) ⟶ G).left V (t c) = 0) ∧
      ∀ a c, TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V (t c)) = if a = c then 1 else 0) ∧
    ∀ f : Γ(G.left, V), ∃ (u : R) (k : ℕ), ∀ θ : R →+* ℂ, θ ρ ≠ 0 → valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * θ ρ ^ k = θ u := by
  intro R _ G _ g M φ hs
  obtain ⟨V₁, r, hV₁, hφr, hss, hle⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.exists_chart R G φ hs
  let β : R →+* Localization.Away r := algebraMap R (Localization.Away r)
  obtain ⟨φ', rfl⟩ : ∃ φ' : Localization.Away r →+* ℂ, φ'.comp β = φ := exists_lift r φ hφr
  have hle' : ⊤ ≤ ptU G β ⁻¹ᵁ V₁ := hle
  letI alg : Algebra R Γ(G.left, V₁) := (cst G.hom V₁).toAlgebra
  have hv : ∀ a : Fin g, ⊤ ≤ ptV M β (Pi.single a 1) ⁻¹ᵁ V₁ := fun a => le_dual (ptV_fst M β _) hle'
  let E := evalHom (ptU G β) V₁ hle'
  let v : Fin g → (Γ(G.left, V₁) →+* DualNumber (Localization.Away r)) :=
    fun a => evalHom (ptV M β (Pi.single a 1)) V₁ (hv a)
  have hEv : ∀ f, E f = valR (ptU G β) V₁ f := fun f => (valR_eq _ _ hle' f).symm
  have hvv : ∀ a f, v a f = valR (ptV M β (Pi.single a 1)) V₁ f := fun a f => (valR_eq _ _ (hv a) f).symm
  have h1 : ∀ x : R, E (algebraMap R Γ(G.left, V₁) x) = β x :=
    fun x => valR_cst G.hom V₁ β (ptU G β) (ptU_over β) hle' x
  have h2 : ∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R Γ(G.left, V₁) x)) = 0 := fun a x => by
    have := valR_cst G.hom V₁ ((algebraMap _ (DualNumber (Localization.Away r))).comp β)
      (ptV M β (Pi.single a 1)) (ptV_over M β _) (hv a) x
    show TrivSqZeroExt.snd (evalHom (ptV M β (Pi.single a 1)) V₁ (hv a) (cst G.hom V₁ x)) = 0
    rw [this]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have h3 : ∀ a x, TrivSqZeroExt.fst (v a x) = E x := fun a x => by
    rw [hvv, hEv, fst_val M β _ (hv a)]
  have h4 : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ' (TrivSqZeroExt.snd (v a x)) = 0) → c = 0 := by
    intro c hc
    obtain ⟨c₀, -, hu⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis R G g M (φ'.comp β) hs V₁ hV₁ (le_one_left β φ' hle') 0
      (fun _ => rfl) (fun f f' => by simp)
    have e1 := hu c fun f => by
      have := hc f
      simp only [hvv] at this
      simp only [snd_val_comp M β φ' _ (hv _)]
      exact this.symm
    have e2 := hu 0 fun f => by simp
    exact e1.trans e2.symm
  obtain ⟨ρ', t', hρ', hE, hvt⟩ := GlobalTheory.CompanionTheory.ExpChart.DualElements.exists_dual_elements R Γ(G.left, V₁) r g E v φ' h1 h2 h3 h4
  let s : Γ(G.left, V₁) := cst G.hom V₁ (r * ρ')
  have hVle : G.left.basicOpen s ≤ V₁ := G.left.basicOpen_le s
  let res : Γ(G.left, V₁) →+* Γ(G.left, G.left.basicOpen s) := (G.left.presheaf.map (homOfLE hVle).op).hom
  have hloc := hV₁.isLocalization_basicOpen s
  have hunit : IsUnit (res s) := IsLocalization.Away.algebraMap_isUnit s
  have hfac : res s = res (cst G.hom V₁ r) * res (cst G.hom V₁ ρ') := by
    show res (cst G.hom V₁ (r * ρ')) = _
    rw [map_mul, map_mul]
  obtain ⟨w, hw⟩ : ∃ w, res (cst G.hom V₁ ρ') * w = 1 :=
    (isUnit_of_mul_isUnit_right (hfac ▸ hunit)).exists_right_inv
  have key : ∀ θ' : Localization.Away r →+* ℂ, (θ'.comp β) (r * ρ') ≠ 0 →
      ⊤ ≤ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left ⁻¹ᵁ G.left.basicOpen s ∧
      (∀ f, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) = θ' (E f)) ∧
      (∀ a b, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a * b) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a *
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) b) ∧
      (∀ a (n : ℕ), valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a ^ n) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a ^ n) ∧
      θ' (β ρ') * valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) w = 1 := by
    intro θ' hθ
    have hx1 := le_one_left β θ' hle'
    have hx : ⊤ ≤ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left ⁻¹ᵁ G.left.basicOpen s :=
      (le_basicOpen_iff _ hx1 s).2 (by
        show valAt' _ V₁ (cst G.hom V₁ (r * ρ')) ≠ 0
        rw [val_cst V₁ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G) hx1]
        exact hθ)
    have hval : ∀ f, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) = θ' (E f) := by
      intro f
      have e : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) =
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left V₁ f := valR_res _ hVle f hx
      rw [e, val_one_left β θ' hle', hEv]
    have hmul : ∀ a b, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a * b) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a *
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) b := fun a b => by
      simp only [valAt'_eq_valR, valR_eq _ _ hx, map_mul]
    refine ⟨hx, hval, hmul, fun a n => ?_, ?_⟩
    · simp only [valAt'_eq_valR, valR_eq _ _ hx, map_pow]
    · have e := congrArg (valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s)) hw
      rw [hmul, hval] at e
      have e1 : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) 1 = 1 := by
        simp only [valAt'_eq_valR, valR_eq _ _ hx, map_one]
      rw [e1] at e
      have e2 : E (cst G.hom V₁ ρ') = β ρ' := h1 ρ'
      rwa [e2] at e
  have hsplit : ∀ θ : R →+* ℂ, θ (r * ρ') ≠ 0 → ∃ θ' : Localization.Away r →+* ℂ, θ'.comp β = θ :=
    fun θ hθ => exists_lift r θ (left_ne_zero_of_mul (by rwa [map_mul] at hθ))
  refine ⟨G.left.basicOpen s, fun c => res (t' c) * w, r * ρ', hV₁.basicOpen s, ?_,
    isStandardSmooth_basicOpen G.hom hV₁ hss s, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hφr hρ'
  · intro θ hθ
    obtain ⟨θ', rfl⟩ := hsplit θ hθ
    obtain ⟨hx, hval, hmul, -, hwv⟩ := key θ' hθ
    refine ⟨hx, fun c => ?_, fun a c => ?_⟩
    · beta_reduce
      rw [hmul, hval, hE, map_zero, zero_mul]
    · beta_reduce
      obtain ⟨D, hD, hL⟩ := tan_der (tan_base M (θ'.comp β) (Pi.single a 1)) hx
      have hy : ⊤ ≤ (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) ⁻¹ᵁ G.left.basicOpen s :=
        (le_preimage_dual_iff (tan_base M (θ'.comp β) (Pi.single a 1)) _).2 hx
      have e : valR (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) (G.left.basicOpen s) (res (t' c)) =
          valR (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) V₁ (t' c) := valR_res _ hVle _ hy
      have e' : D (res (t' c)) = θ' (TrivSqZeroExt.snd (v a (t' c))) := by
        rw [hD, e, snd_val_comp M β θ' _ (hv a), hvv]
      rw [← hD, hL, hval, hE, map_zero, zero_mul, zero_add, e', hvt]
      split_ifs
      · rw [mul_comm]; exact hwv
      · simp
  · intro f
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj s f
    obtain ⟨l, u, hu⟩ := IsLocalization.Away.surj r (E a)
    refine ⟨u * ρ' ^ l, m + l, fun θ hθ => ?_⟩
    obtain ⟨θ', rfl⟩ := hsplit θ hθ
    obtain ⟨hx, hval, hmul, hpow, -⟩ := key θ' hθ
    have hs' : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res s) =
        (θ'.comp β) (r * ρ') := by
      rw [hval]
      have e2 : E (cst G.hom V₁ (r * ρ')) = β (r * ρ') := h1 _
      show θ' (E (cst G.hom V₁ (r * ρ'))) = _
      rw [e2]
      rfl
    have e1 : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) f *
        ((θ'.comp β) (r * ρ')) ^ m = θ' (E a) := by
      rw [← hs', ← hpow, ← hmul, ← hval]
      exact congrArg (valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s)) ha
    have e2 : θ' (E a) * θ' (β r) ^ l = θ' (β u) := by
      rw [← map_pow, ← map_mul]
      exact congrArg θ' hu
    have e3 : (θ'.comp β) (r * ρ') = θ' (β r) * θ' (β ρ') := by
      simp only [RingHom.comp_apply, map_mul]
    have e4 : (θ'.comp β) (u * ρ' ^ l) = θ' (β u) * θ' (β ρ') ^ l := by
      simp only [RingHom.comp_apply, map_mul, map_pow]
    rw [e4, ← e2, ← e1, e3]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords
