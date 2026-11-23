import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts
open GlobalTheory.CxForm (relCot dRel)
open Filter Topology

namespace GlobalTheory.CurveDer

def cst (O : (Sp ℂ).Opens) : ℂ →+* Γ(Sp ℂ, O) :=
  (resG (Sp ℂ) le_top).comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

theorem val_cst {O : (Sp ℂ).Opens} (h : ⊤ ≤ O) (z : ℂ) : valAt' (𝟙 (Sp ℂ)) O (cst O z) = z := by
  refine (GlobalTheory.valAt'_res (𝟙 (Sp ℂ)) le_top _ h).trans ?_
  rw [valAt'_eq_valAt _ le_top]
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (GlobalTheory.LB.resG_self _ _)).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply z

theorem ext {O : (Sp ℂ).Opens} {a b : Γ(Sp ℂ, O)}
    (H : ⊤ ≤ O → valAt' (𝟙 (Sp ℂ)) O a = valAt' (𝟙 (Sp ℂ)) O b) : a = b := by
  by_cases h : ⊤ ≤ O
  · obtain rfl := top_le_iff.1 h
    have := H h
    rw [valAt'_eq_valAt _ le_top, valAt'_eq_valAt _ le_top] at this
    have h2 := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective this
    exact (GlobalTheory.LB.resG_self _ a).symm.trans (h2.trans (GlobalTheory.LB.resG_self _ b))
  · obtain rfl : O = ⊥ := by
      refine eq_bot_iff.2 fun p hp => (h fun q _ => ?_).elim
      rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) q p]
    exact Subsingleton.elim _ _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X}
  {x : Sp ℂ ⟶ S} {c : E → (Sp ℂ ⟶ X)}

theorem eventually_le (hc : IsHolTo Set.univ c) {W : X.Opens} (h : ⊤ ≤ c 0 ⁻¹ᵁ W) :
    ∀ᶠ u in 𝓝 (0 : E), ⊤ ≤ c u ⁻¹ᵁ W :=
  mem_of_superset ((hc W 0).1.mem_nhds ⟨trivial, h⟩) fun _ hu => hu.2

theorem differentiableAt (hc : IsHolTo Set.univ c) {W : X.Opens} (h : ⊤ ≤ c 0 ⁻¹ᵁ W) (f : Γ(X, W)) :
    DifferentiableAt ℂ (fun u => valAt' (c u) W f) 0 :=
  (hc W f).2.differentiableAt ((hc W 0).1.mem_nhds ⟨trivial, h⟩)

theorem le_of (h0 : c 0 = x ≫ e) {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ c 0 ⁻¹ᵁ W := by
  rw [h0, top_le_preimage_comp]
  exact top_le_preimage_mono x h hx

theorem val_app {V : S.Opens} (a : Γ(S, V)) :
    valAt' (𝟙 (Sp ℂ)) (x ⁻¹ᵁ V) (x.app V a) = valAt' x V a :=
  (GlobalTheory.valAt'_comp (𝟙 _) x V a).trans (by rw [Category.id_comp])

def der (hc : IsHolTo Set.univ c) (h0 : c 0 = x ≫ e) (hπ : ∀ u, c u ≫ π = x) (v : E) :
    Conormal.Der π e ((Scheme.Modules.pushforward x).obj (SheafOfModules.unit (Sp ℂ).ringCatSheaf)) where
  app {W V} h := AddMonoidHom.mk'
    (fun f => show Γ(Sp ℂ, x ⁻¹ᵁ V) from cst (x ⁻¹ᵁ V) (fderiv ℂ (fun u => valAt' (c u) W f) 0 v)) fun f g => by
      change cst (x ⁻¹ᵁ V) _ = cst (x ⁻¹ᵁ V) _ + cst (x ⁻¹ᵁ V) _
      refine ext fun hx => ?_
      have hW := le_of h0 h hx
      rw [← map_add, val_cst hx, val_cst hx]
      simp only [GlobalTheory.valAt'_add]
      rw [fderiv_fun_add (differentiableAt hc hW f) (differentiableAt hc hW g)]
      rfl
  res_app {W V V'} h h' f := GlobalTheory.LB.resG_resG (X := Sp ℂ) le_top (x.preimage_mono h') _
  app_res {W W' V} h k f := by
    change cst (x ⁻¹ᵁ V) _ = cst (x ⁻¹ᵁ V) _
    refine ext fun hx => ?_
    rw [val_cst hx, val_cst hx, Filter.EventuallyEq.fderiv_eq
      ((eventually_le hc (le_of h0 h hx)).mono fun u hu => GlobalTheory.valAt'_res (c u) k f hu)]
  app_mul {W V} h f g := by
    change cst (x ⁻¹ᵁ V) _ = x.app V _ * cst (x ⁻¹ᵁ V) _ + x.app V _ * cst (x ⁻¹ᵁ V) _
    refine ext fun hx => ?_
    have hW := le_of h0 h hx
    rw [GlobalTheory.valAt'_add, GlobalTheory.valAt'_mul, GlobalTheory.valAt'_mul, val_cst hx, val_cst hx, val_cst hx, val_app, val_app,
      GlobalTheory.valAt'_appLE _ _ _ _ _ _ hx, GlobalTheory.valAt'_appLE _ _ _ _ _ _ hx, ← h0]
    simp only [GlobalTheory.valAt'_mul]
    rw [fderiv_fun_mul (differentiableAt hc hW f) (differentiableAt hc hW g)]
    rfl
  app_base {W V U} h k a := by
    change cst (x ⁻¹ᵁ V) _ = 0
    refine ext fun hx => ?_
    rw [val_cst hx, GlobalTheory.valAt'_zero, Filter.EventuallyEq.fderiv_eq (f := fun _ => valAt' x U a)
      ((eventually_le hc (le_of h0 h hx)).mono fun u hu =>
        (GlobalTheory.valAt'_appLE (c u) π U W k a hu).trans (by rw [hπ]))]
    simp

theorem fderiv_eq_sum (he : e ≫ π = 𝟙 S) (hc : IsHolTo Set.univ c) (h0 : c 0 = x ≫ e) (hπ : ∀ u, c u ≫ π = x)
    {T : S.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ T) {W : X.Opens} (hW : T ≤ e ⁻¹ᵁ W) (F : Γ(X, W)) {ι : Type} (s : Finset ι)
    (α : ι → Γ(S, T)) (W' : ι → X.Opens) (hW' : ∀ a, T ≤ e ⁻¹ᵁ W' a) (G : ∀ a, Γ(X, W' a))
    (H : Conormal.d he hW F = ∑ a ∈ s, α a • Conormal.d he (hW' a) (G a)) :
    fderiv ℂ (fun u => valAt' (c u) W F) 0 =
      ∑ a ∈ s, valAt' x T (α a) • fderiv ℂ (fun u => valAt' (c u) (W' a) (G a)) 0 := by
  ext v
  have H' := congrArg (QCoh.appLinear (der hc h0 hπ v).lift T) H
  rw [map_sum] at H'
  simp only [map_smul] at H'
  have key {W : X.Opens} (hW : T ≤ e ⁻¹ᵁ W) (F : Γ(X, W)) :
      QCoh.appLinear (der hc h0 hπ v).lift T (Conormal.d he hW F) = (der hc h0 hπ v).app hW F :=
    Conormal.Der.lift_d he _ hW F
  simp only [key] at H'
  let δ : Γ((Scheme.Modules.pushforward x).obj (SheafOfModules.unit (Sp ℂ).ringCatSheaf), T) →+ ℂ :=
    AddMonoidHom.mk' (fun t => valAt' (𝟙 (Sp ℂ)) (x ⁻¹ᵁ T) t) (GlobalTheory.valAt'_add _ _)
  have H2 := congrArg δ H'
  rw [map_sum] at H2
  rw [ContinuousLinearMap.sum_apply]
  refine (val_cst hx _).symm.trans (Eq.trans (b := δ ((der hc h0 hπ v).app hW F)) rfl ?_)
  refine H2.trans (Finset.sum_congr rfl fun a _ => ?_)
  change valAt' (𝟙 (Sp ℂ)) (x ⁻¹ᵁ T) (x.app T (α a) * cst (x ⁻¹ᵁ T) _) = _
  rw [GlobalTheory.valAt'_mul, val_cst hx, val_app]
  rfl

theorem fderiv_ev_eq_sum : ∀ {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} (A : Over S) [GrpObj A] (g : ℕ)
    (cv : (Fin g → ℂ) → CxPts (A.hom ≫ p) σ) (hcv : ∀ u, (cv 0).1 ≫ A.hom = (cv u).1 ≫ A.hom),
    IsHolTo Set.univ (fun u => (cv u).1) →
    ∀ (W T : A.left.Opens) (hTW : T ≤ W) (F : Γ(A.left, W)), cv 0 ∈ ptsIn (A.hom ≫ p) σ T →
    ∀ (n : ℕ) (α : Fin n → Γ(A.left, T)) (W' : Fin n → (Limits.pullback A.hom A.hom).Opens)
      (hW' : ∀ a, T ≤ Limits.pullback.diagonal A.hom ⁻¹ᵁ W' a) (G : ∀ a, Γ(Limits.pullback A.hom A.hom, W' a)),
    GlobalTheory.Twist.resM (relCot A.hom) hTW (dRel A.hom W F) =
                 ∑ a, α a • GlobalTheory.Conormal.d (Limits.pullback.diagonal_fst A.hom) (hW' a) (G a) →
    fderiv ℂ (fun u => ev (A.hom ≫ p) σ W F (cv u)) 0 =
      ∑ a, ev (A.hom ≫ p) σ T (α a) (cv 0) •
        fderiv ℂ (fun u => ev _ σ (W' a) (G a) (GlobalTheory.RelCotAb.pairPt A (cv 0) (cv u) (hcv u))) 0 := by
  intro k _ S p σ A _ g cv hcv hol W T hTW F hx n α W' hW' G H
  have hc : IsHolTo Set.univ (fun u => (RelCotAb.pairPt A (cv 0) (cv u) (hcv u)).1) := by
    refine HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback A.hom A.hom) ?_ ?_
    · simp only [RelCotAb.pairPt, Limits.pullback.lift_fst]
      exact HolFibre.isHolTo_const isOpen_univ _
    · simp only [RelCotAb.pairPt, Limits.pullback.lift_snd]
      exact hol
  have h0 : (RelCotAb.pairPt A (cv 0) (cv 0) (hcv 0)).1 = (cv 0).1 ≫ Limits.pullback.diagonal A.hom :=
    Limits.pullback.hom_ext
      ((Limits.pullback.lift_fst _ _ _).trans (by rw [Category.assoc, Limits.pullback.diagonal_fst, Category.comp_id]))
      ((Limits.pullback.lift_snd _ _ _).trans (by rw [Category.assoc, Limits.pullback.diagonal_snd, Category.comp_id]))
  have H' := (Conormal.resM_d (Limits.pullback.diagonal_fst A.hom) _ hTW _).symm.trans H
  have R := fderiv_eq_sum (Limits.pullback.diagonal_fst A.hom) hc h0 (fun u => Limits.pullback.lift_fst _ _ _) hx _ _
    Finset.univ α W' hW' G H'
  simp only [GlobalTheory.valAt'_comp] at R
  simp only [RelCotAb.pairPt, Limits.pullback.lift_snd] at R
  exact R

end GlobalTheory.CurveDer
