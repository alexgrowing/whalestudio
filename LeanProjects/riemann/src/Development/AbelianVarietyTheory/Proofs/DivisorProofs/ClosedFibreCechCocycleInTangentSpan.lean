import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZeroStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.FibreSpan

theorem pull_cocycle {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {J : Type} (W : J → Z.Opens) (d : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hd : ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d i i') + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d i' i'') = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d i i'')) :
    ∀ i i' i'', resG Y (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') ((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (d i i')) + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i' ⊓ W i'') (ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i' i'')) = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i ⊓ W i'') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i i'')) := by
  intro i i' i''
  have e0 : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have := congrArg (ι.appLE (W i ⊓ W i' ⊓ W i'') _ e0).hom (hd i i' i'')
  simp only [map_add, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at this
  simp only [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  exact this

theorem sum_divisible_eq_sum_mul {R : Type} [CommRing R] {n : ℕ} (a : R) (x F : Fin n → R) :
    ∑ b, -(a * x b) * F b = -a * ∑ b, x b * F b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

set_option maxHeartbeats 1600000 in

theorem fibre_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ θ : Fin n → Γ(X, U.1), ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A _ ι hpb c hc
  have hκ := GlobalTheory.T.polarisation_logDerivative_cechCocycle E H X t U n δ hδ J W j hW hcov hWU hj
  have hz := GlobalTheory.T.maximalIdeal_element_pullback_closedFibre_zero E H X t U m A ι hpb
  have hind : ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m :=
    fun r h'' hr => GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre E H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A ι hpb r h''
      (fun i i' => by
        rw [map_sum]
        exact (Finset.sum_congr rfl fun b _ => map_mul _ _ _).trans (hr i i'))
  obtain ⟨r, ⟨b₀, hb₀⟩, h', hh⟩ := GlobalTheory.T.closed_fibre_cechCocycles_combination_coefficient_nonunit E H X t hP hA U n v hv hu J W hW hcov hWU m hm A ι hpb
    (Fin.cons (fun i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) (fun b i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)))
    (fun b => Fin.cases (pull_cocycle ι W c hc) (fun b => pull_cocycle ι W _ (hκ b)) b)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh
  have hr0 : r 0 ∉ m := by
    intro h0
    have := hind (fun b => r b.succ) h' (fun i i' => by
      have h1 := hh i i'
      rw [hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) (r 0) h0, zero_mul, zero_add] at h1
      exact h1)
    refine hb₀ ?_
    cases b₀ using Fin.cases with
    | zero => exact h0
    | succ b => exact this b
  have hex := hm.exists_inv hr0
  choose y i₀ hi₀ hy using hex
  refine ⟨fun b => -(y * r b.succ), fun i => (ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y) * h' i, fun i i' => ?_⟩
  have key1 : ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O)
      (x : Γ(X, U.1)), (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom x) =
        ((ι ≫ t.G.hom).appLE U.1 O' (hO'.trans fun _ h => hO h)).hom x := by
    intro O hO O' hO' x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key2 : ∀ (O O' : A.left.Opens) (h : O' ≤ O) (hO : O ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1) (x : Γ(X, U.1)),
      resG A.left h (((ι ≫ t.G.hom).appLE U.1 O hO).hom x) = ((ι ≫ t.G.hom).appLE U.1 O' (h.trans hO)).hom x := by
    intro O O' h hO x
    have e := Scheme.Hom.appLE_map (ι ≫ t.G.hom) hO (homOfLE h).op
    exact congrArg (fun φ => φ.hom x) e
  have hle : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := fun x hx => hWU i hx.1
  have h1 := hh i i'
  have hy' : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y * ((ι ≫ t.G.hom).appLE U.1 _ hle).hom (r 0) = 1 := by
    have := congrArg ((ι ≫ t.G.hom).appLE U.1 _ hle).hom hy
    rw [map_add, map_mul, map_one] at this
    have h0 : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom i₀ = 0 :=
      (key1 (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀).symm.trans
        (hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀ hi₀)
    rw [h0, add_zero] at this
    exact this
  have hA1 : ∀ x : Γ(X, U.1), (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom x) =
      ((ι ≫ t.G.hom).appLE U.1 _ hle).hom x := fun x => key1 _ _ _ _ x
  have hB1 : resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i) ((ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  have hB2 : resG A.left (inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i') ((ι.appLE (W i') (ι ⁻¹ᵁ W i') le_rfl).hom ((t.G.hom.appLE U.1 (W i') (hWU i')).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  rw [map_sub, map_sum]
  simp only [map_neg, map_mul, hA1, hB1, hB2] at h1 ⊢
  rw [sum_divisible_eq_sum_mul]
  linear_combination (((ι ≫ t.G.hom).appLE U.1 _ hle).hom y) * h1 + (-((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i'))) * hy'

end GlobalTheory.FibreSpan
