import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldLiftsAffineCoverSmoothGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleVerticalFieldsEqCoboundaryAddLogDerivStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSExists

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} (h : W₁ ≤ W₀) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h), fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

theorem isField_sub {Z : Scheme.{0}} {W₀ : Z.Opens} {d d' : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) (hd' : IsField W₀ d') : IsField W₀ (fun W f => d W f - d' W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · simp only [hd.1 W hW, hd'.1 W hW]; ring
  · simp only [hd.2.1 W hW, hd'.2.1 W hW]; ring
  · simp only [map_sub, hd.2.2 W W' h hW, hd'.2.2 W W' h hW]

theorem lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := GlobalTheory.T.exists_vectorField_lifts_affine_cover_smooth_group

theorem cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := GlobalTheory.T.cechCocycle_verticalFields_eq_coboundary_add_logDerivatives

theorem exists_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t ⊤ U v D Θ := by
  intro E _ _ _ H X t hP hA hK U n v hv hb D
  obtain ⟨J, W, j, d, hWa, hcov, hWj, hd, hlift⟩ := lifts E H X t U D
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => hcov ▸ le_iSup W i
  have hres : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i)
      ((t.G.hom.appLE U.1 (W i) (hWU i)).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i) (homOfLE (inf_le_left : W i ⊓ W i' ≤ W i)).op)
  have hres' : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i')
      ((t.G.hom.appLE U.1 (W i') (hWU i')).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i') (homOfLE (inf_le_right : W i ⊓ W i' ≤ W i')).op)
  have a1 : ∀ i i' (r : Γ(X, U.1)), d i (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres i i' r, (hd i).2.2 _ _ inf_le_left le_rfl, hlift i (hWU i), hres]
  have a2 : ∀ i i' (r : Γ(X, U.1)), d i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres' i i' r, (hd i').2.2 _ _ inf_le_right le_rfl, hlift i' (hWU i'), hres']
  obtain ⟨Θ, h, hh, hhv, hks⟩ := cocycle E H X t hP hA hK U n v hv hb J W j hWa hcov hWj
    (fun i i' O f => d i O f - d i' O f)
    (fun i i' => isField_sub (isField_mono inf_le_left (hd i)) (isField_mono inf_le_right (hd i')))
    (fun i i' hW r => by
      show d i _ _ - d i' _ _ = 0
      rw [a1, a2, sub_self])
    (fun i i' i'' O _ f => sub_add_sub_cancel _ _ _)
  refine ⟨Θ, J, W, j, fun i O f => d i O f - h i O f, by rw [inf_top_eq]; exact hcov, hWj,
    fun i => isField_sub (hd i) (hh i), fun i hW r => ?_, fun i i' O hO f S _ φ g₀ w hg hO' hw => ?_⟩
  · show d i _ _ - h i _ _ = _
    rw [hlift i hW r, hhv i hW r, sub_zero]
  · have e := hks i i' O hO f S φ g₀ w hg hO' hw
    have hv' : ∀ a b : Γ(t.G.left, O), valR g₀ O (a - b) = valR g₀ O a - valR g₀ O b := fun a b => by
      simp only [valR, dif_pos hO', map_sub]
    show valR g₀ O ((d i O f - h i O f) - (d i' O f - h i' O f)) = _
    rw [show (d i O f - h i O f) - (d i' O f - h i' O f) = (d i O f - d i' O f) - (h i O f - h i' O f) by ring,
      hv', e]
    ring

end GlobalTheory.KSExists
