import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts

noncomputable section

namespace GlobalTheory.RelExp

section General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.RelChart

private theorem etale_chart_lemma : ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  exact fun m g A R _ _ ψ B φ b₀ e a a_1 a_2 a_3 a_4 =>
    EtaleFamily.exists_holomorphic_sections m g A R ψ B φ b₀ e a a_1 a_2 a_3 a_4

private theorem exists_open_smoothOfRelativeDimension : ∀ (Z X : Scheme.{0}) (p : Z ⟶ X) [Smooth p] (z : Z), ∃ (g : ℕ) (W : Z.Opens), z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
  intro Z X p _ z
  exact H1.exists_dim p z

private theorem chart_lemma_4 : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' :=
  GlobalTheory.RelChart.exists_chart_with_parameters etale_chart_lemma

private theorem valAt'_presheaf_map_eqToHom {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (s : Γ(Y, V')) : valAt' x V ((Y.presheaf.map (eqToHom h).op).hom s) = valAt' x V' s := by
  subst h
  simp

private theorem evalPt_eqToHom {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (hV : ⊤ ≤ v ⁻¹ᵁ V) (hV' : ⊤ ≤ v ⁻¹ᵁ V') (s : Γ(Y, V')) :
    GlobalTheory.TangentOrigin.evalPt v V hV ((Y.presheaf.map (eqToHom h).op).hom s) =
      GlobalTheory.TangentOrigin.evalPt v V' hV' s := by
  subst h
  simp

private theorem app_appIso_inv_eq_presheaf_map {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (s : Γ(W, U')) :
    (W.ι.app (W.ι ''ᵁ U')).hom ((W.ι.appIso U').inv.hom s) =
      ((W : Scheme.{0}).presheaf.map (eqToHom (W.ι.preimage_image_eq U')).op).hom s := by
  rw [← Scheme.Hom.appIso_inv_app]
  rfl

private theorem valAt'_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (x : Sp ℂ ⟶ W)
    (s : Γ(W, U')) : valAt' (x ≫ W.ι) (W.ι ''ᵁ U') ((W.ι.appIso U').inv.hom s) = valAt' x U' s := by
  rw [GlobalTheory.PointUnif.valAt'_comp, app_appIso_inv_eq_presheaf_map, valAt'_presheaf_map_eqToHom]

private theorem preimage_comp_ι_image_eq_preimage {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ W) : (x ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U') = x ⁻¹ᵁ U' := by
  show x ⁻¹ᵁ (W.ι ⁻¹ᵁ (W.ι ''ᵁ U')) = x ⁻¹ᵁ U'
  rw [Scheme.Hom.preimage_image_eq]

private theorem evalPt_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens)
    (v : Sp (DualNumber ℂ) ⟶ W) (h : ⊤ ≤ (v ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U')) (h' : ⊤ ≤ v ⁻¹ᵁ U') (s : Γ(W, U')) :
    GlobalTheory.TangentOrigin.evalPt (v ≫ W.ι) (W.ι ''ᵁ U') h ((W.ι.appIso U').inv.hom s) =
      GlobalTheory.TangentOrigin.evalPt v U' h' s := by
  rw [GlobalTheory.PointUnif.evalPt_comp, app_appIso_inv_eq_presheaf_map]
  exact evalPt_eqToHom v (W.ι.preimage_image_eq U') h h' s

private theorem exists_lift_through_opens_ι {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ (W.ι ''ᵁ U')) : ∃ x' : Sp R ⟶ W, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, -, hb⟩ := hx (show a ∈ (⊤ : (Sp R).Opens) from trivial)
  exact ⟨b, hb⟩

theorem exists_chart_of_smooth (m : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ))
    (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z) [Smooth p] (hB : IsOpen B) (hb₀ : b₀ ∈ B)
    (hy : IsHolTo B y) (hz₀ : z₀ ≫ p = y b₀) :
    ∃ (g : ℕ) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' := by
  obtain ⟨g, W, hzW, hWsm⟩ := exists_open_smoothOfRelativeDimension Z X p (z₀.base default)
  have hz₀W : Set.range z₀.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default, Scheme.Opens.range_ι]
    exact hzW
  obtain ⟨z₀', rfl⟩ : ∃ z₀' : Sp ℂ ⟶ W, z₀' ≫ W.ι = z₀ := ⟨_, IsOpenImmersion.lift_fac _ _ hz₀W⟩
  obtain ⟨U', t', n, f', N, O, σ', hN, hO, hU', hO', hσ', hσN', hinv', hun'⟩ :=
    chart_lemma_4 m g W X (W.ι ≫ p) B y b₀ z₀' hWsm hB hb₀ hy (by rw [← Category.assoc]; exact hz₀)
  refine ⟨g, W.ι ''ᵁ U', fun i => (W.ι.appIso U').inv.hom (t' i), n, fun j => (W.ι.appIso U').inv.hom (f' j), N, O,
    fun q => σ' q ≫ W.ι, hN, hO, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [preimage_comp_ι_image_eq_preimage]
    exact hU'
  · simp only [valAt'_ι_appIso_inv]
    exact hO'
  · exact isHolTo_of_holAt hN fun q hq => HolAt.post ⟨N, hN, hq, hσ'⟩ W.ι
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσN' q hq
    refine ⟨by rw [Category.assoc]; exact h1, by rw [preimage_comp_ι_image_eq_preimage]; exact h2, fun i => ?_⟩
    rw [valAt'_ι_appIso_inv]
    exact h3 i
  · intro b x hxp hxU hxO
    obtain ⟨x', rfl⟩ := exists_lift_through_opens_ι W U' x hxU
    rw [preimage_comp_ι_image_eq_preimage] at hxU
    simp only [valAt'_ι_appIso_inv] at hxO ⊢
    obtain ⟨h1, h2⟩ := hinv' b x' (by rw [← Category.assoc]; exact hxp) hxU hxO
    exact ⟨h1, by rw [h2]⟩
  · intro v v' hv hv' hp h0 he
    obtain ⟨w, rfl⟩ := exists_lift_through_opens_ι W U' v hv
    obtain ⟨w', rfl⟩ := exists_lift_through_opens_ι W U' v' hv'
    have hw : ⊤ ≤ w ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w]; exact hv
    have hw' : ⊤ ≤ w' ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w']; exact hv'
    have hp' : w ≫ W.ι ≫ p = w' ≫ W.ι ≫ p := by simpa only [Category.assoc] using hp
    have h0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w' :=
      (cancel_mono W.ι).mp (by simpa only [Category.assoc] using h0)
    have he' : ∀ i, GlobalTheory.TangentOrigin.evalPt w U' hw (t' i) = GlobalTheory.TangentOrigin.evalPt w' U' hw' (t' i) := by
      intro i
      rw [← evalPt_ι_appIso_inv W U' w hv hw, ← evalPt_ι_appIso_inv W U' w' hv' hw']
      exact he i
    rw [hun' w w' hw hw' hp' h0' he']

theorem exists_relative_exp_of_smooth (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (m : ℕ)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (hsm : Smooth G.hom)
    (hcon : GeometricallyConnected G.hom) (hB : IsOpen B) (hb₀ : b₀ ∈ B) (hy : IsHolTo B y) :
    ∃ (g : ℕ) (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)), IsOpen B' ∧ b₀ ∈ B' ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        (∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
        IsHolTo Set.univ (fun z => pt ((e b) z)) ∧
        (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧
        (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left →
          ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
      ∀ z₀, e b₀ z₀ = 1 → ∃ ζ : (Fin m → ℂ) → (Fin g → ℂ), ζ b₀ = z₀ ∧ AnalyticAt ℂ ζ b₀ ∧
        ∀ᶠ b in 𝓝 b₀, e b (ζ b) = 1 := by
  haveI := hsm
  have hy' : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨g, U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hinv, hun⟩ :=
    exists_chart_of_smooth m G.left X G.hom B y b₀ (1 : Over.mk (y b₀) ⟶ G).left hB hb₀ hy
      (Over.w (1 : Over.mk (y b₀) ⟶ G))
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart (G := G) (t := t) (f := f) hy' hN hU hO₀ hσ hσN hinv
  obtain ⟨B', e, r, Q, L, hB'o, hb₀', -, -, hQ, hadd, hprop, hinv'⟩ :=
    exists_global_exp (G := G) (t := t) (f := f) GlobalTheory.exists_param_exp_log_pi (hB.mem_nhds hb₀) hy' hO hU hO₀
      hs1 hs2 hs3
  refine ⟨g, B', e, hB'o, hb₀', fun b hb => ?_, fun z₀ hz₀ => ?_⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, hder, -, -, -⟩ := hprop b hb
    have he0 : e b 0 = 1 := by
      have h := hadd b 0 0
      rw [add_zero] at h
      exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
    have hhol' : IsHolTo Set.univ (fun z => pt (e b z)) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hhol z).comp (φ := fun v : Fin g → ℂ => (b, v)) (analyticAt_const.prod analyticAt_id)
    obtain ⟨ht1, ht2⟩ := GlobalTheory.vertical_derivative_in_coordinates X G (y b) g (e b) hhol'
    have hU0 : ⊤ ≤ (show Sp ℂ ⟶ G.left from (e b 0).left) ⁻¹ᵁ U := by
      rw [he0]
      exact hU1
    have hfd : fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0 = ContinuousLinearMap.id ℂ (Fin g → ℂ) :=
      hder.fderiv
    have hinj : Function.Injective (fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0) := by
      rw [hfd]
      intro a a' h
      simpa using h
    let φ : Multiplicative (Fin g → ℂ) →* (Over.mk (y b) ⟶ G) :=
      { toFun := fun z => e b (Multiplicative.toAdd z)
        map_one' := he0
        map_mul' := fun z w => hadd b _ _ }
    have hH : φ.range = ⊤ := by
      refine GlobalTheory.OpenSubgroupPts.subgroup_eq_top_of_nhds_one X G (y b) φ.range U (Fin n ⊕ Fin g) (Sum.elim f t)
        {c | (b, fun j => c (Sum.inl j)) ∈ O ∧
          (b, (fun i => c (Sum.inr i)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q} hsm hcon ?_ hU1 ?_ ?_
      · exact (hO.preimage (by fun_prop)).inter (hQ.preimage (by fun_prop))
      · refine ⟨hO1, ?_⟩
        show (b, crd U t (pt (1 : Over.mk (y b) ⟶ G)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q
        rw [sub_self]
        exact hQ1
      · intro a ha1 ha2
        exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (L (b, crd0 t a)), hinv' b a ha1 ha2.1 ha2.2⟩
    have hsurj : Function.Surjective (e b) := by
      intro a
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hH ▸ Subgroup.mem_top a)
      exact ⟨Multiplicative.toAdd z, hz⟩
    exact ⟨hhol, hadd b, hsurj, hhol', ht1, (ht2 U t hU0 hun).mpr hinj⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, -, hL0, hL, -⟩ := hprop b₀ hb₀'
    exact exists_lift (G := G) (y := y) (U := U) (t := t) (f := f) (O := O) (e := e) (Q := Q) (L := L)
      (β := fun w => w) (x := fun w => (1 : Over.mk (y w) ⟶ G)) (w₀ := b₀) (z₀ := z₀)
      hO hQ hadd hinv' analyticAt_id (HolAt.one hy') hz₀ (hhol z₀) hU1 hO1 hQ1 hL0 hL

end General

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem exists_exp_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  intro X G _ y r hG hr hy
  haveI := hG.comm
  let c : ℂ → (Fin 1 → ℂ) := fun u _ => u
  have hcA : ∀ u, AnalyticAt ℂ c u := fun u =>
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ).analyticAt u
  let y' : (Fin 1 → ℂ) → (Sp ℂ ⟶ X) := fun b => y (b 0)
  let B : Set (Fin 1 → ℂ) := (fun b : Fin 1 → ℂ => b 0) ⁻¹' Metric.ball 0 r
  have hBo : IsOpen B := Metric.isOpen_ball.preimage (continuous_apply 0)
  have hb0 : (0 : Fin 1 → ℂ) ∈ B := by
    show (0 : ℂ) ∈ Metric.ball (0 : ℂ) r
    exact Metric.mem_ball_self hr
  have hy' : IsHolTo B y' := isHolTo_of_holAt hBo fun b hb =>
    HolAt.comp (a := y) (φ := fun b : Fin 1 → ℂ => b 0) ⟨_, Metric.isOpen_ball, hb, hy⟩
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt b)
  obtain ⟨g, B', e', hB'o, hb0', hprop, hfin⟩ :=
    exists_relative_exp_of_smooth X G 1 B y' 0 hG.smooth hG.geomConnected hBo hb0 hy'
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB'o 0 hb0'
  have hcB : ∀ u ∈ Metric.ball (0 : ℂ) (min ε r), c u ∈ B' := by
    intro u hu
    apply hεB
    rw [Metric.mem_ball, dist_zero_right]
    show ‖(fun _ : Fin 1 => u)‖ < ε
    rw [pi_norm_const]
    rw [Metric.mem_ball, dist_zero_right] at hu
    exact lt_of_lt_of_le hu (min_le_left _ _)
  refine ⟨g, min ε r, fun u => e' (c u), lt_min hε hr, min_le_right _ _, ?_, fun u hu => (hprop (c u) (hcB u hu)).2, ?_⟩
  · refine isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    exact ((hprop (c q.1) (hcB q.1 hq.1)).1 q.2).comp (φ := fun q : ℂ × (Fin g → ℂ) => (c q.1, q.2))
      (((ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.fst ℂ ℂ (Fin g → ℂ)).prod
        (ContinuousLinearMap.snd ℂ ℂ (Fin g → ℂ))).analyticAt q)
  · intro z₀ hz₀
    obtain ⟨ζ, h1, h2, h3⟩ := hfin z₀ hz₀
    exact ⟨fun u => ζ (c u), h1, AnalyticAt.comp (f := c) (x := (0 : ℂ)) h2 (hcA 0), (hcA 0).continuousAt.tendsto.eventually h3⟩

end GlobalTheory.RelExp
