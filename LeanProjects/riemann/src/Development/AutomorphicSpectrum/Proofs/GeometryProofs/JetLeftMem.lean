import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dif_pos hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dif_pos (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dif_pos (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
