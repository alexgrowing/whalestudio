import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFormAlongDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFormSumOfSquaresStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormInLocalConeStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.OrderElt

theorem eq_of_associated_pow {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

theorem assoc_prod {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {W : Type} [CommRing W] (f : R →+* W) (ϖ : W)
    (be : LinearMap.BilinForm ℤ Dg.X) (hF : FormAt Dg f ϖ be) {m : ℕ} (y : Fin m → Dg.X) (r : Fin m → R)
    (hr : ∀ i, PsiCoord Dg (y i) (r i)) (c : Fin m → ℕ) :
    Associated (f (∏ i, r i ^ c i)) (ϖ ^ ∑ i, c i * (be (y i) (y i) / 2).toNat) := by
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Associated.prod _ _ _ fun i _ => ?_
  obtain ⟨r', n, hr', hn, ha⟩ := hF (y i)
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_unit_of_coord hr' (hr i)
  have e : (be (y i) (y i) / 2).toNat = n := by rw [hn]; omega
  rw [map_pow, e, pow_mul', hu, map_mul]
  refine Associated.pow_pow ?_
  exact (associated_unit_mul_left _ _ ((Units.isUnit u).map f)).trans ha

theorem diag_eq {R : Type} [CommRing R] [IsDomain R] {Dg : DegPre R} {W : Type} [CommRing W] {f : R →+* W} {ϖ : W}
    {be : LinearMap.BilinForm ℤ Dg.X} (hF : FormAt Dg f ϖ be) (y : Dg.X) :
    be y y = 2 * ((be y y / 2).toNat : ℤ) := by
  obtain ⟨r', n, -, hn, -⟩ := hF y
  rw [hn]; omega

theorem exists_gen_along {X : Scheme.{0}} (EX : EffCartierData X) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    ∃ h : R, ∀ (W : Type) [CommRing W] [IsLocalRing W] (f : R →+* W),
      idlAlong EX.idealSheaf (spMap f ≫ ξ) = Ideal.span {f h} := by
  obtain ⟨k, hk⟩ := FlagMod.exists_chart_of_isLocalRing EX.cover ξ
  refine ⟨FlagMod.ev ξ (EX.U k) hk (EX.f k), fun W _ _ f => ?_⟩
  rw [TraitOrder.idlAlong_comp, TraitGen.idlAlong_idealSheaf_eq EX ξ k hk, Ideal.map_span, Set.image_singleton]

theorem exists_gam {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (f : R →+* W)
    (hf : Function.Injective f) :
    ∃ gam : FractionRing R →+* FractionRing W, ∀ r, gam (algebraMap R _ r) = algebraMap W _ (f r) :=
  ⟨IsLocalization.map _ f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf),
    fun r => IsLocalization.map_eq _ _⟩

theorem exists_elt_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∀ (N' : ℕ) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), 0 < N' → (∀ β ∈ balForms H.bar P.D.toPre.X, (∀ y, 0 ≤ β y y) → (N' : ℝ) * φ.evalZ β ≤ (ℓ β : ℝ)) → ∃ (M : ℕ) (u : R), 0 < M ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre f ϖ be → ∃ n k : ℕ, idlAlong EX.idealSheaf (spMap f ≫ ξ) = Ideal.span {ϖ ^ n} ∧ (M : ℤ) * N * ℓ be = M * N' * n + k ∧ Associated (f u) (ϖ ^ k) := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t hξ P m γ hg hφs hRef hN hEX hR hEt hFU hTors hCone hIn N' ℓ hN' hℓ
  have hR' := hR
  obtain ⟨hRn, hRic, -, hR0⟩ := hR'
  haveI := hRn; haveI := hRic; haveI := hR0
  haveI : Module.Finite ℤ P.D.toPre.X := Module.Finite.trans (𝓞 E) _
  obtain ⟨k, y, a, hya⟩ := GlobalTheory.T.symmetric_form_sum_of_squares _ ℓ
  have hB := GlobalTheory.T.boundary_form_in_local_cone E H D l Xo c Z g φs 𝒩 φ EX N R ξ t hξ P m γ hg hφs hRef hN hEX hR hEt hFU hTors hCone hIn
  obtain ⟨h, hh⟩ := exists_gen_along EX ξ

  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let g0 : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
  have hg0 : Function.Injective g0 := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
  have hW0 : CDvr (PowerSeries K) := FrameCmp.cDvr_powerSeries K
  obtain ⟨gam0, hgam0⟩ := exists_gam g0 hg0
  obtain ⟨be0, hbe0, hF0⟩ := GlobalTheory.T.exists_level_form_along_dvr E H R t P hR _ hW0 PowerSeries.X PowerSeries.X_irreducible g0 gam0 hgam0
  have hco : ∀ j, ∃ r, PsiCoord P.D.toPre (y j) r := fun j => (hF0 (y j)).imp fun r h => h.choose_spec.1
  choose r hr using hco
  have hr0 : ∀ j, r j ≠ 0 := fun j => PsiCoordLocal.ne_zero_of_coord (hr j)
  set num : R := ∏ j, r j ^ (N * (a j).toNat) with hnum
  set den : R := ∏ j, r j ^ (N * (-a j).toNat) with hden

  have hid : ∀ (W : Type) [CommRing W] (f : R →+* W) (ϖ : W) (be : LinearMap.BilinForm ℤ P.D.toPre.X),
      (∀ u v, be u v = be v u) → FormAt P.D.toPre f ϖ be →
      ((∑ j, N * (a j).toNat * (be (y j) (y j) / 2).toNat : ℕ) : ℤ) -
        ((∑ j, N * (-a j).toNat * (be (y j) (y j) / 2).toNat : ℕ) : ℤ) = N * ℓ be := by
    intro W _ f ϖ be hs hF
    have h2 := hya be hs
    have hd := fun j => diag_eq hF (y j)
    have hl : ℓ be = ∑ j, a j * ((be (y j) (y j) / 2).toNat : ℤ) := by
      have : 2 * ℓ be = 2 * ∑ j, a j * ((be (y j) (y j) / 2).toNat : ℤ) := by
        rw [h2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        linear_combination (a j) * hd j
      omega
    push_cast
    rw [hl, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Int.toNat_sub_toNat_neg (a j)
    linear_combination (N : ℤ) * ((be (y j) (y j) / 2).toNat : ℤ) * this

  have hh0 : h ≠ 0 := by
    rintro rfl
    obtain ⟨n0, -, e0⟩ := hB _ hW0 _ PowerSeries.X_irreducible g0 hg0 be0 hbe0 hF0
    rw [hh, map_zero, Ideal.span_singleton_eq_span_singleton] at e0
    exact pow_ne_zero n0 PowerSeries.X_ne_zero ((associated_zero_iff_eq_zero _).1 e0.symm)
  have hden0 : den ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hr0 j)
  have ha0 : h ^ N' * den ≠ 0 := mul_ne_zero (pow_ne_zero _ hh0) hden0
  obtain ⟨u, hu⟩ : h ^ N' * den ∣ num := by
    refine PolDiv.dvd_of_traits ha0 fun W _ _ _ hW f hf => ?_
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    obtain ⟨gam, hgam⟩ := exists_gam f hf
    obtain ⟨be, hbe, hF⟩ := GlobalTheory.T.exists_level_form_along_dvr E H R t P hR W hW ϖ hϖ f gam hgam
    obtain ⟨n, hnr, e⟩ := hB W hW ϖ hϖ f hf be hbe hF
    rw [hh, Ideal.span_singleton_eq_span_singleton] at e
    have hs : ∀ u v, be u v = be v u := hbe.1
    have hA := assoc_prod P.D.toPre f ϖ be hF y r hr (fun j => N * (a j).toNat)
    have hBd := assoc_prod P.D.toPre f ϖ be hF y r hr (fun j => N * (-a j).toNat)
    have hbal : be ∈ balForms H.bar P.D.toPre.X := (balForms_eq_levelForms H P.D.toPre.X).symm ▸ hbe
    have hsd : ∀ v, 0 ≤ be v v := fun v => by have := diag_eq hF v; omega
    have hle := hℓ be hbal hsd
    have hI := hid W f ϖ be hs hF
    have hineq : n * N' + ∑ j, N * (-a j).toNat * (be (y j) (y j) / 2).toNat ≤
        ∑ j, N * (a j).toNat * (be (y j) (y j) / 2).toNat := by
      have h1 : ((n * N' : ℕ) : ℝ) ≤ N * (ℓ be : ℝ) := by
        push_cast
        rw [hnr]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
      have h2 : ((n * N' : ℕ) : ℤ) ≤ N * ℓ be := by exact_mod_cast h1
      omega
    rw [map_mul, map_pow]
    refine ((e.pow_pow (n := N')).mul_mul hBd).dvd_iff_dvd_left.2 ?_
    refine hA.dvd_iff_dvd_right.2 ?_
    rw [← pow_mul, ← pow_add]
    exact pow_dvd_pow ϖ (by rw [mul_comm n N'] at hineq; linarith)
  refine ⟨1, u, one_pos, fun W _ _ _ hW ϖ hϖ f be hs hF => ?_⟩
  haveI : IsDiscreteValuationRing W := hW.1
  have hA := assoc_prod P.D.toPre f ϖ be hF y r hr (fun j => N * (a j).toNat)
  have hBd := assoc_prod P.D.toPre f ϖ be hF y r hr (fun j => N * (-a j).toNat)
  have hI := hid W f ϖ be hs hF
  have hnum0 : f num ≠ 0 := fun e0 => pow_ne_zero _ hϖ.ne_zero ((associated_zero_iff_eq_zero _).1 (e0 ▸ hA).symm)
  have hfe : f num = f h ^ N' * f den * f u := by rw [hu]; simp only [map_mul, map_pow]
  have hfh : f h ≠ 0 := fun e0 => hnum0 (by rw [hfe, e0, zero_pow (Nat.pos_iff_ne_zero.1 hN')]; ring)
  have hfu : f u ≠ 0 := fun e0 => hnum0 (by rw [hfe, e0, mul_zero])
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hfh hϖ
  obtain ⟨k', hk'⟩ := IsDiscreteValuationRing.associated_pow_irreducible hfu hϖ
  refine ⟨n, k', ?_, ?_, hk'⟩
  · rw [hh, Ideal.span_singleton_eq_span_singleton]; exact hn
  · have hc : Associated (ϖ ^ (∑ j, N * (a j).toNat * (be (y j) (y j) / 2).toNat))
        (ϖ ^ (n * N' + ∑ j, N * (-a j).toNat * (be (y j) (y j) / 2).toNat + k')) := by
      refine hA.symm.trans ?_
      rw [hfe, pow_add, pow_add, pow_mul]
      exact ((hn.pow_pow).mul_mul hBd).mul_mul hk'
    have := eq_of_associated_pow hϖ hc
    have hI' := hI
    rw [this] at hI'
    push_cast at hI' ⊢
    linarith

end GlobalTheory.OrderElt
