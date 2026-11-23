import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoordChart

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f h : A →+* B} (e : spMap f = spMap h) : f = h := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (z : Sp B ⟶ Sp A) : ∃ f : A →+* B, spMap f = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem lift_chart {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    {K : Type} [Field K] (y : R →+* K) [IsOpenImmersion x] (hx : x ≫ Y.s = spMap β)
    (hv : SecCoord Y.de Y.th x v) (c : Kˣ)
    {L : Type} [CommRing L] (ψ : L →+* K) (hψ : ∀ l, ψ l ≠ 0 → IsUnit l) (β' : o →+* L)
    (w : Ix g (N' ^ 2) → L) (hβ : ψ.comp β' = y.comp β) (hw : ∀ a, ψ (w a) = c * y (v a))
    (hI : ∀ F ∈ I, MvPolynomial.eval₂ β' w F = 0) :
    ∃ φ : R →+* L, ψ.comp φ = y ∧ φ.comp β = β' ∧ ∃ u : Lˣ, ∀ a, w a = u * φ (v a) := by
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc K _ _ _ h3 h2
  have hL : InMM n N' I β' w := by
    refine ⟨hI, fun q hq a => ?_⟩
    obtain ⟨d, hd⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨d, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hd
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L β' w hL
  have h4 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 K ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts K _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, h2⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal K)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  refine ⟨φ, sp_inj ?_, sp_inj ?_, ?_⟩
  · rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq]
  · rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1]
  · have h6 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 L φ
    rw [hz] at h6
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 w hz2

theorem clear_denom {o σ R L : Type} [CommRing o] [CommRing R] [CommRing L] (β : o →+* R) (φ : R →+* L)
    (v : σ → R) (w : σ → L) (t : R) (h : ∀ a, w a * φ t = φ (v a)) (F : MvPolynomial σ o) :
    ∃ (r : R) (m : ℕ), MvPolynomial.eval₂ (φ.comp β) w F * φ t ^ m = φ r := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨β c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r, m, h1⟩ := hp
    obtain ⟨r', m', h2⟩ := hq
    refine ⟨r * t ^ m' + r' * t ^ m, m + m', ?_⟩
    rw [MvPolynomial.eval₂_add, map_add, map_mul, map_mul, ← h1, ← h2, map_pow, map_pow]
    ring
  | mul_X p a hp =>
    obtain ⟨r, m, h1⟩ := hp
    refine ⟨r * v a, m + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, ← h1, ← h a]
    ring

theorem residue_generic : ∀ (o : Type) [CommRing o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (K : Type) [Field K] (y : R →+* K) (a₀ : Ix g (N' ^ 2)), 0 < N' → IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → (∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r) → y (v a₀) ≠ 0 → Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) = ⊤ ∧ (RingHom.ker y ∈ minimalPrimes R → RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀))) ∈ (I ⊔ Ideal.span {MvPolynomial.X a₀ - 1}).minimalPrimes) := by
  intro o _ g n N' I Y R _ β x v K _ y a₀ _ hox hx hv hfr h0
  let c : Kˣ := (Units.mk0 _ h0)⁻¹
  have hc : ∀ a, y (v a) / y (v a₀) = c * y (v a) := fun a => by
    simp [c, div_eq_inv_mul]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK : ∀ F ∈ I, MvPolynomial.eval₂ (y.comp β) (fun a => y (v a) / y (v a₀)) F = 0 := by
    simpa only [hc] using (Y.loc K _ _ _ h3 h2).1
  constructor
  · set E := Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) with hE
    let β' : o →+* E := (y.comp β).codRestrict E fun t => Subfield.subset_closure (Or.inl ⟨t, rfl⟩)
    let w : Ix g (N' ^ 2) → E := fun a => ⟨y (v a) / y (v a₀), Subfield.subset_closure (Or.inr ⟨a, rfl⟩)⟩
    obtain ⟨φ, hφ, -⟩ := lift_chart Y β x v y hx hv c E.subtype
      (fun l hl => IsUnit.mk0 l (fun h => hl (by rw [h, map_zero]))) β' w rfl (fun a => hc a) (by
        intro F hF
        apply E.subtype.injective
        rw [MvPolynomial.eval₂_comp_left, map_zero]
        exact hK F hF)
    have hy : ∀ r, y r ∈ E := fun r => by rw [← hφ]; exact (φ r).2
    rw [eq_top_iff]
    intro k _
    obtain ⟨r, r', hr, hk⟩ := hfr k
    rw [eq_div_of_mul_eq hr hk]
    exact E.div_mem (hy r) (hy r')
  · intro hmin
    set ev := MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀)) with hev
    refine ⟨⟨RingHom.ker_isPrime ev, sup_le (fun F hF => hK F hF) ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change ev _ = 0
      simp [hev, h0]
    rintro P ⟨hP, hJ⟩ hle
    let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* K := Ideal.Quotient.lift P ev fun a ha => hle ha
    haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    let L := Localization.AtPrime (RingHom.ker e)
    have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
    let ψ : L →+* K := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
    let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
    have hπ : ∀ F, ψ (π F) = ev F := fun F => by
      simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
      rfl
    have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
      conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
      rfl
    have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
    have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
      intro l hl
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
      rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
      intro ha
      apply hl
      change ψ (IsLocalization.mk' L a s) = 0
      rw [IsLocalization.lift_mk'_spec, mul_zero]
      exact ha
    obtain ⟨φ, hφ, hβ, u, hw⟩ := lift_chart Y β x v y hx hv c ψ hψ (π.comp MvPolynomial.C)
      (fun a => π (MvPolynomial.X a)) (by ext t; simp [hπ, hev]) (fun a => by rw [hπ, ← hc]; simp [hev])
      (fun F hF => by rw [hπe, hπ0]; exact hJ (Ideal.mem_sup_left hF))
    have hone : (u : L) * φ (v a₀) = 1 := by
      rw [← hw, ← sub_eq_zero, ← map_one π, ← map_sub, hπ0]
      exact hJ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hker : RingHom.ker y ≤ RingHom.ker φ :=
      hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ (fun r hr => by
        rw [RingHom.mem_ker] at hr ⊢
        rw [← hφ, RingHom.comp_apply, hr, map_zero])
    intro F hF
    obtain ⟨r, m, hr⟩ := clear_denom β φ v (fun a => π (MvPolynomial.X a)) (v a₀)
      (fun a => by
        change π (MvPolynomial.X a) * _ = _
        rw [hw a, mul_right_comm, hone, _root_.one_mul]) F
    rw [hβ, hπe] at hr
    have hyr : r ∈ RingHom.ker y := by
      rw [RingHom.mem_ker] at hF ⊢
      rw [← hφ, RingHom.comp_apply, ← hr, map_mul, hπ, hF, zero_mul]
    have hφr : φ r = 0 := hker hyr
    rw [hφr] at hr
    rw [← hπ0]
    exact ((IsUnit.of_mul_eq_one_right _ hone).pow m).mul_left_eq_zero.1 hr

end GlobalTheory.CoordChart
