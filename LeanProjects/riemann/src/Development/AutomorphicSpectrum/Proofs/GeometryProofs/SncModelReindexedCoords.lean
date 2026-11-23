import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRefine

theorem isLocalization_atPrime {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsPrime]
    (hden : ∀ t : B, ∃ u v : A, algebraMap A B u ∉ q ∧ algebraMap A B v = algebraMap A B u * t) :
    IsLocalization (q.comap (algebraMap A B)).primeCompl (Localization.AtPrime q) := by
  have hmap : ∀ a : A, algebraMap A (Localization.AtPrime q) a =
      algebraMap B (Localization.AtPrime q) (algebraMap A B a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [hmap]
    exact IsLocalization.map_units (Localization.AtPrime q) (⟨algebraMap A B y, hy⟩ : q.primeCompl)
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨u₁, v₁, hu₁, hv₁⟩ := hden a
    obtain ⟨u₂, v₂, hu₂, hv₂⟩ := hden b
    have hd : u₁ * v₂ ∈ (q.comap (algebraMap A B)).primeCompl := by
      change algebraMap A B (u₁ * v₂) ∉ q
      rw [map_mul, hv₂]
      intro hmem
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
      · exact hu₁ h
      · rcases Ideal.IsPrime.mem_or_mem ‹_› h with h | h
        · exact hu₂ h
        · exact b.2 h
    refine ⟨⟨u₂ * v₁, ⟨u₁ * v₂, hd⟩⟩, ?_⟩
    simp only [hmap, map_mul, hv₁, hv₂]
    simp only at hab
    linear_combination (algebraMap B (Localization.AtPrime q) (algebraMap A B u₁) *
      algebraMap B (Localization.AtPrime q) (algebraMap A B u₂)) * hab
  · intro x y hxy
    rw [hmap, hmap] at hxy
    have := IsLocalization.injective (Localization.AtPrime q) (Ideal.primeCompl_le_nonZeroDivisors q) hxy
    exact ⟨1, by rw [hinj this]⟩

theorem formallyEtale_of_denominators {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (hinj : Function.Injective (algebraMap A B))
    (hden : ∀ (q : Ideal B), q.IsPrime → ∀ t : B,
      ∃ u v : A, algebraMap A B u ∉ q ∧ algebraMap A B v = algebraMap A B u * t) :
    Algebra.FormallyEtale A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hloc : ∀ q : PrimeSpectrum B, Algebra.FormallyEtale A (Localization.AtPrime q.asIdeal) := fun q => by
    have := isLocalization_atPrime hinj q.asIdeal (hden q.asIdeal q.2)
    exact Algebra.FormallyEtale.of_isLocalization (q.asIdeal.comap (algebraMap A B)).primeCompl
  rw [Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth]
  refine ⟨Algebra.formallyUnramified_iff_forall.mpr fun q => ?_,
    Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_)⟩
  · have := hloc q
    exact (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp this).1
  · have := hloc q
    exact (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp this).2

theorem smooth_coords_of_denominators {Ω : Type} [Field Ω] [Algebra ℚ Ω] {S S' : Subalgebra ℚ Ω} (hle : S ≤ S')
    (hfg : S'.FG) (hS : Algebra.Smooth ℚ S)
    (hden : ∀ q : Ideal S', q.IsPrime → ∀ t : S',
      ∃ u v : S, Subalgebra.inclusion hle u ∉ q ∧ (v : Ω) = (u : Ω) * t)
    {e : ℕ} (z : Fin e → S) (h₁ : LinearIndependent S fun i => KaehlerDifferential.D ℚ S (z i))
    (h₂ : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) :
    Algebra.Smooth ℚ S' ∧
      LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (Subalgebra.inclusion hle (z i))) ∧
      Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (Subalgebra.inclusion hle (z i))) = ⊤ := by
  letI : Algebra S S' := RingHom.toAlgebra (Subalgebra.inclusion hle : S →+* S')
  haveI : IsScalarTower ℚ S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℚ S' := (Subalgebra.fg_iff_finiteType S').mp hfg
  haveI : Algebra.FiniteType S S' := Algebra.FiniteType.of_restrictScalars_finiteType ℚ S S'
  haveI : Algebra.FinitePresentation ℚ S := hS.finitePresentation
  haveI : Algebra.FormallySmooth ℚ S := hS.formallySmooth
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℚ S
  have hinj : Function.Injective (algebraMap S S') := fun a b h =>
    Subtype.ext (show (a : Ω) = b from congrArg (fun w : S' => (w : Ω)) h)
  haveI : Algebra.FormallyEtale S S' := formallyEtale_of_denominators hinj fun q hq t => by
    obtain ⟨u, v, hu, hv⟩ := hden q hq t
    exact ⟨u, v, hu, Subtype.ext hv⟩
  haveI : Algebra.FormallySmooth S S' :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp inferInstance).2
  exact ⟨⟨Algebra.FormallySmooth.comp ℚ S S', Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩,
    SncRes.coords_of_formallyEtale z h₁ h₂⟩

abbrev bratio {K : Type} {J : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : (k : K) → J k) :
    (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩

abbrev seg {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) :
    ((k : K) → J k) → Ω := fun d => ∏ k, y ⟨k, d k⟩

section Ratios

variable {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω]

theorem seg_ratio_mem (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (T : Subring Ω)
    (h : ∀ p, bratio y c p ∈ T) (d : (k : K) → J k) : seg y d / seg y c ∈ T := by
  simp only [seg]
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => h ⟨k, d k⟩

theorem exists_seg_ratio (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (p : Σ k, J k) : ∃ d : (k : K) → J k, bratio y c p = seg y d / seg y c := by
  classical
  obtain ⟨k, i⟩ := p
  refine ⟨Function.update c k i, ?_⟩
  simp only [seg, bratio]
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [Function.update_of_ne hb, div_self (hc b)]
  · simp

end Ratios

theorem exists_nat_mul_mem_adjoin {Ω : Type} [Field Ω] [CharZero Ω] {W : Set Ω} {a : Ω}
    (ha : a ∈ Algebra.adjoin ℚ W) : ∃ N : ℕ, N ≠ 0 ∧ (N : Ω) * a ∈ Algebra.adjoin ℤ W := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = (r.num : Ω) := by
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [this]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x + y) = (M : Ω) * ((N : Ω) * x) + (N : Ω) * ((M : Ω) * y) := by
      push_cast
      ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x * y) = ((N : Ω) * x) * ((M : Ω) * y) := by
      push_cast
      ring
    rw [this]
    exact mul_mem hx hy

theorem aeval_mem_subring {Ω σ : Type} [Field Ω] (T : Subring Ω) (r : σ → Ω) (h : ∀ p, r p ∈ T)
    (g : MvPolynomial σ ℤ) : MvPolynomial.aeval r g ∈ T := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem T a
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp => simpa using mul_mem hp (h i)

theorem exists_denominator {X X' : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (g : X' ⟶ X)
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {K' : Type} [Fintype K'] {J' : K' → Type} {y' : (Σ k, J' k) → Ω}
    (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k))
    (hspec : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (seg y)) (tie' : CoordTie ℤ ξ' (seg y'))
    (hy : ∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩)
    (hreg : ∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1,
      regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩)
    (c' : (k : K') → J' k) (hc' : ∀ k, y' ⟨k, c' k⟩ ≠ 0) (c : (k : K) → J k)
    (hcc : ∀ k, bx k (c k) = c' (bk k))
    {f : Ω} (hf : f ∈ Algebra.adjoin ℚ (Set.range (bratio y c))) (hf0 : f ≠ 0)
    {S S' : Subalgebra ℚ Ω} (hS : S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range (bratio y c))))
    (hS' : S' = Algebra.adjoin ℚ (insert f⁻¹ (Set.range (bratio y' c')))) (hle : S ≤ S')
    (q : Ideal S') (hq : q.IsPrime) (t : S') :
    ∃ u v : S, Subalgebra.inclusion hle u ∉ q ∧ (v : Ω) = (u : Ω) * t := by
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => by
    rw [← hy, hcc]
    exact hc' _
  have hxc' : seg y' c' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc' k
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hrat : ∀ p : Σ k, J k, bratio y c p = bratio y' c' ⟨bk p.1, bx p.1 p.2⟩ := fun p => by
    simp only [bratio]
    rw [hy p.1 p.2, ← hcc p.1, hy]
  let B' : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun d => seg y' d / seg y' c')
  let B : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c)
  have hblk' : ∀ p, bratio y' c' p ∈ B' := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio y' c' hc' p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  have hblk : ∀ p, bratio y c p ∈ B' := fun p => by
    rw [hrat]
    exact hblk' _
  have hBB' : B ≤ B' := Algebra.adjoin_le (by
    rintro _ ⟨d, rfl⟩
    exact seg_ratio_mem y c B'.toSubring hblk d)
  have hrS' : ∀ p, bratio y' c' p ∈ S' := fun p => by
    rw [hS']
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hrS : ∀ p, bratio y c p ∈ S := fun p => by
    rw [hS]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hB'S' : ∀ b ∈ B', b ∈ S' := fun b hb => by
    have h : B' ≤ S'.restrictScalars ℤ := Algebra.adjoin_le (by
      rintro _ ⟨d, rfl⟩
      exact seg_ratio_mem y' c' S'.toSubring hrS' d)
    exact h hb
  have hBS : ∀ b ∈ B, b ∈ S := fun b hb => by
    have h : B ≤ S.restrictScalars ℤ := Algebra.adjoin_le (by
      rintro _ ⟨d, rfl⟩
      exact seg_ratio_mem y c S.toSubring hrS d)
    exact h hb
  let φ : B' →+* S' := (B'.val : B' →+* Ω).codRestrict S' fun b => hB'S' b b.2
  haveI := hq
  obtain ⟨p', ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X' Ω ξ' ℤ _ (seg y') tie' c' hxc' (q.comap φ) inferInstance
  have hu' : ∀ b (hb : b ∈ B'), (⟨b, hB'S' b hb⟩ : S') ∉ q ↔ unitAt ξ' p' b := fun b hb => hpu ⟨b, hb⟩
  have hnot : ∀ (b b' : Ω) (hb : b ∈ S') (hb' : b' ∈ S'), b * b' = 1 → (⟨b, hb⟩ : S') ∉ q :=
    fun b b' hb hb' h hmem => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (IsUnit.of_mul_eq_one ⟨b', hb'⟩ (Subtype.ext h)))
  have hinvS' : ∀ n : ℕ, (n : Ω)⁻¹ ∈ S' := fun n => by
    have := S'.algebraMap_mem ((n : ℚ)⁻¹)
    simpa using this
  have hnat : ∀ n : ℕ, n ≠ 0 → unitAt ξ' p' (n : Ω) := fun n hn =>
    (hu' _ (natCast_mem B' n)).1 (hnot _ _ _ (hinvS' n) (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)))
  have hchar : ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r p' := fun r hr h => h (hnat r hr.ne_zero)
  have hR : regAt ξ' p' = regAt ξ ⟨g p'.1, hspec _⟩ := hreg p' hchar (hspec _)
  have hB'reg : ∀ b ∈ B', b ∈ regAt ξ' p' := fun b hb => (tie'.ring c' hxc' b).1 hb p' hpc
  have hratreg : ∀ a : ℚ, algebraMap ℚ Ω a ∈ regAt ξ' p' := fun a => by
    have h : algebraMap ℚ Ω a = (a.num : Ω) * (a.den : Ω)⁻¹ := by
      rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    rw [h]
    exact mul_mem (intCast_mem _ _) (hnat _ a.den_ne_zero).2.2
  have hfS' : f ∈ S' := by
    have h : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ S' := Algebra.adjoin_le (by
      rintro _ ⟨p, rfl⟩
      exact hB'S' _ (hblk p))
    exact h hf
  have hfinvS' : f⁻¹ ∈ S' := by
    rw [hS']
    exact Algebra.subset_adjoin (Set.mem_insert _ _)
  obtain ⟨N, hN, hNf⟩ := exists_nat_mul_mem_adjoin hf
  have hNfB' : (N : Ω) * f ∈ B' := by
    have h : Algebra.adjoin ℤ (Set.range (bratio y c)) ≤ B' := Algebra.adjoin_le (by
      rintro _ ⟨p, rfl⟩
      exact hblk p)
    exact h hNf
  have hN0 : (N : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hfu : unitAt ξ' p' ((N : Ω) * f) := (hu' _ hNfB').1 (hnot _ ((N : Ω)⁻¹ * f⁻¹) _
    (mul_mem (hinvS' N) hfinvS') (by field_simp))
  have hfinv : f⁻¹ ∈ regAt ξ' p' := by
    have h := mul_mem (natCast_mem (regAt ξ' p') N) hfu.2.2
    have h2 : (N : Ω) * ((N : Ω) * f)⁻¹ = f⁻¹ := by field_simp
    rwa [h2] at h
  let T : Subalgebra ℚ Ω := { (regAt ξ' p').toSubsemiring with algebraMap_mem' := hratreg }
  have hS'T : S' ≤ T := by
    rw [hS']
    refine Algebra.adjoin_le ?_
    rintro _ (rfl | ⟨p, rfl⟩)
    · exact hfinv
    · exact hB'reg _ (hblk' p)
  have ht : (t : Ω) ∈ regAt ξ ⟨g p'.1, hspec _⟩ := hR ▸ hS'T t.2
  have hp : InChart ξ (seg y) c ⟨g p'.1, hspec _⟩ :=
    ⟨hxc, fun d => hR ▸ hB'reg _ (hBB' (Algebra.subset_adjoin ⟨d, rfl⟩))⟩
  obtain ⟨s, hs, hsu, hst⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (seg y) tie c _ hp t).1 ht
  refine ⟨⟨s, hBS s hs⟩, ⟨s * t, hBS _ hst⟩, ?_, rfl⟩
  have hsu' : unitAt ξ' p' s := by
    unfold unitAt at *
    rw [hR]
    exact hsu
  exact (hu' s (hBB' hs)).2 hsu'

theorem isSncModel_refine : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (e : ℕ) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → (∀ q₁ q₂ : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂) → Cmp.IsSncModel y e bd → Cmp.IsSncModel y' e (bd.map (MvPolynomial.rename fun p : (Σ k, J k) => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, J' k))) := by
  intro X X' Ω _ _ ξ ξ' g K _ J _ y K' _ J' _ y' bk bx e bd hq₀ _ tie tie' _ hy hreg _ hsnc c' hc'
  let c : (k : K) → J k := fun k => (bx k).symm (c' (bk k))
  have hcc : ∀ k, bx k (c k) = c' (bk k) := fun k => (bx k).apply_symm_apply _
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => by
    rw [← hy, hcc]
    exact hc' _
  have hrat : ∀ p : Σ k, J k, bratio y c p = bratio y' c' ⟨bk p.1, bx p.1 p.2⟩ := fun p => by
    simp only [bratio]
    rw [hy p.1 p.2, ← hcc p.1, hy]
  have hrr : Set.range (bratio y c) ⊆ Set.range (bratio y' c') := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hrat p).symm⟩
  obtain ⟨m, f, a, hf, ha, hsum, H⟩ := hsnc c hc
  refine ⟨m, f, a, fun l => Algebra.adjoin_mono hrr (hf l), fun l => Algebra.adjoin_mono hrr (ha l), hsum,
    fun l hfl S' hS' => ?_⟩
  obtain ⟨hsm, z, n, hn, hli, hspan, hbd⟩ := H l hfl _ rfl
  have hle : Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range (bratio y c))) ≤ S' := by
    rw [hS']
    exact Algebra.adjoin_mono (Set.insert_subset_insert hrr)
  have hfg : S'.FG := by
    rw [hS']
    have hfin : (insert (f l)⁻¹ (Set.range (bratio y' c'))).Finite := (Set.finite_range _).insert _
    exact ⟨hfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  obtain ⟨hsm', hli', hspan'⟩ := smooth_coords_of_denominators hle hfg hsm
    (fun q hq t => exists_denominator g bk bx hq₀ tie tie' hy hreg c' hc' c hcc (hf l) hfl rfl hS' hle q hq t)
    z hli hspan
  refine ⟨hsm', ⟨fun i => Subalgebra.inclusion hle (z i), n, hn, hli', hspan', fun q hq => ?_⟩⟩
  haveI := hq
  have key := hbd (q.comap (Subalgebra.inclusion hle : _ →+* S')) inferInstance
  have hv : ∀ w : MRing J, MvPolynomial.aeval (bratio y' c')
      (MvPolynomial.rename (fun p : (Σ k, J k) => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, J' k)) w) =
      MvPolynomial.aeval (bratio y c) w := fun w => by
    rw [MvPolynomial.aeval_rename]
    congr 2
    funext p
    exact (hrat p).symm
  constructor
  · intro h
    obtain ⟨i, hi, hz⟩ := key.1 fun w hw s hs =>
      h _ (Ideal.mem_map_of_mem _ hw) (Subalgebra.inclusion hle s) (hs.trans (hv w).symm)
    exact ⟨i, hi, hz⟩
  · rintro ⟨i, hi, hz⟩
    have h0 := key.2 ⟨i, hi, hz⟩
    have hall : ∀ w ∈ bd.map (MvPolynomial.rename fun p : (Σ k, J k) => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, J' k)),
        ∃ s : S', s ∈ q ∧ (s : Ω) = MvPolynomial.aeval (bratio y' c') w := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ∃ s : S', s ∈ q ∧
        (s : Ω) = MvPolynomial.aeval (bratio y' c') w) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨w, hw, rfl⟩
        have hwS : MvPolynomial.aeval (bratio y c) w ∈
            Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range (bratio y c))) :=
          aeval_mem_subring (Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range (bratio y c)))).toSubring _
            (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) w
        exact ⟨Subalgebra.inclusion hle ⟨_, hwS⟩, h0 w hw ⟨_, hwS⟩ rfl, (hv w).symm⟩
      · exact ⟨0, q.zero_mem, by simp⟩
      · rintro u v _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩
        exact ⟨s₁ + s₂, q.add_mem h₁ h₂, by simp [e₁, e₂]⟩
      · rintro u v _ ⟨s₁, h₁, e₁⟩
        have hu : MvPolynomial.aeval (bratio y' c') u ∈ S' := by
          refine aeval_mem_subring S'.toSubring _ (fun p => ?_) u
          rw [hS']
          exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
        exact ⟨⟨_, hu⟩ * s₁, q.mul_mem_left _ h₁, by simp [e₁]⟩
    intro w hw s hs
    obtain ⟨s', h₁, h₂⟩ := hall w hw
    have : s = s' := Subtype.ext (hs.trans h₂.symm)
    rwa [this]

end GlobalTheory.CompanionTheory.Ar.SncRefine
