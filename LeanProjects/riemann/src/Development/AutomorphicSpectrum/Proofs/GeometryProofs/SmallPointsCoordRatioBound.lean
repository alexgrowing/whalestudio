import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {σ : Type} [Fintype σ]

theorem aeval_scale {R : Type} [CommRing R] {F : MvPolynomial σ ℤ} {n : ℕ} (hF : F.IsHomogeneous n) (c : R)
    (x : σ → R) : MvPolynomial.aeval (fun j => c * x j) F = c ^ n * MvPolynomial.aeval x F := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ j, m j = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_map_hom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : σ → A) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun j => f (t j)) F = f (MvPolynomial.aeval t F) :=
  by simpa using (MvPolynomial.comp_aeval_apply (f := t) f.toIntAlgHom F).symm

variable {Ω : Type} [Field Ω]

def IsFormQuot (x : σ → Ω) (i : σ) (b : Ω) : Prop :=
  ∃ (N n : ℕ) (G : MvPolynomial σ ℤ), N ≠ 0 ∧ G.IsHomogeneous n ∧
    MvPolynomial.aeval x G = (N : Ω) * x i ^ n * b

theorem isFormQuot_of_mem [CharZero Ω] {x : σ → Ω} {i : σ} (hi : x i ≠ 0) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) : IsFormQuot x i b := by
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    refine ⟨1, 1, MvPolynomial.X j, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, ?_⟩
    simp only [MvPolynomial.aeval_X, Nat.cast_one, one_mul, pow_one]
    field_simp
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    simp only [MvPolynomial.aeval_C, pow_zero, mul_one, eq_ratCast, eq_intCast, Rat.cast_def, map_intCast]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', MvPolynomial.C (N' : ℤ) * MvPolynomial.X i ^ n' * G +
      MvPolynomial.C (N : ℤ) * MvPolynomial.X i ^ n * G', mul_ne_zero hN hN', ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n')).mul hG using 1
        omega
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n)).mul hG' using 1
        omega
    · simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, he', eq_intCast,
        Int.cast_natCast, Nat.cast_mul, map_natCast]
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', G * G', mul_ne_zero hN hN', hG.mul hG', ?_⟩
    simp only [map_mul, he, he', Nat.cast_mul]
    ring

theorem common_denominator {κ : Type} [Fintype κ] {x : σ → Ω} {i : σ} {b : κ → Ω}
    (h : ∀ j, IsFormQuot x i (b j)) :
    ∃ (N n : ℕ) (F : κ → MvPolynomial σ ℤ), N ≠ 0 ∧ (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j, MvPolynomial.aeval x (F j) = (N : Ω) * x i ^ n * b j := by
  classical
  choose N n G hN hG he using h
  refine ⟨∏ j, N j, ∑ j, n j, fun j => MvPolynomial.C ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : ℤ) *
    MvPolynomial.X i ^ (∑ l, n l - n j) * G j, Finset.prod_ne_zero_iff.2 fun j _ => hN j, fun j => ?_, fun j => ?_⟩
  all_goals have hle : n j ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · convert ((MvPolynomial.isHomogeneous_C _ _).mul
      ((MvPolynomial.isHomogeneous_X _ i).pow (∑ l, n l - n j))).mul (hG j) using 1
    omega
  · have hp : x i ^ (∑ l, n l) = x i ^ (∑ l, n l - n j) * x i ^ n j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hq : ((∏ l, N l : ℕ) : Ω) = (N j : Ω) * ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : Ω) := by
      rw [← Nat.cast_mul, Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j)]
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, eq_intCast, Int.cast_natCast,
      map_natCast]
    rw [hp, hq]
    ring

theorem aeval_ne_zero_of_unit {L S : Type} [Field L] [CharZero L] [CommRing S] (g : S →+* Ω)
    (hg : Function.Injective g) (φ : S →+* L) {x : σ → Ω} {w : σ → L} {i : σ} (hx : x i ≠ 0) (hw : w i ≠ 0)
    (t : σ → S) (ht : ∀ j, g (t j) = x j / x i) (ht' : ∀ j, φ (t j) * w i = w j)
    {F : MvPolynomial σ ℤ} {n N : ℕ} (hN : N ≠ 0) (hF : F.IsHomogeneous n) {e : S} (he : IsUnit e)
    (hFe : MvPolynomial.aeval x F = (N : Ω) * x i ^ n * g e) : MvPolynomial.aeval w F ≠ 0 := by
  have h1 : x = fun j => x i * g (t j) := funext fun j => by rw [ht, mul_div_cancel₀ _ hx]
  have h2 : MvPolynomial.aeval x F = x i ^ n * g (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h1]
    rw [aeval_scale hF, aeval_map_hom]
  have h3 : MvPolynomial.aeval t F = (N : S) * e := by
    apply hg
    apply mul_left_cancel₀ (pow_ne_zero n hx)
    rw [← h2, hFe, map_mul, map_natCast]
    ring
  have h4 : w = fun j => w i * φ (t j) := funext fun j => by rw [← ht', mul_comm]
  have h5 : MvPolynomial.aeval w F = w i ^ n * φ (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h4]
    rw [aeval_scale hF, aeval_map_hom]
  rw [h5, h3, map_mul, map_natCast]
  exact mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero (Nat.cast_ne_zero.2 hN) (he.map φ).ne_zero)

end Forms

section Germs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unit_germ {p : Cpt ξ} (hinj : Function.Injective (genMap ξ p)) {s : Ω} (h : unitAt ξ p s) :
    ∃ e : X.presheaf.stalk p.1, IsUnit e ∧ genMap ξ p e = s := by
  obtain ⟨h0, ⟨e, rfl⟩, ⟨e', he'⟩⟩ := h
  refine ⟨e, IsUnit.of_mul_eq_one e' (hinj ?_), rfl⟩
  rw [map_mul, he', mul_inv_cancel₀ h0, map_one]

theorem unitAt_natCast [CharZero Ω] {L : Type} [Field L] [CharZero L] {zz : Spec (CommRingCat.of L) ⟶ X}
    (h : genPt ξ ⤳ centre zz) {r : ℕ} (hr : r ≠ 0) : unitAt ξ ⟨centre zz, h⟩ (r : Ω) := by
  have hu : IsUnit ((r : X.presheaf.stalk (centre zz))) := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo zz).hom).map_nonunit _ (IsUnit.mk0 _
      ((map_natCast (Scheme.stalkClosedPointTo zz).hom r).trans_ne ((Nat.cast_ne_zero (R := L)).2 hr)))
  obtain ⟨u, hu⟩ := hu
  have hv : genMap ξ ⟨centre zz, h⟩ (u : X.presheaf.stalk (centre zz)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine ⟨Nat.cast_ne_zero.2 hr, ⟨_, hv⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre zz))ˣ) : _), ?_⟩⟩
  rw [← hv]
  exact map_units_inv _ u

end Germs

theorem ratios_quotients_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE L _ _ z hz i k c hzi hzc
  classical
  obtain ⟨hblk, hvan⟩ := hz
  obtain ⟨zz, ⟨hsp, hco⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y hT L).1 z
    (fun k' => (hblk k').imp fun _ h => IsUnit.mk0 _ h) hvan
  let p : Cpt ξ := ⟨centre zz, hsp⟩
  have hinj : Function.Injective (genMap ξ p) := hT.gen.inj p
  have hfib : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := fun r hr hn => hn (unitAt_natCast hsp hr.ne_zero)
  obtain ⟨hyi, hrat⟩ := hco.2 k₀ i (IsUnit.mk0 _ hzi)
  obtain ⟨hyc, hrat'⟩ := hco.2 k c (IsUnit.mk0 _ hzc)
  have hgerm : ∀ i' : J k₀, ∃ t : X.presheaf.stalk (centre zz),
      genMap ξ p t = y ⟨k₀, i'⟩ / y ⟨k₀, i⟩ ∧ (Scheme.stalkClosedPointTo zz).hom t * z ⟨k₀, i⟩ = z ⟨k₀, i'⟩ := by
    intro i'
    obtain ⟨r, ⟨_, t, h1, h2⟩, h3⟩ := hrat i'
    exact ⟨t, h1, by rw [h2, h3]⟩
  choose t ht ht' using hgerm
  have hchart : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p := ⟨hyi, fun i' => ⟨t i', ht i'⟩⟩
  have hreg : ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ p := by
    intro j
    obtain ⟨r, ⟨_, u, h1, _⟩, _⟩ := hrat' j
    exact ⟨u, h1⟩
  choose s hsB hsU hsa using fun j => ((hE p hfib).2 i hchart).1 _ (hreg j)
  have hSU : unitAt ξ p (∏ j, s j) := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (hsU j).1, Subring.prod_mem _ fun j _ => (hsU j).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact Subring.prod_mem _ fun j _ => (hsU j).2.2
  have hSa : ∀ j, (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩) ∈
      Algebra.adjoin ℚ (Set.range fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_right_comm]
    exact Subalgebra.mul_mem _ (hsa j) (Subalgebra.prod_mem _ fun l _ => hsB l)
  obtain ⟨N, n, F, hN, hF, he⟩ := common_denominator (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i)
    (b := fun j => (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩)) fun j =>
      isFormQuot_of_mem (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i) hyi (hSa j)
  obtain ⟨e, heu, hee⟩ := exists_unit_germ hinj hSU
  refine ⟨n, F, hF, fun j => ?_, ?_⟩
  · rw [he j, he c, div_self hyc]
    field_simp
  · refine aeval_ne_zero_of_unit (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (w := fun i' : J k₀ => z ⟨k₀, i'⟩) (i := i)
      (genMap ξ p) hinj (Scheme.stalkClosedPointTo zz).hom hyi hzi t ht ht' hN (hF c) heu ?_
    rw [he c, div_self hyc, _root_.mul_one, hee]

end GlobalTheory.CompanionTheory.Ar.BlockRatio
