import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
import Development.EtaleCohomology.TateTwists.EtaleSheafSectionLocallyIffOfPresheafFacts

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimLocPf

theorem ring_core {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (q : ℕ) [NeZero q]
    (hq : IsUnit (q : R)) (ζ x : R) (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0)
    (hx : x ^ q = 1) :
    ∃ n < q, ∃ s : R, φ s ≠ 0 ∧ s * (x - ζ ^ n) = 0 ∧ IsPrimitiveRoot (φ ζ) q := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map φ; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have hζK : IsPrimitiveRoot (φ ζ) q := by
    rw [← Polynomial.isRoot_cyclotomic_iff]
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ (Polynomial.cyclotomic q ℤ)
    rw [hζ, map_zero] at h
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic] using h
  have hζq : ζ ^ q = 1 := by
    obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h := congrArg (Polynomial.aeval ζ) hc
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.mp h
  have hxK : (φ x) ^ q = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨n, hn, hnx⟩ := hζK.eq_pow_of_pow_eq_one hxK
  set t := x * ζ ^ (q - n) with ht
  refine ⟨n, hn, ∑ i ∈ Finset.range q, t ^ i, ?_, ?_, hζK⟩
  · have h1 : φ t = 1 := by
      rw [ht, map_mul, map_pow, ← hnx, ← pow_add, Nat.add_sub_cancel' hn.le, hζK.pow_eq_one]
    simp [map_sum, map_pow, h1, hqK]
  · have hg : (∑ i ∈ Finset.range q, t ^ i) * (t - 1) = 0 := by
      rw [geom_sum_mul, ht, mul_pow, hx, ← pow_mul, mul_comm (q - n) q, pow_mul, hζq, one_pow,
        one_mul, sub_self]
    have : x - ζ ^ n = (t - 1) * ζ ^ n := by
      rw [ht, sub_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hn.le, hζq, mul_one, one_mul]
    rw [this, ← mul_assoc, hg, zero_mul]

theorem isUnit_of_basicOpen_top (X : Scheme.{0}) (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  have key : ∀ (O : X.Opens) (_ : O = ⊤) (hle : O ≤ ⊤),
      IsUnit (X.presheaf.map (homOfLE hle).op f) → IsUnit f := by
    intro O hO; subst hO; intro hle hu; simpa using hu
  exact key _ h (X.basicOpen_le f) (X.toRingedSpace.isUnit_res_basicOpen f)

theorem affine_nbhd (U : Scheme.{0}) (s : Γ(U, ⊤)) (y : U) (hy : y ∈ U.basicOpen s) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      IsUnit (g.appTop.hom s) := by
  obtain ⟨W, hWa, hyW, hW⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ U.basicOpen s :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) hy
  refine ⟨W, Scheme.Opens.ι W, hWa, inferInstance, by simpa using hyW, ?_⟩
  apply isUnit_of_basicOpen_top
  rw [← Scheme.preimage_basicOpen_top]
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact hW (by have h := Set.mem_range_self (f := W.ι) z; simpa using h)

theorem cyc_pow_eq_one {R : Type} [CommRing R] (q : ℕ) (ζ : R)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
  exact sub_eq_zero.mp h

theorem mono_pow {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ ^ a) →
    ∃ a : ℕ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ a := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ a
  rw [ha, map_pow]

theorem part3 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤))
    (hx : x ^ q = 1) : Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_pow x ζ.1)]
  intro y
  obtain ⟨n, -, s, hs, hsx, -⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 x ζ.2.2 hx
  have hy : y ∈ U.basicOpen s := (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, n, ?_⟩
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

theorem mono_unit {q : ℕ} {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : (ZMod q)ˣ, g.appTop.hom x = g.appTop.hom ζ ^ (a : ZMod q).val) →
    ∃ a : (ZMod q)ˣ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ (a : ZMod q).val := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ (a : ZMod q).val
  rw [ha, map_pow]

theorem part2 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_unit ξ.1 ζ.1)]
  intro y
  obtain ⟨n, hn, s, hs, hsx, hζK⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 ξ.1 ζ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  obtain ⟨-, -, -, -, -, hξK⟩ := ring_core (U.Γevaluation y).hom q ξ.2.1 ξ.1 ξ.1 ξ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  have hφ : (U.Γevaluation y).hom ξ.1 = (U.Γevaluation y).hom ζ.1 ^ n := by
    have h := congrArg (U.Γevaluation y).hom hsx
    rw [map_mul, map_sub, map_pow, map_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)
  have hcop : n.Coprime q := (hζK.pow_iff_coprime (Nat.pos_of_neZero q) n).mp (hφ ▸ hξK)
  have hy : y ∈ U.basicOpen s :=
    (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

end LateralTheory.EtaleFoundations.PrimLocPf

namespace LateralTheory.EtaleFoundations

def EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

def EtaleLocallyKummerRootsOfUnits : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem etale_locally_roots_of_unity_structure_of_exists_and_kummer (h1 : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder) (h4 : EtaleLocallyKummerRootsOfUnits) :
    EtalePrimitiveRootsExistLocally := by
  intro q _ U
  exact ⟨h1 q U, PrimLocPf.part2 q U, fun ζ x hx => PrimLocPf.part3 q U ζ x hx,
    fun hq u => h4 q U hq u⟩

end LateralTheory.EtaleFoundations
