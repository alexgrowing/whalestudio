import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem splits_of_monic_OO {q : (OO p)[X]} (hq : q.Monic) : q.Splits := by
  refine Splits.of_splits_map_of_injective (i := (OO p).subtype) Subtype.val_injective
    (IsAlgClosed.splits _) fun a ha => ?_
  have h : IsIntegral (OO p) a := ⟨q, hq, by
    have := isRoot_of_mem_roots ha
    rwa [IsRoot, Polynomial.eval_map] at this⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨y, hy⟩

theorem exists_root_residue_OO {q : (OO p)[X]} (hq : q.Monic) {b : kb p}
    (hb : q.eval₂ (residue (OO p)) b = 0) : ∃ a : OO p, q.eval a = 0 ∧ residue (OO p) a = b := by
  have h0 : q.map (residue (OO p)) ≠ 0 := (hq.map _).ne_zero
  have h : b ∈ (q.map (residue (OO p))).roots := by
    rw [mem_roots h0, IsRoot, Polynomial.eval_map, hb]
  rw [(splits_of_monic_OO hq).roots_map_of_ne_zero h0, Multiset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, isRoot_of_mem_roots ha, rfl⟩

theorem isAlgClosed_kb : IsAlgClosed (kb p) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := OO p)) f) hf
  have hs : f.Splits := hq ▸ (splits_of_monic_OO hmon).map _
  exact hs.exists_eval_eq_zero (degree_pos_of_irreducible hirr).ne'

theorem charP_kb : CharP (kb p) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 GlobalTheory.ZH.natCast_residueField_OO

theorem exists_pow_eq_one_kb (x : kb p) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1 := by
  haveI := charP_kb (p := p)
  letI := ZMod.algebra (kb p) p
  have h : (algebraMap (ZMod p) (kb p)).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom (ZMod p)) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact GlobalTheory.ZH.isIntegral_int_residueField_OO
  have h' : IsIntegral (ZMod p) x := h x
  let K := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional h'
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨n, hn, e⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  exact ⟨n, hn, by simpa [y] using congrArg (fun u : Kˣ => ((u : K) : kb p)) e⟩

theorem algEquiv_mem_OO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p} (hx : x ∈ OO p) :
    σ x ∈ OO p := by
  rw [GlobalTheory.ZH.mem_OO_iff, ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one] at hx ⊢
  exact hx.map (σ.toAlgHom.restrictScalars ℤ_[p])

noncomputable def restrictOO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : OO p ≃+* OO p where
  toFun x := ⟨σ x, algEquiv_mem_OO σ x.2⟩
  invFun x := ⟨σ.symm x, algEquiv_mem_OO σ.symm x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) y)

theorem exists_int_map_eq_kb (q : ℤ_[p][X]) : ∃ g : ℤ[X], g.map (Int.castRingHom (kb p)) =
    q.map ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) hc
  rw [map_sub, map_mul, map_natCast, map_natCast, GlobalTheory.ZH.natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
  exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩

theorem exists_residue_restrictOO_eq (a : OO p) (b' : kb p)
    (h : ∀ g : ℤ[X], aeval (residue (OO p) a) g = 0 → aeval b' g = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, residue (OO p) (restrictOO σ a) = b' := by
  have ha : IsIntegral ℤ_[p] (a : PadicAlgCl p) :=
    (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((GlobalTheory.ZH.mem_OO_iff _).1 a.2)
  set f := minpoly ℤ_[p] (a : PadicAlgCl p) with hf
  have key : ∀ c : OO p, (((f.map (GlobalTheory.ZH.padicIntToOO p)).eval c : OO p) : PadicAlgCl p) =
      aeval (c : PadicAlgCl p) f := fun c => by
    rw [Polynomial.eval_map]
    exact hom_eval₂ f (GlobalTheory.ZH.padicIntToOO p) (OO p).subtype c
  obtain ⟨g, hg⟩ := exists_int_map_eq_kb f
  have e : ∀ b : kb p, aeval b g = (f.map (GlobalTheory.ZH.padicIntToOO p)).eval₂ (residue (OO p)) b := fun b => by
    rw [eval₂_map, ← Polynomial.eval_map, ← hg, Polynomial.eval_map]
    rfl
  have h1 : aeval (residue (OO p) a) g = 0 := by
    have : (f.map (GlobalTheory.ZH.padicIntToOO p)).eval a = 0 := Subtype.ext ((key a).trans (minpoly.aeval _ _))
    rw [e, eval₂_hom, this, map_zero]
  obtain ⟨a', ha', rfl⟩ := exists_root_residue_OO ((minpoly.monic ha).map (GlobalTheory.ZH.padicIntToOO p))
    ((e b').symm.trans (h g h1))
  have h2 : aeval (a' : PadicAlgCl p) (minpoly ℚ_[p] (a : PadicAlgCl p)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] ha, aeval_map_algebraMap, ← hf, ← key, ha']
    rfl
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) h2
  exact ⟨σ, congrArg _ (Subtype.ext hσ)⟩

theorem exists_ringEquiv_residue_eq (F : Type) [Field F] [Finite F] (r r' : F →+* kb p) :
    ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), residue (OO p) a = r x → residue (OO p) (σ a) = r' x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  obtain ⟨a₀, ha₀⟩ := residue_surjective (r u)
  obtain ⟨σ, hσ⟩ := exists_residue_restrictOO_eq a₀ (r' u) fun g hg => by
    rw [ha₀] at hg
    have h1 := aeval_algHom_apply r.toIntAlgHom (u : F) g
    have h2 := aeval_algHom_apply r'.toIntAlgHom (u : F) g
    have h3 : aeval (u : F) g = 0 := r.injective ((h1.symm.trans hg).trans (map_zero r).symm)
    exact h2.trans (by rw [h3, map_zero])
  refine ⟨restrictOO σ, fun x a ha => ?_⟩
  let τ := ResidueField.mapEquiv (restrictOO σ)
  have hτ : ∀ c : OO p, τ (residue (OO p) c) = residue (OO p) (restrictOO σ c) := fun c => rfl
  rw [← hτ, ha]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  have hx' : x = (u : F) ^ n := by simpa using (congrArg Units.val hn).symm
  rw [hx', map_pow, map_pow, map_pow, ← ha₀, hτ, hσ]

theorem kb_isAlgClosed_and_conj : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x :=
  fun _ _ => ⟨isAlgClosed_kb, exists_pow_eq_one_kb, exists_ringEquiv_residue_eq⟩

end GlobalTheory.ZJ
