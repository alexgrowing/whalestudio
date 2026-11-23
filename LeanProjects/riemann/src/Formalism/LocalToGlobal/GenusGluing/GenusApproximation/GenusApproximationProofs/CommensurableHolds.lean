import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open scoped TensorProduct

section LocEqSec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem loc_coe_algebraMap (r : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (r : F) := rfl

theorem loc_hcompl_prop (PP : Pl E) (s : 𝓞 E) (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) PP.asIdeal) :
    s ∉ PP.asIdeal ∧ starO s ∉ PP.asIdeal := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    exact ⟨hx.1, hx.2 (starO x) (starO_coe x)⟩
  | one =>
    have h1 : starO (1 : 𝓞 E) = 1 := map_one (starOHom (E := E))
    rw [h1]
    exact ⟨PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one),
      PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)⟩
  | mul x y _ _ hx hy =>
    have hm : starO (x * y) = starO x * starO y := map_mul (starOHom (E := E)) x y
    rw [hm]
    exact ⟨fun h => (PP.isPrime.mem_or_mem h).elim hx.1 hy.1,
      fun h => (PP.isPrime.mem_or_mem h).elim hx.2 hy.2⟩

end LocEqSec

theorem localEquality_holds : LocEq := by
  intro F E _ _ _ _ _ _ hc n PP L
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    obtain ⟨hs1, hs2⟩ := loc_hcompl_prop PP s hs
    set m : 𝓞 E := s * starO s with hm
    have hfix : star ((m : 𝓞 E) : E) = (m : E) := by
      show star ((s : E) * ((starO s : 𝓞 E) : E)) = (s : E) * ((starO s : 𝓞 E) : E)
      rw [starO_coe, star_mul', star_star, mul_comm]
    obtain ⟨a, ha⟩ := (hc.fixed (m : E)).1 hfix
    have hint : IsIntegral ℤ a := by
      have h2 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact m.2
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h2
    set r : 𝓞 F := ⟨a, hint⟩ with hr
    have hrm : algebraMap (𝓞 F) (𝓞 E) r = m := by
      apply RingOfIntegers.ext
      rw [loc_coe_algebraMap]
      exact ha
    have hmp : m ∉ PP.asIdeal := fun h => (PP.isPrime.mem_or_mem h).elim hs1 hs2
    refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨m, ⟨r, ?_, hrm⟩, ?_⟩
    · show r ∉ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap, hrm]
      exact hmp
    · rw [hm, mul_comm, mul_smul]
      exact L.smul_mem _ hsx
  · apply Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le
    rintro _ ⟨r, hr, rfl⟩
    apply Submonoid.subset_closure
    have hr' : algebraMap (𝓞 F) (𝓞 E) r ∉ PP.asIdeal := by
      intro h
      apply hr
      show r ∈ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap]
      exact h
    refine ⟨hr', fun t ht htp => hr' ?_⟩
    have hfix : star (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) :=
      (hc.fixed _).2 ⟨(r : F), rfl⟩
    rw [hfix] at ht
    have : t = algebraMap (𝓞 F) (𝓞 E) r := FaithfulSMul.algebraMap_injective (𝓞 E) E ht
    rw [← this]
    exact htp

section CommensSec

variable {E : Type} [Field E] [NumberField E]

theorem commens_denoms (s : Finset E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (d : E) * x := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) s
  refine ⟨y, hy, fun x hx => ⟨⟨_, hint x hx⟩, ?_⟩⟩
  show (y • x : E) = _
  rw [zsmul_eq_mul]

end CommensSec

theorem commensurable_holds : Commens := by
  intro F E _ _ _ _ _ n N hN
  classical
  obtain ⟨s, hs⟩ := hN.fg
  obtain ⟨d1, hd1, h1⟩ := commens_denoms (s.biUnion fun x => Finset.univ.image x)
  have hA : ∀ y ∈ N, ((d1 : 𝓞 E)) • y ∈ stdLat E n := by
    have hle : N ≤ (stdLat E n).comap (((d1 : 𝓞 E)) • LinearMap.id) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [stdLat, Submodule.mem_pi]
      intro i _
      rw [Submodule.mem_one]
      obtain ⟨o, ho⟩ := h1 (x i) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      refine ⟨o, ?_⟩
      rw [ho, Pi.smul_apply, Algebra.smul_def, map_intCast]
    intro y hy
    have := hle hy
    simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using this
  have hB : ∀ i : Fin n, Pi.single i (1 : E) ∈ Submodule.span E (N : Set (Sp E n)) := by
    intro i
    rw [hN.span_eq_top]
    trivial
  choose f t ht _ hsum using fun i => Submodule.mem_span_iff_exists_finset_subset.1 (hB i)
  obtain ⟨d2, hd2, h2⟩ := commens_denoms (Finset.univ.biUnion fun i => (t i).image (f i))
  have hsingle : ∀ i : Fin n, ((d2 : 𝓞 E)) • Pi.single i (1 : E) ∈ N := by
    intro i
    rw [← hsum i, Finset.smul_sum]
    apply Submodule.sum_mem
    intro a ha
    obtain ⟨o, ho⟩ := h2 (f i a) (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨a, ha, rfl⟩⟩)
    have e : ((d2 : 𝓞 E)) • (f i a • a) = o • a := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul E, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact N.smul_mem o (ht i ha)
  have hC : ∀ y ∈ stdLat E n, ((d2 : 𝓞 E)) • y ∈ N := by
    intro y hy
    rw [stdLat, Submodule.mem_pi] at hy
    choose o ho using fun i => Submodule.mem_one.1 (hy i (Set.mem_univ i))
    have ey : y = ∑ i, o i • Pi.single i (1 : E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, ← ho j, Algebra.smul_def]
    rw [ey, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    rw [smul_comm]
    exact N.smul_mem (o i) (hsingle i)
  refine ⟨((d1 * d2 : ℤ) : 𝓞 F), ?_, ?_, ?_⟩
  · exact_mod_cast mul_ne_zero hd1 hd2
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_comm, mul_smul]
    exact (stdLat E n).smul_mem _ (hA y hy)
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_smul]
    exact N.smul_mem _ (hC y hy)
