import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem laurent_adjoin_eq_of_image_eq {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (h0 : 0 < Module.finrank ℤ O) :
    Function.Injective (algebraMap (𝓞 F) O) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hI : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmem : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : 𝓞 F) ∈ Ideal.span {x} := Ideal.absNorm_mem _
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  have hn0 : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : O) = 0 := by
    rw [← map_natCast (algebraMap (𝓞 F) O), ← hy, map_mul, hx, mul_zero]
  have h2 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (1 : O) =
      ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (0 : O) := by
    rw [smul_zero, zsmul_eq_mul, _root_.mul_one]
    exact_mod_cast h1
  have h3 : (1 : O) = 0 := smul_right_injective O (by exact_mod_cast hn0) h2
  haveI : Subsingleton O := subsingleton_of_zero_eq_one h3.symm
  rw [Module.finrank_zero_of_subsingleton] at h0
  exact lt_irrefl 0 h0

private theorem wachExpansion_smul_compatible {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F)
    (hinj : Function.Injective (algebraMap (𝓞 F) O)) (x : O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c := by
  classical
  let b := Module.finBasis ℤ (𝓞 F)
  let v : Option (Fin (Module.finrank ℤ (𝓞 F))) → O :=
    fun o => Option.elim o x (fun i => algebraMap (𝓞 F) O (b i))
  have hcard : ¬ LinearIndependent ℤ v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hr, RingOfIntegers.rank] at hle
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hcard
  rw [Fintype.sum_option] at hg
  have hmap : algebraMap (𝓞 F) O (∑ j, g (some j) • b j) =
      ∑ j, g (some j) • algebraMap (𝓞 F) O (b j) := by
    rw [map_sum]
    simp only [map_zsmul]
  have hg' : g none • x + algebraMap (𝓞 F) O (∑ j, g (some j) • b j) = 0 := by
    rw [hmap]
    simpa [v] using hg
  have hnone : g none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg'
    have hc0 : ∑ j, g (some j) • b j = 0 := hinj (by rw [hg', map_zero])
    have hall := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun j => g (some j)) hc0
    cases i with
    | none => exact hi h0
    | some j => exact hi (hall j)
  refine ⟨g none, hnone, -(∑ j, g (some j) • b j), ?_⟩
  rw [map_neg, eq_neg_iff_add_eq_zero]
  exact hg'

private theorem surj_comm {F O : Type} [Field F] [NumberField F] [CommRing O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O]
    (hinj : Function.Injective (algebraMap (𝓞 F) O))
    (hs : ∀ x : O, ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  classical
  intro x
  obtain ⟨e, he, c, hc⟩ := hs x
  obtain ⟨P, hPm, hPx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have hQ : Polynomial.aeval (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hc, algebraMap_int_eq, Int.coe_castRingHom, zsmul_eq_mul]
  rw [hex, Polynomial.aeval_algebraMap_apply] at hQ
  have hQ' : Polynomial.aeval c (P.scaleRoots e) = 0 := hinj (by rw [hQ, map_zero])
  have hQF : Polynomial.aeval (c : F) (P.scaleRoots e) = 0 := by
    have h0 := congrArg (algebraMap (𝓞 F) F) hQ'
    rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h0
  have he' : ((e : ℤ) : F) ≠ 0 := by exact_mod_cast he
  have hmul : algebraMap ℤ F e * ((c : F) / e) = (c : F) := by
    rw [eq_intCast]
    field_simp
  have hz : Polynomial.eval₂ (algebraMap ℤ F) ((c : F) / e) P = 0 := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ F) ((c : F) / e) e
    rw [hmul, ← Polynomial.aeval_def, hQF] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by rwa [eq_intCast]))
  let d : 𝓞 F := ⟨(c : F) / e, ⟨P, hPm, hz⟩⟩
  have hed : (e : 𝓞 F) * d = c := by
    apply RingOfIntegers.ext
    show ((e : 𝓞 F) : F) * ((c : F) / e) = (c : F)
    have hcoe : ((e : 𝓞 F) : F) = (e : F) := by
      first
        | simp
        | exact map_intCast (algebraMap (𝓞 F) F) e
    rw [hcoe]
    field_simp
  refine ⟨d, ?_⟩
  apply smul_right_injective O he
  show e • algebraMap (𝓞 F) O d = e • x
  rw [hc, ← hed, map_mul, map_intCast, zsmul_eq_mul]

private theorem exists_finset_adjoin_laurent_preimage {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  have hpos : 0 < Module.finrank ℤ O := by
    rw [hr]
    exact Module.finrank_pos
  have hinj := laurent_adjoin_eq_of_image_eq (F := F) (O := O) hpos
  have hs := wachExpansion_smul_compatible (F := F) (O := O) hr hinj
  have hcomm : ∀ x y : O, x * y = y * x := by
    intro x y
    obtain ⟨a, ha, c, hc⟩ := hs x
    obtain ⟨b, hb, c', hc'⟩ := hs y
    apply smul_right_injective O (mul_ne_zero ha hb)
    show (a * b) • (x * y) = (a * b) • (y * x)
    calc (a * b) • (x * y) = (a • x) * (b • y) := by rw [smul_mul_smul_comm]
      _ = algebraMap (𝓞 F) O (c * c') := by rw [hc, hc', map_mul]
      _ = algebraMap (𝓞 F) O (c' * c) := by rw [_root_.mul_comm c c']
      _ = (b • y) * (a • x) := by rw [hc, hc', map_mul]
      _ = (a * b) • (y * x) := by rw [smul_mul_smul_comm, _root_.mul_comm b a]
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  exact surj_comm hinj hs

theorem UpperTheory.Gal.Ord.surjO :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  apply exists_finset_adjoin_laurent_preimage
  rw [D.rankO, hm]
  simp
