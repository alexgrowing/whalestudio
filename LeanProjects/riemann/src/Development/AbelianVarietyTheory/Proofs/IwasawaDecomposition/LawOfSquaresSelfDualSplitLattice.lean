import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSquareAbsNormConjInvariantMovedPrimesIdealStatement

set_option autoImplicit false

namespace GlobalTheory.LawOfSquares

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity GlobalTheory.BetaEx GlobalTheory.ClassScalarCompare

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

omit [NumberField E] in
theorem idlE_mul' (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J :=
  Submodule.map_mul I J (Algebra.ofId (𝓞 E) E)

theorem idlE_inj : Function.Injective (idlE : Ideal (𝓞 E) → Submodule (𝓞 E) E) :=
  Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective (𝓞 E) E)

omit [NumberField E] in
theorem detSpan_std_le : detSpan (stdLat E n) ≤ 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  choose b hb using fun i => (mem_std _).1 (hv i)
  refine Submodule.mem_one.2 ⟨(Matrix.of fun i j => b j i).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hb j i

omit [NumberField E] in
theorem smul_single_mem (m : 𝓞 E) (i : Fin n) : m • (Pi.single i 1 : Fin n → E) ∈ stdLat E n :=
  Submodule.smul_mem _ _ ((mem_std _).2 fun j => by
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩])

omit [NumberField E] in
theorem pow_mem_detSpan {M : Submodule (𝓞 E) (Fin n → E)} (m : 𝓞 E)
    (h : ∀ i, m • (Pi.single i 1 : Fin n → E) ∈ M) : ((m ^ n : 𝓞 E) : E) ∈ detSpan M := by
  have := det_mem (M := M) ((m : E) • (1 : Matrix (Fin n) (Fin n) E)) (fun i => by
    convert h i using 1
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm, Algebra.smul_def])
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  simpa using this

omit [NumberField E] in
theorem detSpan_std : detSpan (stdLat E n) = 1 := by
  refine le_antisymm detSpan_std_le ?_
  rw [Submodule.one_le]
  simpa using pow_mem_detSpan (M := stdLat E n) 1 (smul_single_mem 1)

omit [NumberField E] in
theorem exists_idlE {M : Submodule (𝓞 E) E} (h : M ≤ 1) : ∃ 𝔟 : Ideal (𝓞 E), M = idlE 𝔟 := by
  refine ⟨M.comap (Algebra.linearMap (𝓞 E) E), (Submodule.map_comap_eq_of_le ?_).symm⟩
  intro x hx
  exact Submodule.mem_one.1 (h hx)

variable [IsCMField E]

theorem absNorm_conjId (H : Host E) (I : Ideal (𝓞 E)) : Ideal.absNorm (conjId H I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (conjId H I) H.bar rfl).toEquiv).symm

theorem eq_of_le_of_absNorm {I J : Ideal (𝓞 E)} (h : I ≤ J) (h0 : J ≠ ⊥) (e : Ideal.absNorm I = Ideal.absNorm J) :
    I = J := by
  obtain ⟨K, rfl⟩ := Ideal.dvd_iff_le.2 h
  have h1 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [map_mul, mul_eq_left₀ h1, Ideal.absNorm_eq_one_iff] at e
  rw [e, Ideal.mul_top]

theorem index_eq (H : Host E) (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E))
    (hL : (⟨L⟩ : GenLat E n).Unimod) (hS : GenLat.SplitSupp H (⟨L⟩ : GenLat E n))
    (h1 : cc ⊔ conjId H cc = ⊤) (h2 : detSpan L * idlE (conjId H cc) = idlE cc) :
    ∃ k : ℕ, k ≠ 0 ∧ (L ⊓ stdLat E n).toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm cc * k ^ 2 := by
  have hb : Bdd (stdLat E n ⊔ L) := by
    obtain ⟨k, hk, h⟩ := bdd_of_unimod ⟨L⟩ hL
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [smul_add]
    exact add_mem (Submodule.smul_mem _ _ hx) (h y hy)
  obtain ⟨𝔞, a0, e1, e2, e3⟩ := GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices E n L (stdLat E n) hb fun m _ => exists_smul_std m
  obtain ⟨𝔟, e4⟩ := exists_idlE ((detSpan_mono (inf_le_right : L ⊓ stdLat E n ≤ _)).trans detSpan_std_le)
  rw [detSpan_std, smul_eq_idlE_mul] at e2
  rw [e4, smul_eq_idlE_mul] at e1
  have c0 := absNorm_ne_zero h1
  have c1 : cc ≠ ⊥ := by rwa [Ne, Ideal.absNorm_eq_zero_iff] at c0
  have c2 : conjId H cc ≠ ⊥ := by rwa [Ne, ← Ideal.absNorm_eq_zero_iff, absNorm_conjId]
  have e5 : 𝔟 * conjId H cc = 𝔞 * cc := idlE_inj (by rw [idlE_mul', idlE_mul', e1, mul_assoc, h2])
  have e6 : Ideal.absNorm 𝔟 = Ideal.absNorm 𝔞 := by
    have := congrArg Ideal.absNorm e5
    rw [map_mul, map_mul, absNorm_conjId] at this
    exact mul_right_cancel₀ c0 this
  have pair : ∀ v ∈ L ⊓ stdLat E n, ∀ w ∈ stdLat E n ⊔ L,
      ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range := by
    intro v hv w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    refine add_mem (Subring.sum_mem _ fun j _ => ?_) ((hL v).1 hv.1 y hy)
    obtain ⟨a, ha⟩ := (mem_std _).1 hv.2 j
    obtain ⟨b, hb⟩ := (mem_std _).1 hx j
    exact mul_mem ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩ ⟨b, hb⟩
  have e7 : idlE (conjId H 𝔟) * detSpan (stdLat E n ⊔ L) ≤ 1 := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    rw [← conjMod_idlE, mem_conjMod, ← e4] at hx
    have := GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing E n _ _ pair _ hx y hy
    rw [IsCMField.complexConj_apply_apply] at this
    exact Submodule.mem_one.2 this
  have e8 : conjId H 𝔟 = 𝔞 := by
    refine eq_of_le_of_absNorm ?_ a0 (by rw [absNorm_conjId, e6])
    have : idlE (conjId H 𝔟) ≤ idlE 𝔞 := by
      calc idlE (conjId H 𝔟) = idlE (conjId H 𝔟) * 1 := (mul_one _).symm
        _ = idlE 𝔞 * (idlE (conjId H 𝔟) * detSpan (stdLat E n ⊔ L)) := by rw [e2]; ring
        _ ≤ idlE 𝔞 * 1 := mul_le_mul_right e7 _
        _ = _ := mul_one _
    exact (Submodule.map_le_map_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) E) _ _).1 this
  obtain ⟨𝔡, rfl⟩ : cc ∣ 𝔟 :=
    (Ideal.isCoprime_iff_sup_eq.2 h1).dvd_of_dvd_mul_right ⟨𝔞, by rw [e5, mul_comm]⟩
  have e9 : conjId H 𝔡 = 𝔡 := by
    have : conjId H (cc * 𝔡) = conjId H cc * conjId H 𝔡 := Ideal.map_mul _ _ _
    rw [← e8, this] at e5
    apply mul_left_cancel₀ (mul_ne_zero c1 c2)
    calc _ = conjId H cc * conjId H 𝔡 * cc := by ring
      _ = _ := by rw [← e5]; ring
  have d0 : Ideal.absNorm 𝔡 ≠ 0 := by
    rintro h
    rw [map_mul, h, mul_zero, eq_comm, Ideal.absNorm_eq_zero_iff] at e6
    exact a0 e6
  obtain ⟨m, -, -, m2, m3⟩ := hS
  have hm : m ^ n ∈ 𝔡 := by
    have := pow_mem_detSpan (M := L ⊓ stdLat E n) m fun i => ⟨m2 (Submodule.smul_mem_smul
      (Ideal.mem_span_singleton_self m) (by simpa using smul_single_mem (E := E) 1 i)), smul_single_mem m i⟩
    rw [e4] at this
    obtain ⟨y, hy, e⟩ := this
    have : y = m ^ n := RingOfIntegers.ext e
    rw [← this]
    exact Ideal.le_of_dvd (Dvd.intro_left cc rfl) hy
  obtain ⟨k, hk⟩ := GlobalTheory.T.isSquare_absNorm_conjInvariant_movedPrimes_ideal E H 𝔡 (by rwa [Ne, Ideal.absNorm_eq_zero_iff] at d0) e9
    fun P hP hle => m3 P hP (hP.mem_of_pow_mem (r := m) n (hle hm))
  refine ⟨k, by rintro rfl; exact d0 hk, ?_⟩
  rw [← e3, ← e6, map_mul, hk, sq]

theorem law_of_squares : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n r : ℕ), Odd r → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)), (⟨L⟩ : GenLat E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) → cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc → ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm cc : ℚ) := by
  intro E _ _ _ H n r ⟨s, hs⟩ L cc hL hS h1 h2
  obtain ⟨k, k0, e⟩ := index_eq H L cc hL hS h1 h2
  have e' : ((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index =
      Ideal.absNorm cc * k ^ 2 := e
  have c0 : Ideal.absNorm cc ≠ 0 := absNorm_ne_zero (H := H) h1
  rw [e', hs]
  generalize Ideal.absNorm cc = N at c0
  have : (0 : ℚ) < N := by positivity
  have : (0 : ℚ) < k := by positivity
  refine ⟨((N : ℚ) ^ s * (k : ℚ) ^ (2 * s + 1))⁻¹, by positivity, ?_⟩
  push_cast
  field_simp
  ring

end GlobalTheory.LawOfSquares
