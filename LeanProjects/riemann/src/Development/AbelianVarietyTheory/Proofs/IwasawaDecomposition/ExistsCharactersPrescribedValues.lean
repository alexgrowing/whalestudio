import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem exists_chars_zmod {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z (p * (p - 1))) :
    ∃ (ψ : AddChar (ZMod p) K) (om : (ZMod p)ˣ →* Kˣ), ψ 1 ≠ 1 ∧ Function.Injective om := by
  haveI := Fact.mk hp
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hpos : 0 < p * (p - 1) := Nat.mul_pos hp.pos hp1
  have h1 : IsPrimitiveRoot (z ^ (p - 1)) p := hz.pow hpos (mul_comm _ _)
  have h2 : IsPrimitiveRoot (z ^ p) (p - 1) := hz.pow hpos rfl
  obtain ⟨u, hu⟩ := h2.isUnit hp1.ne'
  have h3 : IsPrimitiveRoot u (p - 1) := IsPrimitiveRoot.coe_units_iff.1 (hu ▸ h2)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hou : orderOf u = p - 1 := h3.eq_orderOf.symm
  refine ⟨AddChar.zmodChar p h1.pow_eq_one, monoidHomOfForallMemZpowers hg (g' := u) (by rw [hog, hou]), ?_, ?_⟩
  · rw [AddChar.zmodChar_apply, ZMod.val_one, pow_one]
    exact h1.ne_one hp.one_lt
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    rw [map_zpow, monoidHomOfForallMemZpowers_apply_gen, ← orderOf_dvd_iff_zpow_eq_one, hou, ← hog] at hx
    exact orderOf_dvd_iff_zpow_eq_one.1 hx

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

theorem exists_chars_of_roots {X : Fields} (Pr : Primes X) (hPr : Pr.Ok) (m : ℕ) (hm : ∀ i, 2 * m < Pr.g i - 1)
    (hz : ∀ i, ∃ z : X.K, IsPrimitiveRoot z (Pr.g i * (Pr.g i - 1)))
    (mu : Fin m → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (eta : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) :
    ∃ Ch : Chars X Pr m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  classical
  have h0 : ∀ i, ∃ (ψ : AddChar (ZMod (Pr.g i)) X.K) (om : (ZMod (Pr.g i))ˣ →* X.Kˣ),
      ψ 1 ≠ 1 ∧ Function.Injective om := fun i => by
    obtain ⟨z, hz⟩ := hz i
    exact exists_chars_zmod (hPr.g_prime i) hz
  choose ψ om hψ hom using h0
  have hmem : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := fun w => by
    have h := w.2
    unfold Primes.vGs at h
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hg : Function.Injective Pr.g := by
    intro i j hij
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all
  have h1 : ∀ w : {w // w ∈ Pr.vGs}, ∃ (ψw : AddChar (𝓞 X.E ⧸ w.1.asIdeal) X.K)
      (omw : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ), ∀ i, w.1 ∈ Pr.vG i →
      ∃ φ : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i), (∀ x, ψw x = ψ i (φ x)) ∧
        ∀ (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (a : (ZMod (Pr.g i))ˣ), φ x = a → omw x = om i a := fun w => by
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ⟩ := nonempty_equiv_zmod (hPr.g_prime i) w.1 (hPr.vG_norm i w.1 hi)
    refine ⟨(ψ i).compAddMonoidHom φ.toAddMonoidHom, (om i).comp (Units.map φ.toMonoidHom), fun i' hi' => ?_⟩
    obtain rfl : i = i' := hg ((hPr.vG_norm i w.1 hi).symm.trans (hPr.vG_norm i' w.1 hi'))
    refine ⟨φ, fun x => rfl, fun x a h => ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Units.ext h
  choose ψw omw hw using h1
  refine ⟨⟨ψw, fun j w => omw w ^ (2 * (j.1 + 1)), mu, eta⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro w h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, h1, -⟩ := hw w i hi
    apply hψ i
    rw [← map_one φ, ← h1]
    exact DFunLike.congr_fun h 1
  · intro w j j' h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, -, h2⟩ := hw w i hi
    have hj := j.2
    have hj' := j'.2
    have hmi := hm i
    have h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1) := by
      refine eq_of_pow_eq (hPr.g_prime i) (hom i) (by omega) (by omega) fun a => ?_
      rw [← h2 (Units.map φ.symm.toMonoidHom a) a (φ.apply_symm_apply _)]
      exact DFunLike.congr_fun h _
    exact Fin.ext (by omega)
  · intro i w w' hi hi' j a x x' hx hx'
    obtain ⟨φ, -, h2⟩ := hw w i hi
    obtain ⟨φ', -, h2'⟩ := hw w' i hi'
    show omw w x ^ _ = omw w' x' ^ _
    rw [h2 x (Units.map φ.toMonoidHom x) rfl, h2' x' (Units.map φ.toMonoidHom x)]
    show φ' x' = φ x
    rw [hx, hx', map_intCast, map_intCast]
  · intro i w w' hi hi' a
    obtain ⟨φ, h1, -⟩ := hw w i hi
    obtain ⟨φ', h1', -⟩ := hw w' i hi'
    show ψw w _ = ψw w' _
    rw [h1, h1', map_intCast φ, map_intCast φ']
  · intro i
    refine ⟨om i, hom i, fun w hi j a x hx => ?_⟩
    haveI := Fact.mk (hPr.g_prime i)
    obtain ⟨φ, -, h2⟩ := hw w i hi
    show omw w x ^ _ = _
    rw [h2 x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])]

theorem exists_chars : ∀ (B : Base) (X : PreX B.toPre) (mu : Fin B.R.m → HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ)
    (eta : HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ),
    ∃ Ch : Chars B.fields (B.primes X) B.R.m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  intro B X mu eta
  refine exists_chars_of_roots (B.primes X) (GlobalTheory.BasePrimes.primes_ok B X).1 B.R.m (fun i => ?_) (fun i => ?_) mu eta
  · have h1 := (B.primes_sizes X).g_big i
    have h2 := B.R.m_add_three_le_k
    have h3 : 0 < B.fields.f := by
      rw [B.fields_f]
      unfold Ranks.f Ranks.n
      positivity
    refine lt_of_le_of_lt ?_ h1
    nlinarith
  · have hp := B.host.g_prime i
    obtain ⟨z, -, hz⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
    have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hne

end GlobalTheory.BaseChars
