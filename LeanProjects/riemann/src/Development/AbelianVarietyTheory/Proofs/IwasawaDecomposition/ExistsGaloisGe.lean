import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberFieldStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FrameVal

theorem exists_galois_ge (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ IsGalois ℚ N ∧ M ≤ N := by
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  exact ⟨IntermediateField.normalClosure ℚ M ℂ, inferInstance, {}, IntermediateField.le_normalClosure M⟩

theorem exists_roots (n : ℕ) (hn : 0 < n) :
    ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ ∀ x : ℂ, x ^ n = 1 → x ∈ N := by
  have hfin : {x : ℂ | x ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun x hx => ?_
    simpa [Polynomial.mem_nthRoots hn] using hx
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ {x : ℂ | x ^ n = 1}, IntermediateField.finiteDimensional_adjoin fun x hx => ?_,
    fun x hx => IntermediateField.subset_adjoin _ _ hx⟩
  exact IsIntegral.of_pow hn (by rw [show x ^ n = 1 from hx]; exact isIntegral_one)

theorem valuesIn_mono {L : Type} [Field L] [NumberField L] {χ : HChar L} {s : ℝ} {M N : IntermediateField ℚ ℂ}
    (h : χ.ValuesIn s M.val.toRingHom) (hMN : M ≤ N) : χ.ValuesIn s N.val.toRingHom := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨⟨y, hMN y.2⟩, hy⟩

theorem exists_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn 0 M.val.toRingHom := by
  obtain ⟨n, hn, ho⟩ := h
  obtain ⟨N, hN, hr⟩ := exists_roots n hn
  refine ⟨N, hN, fun v _ => ⟨⟨(χ.val v : ℂ), hr _ ?_⟩, by simp [HChar.valTw]⟩⟩
  have h1 : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) ho
  have h2 : χ.val v ^ n = 1 := h1 _
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

theorem exists_of_emb {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x, φ x ∈ M :=
  ⟨φ.toRatAlgHom.fieldRange, (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional, fun x => ⟨x, rfl⟩⟩

open Classical in

theorem frame_values : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : HFrame H e), (∀ j τ, ∃ z : ℤ, e j τ = z) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧ (∀ g x, H.emb g x ∈ M) ∧ (∀ j, (C.mu0 j).ValuesIn 0 M.val.toRingHom) ∧ C.eta.ValuesIn (1 / 2) M.val.toRingHom ∧ C.chiPsi.ValuesIn 0 M.val.toRingHom ∧ C.del.ValuesIn 0 M.val.toRingHom ∧ C.del'.ValuesIn 0 M.val.toRingHom ∧ ∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ M := by
  intro R H e C he
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have alg := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (R.Psi) (embPsi H) hcm
  choose Me hMe hMe' using fun φ : H.E →+* ℂ => exists_of_emb φ
  have hmu : ∀ j, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C.mu0 j).ValuesIn 0 M.val.toRingHom := by
    intro j
    obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have := alg (C.mu0 j) n 0 hi fun i => by
      obtain ⟨z, hz⟩ := he j i
      have h1 : (n i : ℚ) = 2 * -e j i := hn i
      rw [hz] at h1
      have h2 : n i = 2 * -z := by exact_mod_cast h1
      exact ⟨-z, by rw [h2]; ring⟩
    simpa using this
  choose Mm hMm hMm' using hmu
  obtain ⟨M1, hM1, hM1'⟩ := alg C.eta (fun _ => 1) 1 C.isEta.inf fun _ => by simp
  obtain ⟨M2, hM2, hM2'⟩ := alg C.chiPsi (fun _ => 2) 0 C.isChi.inf fun _ => by simp
  rw [Int.cast_one] at hM1'
  rw [Int.cast_zero, zero_div] at hM2'
  obtain ⟨M3, hM3, hM3'⟩ := exists_of_order C.isDel.fin
  obtain ⟨M4, hM4, hM4'⟩ := exists_of_order C.isDel'.fin
  choose Mo hMo hMo' using fun k : Fin 2 => exists_roots (Nat.card (ZMod (H.g k))ˣ) Nat.card_pos
  obtain ⟨N, hN, hG, hle⟩ := exists_galois_ge ((⨆ φ, Me φ) ⊔ (⨆ j, Mm j) ⊔ (⨆ k, Mo k) ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4)
  simp only [sup_le_iff, iSup_le_iff] at hle
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hle
  refine ⟨N, hN, hG, fun g x => h1 _ (hMe' _ x), fun j => valuesIn_mono (hMm' j) (h2 j), valuesIn_mono hM1' h4,
    valuesIn_mono hM2' h5, valuesIn_mono hM3' h6, valuesIn_mono hM4' h7, fun k a => h3 k (hMo' k _ ?_)⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

end GlobalTheory.Mem.FrameVal
