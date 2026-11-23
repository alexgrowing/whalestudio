import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsCohomologicalRankOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits

noncomputable section

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace GlobalTheory.CompanionTheory.Published.Rd.PurityModel

def finUnit {E : Type} [Field E] [NumberField E] : (𝓞 E)ˣ →* (Af E)ˣ :=
  Units.map ((algebraMap E (Af E)).comp (algebraMap (𝓞 E) E)).toMonoidHom

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] (ψ : (Af E)ˣ →* ℂˣ) (hψ : Continuous ψ) (θ : (𝓞 E)ˣ) :
    ∃ k : ℕ, 0 < k ∧ ψ (finUnit θ) ^ k = 1 := by
  have hV : {u | ψ u = 1} ∈ 𝓝 (1 : (Af E)ˣ) := (isOpen_ker_finIdele E ψ hψ).mem_nhds (map_one ψ)
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  let q : (𝓞 E)ˣ →* (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ := Units.map (Ideal.Quotient.mk _).toMonoidHom
  have key : ∀ η : (𝓞 E)ˣ, q η = 1 → ∃ a : Af E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧
      ((finUnit η : (Af E)ˣ) : Af E) = 1 + N • a := by
    intro η hη
    have h3 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)}) (η : 𝓞 E) = Ideal.Quotient.mk _ 1 := congrArg Units.val hη
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h3)
    refine ⟨algebraMap E (Af E) (algebraMap (𝓞 E) E b), fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v b, ?_⟩
    change algebraMap E (Af E) (algebraMap (𝓞 E) E (η : 𝓞 E)) = _
    rw [eq_add_of_sub_eq' hb]
    simp
  refine ⟨Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ, Nat.card_pos, ?_⟩
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ
  have hk : q (θ ^ k) = 1 := by rw [map_pow]; exact pow_card_eq_one'
  obtain ⟨a, ha, e⟩ := key _ hk
  obtain ⟨b, hb, e'⟩ := key (θ ^ k)⁻¹ (by rw [map_inv, hk, inv_one])
  rw [← map_pow, ← map_pow]
  refine hTV (a := finUnit (θ ^ k)) (hTT ⟨?_, ?_⟩)
  · change ((finUnit (θ ^ k) : (Af E)ˣ) : Af E) ∈ T1
    rw [e]; exact (hNW a ha).1
  · change MulOpposite.op (((finUnit (θ ^ k))⁻¹ : (Af E)ˣ) : Af E) ∈ T2
    rw [← map_inv, e']; exact (hNW b hb).2

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def infUnit : (𝓞 E)ˣ →* (Cinf E)ˣ :=
  Units.map ((pInf E).comp ((algebraMap E (Ad E)).comp (algebraMap (𝓞 E) E))).toMonoidHom

theorem norm_chiInf_unit (χ : HChar E) (θ : (𝓞 E)ˣ) : ‖((chiInf χ (infUnit θ) : ℂˣ) : ℂ)‖ = 1 := by
  have hi : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  have hf : ∀ x, pInf E (sFin E x) = 0 := fun x => map_zero (infEq E).symm
  have hi' : ∀ x, pFin E (sInf E x) = 0 := fun x => rfl
  have hf' : ∀ x, pFin E (sFin E x) = x := fun x => rfl
  have e : infId E (infUnit θ) * finId E (finUnit θ) =
      diagUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ) := by
    refine Units.ext (ad_ext ?_ ?_)
    · change pInf E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _
      simp only [map_mul, map_add, map_sub, map_one, hi, hf, sub_self, zero_add, sub_zero, add_zero, mul_one]
      rfl
    · change pFin E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _
      simp only [map_mul, map_add, map_sub, map_one, hi', hf', sub_self, zero_add, sub_zero, add_zero, one_mul]
      rfl
  have h1 := χ.2.2 (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ)
  rw [← e, map_mul] at h1
  obtain ⟨k, hk, h2⟩ := exists_pow_eq_one (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E)) θ
  have h3 : chiInf χ (infUnit θ) ^ k = 1 := by
    have := congrArg (· ^ k) h1
    simp only [mul_pow, one_pow] at this
    rw [show χ.1 (finId E (finUnit θ)) ^ k = 1 from h2, mul_one] at this
    exact this
  have h4 : ‖((chiInf χ (infUnit θ) : ℂˣ) : ℂ)‖ ^ k = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h3]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h4

theorem hecke_pure (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) :
    ∃ w₀ : ℤ, ∀ τ : E →+* ℂ, n τ + n (ComplexEmbedding.conjugate τ) = w₀ := by
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units E
    (fun w => ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ)) (fun θ => by
      have h1 := norm_chiInf_unit χ θ
      rw [GlobalTheory.RegAlgPurityModel.chiInf_eq_prod χ n h, norm_prod] at h1
      have hc : ∀ τ : E →+* ℂ, coord τ (infUnit θ : (Cinf E)ˣ) = τ ((θ : 𝓞 E) : E) := fun τ => coord_algebraMap τ _
      have hp : ∀ w : InfinitePlace E, 0 < w ((θ : 𝓞 E) : E) := fun w => Units.pos_at_place θ w
      have h2 : ∀ w : InfinitePlace E, ‖coord w.embedding (infUnit θ : (Cinf E)ˣ) ^ n w.embedding *
          coord (ComplexEmbedding.conjugate w.embedding) (infUnit θ : (Cinf E)ˣ) ^
            n (ComplexEmbedding.conjugate w.embedding)‖ =
          w ((θ : 𝓞 E) : E) ^ (n w.embedding + n (ComplexEmbedding.conjugate w.embedding)) := fun w => by
        rw [hc, hc, norm_mul, norm_zpow, norm_zpow, zpow_add₀ (hp w).ne', ComplexEmbedding.conjugate_coe_eq,
          Complex.norm_conj, InfinitePlace.norm_embedding_eq]
      simp only [h2] at h1
      have h3 := congrArg Real.log h1
      rw [Real.log_prod (fun w _ => (zpow_pos (hp w) _).ne'), Real.log_one] at h3
      rw [← h3]
      exact Finset.sum_congr rfl fun w _ => by rw [Real.log_zpow, mul_comm])
  have hm : ∀ w : InfinitePlace E, ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ) = c * 2 :=
    fun w => by rw [hc w, (IsTotallyComplex.isComplex w).mult_eq_two]; norm_num
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  refine ⟨n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding), fun τ => ?_⟩
  have h5 : n (InfinitePlace.mk τ).embedding + n (ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding) =
      n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding) := by
    exact_mod_cast (hm _).trans (hm w₀).symm
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rwa [e] at h5
  · rw [e, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ, add_comm] at h5
    exact h5

theorem rank_one (π : CuspSub E 1) (hr : (CG.mk π).IsRegAlg) :
    (∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
    IsCohomological π := by
  refine ⟨?_, GlobalTheory.RegAlgPurityModel.isCohomological_rank_one π hr⟩
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose n hn using (CG.isRegAlg_ofChar χ).1 hr
  obtain ⟨w₀, hw⟩ := hecke_pure χ n hn
  refine ⟨w₀, fun τ => ?_⟩
  change (CG.ofChar χ).infChar (ComplexEmbedding.conjugate τ) = ((CG.ofChar χ).infChar τ).map _
  rw [CG.infChar_ofChar, CG.infChar_ofChar, Multiset.map_singleton, hn, hn, ← hw τ]
  congr 1; push_cast; ring

theorem iff_two_le : GlobalTheory.CompanionTheory.Published.Rd.RegularAlgebraicPurity ↔
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ), 2 ≤ a → ∀ π : CuspSub L a, (CG.mk π).IsRegAlg →
      (∃ w₀ : ℤ, ∀ τ : L →+* ℂ,
        (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
      IsCohomological π := by
  refine ⟨fun H L _ _ _ a ha π hr => H L a (by omega) π hr, fun H L _ _ _ a ha π hr => ?_⟩
  rcases ha.eq_or_lt with rfl | h
  · exact rank_one π hr
  · exact H L a h π hr

theorem hasInfChar_of_isRegAlg {a : ℕ} (ha : 2 ≤ a) {π : CG E a} (h : π.IsRegAlg) (τ : E →+* ℂ) :
    π.HasInfChar τ (π.infChar τ) := by
  by_cases hm : ∃ m, π.HasInfChar τ m
  · obtain ⟨m, hm⟩ := hm
    rwa [hm.infChar_eq]
  · have h1 := (h τ).1
    rw [CG.infChar, dif_neg hm] at h1
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    simp [Multiset.replicate_succ] at h1

end GlobalTheory.CompanionTheory.Published.Rd.PurityModel

end
