import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end

private theorem false_of_three_distinct_primes_over_of_finrank_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) (P Q R : HeightOneSpectrum (𝓞 E))
    (hP : HeightOneSpectrum.under (𝓞 F) P = v) (hQ : HeightOneSpectrum.under (𝓞 F) Q = v)
    (hR : HeightOneSpectrum.under (𝓞 F) R = v) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : False := by
  haveI : FaithfulSMul (𝓞 F) (𝓞 E) := FaithfulSMul.of_field_isFractionRing (𝓞 F) (𝓞 E) F E
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · left
      exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h)
    · exact Or.inr h⟩
  have hv : v.asIdeal ≠ ⊥ := v.ne_bot
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hc := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E hv
  rw [h2] at hc
  have mem : ∀ W : HeightOneSpectrum (𝓞 E), HeightOneSpectrum.under (𝓞 F) W = v →
      W.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro W hW
    rw [IsDedekindDomain.mem_primesOverFinset_iff hv]
    refine ⟨W.isPrime, ⟨?_⟩⟩
    rw [← hW]
    rfl
  have hsub : ({P.asIdeal, Q.asIdeal, R.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [mem P hP, mem Q hQ, mem R hR]
  have h3 := Finset.card_le_card hsub
  have e1 : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have e2 : P.asIdeal ≠ R.asIdeal := fun h => hPR (HeightOneSpectrum.ext h)
  have e3 : Q.asIdeal ≠ R.asIdeal := fun h => hQR (HeightOneSpectrum.ext h)
  rw [Finset.card_insert_of_notMem (by simp [e1, e2]), Finset.card_insert_of_notMem (by simp [e3]),
    Finset.card_singleton] at h3
  omega

private theorem exists_lift_sub_mem_pow_of_mem_wtPart_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : AEF F E) (hi : infPartF F E y = 0) (hf : ∀ Q, ev F E Q y = 0) : y = 0 := by
  have hfin : finPartF F E y = 0 := by
    apply (finAdEquiv F E).injective
    rw [map_zero]
    ext Q
    have h := (hf Q).trans (map_zero (evalV E Q)).symm
    first
      | exact h
      | exact congrArg _ h
      | simpa [ev, evalV] using h
  have h1 := GlobalTheory.HeisThetaF.smul_eq_zero_of_infPartF hi
  have h2 := GlobalTheory.HeisThetaF.smul_eq_zero_of_finPartF hfin
  have h3 : pairA F 1 0 + pairA F 0 1 = (1 : AF F) := by
    exact Prod.ext (add_zero _) (zero_add _)
  calc y = (1 : AF F) • y := (one_smul _ _).symm
    _ = 0 := by rw [← h3, add_smul, h1, h2, add_zero]

theorem UpperTheory.exists_place_of_splitIdempotent_cmExt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
        IsCMExt F E σ → ∀ e, IsSplitIdemF σ e →
        ∃ P : HeightOneSpectrum (𝓞 E), ¬ Fx σ P ∧ ev F E P e = 1 ∧ ∀ Q, Q ≠ P → ev F E Q e = 0 := by
  intro F E _ _ _ _ _ σ hcm e he
  obtain ⟨he2, hes, v, η, hη, hsum⟩ := he
  obtain ⟨α, hηα, hαv, hα0⟩ := id hη
  subst hηα
  have hfix : ∀ a : AF F, cAF σ (algebraMap (AF F) (AEF F E) a) = algebraMap (AF F) (AEF F E) a := by
    intro a
    simp [cAF, sigR]
  have hinj : Function.Injective (algebraMap (AF F) (AEF F E)) := by
    intro a b h
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (R := F) (A := AF F) (B := E)
      (algebraMap F E).injective h
  have hs2 : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he2]
  have heη : e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = e := by
    rw [← hsum, mul_add, he2, hes, add_zero]
  have hsη : cAF σ e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = cAF σ e := by
    rw [← hsum, mul_add, mul_comm, hes, zero_add, hs2]
  have evη0 : ∀ Q : HeightOneSpectrum (𝓞 E), HeightOneSpectrum.under (𝓞 F) Q ≠ v →
      ev F E Q (algebraMap (AF F) (AEF F E) (pairA F 0 α)) = 0 := by
    intro Q hQ
    rw [ev_fin, hα0 _ hQ, map_zero]
  have hinfη := GlobalTheory.WeilPartsF.infPartF_placeIdem (E := E) hη
  have hie : infPartF F E e = 0 := by
    rw [← heη, map_mul, hinfη, mul_zero]
  have his : infPartF F E (cAF σ e) = 0 := by
    rw [← hsη, map_mul, hinfη, mul_zero]
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_add] at hsum
    have h1 : pairA F 0 α = 0 := hinj (by rw [← hsum, map_zero])
    have h2 : α = 0 := congrArg Prod.snd h1
    rw [h2, map_zero] at hαv
    exact zero_ne_one hαv
  have hnes : cAF σ e ≠ 0 := by
    intro h0
    have h1 : e = algebraMap (AF F) (AEF F E) (pairA F 0 α) := by rw [← hsum, h0, add_zero]
    apply hne
    rw [← h0, h1, hfix, ← h1]
  have hover : ∀ (y : AEF F E) (Q : HeightOneSpectrum (𝓞 E)),
      y * algebraMap (AF F) (AEF F E) (pairA F 0 α) = y → ev F E Q y ≠ 0 →
      HeightOneSpectrum.under (𝓞 F) Q = v := by
    intro y Q hy hQ
    by_contra hv
    apply hQ
    rw [← hy, map_mul, evη0 Q hv, mul_zero]
  have prod0 : ∀ Q : HeightOneSpectrum (𝓞 E), ev F E Q e * ev F E Q (cAF σ e) = 0 := by
    intro Q
    rw [← map_mul, hes, map_zero]
  have idem1 : ∀ Q : HeightOneSpectrum (𝓞 E), ev F E Q e ≠ 0 → ev F E Q e = 1 := by
    intro Q hQ
    have h := congrArg (ev F E Q) he2
    rw [map_mul] at h
    exact mul_left_cancel₀ hQ (h.trans (mul_one _).symm)
  obtain ⟨P, hP⟩ : ∃ P, ev F E P e ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (exists_lift_sub_mem_pow_of_mem_wtPart_zero e hie hall)
  obtain ⟨R, hR⟩ : ∃ R, ev F E R (cAF σ e) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hnes (exists_lift_sub_mem_pow_of_mem_wtPart_zero _ his hall)
  have hPv := hover e P heη hP
  have hRv := hover _ R hsη hR
  have hRe : ev F E R e = 0 := by
    rcases mul_eq_zero.mp (prod0 R) with h | h
    · exact h
    · exact absurd h hR
  have hPR : P ≠ R := by
    rintro rfl
    exact hP hRe
  refine ⟨P, ?_, idem1 P hP, ?_⟩
  · intro hfx
    obtain ⟨θ, d, -, -, hd, hσθ, hθθ, hspan, -⟩ := exists_half hcm
    have hsplit : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
      refine ⟨P, R, hPR, ?_, ?_⟩
      · rw [← hPv]
        rfl
      · rw [← hRv]
        rfl
    have hsq := sq_of_split hcm hd hσθ hθθ hspan hsplit
    have hnsq := not_sq_of_fx hcm hd hσθ hθθ hspan hfx
    subst hPv
    exact hnsq hsq
  · intro Q hQP
    by_contra hQ
    have hQv := hover e Q heη hQ
    have hQR : Q ≠ R := by
      rintro rfl
      exact hQ hRe
    exact false_of_three_distinct_primes_over_of_finrank_eq_two hcm.2.2.1 v P Q R hPv hQv hRv (Ne.symm hQP) hPR hQR
