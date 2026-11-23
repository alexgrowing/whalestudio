import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_comap_quot {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ii : Ideal R)
    (Q : Ideal (B ⧸ ii.map (algebraMap R B))) :
    (Q.comap (algebraMap (R ⧸ ii) (B ⧸ ii.map (algebraMap R B)))).comap (Ideal.Quotient.mk ii) =
      (Q.comap (Ideal.Quotient.mk (ii.map (algebraMap R B)))).comap (algebraMap R B) := by
  ext x
  rfl

private theorem dim_quot {B : Type} [CommRing B] (I S : Ideal B) (h : I ≤ S.radical) (d : WithBot ℕ∞)
    (hd : ∀ P ∈ S.minimalPrimes, d ≤ ringKrullDim (B ⧸ P)) (P : Ideal (B ⧸ I))
    (hP : P ∈ (S.map (Ideal.Quotient.mk I)).minimalPrimes) : d ≤ ringKrullDim ((B ⧸ I) ⧸ P) := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  have hIP : I ≤ P' := le_sup_right.trans hP'.1.2
  have hmin : P' ∈ S.minimalPrimes := by
    refine ⟨⟨hP'.1.1, le_sup_left.trans hP'.1.2⟩, ?_⟩
    intro Q hQ hQP
    haveI := hQ.1
    exact hP'.2 ⟨hQ.1, sup_le hQ.2 (h.trans ((Ideal.IsPrime.radical_le_iff hQ.1).mpr hQ.2))⟩ hQP
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I P'), sup_eq_right.mpr hIP]
  exact hd P' hmin

theorem UpperTheory.V.Pa.Core.outOfNil :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing R] (s : MvPowerSeries σ Λ →+* R) (ii ann : Ideal R) (ι : Type) (q : ι → Ideal R) (d : ℕ) (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra R (B i)] (S : ∀ i, Ideal (B i)), (∀ i, ii ≤ q i) → (∀ i, IsCplAt R (q i) (B i)) → (∀ i, ii ≤ (S i).radical.comap (algebraMap R (B i))) → (∀ i, ∀ P ∈ (S i).minimalPrimes, (d : WithBot ℕ∞) ≤ ringKrullDim (B i ⧸ P)) → (∀ i (Q : Ideal (B i)), Q.IsPrime → ii.map (algebraMap R (B i)) ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → (S i ≤ Q ↔ ann ≤ Q.comap (algebraMap R (B i)))) → (∀ i i' (Z Q : Ideal (B i)), Z.IsPrime → Q.IsPrime → S i ≤ Z → Z ≤ Q → (∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q) → Q.comap (algebraMap R (B i)) ≤ q i' → ∃ Z' : Ideal (B i'), Z'.IsPrime ∧ S i' ≤ Z' ∧ Z'.comap (algebraMap R (B i')) = Z.comap (algebraMap R (B i))) → Nonempty (PatchedSupportCompletions s ii ann q d) := by
  intro Λ R σ _ _ _ _ s ii ann ι q d B _ _ _ S hq hcpl hrad hdim hfib hmove
  let J : ∀ i, Ideal (B i) := fun i => ii.map (algebraMap R (B i))
  have hJmax : ∀ i, J i ≤ maximalIdeal (B i) := by
    intro i
    rw [Ideal.map_le_iff_le_comap, (hcpl i).comap_eq]
    exact hq i
  have hJne : ∀ i, J i ≠ ⊤ := fun i h => (IsLocalRing.maximalIdeal.isMaximal (B i)).ne_top (top_le_iff.mp (h ▸ hJmax i))
  haveI : ∀ i, Nontrivial (B i ⧸ J i) := fun i => Ideal.Quotient.nontrivial_iff.mpr (hJne i)
  haveI : ∀ i, IsLocalRing (B i ⧸ J i) := fun i => .of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : ∀ i, J i ≤ RingHom.ker (Ideal.Quotient.mk (J i)) := fun i => by rw [Ideal.mk_ker]
  have hcomap : ∀ i (Z : Ideal (B i ⧸ J i)),
      (Z.comap (algebraMap (R ⧸ ii) (B i ⧸ J i))).comap (Ideal.Quotient.mk ii) =
        (Z.comap (Ideal.Quotient.mk (J i))).comap (algebraMap R (B i)) :=
    fun i Z => comap_comap_quot ii Z
  have hJle : ∀ i (Z : Ideal (B i ⧸ J i)), J i ≤ Z.comap (Ideal.Quotient.mk (J i)) := by
    intro i Z x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Z.zero_mem
  have hgen : ∀ i (Q : Ideal (B i ⧸ J i)),
      ((∀ a, algebraMap (R ⧸ ii) (B i ⧸ J i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) ↔
        ∀ a, algebraMap R (B i) (s (MvPowerSeries.X a)) ∈ Q.comap (Ideal.Quotient.mk (J i))) := by
    intro i Q
    rfl
  refine ⟨⟨fun i => B i ⧸ J i, fun i => ?_, fun i => (S i).map (Ideal.Quotient.mk (J i)), fun i => ?_,
    fun i Q hQ hgQ => ?_, fun i i' Z Q hZ hQ hSZ hZQ hgQ hQq => ?_⟩⟩
  · exact IsCplAt.quotient R (q i) (B i) (R ⧸ ii) ((q i).map (Ideal.Quotient.mk ii)) (B i ⧸ J i) (hcpl i)
      Ideal.Quotient.mk_surjective
      (by
        show Ideal.comap (Ideal.Quotient.mk ii) _ = _
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
        exact sup_eq_left.mpr (hq i))
      Ideal.Quotient.mk_surjective
      (by
        show RingHom.ker (Ideal.Quotient.mk (J i)) = Ideal.map _ (RingHom.ker (Ideal.Quotient.mk ii))
        rw [Ideal.mk_ker, Ideal.mk_ker])
  · intro P hP
    exact dim_quot (J i) (S i) (Ideal.map_le_iff_le_comap.mpr (hrad i)) d (hdim i) P hP
  · haveI := hQ
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hfib i _ (Ideal.comap_isPrime _ Q) (hJle i Q) ((hgen i Q).mp hgQ)
  · haveI := hZ
    haveI := hQ
    rw [hcomap] at hQq
    obtain ⟨Z'', hZ''p, hSZ'', hZ''⟩ := hmove i i' (Z.comap (Ideal.Quotient.mk (J i)))
      (Q.comap (Ideal.Quotient.mk (J i))) (Ideal.comap_isPrime _ Z) (Ideal.comap_isPrime _ Q)
      (Ideal.map_le_iff_le_comap.mp hSZ) (Ideal.comap_mono hZQ) ((hgen i Q).mp hgQ) hQq
    have hiiZ : ii ≤ Z''.comap (algebraMap R (B i')) := by
      rw [hZ'', ← Ideal.map_le_iff_le_comap]
      exact hJle i Z
    have hJZ : J i' ≤ Z'' := Ideal.map_le_iff_le_comap.mpr hiiZ
    have hkZ : RingHom.ker (Ideal.Quotient.mk (J i')) ≤ Z'' := by rw [Ideal.mk_ker]; exact hJZ
    refine ⟨Z''.map (Ideal.Quotient.mk (J i')), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkZ,
      Ideal.map_mono hSZ'', ?_⟩
    apply Ideal.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := ii))
    rw [hcomap, hcomap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkZ, hZ'']
