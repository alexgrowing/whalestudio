import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SumLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EnnrealVolumeRatioStepCancel
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Detsec
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ThickOfDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AnnOfFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Oddm
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_comap {A R : Type} [CommRing A] [CommRing R] (p : A →+* R) (hp : Function.Surjective p)
    (P : Ideal R) : ringKrullDim (A ⧸ P.comap p) = ringKrullDim (R ⧸ P) := by
  have h : RingHom.ker ((Ideal.Quotient.mk P).comp p) = P.comap p := by
    ext a; simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [← h]
  exact ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hp))

private theorem chained_of_comap {A R : Type} [CommRing A] [CommRing R] (p : A →+* R) (hp : Function.Surjective p)
    (I : Ideal R) (D : ℕ) (h : Chained (I.comap p) D) : Chained I D := by
  have hm : (I.comap p).minimalPrimes = Ideal.comap p '' I.minimalPrimes :=
    Ideal.comap_minimalPrimes_eq_of_surjective hp I
  refine ⟨fun P hP => ?_, fun P hP Q hQ => ?_⟩
  · rw [← dim_comap p hp]
    exact h.1 _ (hm ▸ ⟨P, hP, rfl⟩)
  · have h1 := h.2 (P.comap p) (hm ▸ ⟨P, hP, rfl⟩) (Q.comap p) (hm ▸ ⟨Q, hQ, rfl⟩)
    have h2 : ∀ b, Relation.ReflTransGen (fun P Q : Ideal A => P ∈ (I.comap p).minimalPrimes ∧
        Q ∈ (I.comap p).minimalPrimes ∧ (D : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ (P ⊔ Q))) (P.comap p) b →
        Relation.ReflTransGen (fun P Q : Ideal R => P ∈ I.minimalPrimes ∧ Q ∈ I.minimalPrimes ∧
          (D : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (P ⊔ Q))) P (b.map p) := by
      intro b hb
      induction hb with
      | refl => rw [Ideal.map_comap_of_surjective p hp]
      | tail _ hab ih =>
        refine ih.tail ?_
        obtain ⟨ha, hb, hd⟩ := hab
        rw [hm] at ha hb
        obtain ⟨a, ha, rfl⟩ := ha
        obtain ⟨b, hb, rfl⟩ := hb
        rw [Ideal.map_comap_of_surjective p hp, Ideal.map_comap_of_surjective p hp]
        refine ⟨ha, hb, ?_⟩
        have : (a ⊔ b).comap p = a.comap p ⊔ b.comap p := by
          conv_lhs => rw [← Ideal.map_comap_of_surjective p hp a, ← Ideal.map_comap_of_surjective p hp b,
            ← Ideal.map_sup, Ideal.comap_map_of_surjective p hp]
          exact sup_eq_left.2 (le_sup_of_le_left (Ideal.comap_mono bot_le))
        rwa [← dim_comap p hp, this]
    have h3 := h2 _ h1
    rwa [Ideal.map_comap_of_surjective p hp] at h3

private theorem cc_mem {σ O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Nontrivial R]
    (p : MvPowerSeries σ O →+* R) (f : MvPowerSeries σ O) (hf : p f = 0) :
    MvPowerSeries.constantCoeff f ∈ maximalIdeal O := by
  intro hu
  have := (MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map p
  rw [hf] at this
  exact not_isUnit_zero this

private theorem detsec' (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (a b g D : ℕ) (hg : g ≠ 0) (f : Fin b → MvPowerSeries (Fin a ⊕ Fin g) O)
    (M : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin a ⊕ Fin g) O)) (h : a = b + D)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) ∈ maximalIdeal O)
    (hM : ∀ i j, MvPowerSeries.constantCoeff (M i j) ∈ maximalIdeal O) :
    Chained (Ideal.span (Set.range f ∪ Set.range (M *ᵥ fun j => MvPowerSeries.X (.inr j)) ∪ {M.det})) D := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg
  exact detsec O a b g D f M h hf hM

theorem UpperTheory.V.Fr.sharp3 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → ∃ I : Ideal L.R, L.Sharp I := by
  intro l _ O _ _ _ _ F C₀ hF S x L hB hx
  obtain ⟨-, -, hcmp, htri⟩ := loc_rho hF (Or.inr rfl) S x L
  have hoff : ∀ I : Ideal L.R, Chained I (3 * F.d + 1) → ∀ P ∈ I.minimalPrimes, L.ρ.OffTri P := by
    intro I hI P hP
    refine ⟨fun h => hP.1.1.ne_top (top_le_iff.1 ((htri hx).1 ▸ h)), fun h => ?_⟩
    have h1 := (krull_dim_lt_of_not_le_triangular hF (Or.inr rfl) S x L hB hx).1
    have h2 : ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (L.R ⧸ L.ρ.triM) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)
    have h3 := ((hI.1 P hP).trans h2).trans_lt h1
    have h4 : 3 * F.d + 1 + 1 < 3 * F.d := by exact_mod_cast h3
    omega
  by_cases hee : S.u.ee ≤ x
  · obtain ⟨E⟩ := epres hF S x L hee
    have hG : ∀ i, E.Go i ∈ RingHom.ker E.p := fun i =>
      E.ker ▸ Ideal.subset_span (Or.inr ⟨i, rfl⟩)
    have hFe : ∀ i, E.Fe i ∈ RingHom.ker E.p := fun i =>
      E.ker ▸ Ideal.subset_span (Or.inl ⟨i, rfl⟩)
    choose M hM hGM using fun i => oddm L.O' E.a E.g (E.Go i) (E.odd i) (E.min _ (hG i))
    have hGo : E.Go = Matrix.of M *ᵥ fun j => MvPowerSeries.X (.inr j) := funext hGM
    have hch : Chained (Ideal.span {E.p (Matrix.of M).det}) (3 * F.d + 1) := by
      refine chained_of_comap E.p.toRingHom E.surj _ _ ?_
      have h1 := detsec' L.O' E.a E.b E.g _ (gpos hF S x L hx E) E.Fe (Matrix.of M) E.num
        (fun i => cc_mem E.p.toRingHom _ (hFe i)) hM
      rw [← hGo, Ideal.span_union, ← E.ker] at h1
      convert h1 using 1
      have : Ideal.span {E.p (Matrix.of M).det} = (Ideal.span {(Matrix.of M).det}).map E.p.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]; rfl
      rw [this, Ideal.comap_map_of_surjective E.p.toRingHom E.surj, sup_comm]
      rfl
    refine ⟨_, fun h => absurd hee h, fun P hP hne => ?_, hch, fun P hP => ?_⟩
    · rw [E.ee, Ideal.span_le, Set.range_subset_iff, not_forall] at hne
      obtain ⟨j, hj⟩ := hne
      rw [Ideal.span_singleton_le_iff_mem]
      refine (hP.mem_or_mem ?_).resolve_right hj
      have h1 : ((Matrix.of M).adjugate *ᵥ E.Go) j = (Matrix.of M).det * MvPowerSeries.X (.inr j) := by
        rw [hGo, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
      have h2 : ((Matrix.of M).adjugate *ᵥ E.Go) j ∈ RingHom.ker E.p := by
        rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hG i)
      rw [h1, RingHom.mem_ker, map_mul] at h2
      rw [h2]
      exact P.zero_mem
    · by_cases he : L.ρ.ee ≤ P
      · exact Or.inr (thick hF S x L E _ hGo P hP.1.1 ⟨hoff _ hch P hP, rfl, he⟩
          (hP.1.2 (Ideal.mem_span_singleton_self _)))
      · exact Or.inl ⟨hoff _ hch P hP, fun _ => he⟩
  · obtain ⟨N, N', p, f, hN, hp, hk⟩ := pres hF (Or.inr rfl) S x L
    have hch : Chained (⊥ : Ideal L.R) (3 * F.d + 1) := by
      refine chained_of_comap p.toRingHom hp _ _ ?_
      haveI hco : IsCO L.O' (MvPowerSeries (Fin N) L.O') := co_mvps L.O' L.O' (Fin N)
      haveI : IsNoetherianRing (MvPowerSeries (Fin N) L.O') := hco.toIsNoetherian
      haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin N) L.O')) (MvPowerSeries (Fin N) L.O') :=
        hco.complete
      have h1 := c1ch (MvPowerSeries (Fin N) L.O') N' (3 * F.d + 1) f
        (by rw [nilradical_eq_zero]; exact Ideal.isPrime_bot) ⟨L.O', L.cO, L.dO, L.vO, inferInstance, _, hco⟩
        (fun i hu => by
          have h0 : f i ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨i, rfl⟩
          have := hu.map p
          rw [RingHom.mem_ker.1 h0] at this
          exact not_isUnit_zero this)
        (by
          rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
            Nat.card_eq_fintype_card, Fintype.card_fin, hN]
          norm_cast
          omega)
      rw [← hk] at h1
      exact h1
    refine ⟨⊥, fun _ => rfl, fun _ _ _ => bot_le, hch, fun P hP => Or.inl ⟨hoff _ hch P hP, fun _ h => hee ?_⟩⟩
    exact ((hcmp P).2.2.1 h).trans ((Ideal.comap_mono (le_maximalIdeal hP.1.1.ne_top)).trans L.lies.le)
