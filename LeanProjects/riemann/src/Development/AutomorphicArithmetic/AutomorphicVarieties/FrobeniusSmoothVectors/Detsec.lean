import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EnnrealVolumeRatioStepCancel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDetps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.detsec_dim {R S : Type} [CommRing R] [CommRing S] (p : R →+* S)
    (hp : Function.Surjective p) (J : Ideal S) : ringKrullDim (R ⧸ J.comap p) = ringKrullDim (S ⧸ J) :=
  ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective (Ideal.quotientMap J p le_rfl)
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hp⟩)

private theorem UpperTheory.V.Fr.detsec_comap {R S : Type} [CommRing R] [CommRing S] (p : R →+* S)
    (hp : Function.Surjective p) (J : Ideal S) (D : ℕ) : Chained (J.comap p) D ↔ Chained J D := by
  have e := Ideal.comap_minimalPrimes_eq_of_surjective hp J
  have hs : ∀ P Q : Ideal S, P.comap p ⊔ Q.comap p = (P ⊔ Q).comap p := fun P Q => by
    conv_rhs => rw [← Ideal.map_comap_of_surjective p hp P, ← Ideal.map_comap_of_surjective p hp Q, ← Ideal.map_sup,
      Ideal.comap_map_of_surjective p hp]
    exact (sup_eq_left.2 (le_sup_of_le_left (Ideal.comap_mono bot_le))).symm
  have mm : ∀ P : Ideal S, (P.comap p).map p = P := Ideal.map_comap_of_surjective p hp
  unfold Chained
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun P hP => detsec_dim p hp P ▸ h1 _ ⟨P, hP, rfl⟩, fun P hP Q hQ => ?_⟩
    have := Relation.ReflTransGen.lift (fun I : Ideal R => I.map p) (p := fun P Q => P ∈ J.minimalPrimes ∧
      Q ∈ J.minimalPrimes ∧ (D : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ (P ⊔ Q))) ?_ _ _ (h2 _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩)
    · simpa only [Function.onFun, mm] using this
    · rintro _ _ ⟨⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, h⟩
      simp only [Function.onFun, mm]
      rw [hs, detsec_dim p hp] at h
      exact ⟨hP, hQ, (congrArg₂ (fun A B : Ideal S => (D : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ (A ⊔ B))) (mm P) (mm Q)).mpr h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      rw [detsec_dim p hp]
      exact h1 P hP
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩
      refine Relation.ReflTransGen.lift (fun I : Ideal S => I.comap p) ?_ _ _ (h2 P hP Q hQ)
      rintro P Q ⟨hP, hQ, h⟩
      refine ⟨⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩, ?_⟩
      rw [hs, detsec_dim p hp]
      exact h

private theorem UpperTheory.V.Fr.detsec_ker (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsCO O R] (σ : Type) [Finite σ] (a : σ → R) (ha : ∀ s, a s ∈ maximalIdeal R)
    (F : MvPowerSeries σ R →ₐ[O] R) (hC : ∀ x, F (MvPowerSeries.C x) = x) (hX : ∀ s, F (MvPowerSeries.X s) = a s) :
    RingHom.ker (F : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range fun s => (MvPowerSeries.X s - MvPowerSeries.C (a s) : MvPowerSeries σ R)) := by
  set K := Ideal.span (Set.range fun s => (MvPowerSeries.X s - MvPowerSeries.C (a s) : MvPowerSeries σ R)) with hK
  have h1 : K ≤ RingHom.ker (F : MvPowerSeries σ R →+* R) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    simp [RingHom.mem_ker, hC, hX]
  refine le_antisymm (fun G hG => ?_) h1
  haveI := co_mvps O R σ
  haveI : Nontrivial (MvPowerSeries σ R ⧸ K) :=
    Ideal.Quotient.nontrivial_iff.2 fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ h1))
  haveI := co_quot O _ _ (Ideal.Quotient.mkₐ O K) (Ideal.Quotient.mkₐ_surjective O K)
  let c : R →ₐ[O] MvPowerSeries σ R :=
    { (MvPowerSeries.C : R →+* MvPowerSeries σ R) with commutes' := fun _ => MvPowerSeries.algebraMap_apply.symm }
  let f : R →ₐ[O] MvPowerSeries σ R ⧸ K := (Ideal.Quotient.mkₐ O K).comp c
  have hf : ∀ s, f (a s) ∈ maximalIdeal _ := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact ha s
  have key := (co_ev O R _ σ f (fun s => f (a s)) hf).unique (y₁ := Ideal.Quotient.mkₐ O K) (y₂ := f.comp F)
    ⟨fun _ => rfl, fun s => Ideal.Quotient.eq.2 (Ideal.subset_span ⟨s, rfl⟩)⟩
    ⟨fun x => by simp [hC], fun s => by simp [hX]⟩
  have h2 : F G = 0 := hG
  have h3 := DFunLike.congr_fun key G
  rw [AlgHom.comp_apply, h2, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

private theorem UpperTheory.V.Fr.detsec_sec (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R]
    [IsCO O R] (σ : Type) [Fintype σ] (a : σ → R) (ha : ∀ s, a s ∈ maximalIdeal R)
    (F : MvPowerSeries σ R →ₐ[O] R) (hC : ∀ x, F (MvPowerSeries.C x) = x) (hX : ∀ s, F (MvPowerSeries.X s) = a s)
    (I : Ideal (MvPowerSeries σ R)) (hI : I.radical.IsPrime) (b D : ℕ) (f : Fin b → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hd : ((D + 1 + (Fintype.card σ + b) : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries σ R ⧸ I.radical)) :
    Chained (Ideal.span (Set.range f) ⊔ I.map (F : MvPowerSeries σ R →+* R)) D := by
  haveI := co_mvps O R σ
  haveI : Nontrivial (MvPowerSeries σ R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 fun h => hI.ne_top (by rw [h, Ideal.radical_top])
  haveI hco := co_quot O _ _ (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hF : Function.Surjective (F : MvPowerSeries σ R →+* R) := fun x => ⟨MvPowerSeries.C x, hC x⟩
  let e : σ ⊕ Fin b → MvPowerSeries σ R :=
    Sum.elim (fun s => MvPowerSeries.X s - MvPowerSeries.C (a s)) fun i => MvPowerSeries.C (f i)
  have he : ∀ s, e s ∈ maximalIdeal (MvPowerSeries σ R) := fun s => by
    rw [← res_eq_zero_iff O, ← res_map F, res_eq_zero_iff]
    rcases s with s | i
    · simp [e, hC, hX]
    · simpa [e, hC] using hf i
  let q : Fin (Fintype.card σ + b) ≃ σ ⊕ Fin b := (Fintype.equivFinOfCardEq (by simp)).symm
  have hn : (nilradical (MvPowerSeries σ R ⧸ I)).IsPrime := by
    have h1 : nilradical (MvPowerSeries σ R ⧸ I) = I.radical.map (Ideal.Quotient.mk I) := by
      rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by simp), Ideal.map_quotient_self]
      rfl
    rw [h1]
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using Ideal.le_radical)
  have h := c1ch (MvPowerSeries σ R ⧸ I) (Fintype.card σ + b) D (fun i => Ideal.Quotient.mk I (e (q i))) hn
    ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hco⟩
    (fun i => by
      have := he (q i)
      rw [← res_eq_zero_iff O, ← res_map (Ideal.Quotient.mkₐ O I), res_eq_zero_iff] at this
      exact this)
    (hd.trans (ringKrullDim_le_of_surjective (Ideal.Quotient.factor I.le_radical)
      (Ideal.Quotient.factor_surjective _)))
  rw [← detsec_comap (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective] at h
  rw [← detsec_comap _ hF]
  convert h using 1
  have h1 : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (e (q i))) =
      (Ideal.span (Set.range e)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact congrArg _ (q.surjective.range_comp (Ideal.Quotient.mk I ∘ e))
  have h2 : Ideal.span (Set.range f) = (Ideal.span (Set.range fun i =>
      (MvPowerSeries.C (f i) : MvPowerSeries σ R))).map (F : MvPowerSeries σ R →+* R) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact (hC _).symm
  rw [h1, h2, ← Ideal.map_sup, Ideal.comap_map_of_surjective _ hF,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, detsec_ker O R σ a ha F hC hX, Set.Sum.elim_range, Ideal.span_union]
  ac_rfl

private theorem UpperTheory.V.Fr.detsec_num (x : WithBot ℕ∞) (y : ℕ∞) (D b g c : ℕ) (h2 : y ≤ (g + 1 : ℕ))
    (h3 : (y : WithBot ℕ∞) + x = (D + 1 + b + (g + 1) : ℕ) + (c : WithBot ℕ∞)) :
    ((D + 1 + (c + b) : ℕ) : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.add_bot] at h3
    exact absurd h3.symm (by exact_mod_cast WithBot.coe_ne_bot)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe x =>
      lift y to ℕ using ne_top_of_le_ne_top (ENat.coe_ne_top _) h2
      have h5 : y ≤ g + 1 := by exact_mod_cast h2
      have h6 : y + x = D + 1 + b + (g + 1) + c := by exact_mod_cast h3
      have h7 : D + 1 + (c + b) ≤ x := by omega
      exact_mod_cast h7

private theorem UpperTheory.V.Fr.detsec_gen (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [IsCO O R] (b g D : ℕ)
    (f : Fin b → R) (M : Matrix (Fin (g + 1)) (Fin (g + 1)) R) (m : Fin (g + 1) → R)
    (hd : ringKrullDim R = (D + 1 + b + (g + 1) : ℕ)) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hM : ∀ i j, M i j ∈ maximalIdeal R) (hm : ∀ j, m j ∈ maximalIdeal R) :
    Chained (Ideal.span (Set.range f ∪ Set.range (M *ᵥ m) ∪ {M.det})) D := by
  haveI := co_mvps O R ((Fin (g + 1) × Fin (g + 1)) ⊕ Fin (g + 1))
  haveI : IsDomain (MvPowerSeries ((Fin (g + 1) × Fin (g + 1)) ⊕ Fin (g + 1)) R) := NoZeroDivisors.to_isDomain _
  let v : (Fin (g + 1) × Fin (g + 1)) ⊕ Fin (g + 1) → R := Sum.elim (fun p => M p.1 p.2) m
  have hv : ∀ s, v s ∈ maximalIdeal R := by
    rintro (p | j)
    · exact hM _ _
    · exact hm _
  obtain ⟨F, ⟨hC, hX⟩, -⟩ := co_ev O R R _ (AlgHom.id O R) v hv
  obtain ⟨h1, h2⟩ := UpperTheory.V.CA.g_detps R g
  have h3 := @co_caten O _ _ _ _ _ _ _ _ _ _ h1
  rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, hd, Nat.card_eq_fintype_card] at h3
  have h4 := detsec_sec O R _ v hv F hC hX _ h1 b D f hf (detsec_num _ _ D b g _ h2 h3)
  convert h4 using 1
  rw [Set.union_assoc, Ideal.span_union, Ideal.map_span, Set.image_union, Set.image_singleton, ← Set.range_comp,
    RingHom.map_det]
  congr 4
  · funext i
    simp [hX, v, Matrix.mulVec, dotProduct]
  · congr 1
    ext i j
    simp [hX, v]

theorem UpperTheory.V.Fr.detsec :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (a b g D : ℕ) (f : Fin b → MvPowerSeries (Fin a ⊕ Fin (g + 1)) O) (M : Matrix (Fin (g + 1)) (Fin (g + 1)) (MvPowerSeries (Fin a ⊕ Fin (g + 1)) O)), a = b + D → (∀ i, MvPowerSeries.constantCoeff (f i) ∈ maximalIdeal O) → (∀ i j, MvPowerSeries.constantCoeff (M i j) ∈ maximalIdeal O) → Chained (Ideal.span (Set.range f ∪ Set.range (M *ᵥ fun j => MvPowerSeries.X (.inr j)) ∪ {M.det})) D := by
  intro O _ _ _ _ a b g D f M hab hf hM
  haveI := co_mvps O O (Fin a ⊕ Fin (g + 1))
  haveI : IsDomain (MvPowerSeries (Fin a ⊕ Fin (g + 1)) O) := NoZeroDivisors.to_isDomain _
  have hm : ∀ x : MvPowerSeries (Fin a ⊕ Fin (g + 1)) O, MvPowerSeries.constantCoeff x ∈ maximalIdeal O →
      x ∈ maximalIdeal (MvPowerSeries (Fin a ⊕ Fin (g + 1)) O) := fun x hx hu =>
    hx (MvPowerSeries.isUnit_iff_constantCoeff.1 hu)
  refine detsec_gen O _ b g D f M _ ?_ (fun i => hm _ (hf i)) (fun i j => hm _ (hM i j)) fun j => hm _ ?_
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one, Nat.card_sum,
      Nat.card_fin, Nat.card_fin, hab]
    have : D + 1 + b + (g + 1) = 1 + (b + D + (g + 1)) := by omega
    rw [this]
    push_cast
    rfl
  · rw [MvPowerSeries.constantCoeff_X]
    exact zero_mem _
