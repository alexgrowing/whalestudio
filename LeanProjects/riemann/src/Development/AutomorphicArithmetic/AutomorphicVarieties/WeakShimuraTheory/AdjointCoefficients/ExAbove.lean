import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ConeCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem sum_deg (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] {V : Type} [Fintype V]
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal) :
    ∑ v, locDeg (pl v) ≤ Module.finrank ℚ F := by
  classical
  have hl : l.Prime := Fact.out
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 F)
  rw [RingOfIntegers.rank] at hsum
  have hover : ∀ v, (pl v).asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => by
    refine ⟨(pl v).isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ (pl v).isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hm v
  let e : V → (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => ⟨(pl v).asIdeal, hover v⟩
  have he : Function.Injective e := fun a b h => hi (HeightOneSpectrum.ext (congrArg Subtype.val h))
  rw [← hsum]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩)))
  rw [Finset.sum_map]
  rfl

private theorem cc_ex {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (w : InfinitePlace F) : ∃ c : G F Ω, IsCCAt w c := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois F Ω := {}
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
  let cj : ℂ →ₐ[F] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  refine ⟨(cj.comp j).restrictNormal' Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
  · rw [show j.toRingHom.comp (algebraMap F Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
    exact w.mk_embedding

private theorem contAct {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup G] (ρ : Representation k G M)
    (h : IsOpen (ρ.ker : Set G)) : ContAction ρ := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (ρ.ker : Set G), h.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have hx' : ρ (g⁻¹ * x) = 1 := hx
  have : ρ x = ρ g := by rw [← mul_inv_cancel_left g x, map_mul, hx', mul_one]
  simp only [this]

private theorem ex_above (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : l.Prime := Fact.out
  haveI : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  obtain ⟨P, hP, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(l : ℤ)})
  have hm : ((l : ℕ) : 𝓞 F) ∈ P := by
    have : (l : ℤ) ∈ P.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.ne_zero (by exact_mod_cast hm)

theorem UpperTheory.V.Ws.X1.ecG :
    GC.Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GC.GLink l S K π → (∀ w ∈ S, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → ∀ (V : Type) (ι : V ≃ S) (A : V → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) (ι v).1) → ∀ (k W : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup W] [Module k W] [Module.Finite k W] (ρ : Representation k Γ W) (b : V → Submodule k W) (m e : ℕ), IsOpen (ρ.ker : Set Γ) → (∀ v, ∀ s ∈ Dec (F := F) (A v), ∀ X ∈ b v, ρ (π s) X ∈ b v) → (∀ f : W →ₗ[k] k, (∀ g X, f (ρ (π g) X) = (GC.cycF F Ω l k g : k) * f X) → f = 0) → (∀ v, Module.finrank k (b v) = m) → (∀ g : G F Ω, IsCC g → Module.finrank k (LinearMap.ker (ρ (π g) - 1)) ≤ e) → Module.Finite k (Fr.coneH2 (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) ∧ Module.finrank k (Fr.coneH2 (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) + Module.finrank k (Fr.coneH0 ρ b) + Module.finrank ℚ F * m ≤ Module.finrank k (Fr.H1C (fun v => π.comp (Dec (F := F) (A v)).subtype) ρ b) + Module.finrank ℚ F * e := by
  intro hP F Ω _ _ _ _ _ l _ hF S K Γ _ _ _ _ _ _ π hg honly V ι A hA k W _ _ _ _ _ _ ρ b m e hop hb hdual hm he
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  letI : Fintype V := Fintype.ofEquiv S ι.symm
  letI : TopologicalSpace W := ⊥
  haveI : DiscreteTopology W := ⟨rfl⟩
  letI : ∀ v, TopologicalSpace (W ⧸ b v) := fun _ => ⊥
  haveI : ∀ v, DiscreteTopology (W ⧸ b v) := fun _ => ⟨rfl⟩
  haveI : ∀ v, CompactSpace (Dec (F := F) (A v)) := fun v =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (A v)).isCompact
  have hρ : ContAction ρ := contAct ρ hop
  choose c hc using fun w : InfinitePlace F => cc_ex (Ω := Ω) w
  have hA' : ∀ w : S, IsPlaceOver (A (ι.symm w)) w.1 := fun w => by simpa using hA (ι.symm w)
  have hD : Loc.H0dual (GC.cycF F Ω l k) (ρ.comp π) = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun f hf => hdual f hf
  let d : ∀ v, Dec (F := F) (A v) →* Γ := fun v => π.comp (Dec (F := F) (A v)).subtype
  have hdc : ∀ v, Continuous (d v) := fun v => hg.cont.comp continuous_subtype_val
  let τ : ∀ v, Representation k (Dec (F := F) (A v)) (W ⧸ b v) := fun v =>
    Representation.quotient (ρ.comp (d v)) (b v) fun g X hX => hb v g.1 g.2 X hX
  have hτq : ∀ v s m, (b v).mkQ (ρ (d v s) m) = τ v s ((b v).mkQ m) := fun _ _ _ => rfl
  have hτ : ∀ v, ContAction (τ v) := fun v => by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨m, rfl⟩ := (b v).mkQ_surjective m
    exact (continuous_of_discreteTopology (f := (b v).mkQ)).comp (hρ.comp ((hdc v).prodMk continuous_const))
  have hE := fun v => GC.locEuler hP.lf hP.lt hP.le F Ω l (ι v).1 (A v) (hA v) k (W ⧸ b v) (τ v) (hτ v)
  obtain ⟨f1, f2, -⟩ := GC.H2_galois_quotient_eq hP F Ω l hF S K Γ π hg k W ρ hρ _ hc _ hA'
  have hO := GC.H2_galois_quotient_surjective hP F Ω l hF S K Γ π hg k W ρ hρ _ hc _ hA' hD (fun w => W ⧸ b (ι.symm w))
    (fun w => τ (ι.symm w)) (fun w => (b (ι.symm w)).mkQ) (fun w => hτq (ι.symm w))
    fun w => (b (ι.symm w)).mkQ_surjective
  have hC := GC.coneCount l Γ V (fun v => Dec (F := F) (A v)) d hdc k W ρ hρ (fun v => W ⧸ b v) τ
    (fun v => (b v).mkQ) hτq (fun v => (b v).mkQ_surjective) f1 f2 fun v => (hE v).1
  have hbq : (fun v => LinearMap.ker (b v).mkQ) = b := funext fun v => Submodule.ker_mkQ _
  rw [hbq] at hC
  obtain ⟨-, g2, hC⟩ := hC
  refine ⟨g2, ?_⟩
  have hK := Submodule.finrank_mono (s := ⨅ v, LinearMap.ker (compatiblePairH2 ρ (τ v) (d v) (hdc v) (b v).mkQ
      continuous_of_discreteTopology (hτq v)))
    (t := ⨅ w : S, LinearMap.ker (compatiblePairH2 ρ (τ (ι.symm w)) (π.comp (Dec (F := F) (A (ι.symm w))).subtype)
      (hdc (ι.symm w)) (b (ι.symm w)).mkQ continuous_of_discreteTopology (hτq (ι.symm w))))
    (le_iInf fun w => iInf_le _ (ι.symm w))
  have s2 : ∑ w : S, Module.finrank k (H2 (τ (ι.symm w))) = ∑ v, Module.finrank k (H2 (τ v)) :=
    ι.symm.sum_comp fun v => Module.finrank k (H2 (τ v))
  have sR : ∑ w : InfinitePlace F, Module.finrank k (LinearMap.ker (ρ (π (c w)) - 1)) ≤ Module.finrank ℚ F * e := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun w : InfinitePlace F => Module.finrank k (LinearMap.ker (ρ (π (c w)) - 1))) e
      fun w _ => he _ (by obtain ⟨j, hj, -⟩ := hc w; exact ⟨j, hj⟩)
    refine this.trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank]
    omega
  obtain ⟨w0, hw0⟩ := ex_above l F
  obtain ⟨q, hq⟩ : ∃ q, q + m = Module.finrank k W :=
    ⟨_, by rw [← hm (ι.symm ⟨w0, hg.above _ hw0⟩)]; exact Submodule.finrank_quotient_add_finrank _⟩
  have hloc : ∀ v, Module.finrank k (H1 (τ v)) = Module.finrank k (H0 (τ v)) + Module.finrank k (H2 (τ v)) + locDeg (ι v).1 * q := fun v => by
    have a1 := (b v).finrank_quotient_add_finrank
    rw [hm v, ← hq] at a1
    rw [(hE v).2.2.1 (honly _ (ι v).2), Nat.add_right_cancel a1]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun v _ => hloc v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hdeg := Nat.mul_le_mul_right q (sum_deg l F (fun v => (ι v).1)
    (fun x y h => ι.injective (Subtype.ext h)) fun v => honly _ (ι v).2)
  rw [s2, ← hq, mul_add] at hO
  change Module.finrank k (Fr.coneH2 d ρ b) + _ + _ ≤ Module.finrank k (Fr.H1C d ρ b) + _
  omega
