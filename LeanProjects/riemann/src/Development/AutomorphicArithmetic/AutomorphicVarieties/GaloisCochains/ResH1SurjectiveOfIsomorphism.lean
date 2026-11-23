import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ConeCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem cast_toZModPow_one (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) k (PadicInt.toZModPow 1 x) =
      ZMod.castHom (dvd_refl l) k (PadicInt.toZMod x) := by
  have hx : x - (PadicInt.zmodRepr x : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := PadicInt.sub_zmodRepr_mem x
  have h1 : PadicInt.toZMod (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]; exact hx
  have h2 : PadicInt.toZModPow 1 (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p]; exact hx
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]
  simp only [map_natCast]

private theorem sum_deg (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] {V : Type} [Fintype V]
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal) :
    ∑ v, locDeg (pl v) ≤ finrank ℚ F := by
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

section

variable {k G H M : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]

private theorem resH1_surjective_of_isomorphism (τ : Representation k H M) (j : G →* H) (hj : Continuous j) (r : H →* G) (hr : Continuous r)
    (h1 : ∀ x, j (r x) = x) (h2 : ∀ x, r (j x) = x) : Function.Surjective (resH1 τ j hj) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨Submodule.Quotient.mk ⟨z.1 ∘ r, z.2.1.comp hr, fun g h => ?_⟩, ?_⟩
  · have := z.2.2 (r g) (r h)
    simp only [MonoidHom.comp_apply, h1] at this
    simp only [Function.comp_apply, map_mul, this]
  · refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
    change z.1 (r (j g)) = z.1 g
    rw [h2]

private theorem ker_le {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup W] [Module k W] [TopologicalSpace W]
    [DiscreteTopology W] (ρ : Representation k Γ W) (τ : Representation k H M) (j : G →* H) (r : H →* G)
    (hr : Continuous r) (h1 : ∀ x, j (r x) = x) (a : G →* Γ) (ha : Continuous a) (b : H →* Γ) (hb : Continuous b)
    (hab : ∀ x, a x = b (j x)) (q : W →ₗ[k] M) (hq : Continuous q)
    (ea : ∀ s m, q (ρ (a s) m) = (τ.comp j) s (q m)) (eb : ∀ s m, q (ρ (b s) m) = τ s (q m)) :
    LinearMap.ker (compatiblePairH2 ρ (τ.comp j) a ha q hq ea) ≤ LinearMap.ker (compatiblePairH2 ρ τ b hb q hq eb) := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c, hc, hz⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
  refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ r, hc.comp hr, funext fun p => ?_⟩)
  have := congrFun hz (r p.1, r p.2)
  change τ (j (r p.1)) (c (r p.2)) - c (r p.1 * r p.2) + c (r p.1) = q (z.1 (a (r p.1), a (r p.2))) at this
  rw [hab, hab, h1, h1, ← map_mul] at this
  exact this

private theorem contAct [IsTopologicalGroup G] (ρ : Representation k G M) (h : IsOpen (ρ.ker : Set G)) :
    ContAction ρ := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (ρ.ker : Set G), h.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have hx' : ρ (g⁻¹ * x) = 1 := hx
  have : ρ x = ρ g := by rw [← mul_inv_cancel_left g x, map_mul, hx', mul_one]
  simp only [this]

end

theorem UpperTheory.V.GC.ec :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → Φ.EC := by
  intro hP F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL E W _ _ _ _ _ _ ρ b hop hb hdual
  classical
  letI : TopologicalSpace W := ⊥
  haveI : DiscreteTopology W := ⟨rfl⟩
  letI : ∀ v, TopologicalSpace (W ⧸ b v) := fun _ => ⊥
  haveI : ∀ v, DiscreteTopology (W ⧸ b v) := fun _ => ⟨rfl⟩
  have hρ : ContAction ρ := contAct ρ hop
  have hpl : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal := fun v => (hL.loc.mem _).1 ⟨v, rfl⟩
  let u0 : Φ.V → S := fun v => ⟨pl v, hL.g.above _ (hpl v)⟩
  have hu0 : Function.Bijective u0 := ⟨fun x y h => hL.loc.inj (congrArg Subtype.val h), fun w => by
    obtain ⟨v, hv⟩ := (hL.loc.mem w.1).2 (hL.only w.1 w.2)
    exact ⟨v, Subtype.ext hv⟩⟩
  let u : S ≃ Φ.V := (Equiv.ofBijective u0 hu0).symm
  have hu : ∀ w : S, pl (u w) = w.1 := fun w => congrArg Subtype.val (u.symm_apply_apply w)
  have hA : ∀ w : S, IsPlaceOver (A (u w)) w.1 := fun w => hu w ▸ hL.loc.isOver (u w)
  have hc : ∀ w : InfinitePlace F, IsCCAt w (c (e.symm w)) := fun w => by
    simpa using hL.cc (e.symm w)
  have hcyc : ∀ g, Φ.om E (π g) = cycF F Ω l E g := fun g => by
    apply Units.ext
    have := cast_toZModPow_one l E (cycZ F Ω l g : ℤ_[l])
    simp only [Frame.om, cycF, cycMod, MonoidHom.comp_apply, hL.eps, Units.coe_map]
    exact this.symm
  have hD : Loc.H0dual (cycF F Ω l E) (ρ.comp π) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun f hf => hdual f fun g X => ?_
    obtain ⟨g, rfl⟩ := hL.g.onto g
    rw [hcyc]
    exact hf g X
  let j : ∀ v, Φ.Gv v →* Dec (F := F) (A v) := fun v =>
    (ι v).codRestrict _ fun s => by rw [← hL.loc.range]; exact ⟨s, rfl⟩
  have hjc : ∀ v, Continuous (j v) := fun v => (hL.loc.cont v).subtype_mk _
  have hjb : ∀ v, Function.Bijective (j v) := fun v =>
    ⟨fun x y h => hL.loc.ι_inj v (congrArg Subtype.val h), fun x => by
      have hx : x.1 ∈ (ι v).range := by rw [hL.loc.range]; exact x.2
      obtain ⟨s, hs⟩ := hx
      exact ⟨s, Subtype.ext hs⟩⟩
  let r : ∀ v, Dec (F := F) (A v) →* Φ.Gv v := fun v => (MulEquiv.ofBijective (j v) (hjb v)).symm.toMonoidHom
  have hrc : ∀ v, Continuous (r v) := fun v =>
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective (j v) (hjb v)).toEquiv) (hjc v)
  have h1 : ∀ v x, j v (r v x) = x := fun v => (MulEquiv.ofBijective (j v) (hjb v)).apply_symm_apply
  have h2 : ∀ v x, r v (j v x) = x := fun v => (MulEquiv.ofBijective (j v) (hjb v)).symm_apply_apply
  let d : ∀ v, Dec (F := F) (A v) →* Φ.Γ := fun v => π.comp (Dec (F := F) (A v)).subtype
  have hdc : ∀ v, Continuous (d v) := fun v => hL.g.cont.comp continuous_subtype_val
  have hdj : ∀ v s, Φ.loc v s = d v (j v s) := hL.loc_eq
  have hlc : ∀ v, Continuous (Φ.loc v) := fun v => ((hdc v).comp (hjc v)).congr fun s => (hdj v s).symm
  let τ : ∀ v, Representation E (Dec (F := F) (A v)) (W ⧸ b v) := fun v =>
    Representation.quotient (ρ.comp (d v)) (b v) fun g X hX => by
      have := hb v (r v g) X hX
      rw [hdj, h1] at this
      exact this
  have hτq : ∀ v s m, (b v).mkQ (ρ (d v s) m) = τ v s ((b v).mkQ m) := fun _ _ _ => rfl
  have hσq : ∀ v s m, (b v).mkQ (ρ (Φ.loc v s) m) = ((τ v).comp (j v)) s ((b v).mkQ m) := fun v s m => by
    rw [hdj]; rfl
  have hτ : ∀ v, ContAction (τ v) := fun v => by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨m, rfl⟩ := (b v).mkQ_surjective m
    exact (continuous_of_discreteTopology (f := (b v).mkQ)).comp (hρ.comp ((hdc v).prodMk continuous_const))
  have hE := fun v => locEuler hP.lf hP.lt hP.le F Ω l (pl v) (A v) (hL.loc.isOver v) E (W ⧸ b v) (τ v) (hτ v)
  have hon := fun v => resH1_surjective_of_isomorphism (τ v) (j v) (hjc v) (r v) (hrc v) (h1 v) (h2 v)
  obtain ⟨f1, f2, -⟩ := H2_galois_quotient_eq hP F Ω l hL.real S K Φ.Γ π hL.g E W ρ hρ _ hc _ hA
  have hO := H2_galois_quotient_surjective hP F Ω l hL.real S K Φ.Γ π hL.g E W ρ hρ _ hc _ hA hD (fun w => W ⧸ b (u w))
    (fun w => τ (u w)) (fun w => (b (u w)).mkQ) (fun w => hτq (u w)) fun w => (b (u w)).mkQ_surjective
  have hC := coneCount l Φ.Γ Φ.V Φ.Gv Φ.loc hlc E W ρ hρ (fun v => W ⧸ b v) (fun v => (τ v).comp (j v))
    (fun v => (b v).mkQ) hσq (fun v => (b v).mkQ_surjective) f1 f2
    fun v => haveI := (hE v).1; Module.Finite.of_surjective _ (hon v)
  have hbq : (fun v => LinearMap.ker (b v).mkQ) = b := funext fun v => Submodule.ker_mkQ _
  rw [hbq] at hC
  obtain ⟨-, g2, hC⟩ := hC
  refine ⟨g2, ?_⟩
  have hK := Submodule.finrank_mono (s := ⨅ v, LinearMap.ker (compatiblePairH2 ρ ((τ v).comp (j v)) (Φ.loc v) (hlc v) (b v).mkQ
      continuous_of_discreteTopology (hσq v)))
    (t := ⨅ w : S, LinearMap.ker (compatiblePairH2 ρ (τ (u w)) (π.comp (Dec (F := F) (A (u w))).subtype) (hdc (u w)) (b (u w)).mkQ
      continuous_of_discreteTopology (hτq (u w))))
    (le_iInf fun w => (iInf_le _ (u w)).trans
      (ker_le ρ _ (j _) (r _) (hrc _) (h1 _) _ _ _ _ (hdj _) _ _ _ _))
  have s2 : ∑ w : S, finrank E (H2 (τ (u w))) = ∑ v, finrank E (H2 (τ v)) :=
    u.sum_comp fun v => finrank E (H2 (τ v))
  have sR : ∑ w : InfinitePlace F, finrank E (LinearMap.ker (ρ (π (c (e.symm w))) - 1)) =
      ∑ w, finrank E (LinearMap.ker (ρ (Φ.cw w) - 1)) := by
    rw [e.symm.sum_comp fun w => finrank E (LinearMap.ker (ρ (π (c w)) - 1))]
    exact Finset.sum_congr rfl fun w _ => by rw [hL.cw]
  have hloc : ∀ v, finrank E (H1 ((τ v).comp (j v))) + Φ.dv v * finrank E (b v) ≤
      finrank E (H0 ((τ v).comp (j v))) + finrank E (H2 (τ v)) + locDeg (pl v) * finrank E W := fun v => by
    haveI := (hE v).1
    have a1 := LinearMap.finrank_le_finrank_of_surjective (hon v)
    have a2 := (hE v).2.2.1 (hpl v)
    have a3 : H0 ((τ v).comp (j v)) = H0 (τ v) := le_antisymm
      (fun m hm g => by have := hm (r v g); rwa [MonoidHom.comp_apply, h1] at this) fun m hm g => hm (j v g)
    rw [a3, hL.dv, ← (b v).finrank_quotient_add_finrank, mul_add]
    omega
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hloc v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hdeg := Nat.mul_le_mul_right (finrank E W) (sum_deg l F pl hL.loc.inj hpl)
  rw [s2, sR] at hO
  omega
