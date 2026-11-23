import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem exists_conj (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] :
    ∃ c : G (W.Lp L) Ω, ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  let j : Ω →ₐ[L] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := (j : Ω →+* ℂ).toAlgebra
  haveI : IsScalarTower (W.Lp L) Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes (x : L)).symm
  let s : ℂ →ₐ[W.Lp L] ℂ :=
    { starRingEnd ℂ with commutes' := fun x => (mem_maximalRealSubfield_iff (x : L)).1 x.2 φ }
  exact ⟨s.restrictNormal' Ω, j, fun x => s.restrictNormal_commutes Ω x⟩

private theorem ne_top {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) : A ≠ ⊤ := by
  rintro rfl
  refine v.ne_bot (eq_bot_iff.2 fun x hx => ?_)
  have h1 := (h x).2 hx
  rw [valuation_lt_one_iff'] at h1
  have h2 := h1.2.resolve_right fun h' => h' (ValuationSubring.mem_top _)
  simpa using h2

private theorem val_nat {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {v : W.Plc k} (h : IsPlaceOver A v) (q : ℕ) : A.valuation (q : Ω) < 1 ↔ (q : 𝓞 k) ∈ v.asIdeal := by
  simpa using h (q : 𝓞 k)

private theorem fin_nat {k : Type} [Field k] [NumberField k] {q : ℕ} (hq : q ≠ 0) :
    {v : W.Plc k | (q : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {(q : 𝓞 k)}) (by simpa using hq)
  simpa [Ideal.dvd_span_singleton] using h

private theorem eq_of_mem {k : Type} [Field k] [NumberField k] {v : W.Plc k} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : 𝓞 k) ∈ v.asIdeal) (h2 : (q : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := 𝓞 k) ((Nat.coprime_primes hp hq).2 hne)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)))

theorem UpperTheory.V.Ws.Lk.mkSet :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], l ≠ 2 → (∀ A : ValuationSubring Ω, Ine (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → l ∈ S → (∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ A₀ : W.Vl l L → ValuationSubring Ω, (∀ v, IsPlaceOver (A₀ v) v.1) → ∀ (v₀ : W.Plc (W.Lp L)) (B : ValuationSubring Ω) (p : ℕ), p.Prime → p ≠ 2 → p ∉ S → ¬ (p : ℤ) ∣ discr L → ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v₀.asIdeal → normV v₀ = p → IsPlaceOver B v₀ → Dec (F := W.Lp L) B ≤ (W.resP L Ω).range → ∃ s : W.HidaSetting l L Ω, (∀ v : W.Vl l L, s.A v = A₀ v) ∧ s.A s.v0 = B ∧ s.S.Finite ∧ (∀ q ∈ S, ¬ B.valuation (q : Ω) < 1) ∧ ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ s.S → ∀ q ∈ S, ¬ A.valuation (q : Ω) < 1 := by
  classical
  intro l hl L Ω _ _ _ _ _ _ hodd hunr S hS hlS hsp A₀ hA₀ v₀ B p hp hp2 hpS hpd hpv hnv hB hBs
  have hq0 : ∀ q ∈ S, (q : 𝓞 (W.Lp L)) ∉ v₀.asIdeal := fun q hq h =>
    hpS (eq_of_mem hp (hS q hq) hpv h ▸ hq)
  obtain ⟨c, hc⟩ := exists_conj L Ω
  have hex : ∀ v : W.Plc (W.Lp L), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧
      (∀ h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal, A = A₀ ⟨v, h⟩) ∧ (v = v₀ → A = B) := by
    intro v
    by_cases h : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact ⟨A₀ ⟨v, h⟩, hA₀ ⟨v, h⟩, fun _ => rfl, fun e => absurd (e ▸ h) (hq0 l hlS)⟩
    · by_cases e : v = v₀
      · exact ⟨B, e ▸ hB, fun h' => absurd h' h, fun _ => rfl⟩
      · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
        exact ⟨A, hA, fun h' => absurd h' h, fun e' => absurd e' e⟩
  choose A hA hAl hA0 using hex
  choose w hw using fun v => (places L Ω l (A v)).1 (ne_top (hA v))
  have hfin : {v : W.Plc (W.Lp L) | (∃ q ∈ S, (q : 𝓞 (W.Lp L)) ∈ v.asIdeal) ∧ (l : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite :=
    (S.finite_toSet.biUnion fun q hq => fin_nat (k := W.Lp L) (hS q hq).ne_zero).subset fun v hv => by
      obtain ⟨⟨q, hq, h⟩, -⟩ := hv
      exact Set.mem_biUnion hq h
  refine ⟨{ odd := hodd, unr := fun B _ _ => hunr B, c := c, hc := hc, w := w, A := A, hw := hw, hA := hA,
            St := hfin.toFinset, St_l := fun u hu => (hfin.mem_toFinset.1 hu).2, v0 := v₀, v0_St := ?_, p := p,
            p_prime := hp, p_odd := hp2, p_ne := fun e => hpS (e ▸ hlS), p_unr := hpd, norm_v0_eq_one := hnv,
            split := ?_ }, fun v => hAl v.1 v.2, hA0 v₀ rfl, ?_, fun q hq h => hq0 q hq ((val_nat hB q).1 h), ?_⟩
  · intro h
    obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
    exact hq0 q hq h
  · rintro v (h | h | rfl)
    · exact hsp l hlS _ ((val_nat (hA v) l).2 h)
    · obtain ⟨⟨q, hq, h⟩, -⟩ := hfin.mem_toFinset.1 h
      exact hsp q hq _ ((val_nat (hA v) q).2 h)
    · rw [hA0 v rfl]; exact hBs
  · exact (fin_nat hl.out.ne_zero).union ((Finset.finite_toSet _).union (Set.finite_singleton v₀))
  · intro A' v hv hvS q hq h
    refine hvS ?_
    by_cases h' : (l : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact Or.inl h'
    · exact Or.inr (Or.inl (hfin.mem_toFinset.2 ⟨⟨q, hq, (val_nat hv q).1 h⟩, h'⟩))
