import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ValLtIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IncLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.HomOfDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FibLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChCore

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

namespace UpperTheory.V.Cu.RankFourReductionTypeChain

private theorem ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)

private theorem supp_of {Γ A R K : Type} [Group Γ] [CommRing A] [CommRing R] [CommRing K] (r : Γ →* M4 A) (f : A →+* R)
    (φ : R →+* K) (q : Ideal R) (hq : ∀ z ∈ q, φ z = 0) {S : Finset (ℤ × ℤ)} (h : redIdeal S (mapRep f r) ≤ q) :
    Supp S (mapRep (φ.comp f) r) := fun g i j hij hw => by
  simpa [mapRep_apply] using hq _ (h (Ideal.subset_span ⟨g, i, j, hij, hw, rfl⟩))

private theorem ent_of {Γ A R K : Type} [Group Γ] [CommRing A] [CommRing R] [Field K] (r : Γ →* M4 A) (f : A →+* R)
    (φ : R →+* K) (q : Ideal R) (hq : ∀ z, φ z = 0 ↔ z ∈ q) (hY : redIdeal yY (mapRep f r) ≤ q)
    {S : Finset (ℤ × ℤ)} (hS : ¬ redIdeal S (mapRep f r) ≤ q) {w : ℤ × ℤ} (hw : ∀ u ∈ yY, u ∉ S → u = w) :
    Ent (mapRep (φ.comp f) r) w := by
  classical
  by_contra hn
  refine hS (Ideal.span_le.2 ?_)
  rintro _ ⟨g, i, j, hij, hwS, rfl⟩
  by_cases hy : wt i j ∈ yY
  · refine (hq _).1 ?_
    by_contra h0
    exact hn ⟨g, i, j, hw _ hy hwS, by simpa [mapRep_apply] using h0⟩
  · exact hY (Ideal.subset_span ⟨g, i, j, hij, hy, rfl⟩)

private theorem w1 : ∀ u ∈ yY, u ∉ ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) → u = wTh := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))

private theorem w2 : ∀ u ∈ yY, u ∉ ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) → u = -wTh := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))

private theorem w3 : ∀ u ∈ yY, u ∉ ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) → u = -wBe := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))

private theorem w4 : ∀ u ∈ yY, u ∉ ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) → u = wBe := by
  first
  | decide
  | (intro u hu hS
     simp only [yY, Finset.mem_insert, Finset.mem_singleton] at hu
     rcases hu with rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; exact hS (by simp)))

private theorem t1 : ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wBe, -wBe, -wAl, -wTh, -wPs} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.head _, by first | decide | (intro h; have := congrArg (fun s => -wAl ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩

private theorem t2 : ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wBe, -wBe, wAl, wTh, wPs} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.head _), by first | decide | (intro h; have := congrArg (fun s => wAl ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩

private theorem t3 : ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wTh, -wTh, wPs, wBe, -wAl} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), by first | decide | (intro h; have := congrArg (fun s => wPs ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩

private theorem t4 : ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) ∈ redTypes ∧
    ({wTh, -wTh, -wPs, -wBe, wAl} : Finset (ℤ × ℤ)) ≠ yY :=
  ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), by first | decide | (intro h; have := congrArg (fun s => -wPs ∈ s) h; simp [yY, wAl, wBe, wTh, wPs] at this)⟩

private theorem ch_core4 (hRA : RedA) (hYC : YCoin) (hFY : FibY) {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type}
    [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)]
    {a : O →+* Λ} (hS : Φ.Std l a) (hne : Nonempty Φ.ι)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hIA : InA c)
    (hE : Ent c.r (-wPs) ∨ (Ent c.r (-wBe) ∧ Ent c.r (-wTh)))
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes ∧ S ≠ yY} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes ∧ S ≠ yY} :=
    Set.Finite.to_subtype ((List.finite_toSet redTypes).subset fun S h => h.1)
  have hb : ∀ t, ∀ q : Ideal R, q.IsPrime → B t ≤ q → (∀ S, ¬ A S ≤ q) → ringKrullDim (R ⧸ q) < N := by
    intro t q hq hle hr
    haveI := hq
    have hq0 : ∀ z, ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) z = 0 ↔ z ∈ q := fun z => by
      rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q))),
        Ideal.Quotient.eq_zero_iff_mem]
    have hfib : ringKrullDim (R ⧸ q) ≤
        ringKrullDim (X.B ⧸ q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) + (2 + 4 * Nat.card Φ.ι : ℕ) := by
      by_cases hYq : redIdeal yY (X.P.map (f : X.A →+* R)).r ≤ q
      · exact hFY Φ l a hS X c hc R f hdef q _ rfl (supp_of X.P.r _ _ q (fun z hz => (hq0 z).2 hz) hYq)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t4⟩) w4)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t3⟩) w3)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t1⟩) w1)
          (ent_of X.P.r _ _ q hq0 hYq (hr ⟨_, t2⟩) w2)
      · exact fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
          ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q (fun z hz => (hq0 z).1 hz)
          fun S hS' => by
            by_cases hSY : S = yY
            · subst hSY
              exact hYq
            · exact hr ⟨S, hS', hSY⟩)
    exact ch_num hfib
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (hRA Φ l a hS d C hB c hc hIA hE R _ hdef S.1 S.2.1 S.2.2).trans_lt (by exact_mod_cast hN1))
    hb _ hPQ.2.2
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  have hYp : ¬ redIdeal yY (X.P.map (f : X.A →+* R)).r ≤ p := by
    intro hle
    haveI := hp
    obtain ⟨v⟩ := hne
    have hq0 : ∀ z ∈ p, ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)) z = 0 := fun z hz => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]
    have hpair := hdef.1.pair.map ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))
    rw [PD.map_map] at hpair
    have hsupp := supp_of X.P.r (f : X.A →+* R) _ p hq0 hle
    have h1 : res Λ R ((f : X.A →+* R) (X.P.n v 1 0)) = c.n v 1 0 := by
      rw [← hdef.1.red]
      rfl
    have hu : IsUnit ((f : X.A →+* R) (X.P.n v 1 0)) := by
      by_contra hu
      have h4 := (res_eq_zero_iff Λ R _).2 ((mem_maximalIdeal _).2 hu)
      rw [h1] at h4
      exact hIA.2 v h4
    have hn : (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
        (f : X.A →+* R))).n v 1 0 ≠ 0 := by
      have := (hu.map ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))).ne_zero
      simpa only [PD.map_n, Matrix.map_apply, RingHom.comp_apply] using this
    have hBle : ∀ (i i' : Fin 4) (hi : i ≠ i'), (∀ s ∈ Φ.Gv v,
        (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
          (f : X.A →+* R))).ψ v i s =
        (X.P.map (((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)).comp
          (f : X.A →+* R))).ψ v i' s) → B ⟨(v, i, i'), hi⟩ ≤ p := fun i i' hi hh => by
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp) ((Ideal.span_singleton_le_iff_mem _).2 hϖp))
        (Ideal.span_le.2 ?_)
      rintro _ ⟨s, hs, rfl⟩
      have e := hh s (hU v s hs)
      simp only [PD.map_ψ, RingHom.comp_apply] at e
      have e2 : ∀ k, φ (X.ψ v k s) = (f : X.A →+* R) (X.P.ψ v k s) := fun k => by
        show (f : X.A →+* R) (algebraMap X.B X.A (X.ψ v k s)) = _
        rw [X.ψ_map v k s (hU v s hs)]
      show φ (X.ψ v i s - X.ψ v i' s) ∈ p
      rw [map_sub, e2, e2, ← Ideal.Quotient.eq_zero_iff_mem,
        ← map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))), map_sub, map_sub, e, sub_self]
    rcases hYC Φ _ _ hpair hsupp v hn with h01 | h13
    · exact hBp ⟨(v, 0, 1), (by decide : (0 : Fin 4) ≠ 1)⟩ (hBle 0 1 (by decide) h01)
    · exact hBp ⟨(v, 1, 3), (by decide : (1 : Fin 4) ≠ 3)⟩ (hBle 1 3 (by decide) h13)
  have hirr : ∀ S ∈ redTypes, ¬ redIdeal S (X.P.map (f : X.A →+* R)).r ≤ p := fun S hS' => by
    by_cases hSY : S = yY
    · subst hSY
      exact hYp
    · exact hA ⟨S, hS', hSY⟩
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) hirr)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]

end UpperTheory.V.Cu.RankFourReductionTypeChain
