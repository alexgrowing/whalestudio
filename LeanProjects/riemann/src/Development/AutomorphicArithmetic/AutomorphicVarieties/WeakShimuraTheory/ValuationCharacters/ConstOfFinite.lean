import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RedList
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ClChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CurveNorm

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Ch

theorem flat_min {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (f : A →+* R) (hf : f.Flat) {q : Ideal A}
    (hq : q ∈ minimalPrimes A) (hle : q ≤ (maximalIdeal R).comap f) : ∃ Q ∈ minimalPrimes R, Q.comap f = q := by
  letI := f.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : q.IsPrime := hq.1.1
  haveI : ((maximalIdeal R).comap f).IsPrime := Ideal.comap_isPrime f _
  haveI : (maximalIdeal R).LiesOver ((maximalIdeal R).comap f) := ⟨rfl⟩
  obtain ⟨P, -, hPp, hPq⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal R) hle
  haveI := hPp
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
  refine ⟨Q, hQ, ?_⟩
  haveI : Q.IsPrime := hQ.1.1
  have hle2 : Q.comap f ≤ q := by
    rw [hPq.over]
    exact Ideal.comap_mono hQP
  exact le_antisymm hle2 (hq.2 ⟨Ideal.comap_isPrime f Q, bot_le⟩ hle2)

def Adj (R : Type) [CommRing R] (D : ℕ) (P Q : Ideal R) : Prop :=
  P ∈ minimalPrimes R ∧ Q ∈ minimalPrimes R ∧ (D : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (P ⊔ Q))

private theorem ringKrullDim_quotient_eq_quotient_comap_of_surjective {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Surjective p) (Q : Ideal B) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap p) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk Q).comp p) :=
    Ideal.Quotient.mk_surjective.comp hp
  have hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs).symm,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hk)]

theorem chain (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    {R : Type} [CommRing R] [Nontrivial R] [Algebra O R] {a b D : ℕ} (π : MvPowerSeries (Fin a) O →ₐ[O] R)
    (f : Fin b → MvPowerSeries (Fin a) O) (hπ : Function.Surjective π) (hk : RingHom.ker π = Ideal.span (Set.range f))
    (hD : b + D ≤ a) {P Q : Ideal R} (hP : P ∈ minimalPrimes R) (hQ : Q ∈ minimalPrimes R) :
    Relation.ReflTransGen (Adj R D) P Q := by
  classical
  haveI : IsCO O O := inferInstance
  haveI : IsCO O (MvPowerSeries (Fin a) O) := co_mvps O O (Fin a)
  haveI : IsDomain (MvPowerSeries (Fin a) O) := NoZeroDivisors.to_isDomain _
  have hdim := ((UpperTheory.V.CA.cl_cm).1 O a).2
  have hcl : UpperTheory.V.CA.IsCL O (MvPowerSeries (Fin a) O) := by
    refine ⟨inferInstance, IsCO.complete (O := O), IsCO.isLocalHom, ?_⟩
    refine Module.Finite.of_surjective (Algebra.linearMap O (ResidueField (MvPowerSeries (Fin a) O))) ?_
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) z
    refine ⟨c, ?_⟩
    rw [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply O (MvPowerSeries (Fin a) O)]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← neg_sub]
    exact neg_mem hc
  have hne : RingHom.ker π ≠ ⊤ := RingHom.ker_ne_top _
  have hara : ReciprocityTheory.CA.AraLE (RingHom.ker π) b := by
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · exact Finset.card_image_le.trans (by simp)
    · rw [hk, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hdimle : ((D + b + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin a) O) := by
    rw [hdim]
    exact_mod_cast (by omega : D + b + 1 ≤ a + 1)
  have hp : Function.Surjective (π : MvPowerSeries (Fin a) O →+* R) := hπ
  have hmin : (RingHom.ker π).minimalPrimes =
      Ideal.comap (π : MvPowerSeries (Fin a) O →+* R) '' (⊥ : Ideal R).minimalPrimes := by
    have := Ideal.comap_minimalPrimes_eq_of_surjective hp ⊥
    exact this
  have hc : ∀ Q ∈ (⊥ : Ideal R).minimalPrimes,
      Q.comap (π : MvPowerSeries (Fin a) O →+* R) ∈ (RingHom.ker π).minimalPrimes :=
    fun Q hQ => hmin ▸ ⟨Q, hQ, rfl⟩
  have key := UpperTheory.V.AlgebraTools.Conn.clChain hcl (RingHom.ker π) b D hne hara hdimle _ (hc P hP) _ (hc Q hQ)
  rw [← Ideal.map_comap_of_surjective (π : MvPowerSeries (Fin a) O →+* R) hp P,
    ← Ideal.map_comap_of_surjective (π : MvPowerSeries (Fin a) O →+* R) hp Q]
  refine Relation.ReflTransGen.lift (Ideal.map (π : MvPowerSeries (Fin a) O →+* R)) (fun x y hxy => ?_) _ _ key
  obtain ⟨hx, hy, hd⟩ := hxy
  rw [hmin] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  show Adj R D _ _
  rw [Ideal.map_comap_of_surjective _ hp, Ideal.map_comap_of_surjective _ hp]
  refine ⟨hx', hy', ?_⟩
  have hsup : (x' ⊔ y').comap (π : MvPowerSeries (Fin a) O →+* R) =
      x'.comap (π : MvPowerSeries (Fin a) O →+* R) ⊔ y'.comap (π : MvPowerSeries (Fin a) O →+* R) := by
    conv_lhs => rw [← Ideal.map_comap_of_surjective _ hp x', ← Ideal.map_comap_of_surjective _ hp y',
      ← Ideal.map_sup, Ideal.comap_map_of_surjective _ hp]
    exact sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)
  rw [ringKrullDim_quotient_eq_quotient_comap_of_surjective _ hp, hsup]
  exact hd

theorem nice {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (ϖ : R) (hϖ : ϖ ∈ maximalIdeal R) (N : ℕ)
    (hN : 1 ≤ N) {ι κ : Type} [Finite ι] [Finite κ] (a : ι → Ideal R) (b : κ → Ideal R)
    (ha : ∀ i, ringKrullDim (R ⧸ a i) < N)
    (hb : ∀ k, ∀ q : Ideal R, q.IsPrime → b k ≤ q → (∀ i, ¬ a i ≤ q) → ringKrullDim (R ⧸ q) < N)
    (I : Ideal R) (hI : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I)) :
    ∃ p : Ideal R, p.IsPrime ∧ I ≤ p ∧ ringKrullDim (R ⧸ p) = 1 ∧ ϖ ∈ p ∧ (∀ i, ¬ a i ≤ p) ∧ ∀ k, ¬ b k ≤ p := by
  let T := Σ k : κ, {q : Ideal R // q ∈ (b k).minimalPrimes ∧ ∀ i, ¬ a i ≤ q}
  haveI : ∀ k : κ, Finite {q : Ideal R // q ∈ (b k).minimalPrimes ∧ ∀ i, ¬ a i ≤ q} := fun k =>
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (b k)).subset
      (fun q hq => hq.1)).to_subtype
  haveI : Finite T := inferInstance
  let c : ι ⊕ T → Ideal R := Sum.elim a (fun t => t.2.1)
  have hc : ∀ j, UpperTheory.V.Pr.qdim (c j) < N := by
    rintro (i | ⟨k, q, hq, hqa⟩)
    · exact ha i
    · exact hb k q hq.1.1 hq.1.2 hqa
  obtain ⟨p, hp, hIp, hd, hϖp, hav⟩ := UpperTheory.V.Pr.nicePrimeEx R ϖ hϖ N hN (ι ⊕ T) c hc I hI
  refine ⟨p, hp, hIp, hd, hϖp, fun i => hav (Sum.inl i), fun k hk => ?_⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hk
  by_cases hqa : ∀ i, ¬ a i ≤ q
  · exact hav (Sum.inr ⟨k, q, hq, hqa⟩) hqp
  · push_neg at hqa
    obtain ⟨i, hi⟩ := hqa
    exact hav (Sum.inl i) (hi.trans hqp)

private theorem eq_C_constantCoeff_of_pow_char_pow_eq_self {k : Type} [Field k] (l n : ℕ) [Fact l.Prime] [CharP (PowerSeries k) l]
    (hn : 1 ≤ n) (y : PowerSeries k) (hy : y ^ (l ^ n) = y) :
    y = PowerSeries.C (PowerSeries.constantCoeff y) := by
  have hc : (PowerSeries.constantCoeff y) ^ (l ^ n) = PowerSeries.constantCoeff y := by
    have := congrArg PowerSeries.constantCoeff hy
    rwa [map_pow] at this
  have hz : (y - PowerSeries.C (PowerSeries.constantCoeff y)) ^ (l ^ n) =
      y - PowerSeries.C (PowerSeries.constantCoeff y) := by
    rw [sub_pow_char_pow, hy, ← map_pow, hc]
  by_contra hne
  have hz0 : y - PowerSeries.C (PowerSeries.constantCoeff y) ≠ 0 := sub_ne_zero.mpr hne
  have hcc : PowerSeries.constantCoeff (y - PowerSeries.C (PowerSeries.constantCoeff y)) = 0 := by
    simp
  have ho := PowerSeries.order_pow (y - PowerSeries.C (PowerSeries.constantCoeff y)) (l ^ n)
  rw [hz] at ho
  have hnt : (y - PowerSeries.C (PowerSeries.constantCoeff y)).order ≠ ⊤ :=
    fun h => hz0 (PowerSeries.order_eq_top.mp h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnt
  rw [← hm, nsmul_eq_mul] at ho
  have hmm : m = l ^ n * m := by exact_mod_cast ho
  have hl2 : 2 ≤ l ^ n :=
    le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow (by omega) l)
  have hm0 : m = 0 := by nlinarith
  have hco := PowerSeries.coeff_order hz0
  rw [← hm, ENat.toNat_coe, hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hco
  exact hco hcc

theorem curve (l : ℕ) [Fact l.Prime] (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CharP (ResidueField O) l] [CommRing R] [Algebra O R] [IsCO O R] (p : Ideal R) (hp : p.IsPrime)
    (hd : ringKrullDim (R ⧸ p) = 1) (hm : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ p) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra O K) (j : R →ₐ[O] PowerSeries K),
      (∀ x, j x = 0 ↔ x ∈ p) ∧ ∀ x ∈ maximalIdeal R, PowerSeries.constantCoeff (j x) = 0 := by
  haveI := hp
  haveI : Nontrivial (R ⧸ p) := inferInstance
  haveI : IsCO O (R ⧸ p) :=
    co_quot O R (R ⧸ p) (Ideal.Quotient.mkₐ O p) (Ideal.Quotient.mkₐ_surjective O p)
  haveI : IsAdicComplete (maximalIdeal (R ⧸ p)) (R ⧸ p) := IsCO.complete (O := O)
  haveI := Fintype.ofFinite (ResidueField O)
  have hl : ((l : ℕ) : R ⧸ p) = 0 := by
    have h1 : ((l : ℕ) : O) ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ l
    have h2 := hm _ h1
    rw [map_natCast] at h2
    rw [← map_natCast (Ideal.Quotient.mk p), Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  haveI : CharP (R ⧸ p) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hl
  haveI : Finite (ResidueField (R ⧸ p)) := by
    haveI : IsLocalHom (algebraMap O (R ⧸ p)) := IsCO.isLocalHom
    refine Finite.of_surjective (ResidueField.map (algebraMap O (R ⧸ p))) ?_
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨residue O a, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact ha
  obtain ⟨k, _, hk, f, hinj, hloc, -⟩ := UpperTheory.V.Pr.T.curveNorm (R := R ⧸ p) l hd
  haveI : CharP (PowerSeries k) l :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by rw [← map_natCast f, hl, map_zero])
  obtain ⟨n, -, hcard⟩ := FiniteField.card (ResidueField O) l
  have hconst : ∀ a : O, f (algebraMap O (R ⧸ p) a) =
      PowerSeries.C (PowerSeries.constantCoeff (f (algebraMap O (R ⧸ p) a))) := by
    intro a
    apply eq_C_constantCoeff_of_pow_char_pow_eq_self l n n.pos
    have hq : a ^ (l ^ (n : ℕ)) - a ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sub, map_pow, ← hcard, FiniteField.pow_card, sub_self]
    have h3 : algebraMap O (R ⧸ p) (a ^ (l ^ (n : ℕ)) - a) = 0 := by
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
      exact hm _ hq
    exact sub_eq_zero.mp (by rw [← map_pow, ← map_sub, ← map_pow, ← map_sub, h3, map_zero])
  letI : Algebra O k :=
    ((PowerSeries.constantCoeff).comp (f.comp (algebraMap O (R ⧸ p)))).toAlgebra
  refine ⟨k, inferInstance, hk, inferInstance,
    { toRingHom := f.comp (Ideal.Quotient.mk p), commutes' := fun a => ?_ }, fun x => ?_, fun x hx => ?_⟩
  · show f (Ideal.Quotient.mk p (algebraMap O R a)) = _
    rw [PowerSeries.algebraMap_apply, Ideal.Quotient.mk_algebraMap, hconst a]
    rfl
  · show f (Ideal.Quotient.mk p x) = 0 ↔ x ∈ p
    rw [map_eq_zero_iff f hinj, Ideal.Quotient.eq_zero_iff_mem]
  · show PowerSeries.constantCoeff (f (Ideal.Quotient.mk p x)) = 0
    have hxu : ¬ IsUnit (Ideal.Quotient.mk p x) := by
      intro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul, ← map_one (Ideal.Quotient.mk p), Ideal.Quotient.eq] at hy
      have h4 : x * y' - 1 ∈ maximalIdeal R := IsLocalRing.le_maximalIdeal hp.ne_top hy
      have h5 : (1 : R) ∈ maximalIdeal R := by
        have := sub_mem (Ideal.mul_mem_right y' _ hx) h4
        simpa using this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h5)
    have hfu : ¬ IsUnit (f (Ideal.Quotient.mk p x)) := fun h => hxu (hloc.map_nonunit _ h)
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not] at hfu
    exact hfu

theorem irr {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {a : O →+* Λ} (hok : Φ.Ok ((residue Λ).comp a)) {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {P : PD Φ.ι Γ R} (hP : Φ.Lifts a c P) {K : Type} [Field K]
    (φ : R →+* K) (q : Ideal R) (hq : ∀ x, φ x = 0 → x ∈ q) (h : ∀ S ∈ redTypes, ¬ redIdeal S P.r ≤ q) :
    Irr (mapRep φ P.r) := by
  classical
  have hred := hP.red
  have hdiag := hc.res.diag
  have key : ∀ i j : Fin 4, i ≠ j → IsUnit (P.r Φ.g0 i i - P.r Φ.g0 j j) := by
    intro i j hij
    have hu := hok.dist i j hij
    rw [← hdiag Φ.g0 i, ← hdiag Φ.g0 j, ← hred] at hu
    by_contra hn
    have hm : P.r Φ.g0 i i - P.r Φ.g0 j j ∈ maximalIdeal R := hn
    have h0 : res Λ R (P.r Φ.g0 i i - P.r Φ.g0 j j) = 0 := by
      simp [res, (IsLocalRing.residue_eq_zero_iff _).2 hm]
    apply hu.ne_zero
    simpa [PD.map, mapRep, map_sub] using h0
  by_contra hn
  obtain ⟨S, hS, hsupp⟩ := (redList (mapRep φ P.r) (fun g => φ (algebraMap Λ R (a ↑(Φ.ν g)))) Φ.g0
    (fun g => isGSp_map φ (hP.pair.mult g))
    (hP.pair.nrm.map (map_zero φ))
    (fun i j hij heq => ((key i j hij).map φ).ne_zero (by
      rw [map_sub]
      simpa [mapRep] using sub_eq_zero.mpr heq))).1 hn
  apply h S hS
  rw [redIdeal, Ideal.span_le]
  rintro x ⟨g, i, j, hij, hw, rfl⟩
  apply hq
  have := hsupp g i j hij hw
  simpa [mapRep] using this

end UpperTheory.V.Ws.Ch
