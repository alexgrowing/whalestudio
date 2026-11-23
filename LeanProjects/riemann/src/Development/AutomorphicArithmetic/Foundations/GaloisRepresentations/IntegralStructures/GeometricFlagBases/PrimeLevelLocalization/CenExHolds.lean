import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.ShapeOfTorusCentrePower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.NatCastNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.ConjInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.MulVecInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.ExistsUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LocIdx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.SpanAbsNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl

theorem cenEx_holds : CenEx := fun E _ _ _ n d x hd hx w _ _ =>
  (UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.cenEx E n d x hd hx w).imp fun _ h => h.1

private theorem q_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    {N : Lv p} {w : Plc E} (σ : Site S N w) : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))

private theorem dvd_of {E : Type} [Field E] [NumberField E] (w : Plc E) {q c : ℕ} (hq : q.Prime) (h1 : (q : 𝓞 E) ∈ w.asIdeal)
    (h2 : (c : 𝓞 E) ∈ w.asIdeal) : q ∣ c := by
  by_contra h
  obtain ⟨a, b, e⟩ : IsCoprime (q : 𝓞 E) (c : 𝓞 E) := (hq.coprime_iff_not_dvd.2 h).cast
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem tjOK_of (h1 : Sides) (h2 : Dict) (h3 : LevBasic) : TjOK := by
  rintro E _ _ _ A n p _ S F x hx N w σ i hi _ ⟨hw, t, z, ht, hz, rfl⟩
  have s := shpOf h1 E A n x hx σ.q σ.atp.prime σ.good.1 w (q_mem σ) hw i hi t z ht hz
  obtain ⟨a1, a2⟩ := tCong h1 h2 h3 E A n p S F x hx N w σ i hi _ s
  obtain ⟨m1, m2, m3⟩ := tMult h1 h2 h3 E A n p S F x hx N w σ i hi _ s
  exact ⟨m1, a1, a2, tKill h1 h2 h3 E A n p S F x hx N w σ i hi _ s, tCard h1 h2 h3 E A n p S F x hx N w σ i hi _ s,
    by rw [F.mult]; exact m2, m3⟩

theorem tjIdx_of (h1 : Sides) (h2 : Dict) (h3 : LevBasic) : TjIdx := by
  rintro E _ _ _ A n p _ S F x hx N w σ i hi _ ⟨hw, t, z, ht, hz, rfl⟩ _
  have s := shpOf h1 E A n x hx σ.q σ.atp.prime σ.good.1 w (q_mem σ) hw i hi t z ht hz
  generalize loc hw t * z ^ i = g at s
  obtain ⟨l1, l2, l3⟩ := levLoc h1 h2 h3 E A n p S F x hx N w σ i hi g s
  rw [← locIdx E n w i hi _ s.at_w, Subgroup.inf_relIndex_left]
  have e1 : (σ.K₀.comap F.j).map F.j = σ.K₀ := Subgroup.map_comap_eq_self_of_surjective F.surj _
  have e2 : (σ.K₀.comap F.j).map (comp w) = KGL w n :=
    le_antisymm (by rintro _ ⟨k, hk, rfl⟩; exact l1 k hk) fun κ hκ => l2 κ hκ
  conv_lhs => rw [← e1]
  conv_rhs => rw [← e2]
  rw [← Subgroup.relIndex_comap, ← Subgroup.relIndex_comap, e1, e2, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (Subgroup.comap (comp w) _)]
  congr 1
  ext k
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, and_congr_left_iff]
  intro hk
  simpa only [map_mul, map_inv] using l3 k hk

theorem memEx_of (h1 : Sides) (h2 : Dict) (h3 : LevBasic) : MemEx := by
  intro E _ _ _ A n p _ S F d x hd hx2 hx N
  obtain ⟨-, b2, b3, -, b5, b6⟩ := h3 p S.D S.G S.L
  refine ⟨fun k hk => ⟨⟨S.L.KN N.1, k, N, le_rfl, KN_anti (one_dvd _), integ_of_mem hk, dvd_rfl, fun k' hk' u hu =>
    b5 _ _ (b3 N.1) _ (mul_mem hk (KN_anti (one_dvd _) hk')) u hu⟩, ⟨rfl, rfl, hk⟩, rfl⟩, fun w σ i hi => ?_⟩
  obtain ⟨s1, hw, s3, -⟩ := h1 E A x hx σ.q σ.atp.prime σ.good.1 w (q_mem σ)
  obtain ⟨z, hz⟩ := cenEx_holds E n d x hd hx2 w s1 fun q hq hqw u hu => s3 u (by
    rwa [(Nat.prime_dvd_prime_iff_eq hq σ.atp.prime).1 (dvd_of w hq hqw (q_mem σ))] at hu)
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : w.adicCompletion E, Formalism.UG.IsUnifV E w ϖ := w.valuedAdicCompletion_surjective E _
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, Formalism.UG.IsUnifV, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  let t : GLw n w := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) (by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun k _ => by split_ifs <;> simp [h0])
  have hH : IsH F x w i (F.j (loc hw t * z ^ i)) := ⟨hw, t, z, ⟨ϖ, hϖ, rfl⟩, hz, rfl⟩
  obtain ⟨t1, t2⟩ := tjOK_of h1 h2 h3 E A n p S F x hx N w σ i hi _ hH
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hc : 0 < Ideal.absNorm w.asIdeal ^ i := pow_pos (Nat.pos_of_ne_zero hN0) i
  have hp : (Ideal.absNorm w.asIdeal).Coprime p := by
    refine ((Fact.out : p.Prime).coprime_iff_not_dvd.2 fun h => σ.atp.ne ?_).symm
    have h4 : Ideal.absNorm w.asIdeal ∣ σ.q ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (q_mem σ))
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out σ.atp.prime).1 ((Fact.out : p.Prime).dvd_of_dvd_pow (h.trans h4))).symm
  have hK1 : σ.K₀ ≤ S.L.KN 1 := fun k hk => ((σ.isLev k).1 hk).1
  refine ⟨⟨σ.K₀, _, ⟨N.1 * Ideal.absNorm w.asIdeal ^ i, N.2.1.trans (Nat.le_mul_of_pos_right _ hc),
    N.2.2.mul_left (hp.pow_left i)⟩, b2 _ _ _ _ (b3 N.1) σ.isLev ((Ideal.span_singleton_le_iff_mem _).2 σ.mem), hK1, t1,
    Dvd.intro _ rfl, fun k hk u hu => ?_⟩, hi, rfl, hH, rfl⟩
  have := b6 N.1 _ _ t1 t2.back hc _ (b5 _ _ (b3 _) k (hK1 hk) u hu)
  simpa only [mul_assoc, _root_.mul_inv_rev] using this

end UpperTheory.Gal.Int.Geo.Pl
