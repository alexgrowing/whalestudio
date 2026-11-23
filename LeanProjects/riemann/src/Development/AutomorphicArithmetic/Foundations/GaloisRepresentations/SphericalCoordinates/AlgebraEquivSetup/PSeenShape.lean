import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem seenShape_not_both {E : Type} [Field E] [NumberField E] {u : Plc E} {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hne : a ≠ b) (h1 : (a : 𝓞 E) ∈ u.asIdeal) (h2 : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨c, d, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hb).2 hne)
  have e' := congrArg (Int.cast : ℤ → 𝓞 E) e
  push_cast at e'
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private theorem seenShape_nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {u : Plc E} {m : ℕ}
    (h : (m : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
  rw [e, Ideal.mem_comap, map_natCast]
  exact h

theorem UpperTheory.Gal.W2.Seed.pSeenShape :
    StabKer → SiteFact → CenFacts → LevBasic → UpperTheory.Gal.CertificateRingHomMap.LocComm → SeenShape := by
  intro hSK hSF hCF hLB hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty g θ hs
  have key : ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK :=
    hSK E A n p S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty
  rcases hs with ⟨hd, hst, hr, hθ⟩ | ⟨w, σ, i, B, hfree, hqr, hK, ⟨hi, hgK, ⟨hws, t, z, ht, hz, hh⟩, -⟩, hB, hθ⟩
  · refine ⟨?_, Or.inl ⟨hd, key _ hst hr, hθ⟩⟩
    rw [hd.1]
    exact fun k hk => key k (hstab k hk) (KN_anti hrN hk)
  · have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
    have hpp : p.Prime := Fact.out
    have hpw : (p : 𝓞 E) ∉ w.asIdeal := fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne hqw h
    let w' : Spl E p := ⟨w, hws, hpw⟩
    have hrU : ∀ u ∈ W, (r : 𝓞 E) ∈ u.1.asIdeal := haux.half.above
    have hqU : ∀ u ∈ W, ((σ.q : ℕ) : 𝓞 E) ∉ u.1.asIdeal := fun u hu h =>
      seenShape_not_both σ.atp.prime haux.prime hqr h (hrU u hu)
    have hcen := hCF E A n hodd.pos x hgen σ.q σ.atp.prime σ.good.1 w hqw z hz
    have hap1 : ∀ u ∈ W, GlobalTheory.Cong.Apart w u.1 := fun u hu => ((hc E n u.1 u.2.1).2.1 w).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => seenShape_not_both (u := w) σ.atp.prime haux.prime hqr hqw
        (e ▸ seenShape_nat_mem_cj (hrU u hu))⟩
    have hap2 : ∀ u ∈ W, GlobalTheory.Cong.Apart u.1 w := fun u hu => ((hc E n w hws).2.1 u.1).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => hqU u hu (e ▸ seenShape_nat_mem_cj hqw)⟩
    have hσK : σ.K₀ ≤ S.L.KN r := by
      obtain ⟨-, h2, h3, -⟩ := hLB p S.D S.G S.L
      refine h2 _ _ _ _ σ.isLev (h3 r) (Ideal.mul_le_left.trans (Ideal.span_singleton_le_span_singleton.2 ?_))
      have hd : r ∣ ordCompl[σ.q] N.1 := Nat.dvd_ordCompl_of_dvd_not_dvd hrN fun h =>
        hqr ((Nat.prime_dvd_prime_iff_eq σ.atp.prime haux.prime).1 h)
      exact Nat.cast_dvd_cast hd
    have hzi : ∀ a, (z ^ i)⁻¹ * a = a * (z ^ i)⁻¹ := fun a =>
      ((Commute.pow_left (show Commute z a from hcen.1 a) i).inv_left).eq
    have hw0 : comp w₀ z = 1 := (hz w₀).2 (hfree.2.2.2.1 w₀ V.shape.mem)
    refine ⟨?_, Or.inr ⟨w', t, z, i, B, hfree, hap1, hi, ht, hz, hB, ?_, ?_, ?_, ?_, ?_, hθ⟩⟩
    · rw [hgK]
      exact fun k hk => key k (hK k hk) (hσK hk)
    · exact fun u hu => hcen.2 u fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne h hu
    · have e : (UpperTheory.Gal.CertificateRingHomMap.loc hws t * z ^ i)⁻¹ = UpperTheory.Gal.CertificateRingHomMap.loc hws t⁻¹ * (z ^ i)⁻¹ := by
        rw [_root_.mul_inv_rev, map_inv]
        exact hzi _
      rw [hh, (hty.fac w').2 t⁻¹, ← map_inv F.j, e, map_mul]
    · refine ⟨fun a => ?_, ?_⟩
      · obtain ⟨a', rfl⟩ := F.surj a
        rw [← map_mul, ← map_mul, hzi]
      · rw [hty.L_eq]
        refine ((hty.fac ⟨w₀, hw⟩).1 (z ^ i)⁻¹).trans ?_
        show comp w₀ (z ^ i)⁻¹ = 1
        rw [map_inv, map_pow, hw0, one_pow, inv_one]
    · intro u hu
      rw [hh, (hty.fac u).1, map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hws (hap2 u hu),
        hcen.2 _ (hqU u hu), one_pow, one_mul]
    · rw [hgK]
      exact hSF E A n p S F x hgen N w' σ (L w') (hty.fac w')
