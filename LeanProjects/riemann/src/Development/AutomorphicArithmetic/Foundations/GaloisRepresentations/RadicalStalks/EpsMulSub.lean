import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem eps_mul_sub {p : ℕ} (hp : p.Prime) {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f)
    (ω : C) (tr nm z : ℤ) (hq : ω * ω - (tr : C) * ω + (nm : C) = 0) (hz : (p : ℤ) ∣ z ^ 2 - tr * z + nm)
    (hd : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm) (hw : ω - (z : C) ∈ w) : (p : C) ∣ π.ε * (ω - (z : C)) := by
  set I : Ideal C := Ideal.span {(p : C)} with hI
  have key : ∀ t : C, (p : C) ∣ t ↔ Ideal.Quotient.mk I t = 0 := fun t => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have cast_dvd : ∀ t : ℤ, (p : ℤ) ∣ t → Ideal.Quotient.mk I (t : C) = 0 := by
    intro t ht
    apply (key _).mp
    obtain ⟨r, hr⟩ := ht
    exact ⟨(r : C), by rw [hr]; push_cast; ring⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (p : ℤ) ∣ 2 * z - tr := by
    intro h
    apply hd
    have e1 : tr ^ 2 - 4 * nm = (2 * z - tr) ^ 2 - 4 * (z ^ 2 - tr * z + nm) := by ring
    rw [e1]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right hz 4)
  obtain ⟨u0, v0, huv⟩ := (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hnd
  set mk := Ideal.Quotient.mk I
  set X := mk (ω - (z : C)) with hX
  set E := mk π.ε with hEdef
  set A := mk π.a with hAdef
  set Y := mk (((2 * z - tr : ℤ)) : C) with hY
  set S := mk (v0 : C) with hS
  have hp0 : mk (p : C) = 0 := (key _).mp dvd_rfl
  have hSY : S * Y = 1 := by
    have h := congrArg (fun t : ℤ => mk (t : C)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, map_add, map_mul, map_one,
      hp0, mul_zero, zero_add] at h
    rw [hS, hY, ← map_mul]
    simpa [map_mul] using h
  have hE : E * E = E := by
    have h := (key _).mp π.idem
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  obtain ⟨e, he⟩ := π.nil
  have hAE : A ^ e * E = 0 := by
    have h := (key _).mp he
    rwa [map_mul, map_pow] at h
  obtain ⟨u, hu⟩ := π.gen _ hw
  have hEX : E * X = A * mk u := by
    have h := (key _).mp hu
    rwa [map_sub, map_mul, map_mul, sub_eq_zero] at h
  have hXY : X * (X + Y) = 0 := by
    have e2 : (ω - (z : C)) * (ω - (z : C) + ((2 * z - tr : ℤ) : C)) =
        (ω * ω - (tr : C) * ω + (nm : C)) - ((z ^ 2 - tr * z + nm : ℤ) : C) := by
      push_cast
      ring
    have h := congrArg mk e2
    rw [map_mul, map_add, hq, zero_sub, map_neg, cast_dvd _ hz, neg_zero] at h
    exact h
  have h1 : X = -S * X ^ 2 := by
    calc X = X * (S * Y) := by rw [hSY, _root_.mul_one]
      _ = S * (X * (X + Y)) - S * X ^ 2 := by ring
      _ = -S * X ^ 2 := by rw [hXY]; ring
  have hpow : ∀ n : ℕ, X = (-S) ^ n * X ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc X = (-S) ^ n * X ^ (n + 1) := ih
        _ = (-S) ^ n * X ^ n * X := by ring
        _ = (-S) ^ n * X ^ n * (-S * X ^ 2) := by rw [← h1]
        _ = (-S) ^ (n + 1) * X ^ (n + 1 + 1) := by ring
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hE]
  have hEXe : E * X ^ e = 0 := by
    calc E * X ^ e = E ^ (e + 1) * X ^ e := by rw [hEpow]
      _ = E * (E * X) ^ e := by ring
      _ = (A ^ e * E) * mk u ^ e := by rw [hEX]; ring
      _ = 0 := by rw [hAE, zero_mul]
  apply (key _).mpr
  rw [map_mul]
  calc E * X = E * ((-S) ^ e * X ^ (e + 1)) := by rw [← hpow]
    _ = (-S) ^ e * X * (E * X ^ e) := by ring
    _ = 0 := by rw [hEXe, mul_zero]

theorem UpperTheory.Gal.Ord.lie :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      (∀ (c : 𝓞 D.F) (h : HdR o.A), hom o c (hom o π.ε h) - β (b.t i c) • hom o π.ε h ∈ Fil o.A) ∧
      (∃ h₀ : HdR o.A, hom o π.ε h₀ ∉ Fil o.A ∧ ∀ h : HdR o.A, ∃ l : k, hom o π.ε h - l • hom o π.ε h₀ ∈ Fil o.A) ∧
      ∀ h : HdR o.A, hom o D.ω (hom o π.ε h) = β b.ρ • hom o π.ε h := by
  intro p _ D R _ b N _ _ hm k _ _ hk β o i w f hw _ _ π
  have hpp : p.Prime := Fact.out
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hpp).mpr hk
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o.A o.ab
  have HL : LieExact o.A := (GlobalTheory.abelianDeRham.2.1 k o.A g o.ab hg).1
  set τ : 𝓞 D.F →+* k := β.comp (b.t i) with hτ
  have hhom_mul : ∀ (c d : 𝓞 D.F) (h : HdR o.A), hom o (c * d) h = hom o c (hom o d h) := by
    intro c d h
    simp [UpperTheory.Gal.Ord.hom, map_mul, Module.End.mul_apply]
  have hhom_add : ∀ (c d : 𝓞 D.F) (h : HdR o.A), hom o (c + d) h = hom o c h + hom o d h := by
    intro c d h
    simp [UpperTheory.Gal.Ord.hom, map_add, LinearMap.add_apply]
  have hhom_int : ∀ (n : ℤ) (h : HdR o.A), hom o (n : 𝓞 D.F) h = (n : k) • h := by
    intro n h
    exact GlobalTheory.HTCount.crysAct_intCast o n h
  have hLc : ∀ (c : 𝓞 D.F) (h : HdR o.A), HL.toLie (OActN.toF D o.act) (hom o c h) =
      c • HL.toLie (OActN.toF D o.act) h := fun c h => GlobalTheory.HTLieRho.toLie_crys o HL c h
  have hρ : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have h0 := congrArg β b.ρ_root
    simpa using h0
  obtain ⟨r, hr⟩ := D.split
  have hrk : ((r ^ 2 - D.tr * r + D.nm : ℤ) : k) = 0 := by
    obtain ⟨s, hs⟩ := hr
    rw [hs]
    push_cast
    rw [hk, zero_mul]
  obtain ⟨z, hzk, hz⟩ : ∃ z : ℤ, (z : k) = β b.ρ ∧ (p : ℤ) ∣ z ^ 2 - D.tr * z + D.nm := by
    have hfac : (β b.ρ - (r : k)) * (β b.ρ - ((D.tr : k) - (r : k))) = 0 := by
      have e0 : (β b.ρ - (r : k)) * (β b.ρ - ((D.tr : k) - (r : k))) =
          (β b.ρ ^ 2 - (D.tr : k) * β b.ρ + D.nm) - ((r ^ 2 - D.tr * r + D.nm : ℤ) : k) := by
        push_cast
        ring
      rw [e0, hρ, hrk, sub_zero]
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact ⟨r, (sub_eq_zero.mp h0).symm, hr⟩
    · refine ⟨D.tr - r, ?_, ?_⟩
      · push_cast
        exact (sub_eq_zero.mp h0).symm
      · have e1 : (D.tr - r) ^ 2 - D.tr * (D.tr - r) + D.nm = r ^ 2 - D.tr * r + D.nm := by ring
        rw [e1]
        exact hr
  have hwz : D.ω - (z : 𝓞 D.F) ∈ w := by
    rw [← hw, RingHom.mem_ker, map_sub, map_intCast, RingHom.comp_apply, b.t_ω, hzk, sub_self]
  have hε := eps_mul_sub hpp π D.ω D.tr D.nm z (GlobalTheory.HTLieRho.omega_quad D) hz D.disc_p hwz
  have hp_zero : ∀ h, hom o (p : 𝓞 D.F) h = 0 := by
    intro h
    have h0 := hhom_int (p : ℤ) h
    rw [Int.cast_natCast, Int.cast_natCast, hk, zero_smul] at h0
    exact h0
  have hεω : ∀ h, hom o π.ε (hom o D.ω h) = (β b.ρ) • hom o π.ε h := by
    intro h
    obtain ⟨y, hy⟩ := hε
    have e3 : π.ε * D.ω = (p : 𝓞 D.F) * y + (z : 𝓞 D.F) * π.ε := by
      rw [← hy]
      ring
    rw [← hhom_mul, e3, hhom_add, hhom_mul, hp_zero, hhom_mul, hhom_int, hzk, zero_add]
  have hτε : τ π.ε = 1 := by
    have h0 : π.ε - 1 ∈ RingHom.ker τ := hw ▸ π.one
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hoff : ∀ j, j ≠ i → β (b.t j π.ε) = 0 := by
    intro j hj
    have hprime : (RingHom.ker (β.comp (b.t j))).IsPrime := RingHom.ker_isPrime _
    have hpmem : (p : 𝓞 D.F) ∈ RingHom.ker (β.comp (b.t j)) := by
      rw [RingHom.mem_ker, map_natCast, hk]
    have hne : RingHom.ker (β.comp (b.t j)) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.mem_bot] at hpmem
      exact (Nat.cast_ne_zero.mpr hpp.ne_zero) hpmem
    have hmax : (RingHom.ker (β.comp (b.t j))).IsMaximal := hprime.isMaximal hne
    have hne' : RingHom.ker (β.comp (b.t j)) ≠ w := by
      rw [← hw]
      exact (b.apart i j (Ne.symm hj) k β).symm
    have h1 := π.off _ hmax hpmem hne'
    rwa [RingHom.mem_ker, RingHom.comp_apply] at h1
  have hkey : ∀ h, HL.toLie (OActN.toF D o.act) (hom o π.ε h) ∈ GlobalTheory.Serre.Lie.eig (OActN.toF D o.act) τ := by
    intro h
    obtain ⟨u, hu, wv, hwv, hdec⟩ := GlobalTheory.HTLieRho.lie_decomp o β rfl HL (HL.toLie (OActN.toF D o.act) h)
    obtain ⟨hu', rfl⟩ := HL.toLie_surjective (OActN.toF D o.act) u
    choose hs hhs using fun j => HL.toLie_surjective (OActN.toF D o.act) (wv j)
    have hu0 : HL.toLie (OActN.toF D o.act) (hom o π.ε hu') = 0 := by
      have e4 : HL.toLie (OActN.toF D o.act) (hom o π.ε (hom o D.ω hu')) =
          (β b.ρ) • HL.toLie (OActN.toF D o.act) (hom o π.ε hu') := by
        rw [hεω, map_smul]
      have e5 : HL.toLie (OActN.toF D o.act) (hom o π.ε (hom o D.ω hu')) =
          ((D.tr : k) - β b.ρ) • HL.toLie (OActN.toF D o.act) (hom o π.ε hu') := by
        calc HL.toLie (OActN.toF D o.act) (hom o π.ε (hom o D.ω hu'))
            = π.ε • (D.ω • HL.toLie (OActN.toF D o.act) hu') := by rw [hLc, hLc]
          _ = π.ε • (((D.tr : k) - β b.ρ) • HL.toLie (OActN.toF D o.act) hu') := by rw [hu]
          _ = π.ε • HL.toLie (OActN.toF D o.act) (((D.tr : k) - β b.ρ) • hu') := by rw [map_smul]
          _ = HL.toLie (OActN.toF D o.act) (hom o π.ε (((D.tr : k) - β b.ρ) • hu')) := by rw [hLc]
          _ = ((D.tr : k) - β b.ρ) • HL.toLie (OActN.toF D o.act) (hom o π.ε hu') := by
            rw [map_smul, map_smul]
      have e6 : (β b.ρ - ((D.tr : k) - β b.ρ)) • HL.toLie (OActN.toF D o.act) (hom o π.ε hu') = 0 := by
        rw [sub_smul, ← e4, ← e5, sub_self]
      exact (smul_eq_zero.mp e6).resolve_left (GlobalTheory.HTLieRho.two_rho_sub_ne_zero b β)
    have hsum : HL.toLie (OActN.toF D o.act) h = HL.toLie (OActN.toF D o.act) (hu' + ∑ j, hs j) := by
      rw [hdec, map_add, map_sum]
      simp only [hhs]
    have hLε : HL.toLie (OActN.toF D o.act) (hom o π.ε h) = wv i := by
      rw [hLc, hsum, ← hLc, map_add, map_sum, map_add, map_sum, hu0, zero_add]
      have e9 : ∀ j, HL.toLie (OActN.toF D o.act) (hom o π.ε (hs j)) = β (b.t j π.ε) • wv j := by
        intro j
        rw [hLc, hhs j]
        exact GlobalTheory.Serre.Lie.mem_eig_iff.mp (hwv j) π.ε
      simp only [e9]
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hoff j hj, zero_smul]) (by simp)]
      have e10 : β (b.t i π.ε) = 1 := hτε
      rw [e10, one_smul]
    rw [hLε]
    exact hwv i
  refine ⟨?_, ?_, ?_⟩
  · intro c h
    rw [← HL.ker_toLie (OActN.toF D o.act), LinearMap.mem_ker, map_sub, map_smul, hLc,
      GlobalTheory.Serre.Lie.mem_eig_iff.mp (hkey h) c]
    exact sub_eq_zero.mpr rfl
  · have hr1 := GlobalTheory.UPel.HT.Obj.lieRank o k (𝟙 _) β (by simp) i
    rw [hm] at hr1
    obtain ⟨bs⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff _ _ _).mp hr1
    obtain ⟨h₀, hh₀⟩ := HL.toLie_surjective (OActN.toF D o.act) (bs 0)
    have hLε0 : HL.toLie (OActN.toF D o.act) (hom o π.ε h₀) = bs 0 := by
      rw [hLc, hh₀, GlobalTheory.Serre.Lie.mem_eig_iff.mp (bs 0).2 π.ε]
      have e10 : (β.comp (b.t i)) π.ε = 1 := hτε
      rw [e10, one_smul]
    refine ⟨h₀, ?_, ?_⟩
    · rw [← HL.ker_toLie (OActN.toF D o.act), LinearMap.mem_ker, hLε0]
      intro h0
      apply bs.ne_zero 0
      exact Subtype.ext h0
    · intro h
      have hv := hkey h
      have e7 := bs.sum_repr ⟨_, hv⟩
      rw [Fin.sum_univ_one] at e7
      have e8 : bs.repr ⟨_, hv⟩ 0 • (bs 0 : GlobalTheory.Serre.Lie (OActN.toF D o.act)) =
          HL.toLie (OActN.toF D o.act) (hom o π.ε h) := by
        simpa using congrArg Subtype.val e7
      refine ⟨bs.repr ⟨_, hv⟩ 0, ?_⟩
      rw [← HL.ker_toLie (OActN.toF D o.act), LinearMap.mem_ker, map_sub, map_smul, hLε0, e8, sub_self]
  · intro h
    rw [← hhom_mul, mul_comm, hhom_mul, hεω]
