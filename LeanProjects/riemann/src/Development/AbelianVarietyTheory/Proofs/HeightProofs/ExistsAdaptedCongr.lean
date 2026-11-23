import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Matrix

namespace GlobalTheory.AdaptCongr

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.Move

theorem trivAt_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {Λ : GenLat E n} {a b : ℕ}
    (ha : Λ.TrivAt a) (hb : Λ.TrivAt b) : Λ.TrivAt (a * b) := by
  obtain ⟨k, hk, h1, h2⟩ := ha
  obtain ⟨m, hm, h3, h4⟩ := hb
  have hg : Ideal.span {((Nat.gcd k m : ℕ) : 𝓞 E)} ≤ Ideal.span {(k : 𝓞 E)} ⊔ Ideal.span {(m : 𝓞 E)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : ((Nat.gcd k m : ℕ) : 𝓞 E) = (k : 𝓞 E) * (Nat.gcdA k m : ℤ) + (m : 𝓞 E) * (Nat.gcdB k m : ℤ) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) (Nat.gcd_eq_gcd_ab k m)
      push_cast at this
      exact this
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨Nat.gcd k m, (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _)).mul_right
    (hm.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h1 h3
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h2 h4

theorem exists_move_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), IsUnE (IsCMField.complexConj E) 1 γ.1 ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ ∃ s : 𝓞 E, s ≠ 0 ∧ Ideal.span {s} • Λ'.La ≤ stdLat E n ∧ Ideal.span {s} • stdLat E n ≤ Λ'.La ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P ∧ ((bad * M : ℕ) : 𝓞 E) ∉ P) ∧ ∃ k : ℕ, k.Coprime (bad * M) ∧ Ideal.span {(k : 𝓞 E)} • Λ'.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ'.La := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  refine ⟨γ, Λ', hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU, s, hs0, (span_smul_le _ _ _).2 h1,
    (span_smul_le _ _ _).2 h2, fun P hP hsP => ⟨(hmov P hP).1 (hs P hP hsP).1, (hs P hP hsP).2⟩, k, hk,
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)

theorem not_mem_of_coprime {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : a.Coprime b)
    (hb : (b : R) ∈ I) : (a : R) ∉ I := fun ha => by
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := R) h)
  exact hI ((Ideal.eq_top_iff_one _).2 (huv ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

theorem exists_adapted_congr : ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (Λ : GenLat D.host.E n) (e : ℕ), 0 < badN D → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), (∀ p ∈ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j n).pd} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) → ∃ Λ' : GenLat D.host.E n, (∃ ga : (Fin n → D.host.E) ≃ₗ[D.host.E] (Fin n → D.host.E), (∀ v w : Fin n → D.host.E, ∑ i, IsCMField.complexConj D.host.E (ga v i) * ga w i = ∑ i, IsCMField.complexConj D.host.E (v i) * w i) ∧ Λ'.La = Λ.La.map ((ga : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E)).restrictScalars (𝓞 D.host.E)) ∧ ∃ t : ℕ, Nat.Coprime t ((badN D * (T.dδ j n).l₂.M) ^ (e + 1)) ∧ ∀ v ∈ stdLat D.host.E n, ∃ u ∈ stdLat D.host.E n, t • (ga v - v) = ((badN D * (T.dδ j n).l₂.M) ^ (e + 1)) • u) ∧ Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j n).l₂.M ∧ Λ'.TrivAt (Ideal.absNorm la.asIdeal) ∧ (∃ k : ℕ, (k : 𝓞 T.Q.c.F) ∉ la.asIdeal ∧ Ideal.span {(k : 𝓞 D.host.E)} • Λ'.La ≤ stdLat D.host.E n ∧ Ideal.span {(k : 𝓞 D.host.E)} • stdLat D.host.E n ≤ Λ'.La) ∧ (∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Λ'.La ≤ stdLat D.host.E n ∧ Ideal.span {m} • stdLat D.host.E n ≤ Λ'.La ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((badN D * (T.dδ j n).l₂.M * Ideal.absNorm la.asIdeal : ℕ) : 𝓞 D.host.E) ∉ P) ∧ GenLat.SplitSupp T.Q.H Λ' ∧ ∃ N' : ℕ, Λ'.LevOK N' (T.dδ j n).l₂.M ∧ ((N' : 𝓞 T.Q.c.F) ∉ la.asIdeal) := by
  intro D T hF j hj n Λ e hb hU hTb hTM la hla
  have hMpos : 0 < (T.dδ j n).l₂.M := by have := (T.dδ j n).l₂.three_le; omega
  have hl : 0 < Ideal.absNorm la.asIdeal :=
    Nat.pos_of_ne_zero fun h0 => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hT : Λ.TrivAt ((badN D * (T.dδ j n).l₂.M) ^ (e + 1)) := by
    obtain ⟨k, hk, h1, h2⟩ := trivAt_mul hTb hTM
    exact ⟨k, hk.pow_right _, h1, h2⟩
  obtain ⟨γ, Λ', hγ, ⟨t, ht, hc⟩, hmove, hU', s, hs0, hs1, hs2, hs, k, hk, hk1, hk2⟩ :=
    exists_move_split D.host.E T.Q.H n _ (Ideal.absNorm la.asIdeal) Λ (pow_pos (Nat.mul_pos hb hMpos) _) hl hU hT
  have hkl : k.Coprime (Ideal.absNorm la.asIdeal) := hk.coprime_mul_right_right
  have hkbM : k.Coprime (badN D * (T.dδ j n).l₂.M) :=
    hk.coprime_mul_left_right.coprime_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero e))
  have hkla : (k : 𝓞 T.Q.c.F) ∉ la.asIdeal := not_mem_of_coprime la.isPrime.ne_top hkl (Ideal.absNorm_mem _)
  have h2b : 2 ∣ badN D := by
    unfold badN
    have hQ : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    exact ((hQ.mul_right _).mul_right _).mul_right _
  let ga : (Fin n → D.host.E) ≃ₗ[D.host.E] (Fin n → D.host.E) := Matrix.toLinearEquiv' γ.1 γ.invertible
  have hga : ∀ v, ga v = γ.1 *ᵥ v := fun v => rfl
  have hM : (T.dδ j n).l₂.M = T.Q.l.M * (T.dδ j n).pd := (hF.sh.dLev j hj n).2.1
  have hlM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hF.p.toLawsCore.pins.2.1.1
  refine ⟨Λ', ⟨ga, fun v w => ?_, ?_, t, ht, fun v hv => ?_⟩, hU', ⟨k, hkbM.coprime_mul_right_right, hk1, hk2⟩,
    ⟨k, hkbM.coprime_mul_left_right, hk1, hk2⟩, ⟨k, hkl, hk1, hk2⟩, ⟨k, hkla, hk1, hk2⟩,
    ⟨s, hs0, hs1, hs2, fun P hP hsP => ⟨(hs P hP hsP).1, fun h => (hs P hP hsP).2 ?_⟩⟩,
    ⟨s, hs0, hs1, hs2, fun P hP hsP => (hs P hP hsP).1⟩, (T.dδ j n).l₂.M * k, ⟨?_, dvd_mul_right _ _, ?_⟩, ?_⟩
  · rw [hga, hga, ← hermE_one, hγ, hermE_one]
  · ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := ga.surjective v
      exact ⟨u, (hmove u).2 hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hmove u).1 hu
  · exact hc v hv
  · refine Ideal.mem_of_dvd _ (Nat.cast_dvd_cast ?_) h
    rw [mul_comm]
    exact Nat.mul_dvd_mul_left _ (dvd_pow_self _ (Nat.succ_ne_zero e))
  · exact (T.dδ j n).l₂.odd.mul
      (Nat.coprime_two_right.1 (hkbM.coprime_mul_right_right.coprime_dvd_right h2b))
  · show _ ≤ Λ'.La ⊓ stdLat D.host.E n
    refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
    refine Ideal.span_singleton_le_span_singleton.2 ?_
    rw [Nat.cast_mul]
    exact dvd_mul_left _ _
  · intro h
    rw [hM, hlM, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h
    rcases la.isPrime.mem_or_mem h with h | h
    · rcases la.isPrime.mem_or_mem h with h | h
      · rcases la.isPrime.mem_or_mem h with h | h
        · exact hla _ (by simp) h
        · exact hla _ (by simp) h
      · exact hla _ (by simp) h
    · exact hkla h

end GlobalTheory.AdaptCongr
