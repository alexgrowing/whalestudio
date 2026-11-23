import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.HalfIncl

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem mem_of_loc {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

theorem loc_self (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

variable [Module E W] [IsScalarTower (𝓞 E) E W]

theorem loc_smul {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k k' : E}
    (hx : k' • x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E) * k') :
    k • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨t, ht, hx⟩ := hx
  refine ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
  have : (t * s) • k • x = r • t • k' • x := by
    simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul]
    congr 1
    have h' : algebraMap (𝓞 E) E s * k = algebraMap (𝓞 E) E r * k' := h
    linear_combination (algebraMap (𝓞 E) E t) * h'
  rw [this]
  exact M.smul_mem _ hx

theorem loc_smul' {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k : E}
    (hx : x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E)) :
    k • x ∈ localization₂ Q.asIdeal M :=
  loc_smul (k' := 1) (by rwa [one_smul]) r s hs (by rwa [mul_one])

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem mem_mulLat (M : Submodule (𝓞 E) W) {c : ℕ} (hc : c ≠ 0) (y : W) :
    y ∈ mulLat c M ↔ (c : E)⁻¹ • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  have e : ∀ m : W, (c : 𝓞 E) • m = (c : E) • m := fun m => by
    rw [← algebraMap_smul E, map_natCast]
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [e, smul_smul, hcE] using hm
  · intro h
    exact ⟨_, h, by simp [e, smul_smul, hcE]⟩

theorem nat_notMem {Q : HeightOneSpectrum (𝓞 E)} {n p : ℕ} (h : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ Q.asIdeal) :
    (n : 𝓞 E) ∉ Q.asIdeal := fun hn => by
  obtain ⟨u, v, huv⟩ : IsCoprime (n : 𝓞 E) (p : 𝓞 E) := h.cast
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left _ hn) (Q.asIdeal.mul_mem_left _ hp)))

theorem exists_prime_over {p : ℕ} (hp : p.Prime) : ∃ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 E) := fun h => by
    have : IsUnit (p : ℤ) := isUnit_of_map_unit (algebraMap ℤ (𝓞 E)) _ (by simpa using h)
    exact hp.one_lt.ne' (by simpa [Int.isUnit_iff_natAbs_eq] using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 E)}) (by simpa [Ideal.span_singleton_eq_top] using hu)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩,
    hle (Ideal.mem_span_singleton_self _)⟩

theorem expS_conj [StarRing E] {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S)
    (Q : HeightOneSpectrum (𝓞 E)) : expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.CharValCompare.conjP_conjP]
  by_cases h1 : Q ∈ S
  · simp [h1, hS Q h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

theorem expS_cases [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    (Q ∈ S ∧ expS S Q = 1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∈ S ∧ expS S Q = -1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∉ S ∧ expS S Q = 0) := by
  unfold expS
  by_cases h1 : Q ∈ S
  · simp [h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

end Loc

theorem half_inclusions : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  intro X A a b S SG ϖ p g cA N N' hC hN hN'
  obtain ⟨hX, ⟨hδ, -, hSc, hAS, hfg, hLa⟩, hAc, -, hp, hϖ, hcop, hS, hSG, hg, hcA⟩ := hC
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hg)
  have hcA0 : cA ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hcA)
  have hpE : (p : X.E) ≠ 0 := by exact_mod_cast hp0
  have hgE : (g : X.E) ≠ 0 := by exact_mod_cast hg0
  have hcE : (cA : X.E) ≠ 0 := by exact_mod_cast hcA0
  have hpO : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp0
  have hϖO : ϖ ≠ 0 := left_ne_zero_of_mul (hϖ ▸ hpO)
  obtain ⟨w, hw⟩ : ∃ w, w = X.conjO ϖ := ⟨_, rfl⟩
  have hstar : star (ϖ : X.E) = (w : X.E) := by rw [hw]; rfl
  have hconj : ∀ Q : HeightOneSpectrum (𝓞 X.E), w ∈ Q.asIdeal → conjPrime₂ Q ∈ S := fun Q h =>
    (hS _).2 (Or.inl (by rw [hw] at h; exact h))
  rw [← hw] at hϖ hcop hAc
  have hwO : w ≠ 0 := right_ne_zero_of_mul (hϖ ▸ hpO)
  have hpE' : (p : X.E) = (ϖ : X.E) * (w : X.E) := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) hϖ
    rw [map_mul, map_natCast] at this
    exact this.symm
  have hϖE : (ϖ : X.E) ≠ 0 := left_ne_zero_of_mul (hpE' ▸ hpE)
  have hwE : (w : X.E) ≠ 0 := right_ne_zero_of_mul (hpE' ▸ hpE)
  have hSw : ∀ Q ∈ S, w ∉ Q.asIdeal := fun Q hQ h => hSc Q hQ (hconj Q h)
  have hnS : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ S → ϖ ∉ Q.asIdeal := fun Q hQ h => hQ ((hS Q).2 (Or.inl h))
  have hpm : ∀ Q : HeightOneSpectrum (𝓞 X.E), ϖ ∈ Q.asIdeal → (p : 𝓞 X.E) ∈ Q.asIdeal := fun Q h =>
    hϖ ▸ Q.asIdeal.mul_mem_right _ h
  have hone : ∀ Q : HeightOneSpectrum (𝓞 X.E), (1 : 𝓞 X.E) ∉ Q.asIdeal := fun Q => Q.asIdeal.primeCompl.one_mem
  have hmul : ∀ (Q : HeightOneSpectrum (𝓞 X.E)) {s t : 𝓞 X.E}, s ∉ Q.asIdeal → t ∉ Q.asIdeal → s * t ∉ Q.asIdeal :=
    fun Q _ _ hs ht => Q.asIdeal.primeCompl.mul_mem hs ht
  have hAA : A.AA ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := exists_prime_over (E := X.E) hp
    have h1 : localization₂ Q.asIdeal A.AA = localization₂ Q.asIdeal 1 := by
      rcases Q.isPrime.mem_or_mem (hϖ ▸ hQ) with h | h
      · exact hAS Q ((hS Q).2 (Or.inl h))
      · exact hAc Q ((mem_divs hwO Q).2 h)
    intro h0
    have h2 : (1 : X.E) ∈ localization₂ Q.asIdeal A.AA := h1 ▸ loc_self Q (Submodule.mem_one.2 ⟨1, map_one _⟩)
    obtain ⟨s, hs, h3⟩ := h2
    rw [h0, Submodule.mem_bot, Algebra.smul_def, mul_one, RingOfIntegers.coe_eq_zero_iff] at h3
    exact hs (h3 ▸ Q.asIdeal.zero_mem)
  have hloc := fun P hP => (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hfg hAA hN hN').2.2.2 P (hAS P hP)
  have hhom : ∀ T : Finset (HeightOneSpectrum (𝓞 X.E)), (∀ P ∈ T, P ∈ S) → ∀ y : HomE X.E a b,
      y ∈ homAt T N N' ↔ ∀ P ∈ T, y ∈ localization₂ P.asIdeal (per A N N') := fun T hT y =>
    forall₂_congr fun P hP => (hloc P (hT P hP) y).symm
  have hhS := hhom S fun _ h => h
  have hhG := hhom SG fun P h => (hS P).2 (Or.inr h)
  have hhD := hhom (divs ϖ) fun P h => (hS P).2 (Or.inl ((mem_divs hϖO P).1 h))
  have hcoc := (GlobalTheory.MomT.CocInt.cocycle_integral X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  have hpg : p * g ≠ 0 := mul_ne_zero hp0 hg0
  simp only [hstar]
  refine ⟨hAA, fun y hy => ?_, fun y hy => ?_, fun x _ hx t ht htx => ?_, fun y hy => ⟨?_, ?_, ?_, ?_⟩,
    fun y n hn hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e]
    · refine loc_smul' (loc_self Q hy) 1 (w * w) (hmul Q (hSw Q h1) (hSw Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * g * ϖ * ϖ) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * ϖ) w (fun h => h2 (hconj Q h)) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 hy Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e] at h
    · refine loc_smul h (g * g * w * w) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h 1 (ϖ * ϖ) (hmul Q (hnS Q h1) (hnS Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h (g * w) ϖ (hnS Q h1) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 ht Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg] at h
    · by_cases hQ : ϖ ∈ Q.asIdeal
      · have h3 := (hhD x).1 hx Q ((mem_divs hϖO Q).2 hQ)
        have h4 := (hhS _).1 ((mem_mulLat _ hpg _).1 htx) Q h1
        have h5 : (1 : X.E) • (t - x) ∈ localization₂ Q.asIdeal (per A N N') := by
          refine loc_smul h4 (p * g) 1 (hone Q) ?_
          push_cast; field_simp
        rw [one_smul] at h5
        have h6 := add_mem h3 h5
        rw [add_sub_cancel] at h6
        refine loc_smul' h6 (cA * g) 1 (hone Q) ?_
        push_cast; field_simp
      · refine loc_smul h 1 p (hSG Q (((hS Q).1 h1).resolve_left hQ)) ?_
        push_cast; field_simp
    · refine loc_smul h (cA * g * (cA * (p * g))) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul h (cA * g) 1 (hone Q) ?_
      push_cast; field_simp
  · exact (hhS y).2 fun P _ => loc_self P hy
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg]
    · refine loc_smul' (loc_self Q hy) (cA * (p * g) * (cA * g * w)) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul' (loc_self Q hy) 1 ϖ (hnS Q h1) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (cA * g * w) 1 (hone Q) ?_
      push_cast; field_simp
  · refine (mem_mulLat _ hpg _).2 ((hhG _).2 fun P hP => ?_)
    rw [smul_smul]
    refine loc_smul' (loc_self P hy) cA ϖ (fun h => hSG P hP (hpm P h)) ?_
    push_cast; simp only [hpE']; field_simp
  · rw [mem_mulLat _ hpg, hhS, smul_smul, mem_smulLat]
    constructor
    · intro h
      refine ⟨(ϖ : X.E)⁻¹ • y, mem_of_loc fun Q => ?_, by rw [smul_smul, mul_inv_cancel₀ hϖE, one_smul]⟩
      by_cases hQ : ϖ ∈ Q.asIdeal
      · refine loc_smul (h Q ((hS Q).2 (Or.inl hQ))) 1 cA (nat_notMem hcA (hpm Q hQ)) ?_
        push_cast; simp only [hpE']; field_simp
      · refine loc_smul' (loc_self Q hy) 1 ϖ hQ ?_
        push_cast; field_simp
    · rintro ⟨m, hm, rfl⟩ P _
      rw [smul_smul]
      refine loc_smul' (loc_self P hm) cA 1 (hone P) ?_
      push_cast; simp only [hpE']; field_simp
  · obtain ⟨m, hm, e⟩ := hy
    have hn0 : (n : X.E) ≠ 0 := by
      have : n ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hn)
      exact_mod_cast this
    have e' : y = ((n : X.E)⁻¹ * ((ϖ : X.E) / (w : X.E))) • m := by
      have e2 : ((ϖ : X.E) / (w : X.E)) • m = (n : X.E) • y := e
      rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    refine (mem_mulLat _ hp0 _).2 ((hhD _).2 fun P hP => ?_)
    have hP' := (mem_divs hϖO P).1 hP
    have hw' := hSw P ((hS P).2 (Or.inl hP'))
    rw [e', smul_smul]
    refine loc_smul' (loc_self P hm) 1 (n * (w * w)) (hmul P (nat_notMem hn (hpm P hP')) (hmul P hw' hw')) ?_
    push_cast; simp only [hpE']; field_simp
  · refine hcoc x y fun Q => ⟨((p * g : ℕ) : X.E) ^ expS S Q, zpow_ne_zero _ (by exact_mod_cast hpg),
      (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h
  · refine hcoc x y fun Q => ⟨((cA * (p * g) : ℕ) : X.E) ^ (-expS S Q),
      zpow_ne_zero _ (by exact_mod_cast mul_ne_zero hcA0 hpg), (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h

end GlobalTheory.MomT.HalfIncl
