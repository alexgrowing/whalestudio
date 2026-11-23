import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ThShape

section Reps

variable {H V : Type} [AddCommGroup H] [AddCommGroup V]

theorem relIndex_dvd_of_le (B K L : AddSubgroup H) (h : K ≤ L) : B.relIndex K ∣ B.relIndex L := by
  rw [← AddSubgroup.relIndex_sup_left K B, ← AddSubgroup.relIndex_sup_left L B]
  exact Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex B (B ⊔ K) (B ⊔ L) le_sup_left (sup_le_sup_left h B))

theorem sum_reps_eq {M : Type} [AddCommMonoid M] {Λ B : AddSubgroup H} {R R' : Finset H} (F : H → M)
    (hR : IsReps Λ B R) (hR' : IsReps Λ B R') (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ y ∈ R', F y := by
  have h0 : IsReps Λ (⊥ : AddSubgroup H) ({0} : Finset H) := by
    refine ⟨by simp, by simp, ?_⟩
    intro y hy
    rw [AddSubgroup.mem_bot] at hy
    exact ⟨0, by simp, by simp [hy]⟩
  have := (GlobalTheory.RepsMod.reps_facts H).2.2.1 M Λ B B ⊥ R R' {0} F le_rfl bot_le
    (fun y hy => ⟨y, hy, 0, by simp, by simp⟩)
    (fun y₁ _ y₂ h₂ h => by rw [AddSubgroup.mem_bot] at h₂; simpa [h₂] using h) hR hR' h0 hF
  simpa using this

theorem reps_map (f : H →+ V) (hf : Function.Injective f) {Λ B : AddSubgroup H} {R : Finset H} (hR : IsReps Λ B R) :
    IsReps (Λ.map f) (B.map f) (R.map ⟨f, hf⟩) := by
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    exact ⟨y, h1 y hy, rfl⟩
  · intro x hx x' hx' h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hx'
    obtain ⟨l, hl, e⟩ := h
    have : l = y - y' := hf (by rw [map_sub]; exact e)
    rw [h2 y hy y' hy' (this ▸ hl)]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, h⟩ := h3 y hy
    exact ⟨f x, Finset.mem_map.2 ⟨x, hx, rfl⟩, y - x, h, map_sub f y x⟩

theorem reps_shift {Λ B : AddSubgroup H} {R : Finset H} (hR : IsReps Λ B R) {b : H} (hb : b ∈ B) :
    IsReps Λ B (R.map (addLeftEmbedding b)) := by
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    exact add_mem hb (h1 y hy)
  · intro x hx x' hx' h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hx'
    simp only [addLeftEmbedding_apply, add_sub_add_left_eq_sub] at h
    rw [h2 y hy y' hy' h]
  · intro y hy
    obtain ⟨x, hx, h⟩ := h3 (y - b) (sub_mem hy hb)
    refine ⟨b + x, Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    rwa [← sub_sub]

theorem repsOf_spec {Λ B : AddSubgroup V} [Module ℂ V] (h : ∃ R, IsReps Λ B R) : IsReps Λ B (repsOf Λ B) :=
  Classical.epsilon_spec h

theorem hatS_ind [Module ℂ V] (Hs : Sesq V) (vol : ℝ) {B K : AddSubgroup V} {SA : Finset V} (hA : IsReps B K SA) (y : V)
    (hy : ∀ t ∈ B, brk Hs y t = 1) :
    hatS Hs vol SA (indL B) y = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) := by
  obtain ⟨t₀, ht₀, h0⟩ := hA.2.2 0 (zero_mem _)
  have h0' : t₀ ∈ B := by simpa using h0
  have : ∑ t ∈ SA, indL B t * (brk Hs y t)⁻¹ = 1 := by
    rw [Finset.sum_eq_single t₀]
    · simp [indL, h0', hy t₀ h0']
    · intro t ht hne
      have : t ∉ B := fun h => hne (hA.2.1 t ht t₀ ht₀ (sub_mem h h0'))
      simp [indL, this]
    · intro h; exact absurd ht₀ h
  rw [hatS, this, mul_one]

end Reps

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (x : W) :
    x ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • x ∈ localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem mem_loc_self (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Submonoid.one_mem _, by simpa using hx⟩

theorem nat_smul_mem {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) (n : ℕ) : (n : E) • x ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx n

theorem mem_of_inv_smul {M : Submodule (𝓞 E) W} {x : W} {n : ℕ} (hn : 0 < n) (hx : (n : E)⁻¹ • x ∈ M) : x ∈ M := by
  have := nat_smul_mem hx n
  rwa [smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')] at this

theorem loc_le_sup (P : HeightOneSpectrum (𝓞 E)) {M M₀ : Submodule (𝓞 E) W} {r : 𝓞 E} (hr : r ≠ 0)
    (h : ∀ m ∈ M, r • m ∈ M₀) :
    (localization₂ P.asIdeal M).toAddSubgroup ≤ (localization₂ P.asIdeal M₀).toAddSubgroup ⊔ M.toAddSubgroup := by
  rintro x ⟨s, hs, hx⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {r}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hr)
  have key : ∃ i j : ℕ, r ∣ s ^ i - s ^ (i + (j + 1)) := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite fun i : ℕ => Ideal.Quotient.mk (Ideal.span {r}) (s ^ i)
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm e.symm (by omega)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact ⟨i, k, Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e)⟩
  obtain ⟨i, j, u, hu⟩ := key
  have e : x = (x - s ^ (j + 1) • x) + s ^ (j + 1) • x := by abel
  rw [e]
  refine AddSubgroup.add_mem_sup ⟨s ^ (i + 1), pow_mem hs _, ?_⟩ ?_
  · have : s ^ (i + 1) • (x - s ^ (j + 1) • x) = r • (u • (s • x)) := by
      rw [smul_sub, smul_smul, smul_smul, smul_smul, ← sub_smul, ← hu]
      congr 1; ring
    rw [this]
    exact h _ (M.smul_mem u hx)
  · rw [pow_succ, mul_smul]
    exact M.smul_mem _ hx

theorem exists_smul_le {M M₀ : Submodule (𝓞 E) W} (hM : M.FG) (h₀ : ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ M₀) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ ∀ m ∈ M, r • m ∈ M₀ := by
  obtain ⟨T, rfl⟩ := hM
  choose n hn hn' using h₀
  refine ⟨((∏ t ∈ T, n t : ℕ) : 𝓞 E), Nat.cast_ne_zero.2 (Finset.prod_pos fun t _ => hn t).ne', fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)
    have := hn' x
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem this k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact M₀.smul_mem a hx

variable [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem expS_cases (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 E)) :
    (Q ∈ S ∧ expS S Q = 1 ∧ expS S (conjPrime₂ Q) = -1) ∨ (conjPrime₂ Q ∈ S ∧ expS S Q = -1 ∧ expS S (conjPrime₂ Q) = 1) ∨
      (expS S Q = 0 ∧ expS S (conjPrime₂ Q) = 0) := by
  by_cases h : Q ∈ S
  · left; simp [expS, h, hS Q h, conjP_conjP']
  · by_cases h' : conjPrime₂ Q ∈ S
    · right; left; simp [expS, h, h']
    · right; right; simp [expS, h, h', conjP_conjP']

end Loc

section Main

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem embH_injective (hδ : A.δ ≠ 0) (hT : Nonempty X.Tau) :
    Function.Injective (embH (a := a) (b := b) (X.embC A.σ₀) A.δ) := by
  obtain ⟨τ⟩ := hT
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply LinearMap.pi_ext'
  intro j
  apply LinearMap.ext_ring
  funext i
  have := congrFun (congrFun (congrFun hx τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, mul_eq_zero, hδ, false_or, map_eq_zero] at this
  simpa using this

theorem loc_index_ne_zero (hFG : A.AA.FG) (hAA : A.AA ≠ ⊥) {N L : Submodule (𝓞 X.E) (Sp X.E a)}
    {N' L' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') (hL : IsSdLat L) (hL' : IsSdLat L')
    (P : HeightOneSpectrum (𝓞 X.E)) :
    (localization₂ P.asIdeal (per A L L')).toAddSubgroup.relIndex (localization₂ P.asIdeal (per A N N')).toAddSubgroup ≠ 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hAA hN hN'
  obtain ⟨r, hr, h⟩ := exists_smul_le h1 (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b L L' hFG hAA hL hL').2.1
  intro h0
  have h4 := AddSubgroup.relIndex_eq_zero_of_le_right (loc_le_sup P hr h) h0
  rw [AddSubgroup.relIndex_sup_left] at h4
  refine h3 r hr (AddSubgroup.relIndex_eq_zero_of_le_left ?_ h4)
  rintro _ ⟨m, hm, rfl⟩
  exact mem_loc_self P (h m hm)

theorem volC_pos (hFG : A.AA.FG) (hAA : A.AA ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {N : Submodule (𝓞 X.E) (Sp X.E a)}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') : 0 < volC A.AA S N N' := by
  have s1 : IsSdLat (Formalism.L2.Col.stdLat X.E a) := ⟨stdLat_lattice, stdLat_unimodular⟩
  have s2 : IsSdLat (Formalism.L2.Col.stdLat X.E b) := ⟨stdLat_lattice, stdLat_unimodular⟩
  refine Finset.prod_pos fun P _ => div_pos ?_ ?_
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (loc_index_ne_zero A hFG hAA hN hN' s1 s2 P))
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (loc_index_ne_zero A hFG hAA s1 s2 hN hN' P))

theorem Wx_mul {x y : HomE X.E a b} (h : ∃ n : ℤ, coc A x y = n) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = Wx A (x + y) F := by
  obtain ⟨n, hn⟩ := h
  rw [(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1, hn]
  funext z
  have : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((n : ℤ) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (-n)]
    congr 1
    push_cast
    ring
  rw [this, one_mul]

theorem Wx_sum {κ : Type} (x : HomE X.E a b) (T : Finset κ) (F : κ → VCx X.Tau a b → ℂ) :
    Wx A x (fun z => ∑ i ∈ T, F i z) = fun z => ∑ i ∈ T, Wx A x (F i) z := by
  funext z
  simp only [Wx, opU, Finset.sum_mul, Finset.mul_sum]

theorem coc_neg_sub (t s : HomE X.E a b) : coc A (-t) (t - s) = coc A t s - coc A t t := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  have h0 : coc A 0 (t - s) = 0 := by
    have := (h 0 0 (t - s)).1
    rw [add_zero] at this
    linarith
  have h1 := (h (-t) t (t - s)).1
  have h2 := (h t (t - s) s).2.1
  rw [neg_add_cancel, h0] at h1
  rw [sub_add_cancel] at h2
  linarith

variable {S : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem coc_int_twO (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 X.E) → ℤ} (he : ∀ Q, e (conjPrime₂ Q) = -e Q) {x y : HomE X.E a b}
    (hx : x ∈ twist₂ (per A N N') c e) (hy : y ∈ twist₂ (per A N N') c e) : ∃ n : ℤ, coc A x y = n := by
  refine (GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ hL).2.2 x y fun Q => ⟨(c : X.E) ^ e Q, zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne'),
    (mem_twO _ _ _ _).1 hx Q, ?_⟩
  have := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
  rwa [he, zpow_neg, inv_inv, ← star_natCast (R := X.E) c, ← star_zpow₀] at this

theorem expS_conj (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 X.E)) : expS S (conjPrime₂ Q) = -expS S Q := by
  rcases expS_cases S hS Q with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem two_lifts (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (hS : ∀ P ∈ S, conjPrime₂ P ∉ S)
    {c c' D : ℕ} (hc : 0 < c) (hc' : 0 < c') (hD : 0 < D) {s t : HomE X.E a b}
    (hs : s ∈ halfAO S (per A N N') c') (ht : t ∈ halfAO S (per A N N') D)
    (h : ∀ P ∈ S, (c : X.E)⁻¹ • (t - s) ∈ localization₂ P.asIdeal (per A N N')) :
    t - s ∈ halfBO S (per A N N') c ∧ ∃ n : ℤ, coc A (-t) (t - s) = n := by
  have hs' := (mem_twO _ _ _ _).1 hs
  have ht' := (mem_twO _ _ _ _).1 ht
  constructor
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    have h1 := hs' Q
    have h2 := ht' Q
    rcases expS_cases S hS Q with ⟨hQ, e1, -⟩ | ⟨-, e1, -⟩ | ⟨e1, -⟩
    · rw [e1, zpow_one]; exact h Q hQ
    · rw [e1, neg_neg, zpow_one] at h1 h2
      rw [e1, zpow_neg, inv_inv, zpow_one]
      exact nat_smul_mem (sub_mem (mem_of_inv_smul hD h2) (mem_of_inv_smul hc' h1)) c
    · rw [e1, neg_zero, zpow_zero] at h1 h2
      rw [e1, zpow_zero, smul_sub]
      exact sub_mem h2 h1
  · obtain ⟨n₁, h₁⟩ := coc_int_twO A hX hδ hL hD (fun Q => by rw [expS_conj hS]) ht ht
    obtain ⟨n₂, h₂⟩ : ∃ n : ℤ, coc A t s = n := by
      refine (GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ hL).2.2 t s fun Q => ?_
      have h1 := hs' Q
      have h2 := ht' Q
      have h3 := hs' (conjPrime₂ Q)
      have h4 := ht' (conjPrime₂ Q)
      rcases expS_cases S hS Q with ⟨hQ, e1, e2⟩ | ⟨hQ, e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, zpow_neg, inv_inv, zpow_one] at h1
        rw [e2, neg_neg, zpow_one] at h3
        refine ⟨(c' : X.E)⁻¹, inv_ne_zero (Nat.cast_ne_zero.2 hc'.ne'), ?_, ?_⟩
        · have := add_mem h1 (nat_smul_mem (mem_of_inv_smul hc (h Q hQ)) c')
          rwa [← smul_add, add_sub_cancel, ← inv_inv (c' : X.E)] at this
        · rwa [star_inv₀, star_natCast]
      · rw [e1, neg_neg, zpow_one] at h2
        rw [e2, zpow_neg, inv_inv, zpow_one] at h4
        refine ⟨(D : X.E), Nat.cast_ne_zero.2 hD.ne', h2, ?_⟩
        have := sub_mem h4 (nat_smul_mem (mem_of_inv_smul hc (h _ hQ)) D)
        rwa [← smul_sub, sub_sub_cancel, ← star_natCast (R := X.E) D] at this
      · rw [e1, neg_zero, zpow_zero] at h2
        rw [e2, neg_zero, zpow_zero, inv_one] at h3
        exact ⟨1, one_ne_zero, h2, by rwa [star_one]⟩
    exact ⟨n₂ - n₁, by rw [coc_neg_sub, h₁, h₂]; push_cast; ring⟩

theorem thInd_shape : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∃ n : ℕ, n ≠ 0 ∧ n ∣ (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ∧ ∀ x ∈ divLat cA (homAt S N N'), ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') → ∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (halfBO S (per A N N') c).toAddSubgroup R → A.thInd S N N' c x = fun z => (n : ℂ)⁻¹ * Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
  intro X A a b S N N' cA c hX ⟨hδ, hT, hS, hU, hFG, hLa⟩ hAA hN hN' hcA hc
  obtain ⟨hfix, hL⟩ := hLa N N' hN hN'
  obtain ⟨-, -, hidx, hloc⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hAA hN hN'
  have hinj := embH_injective A (a := a) (b := b) hδ hT
  have hc0 : (c : X.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hBB : ∀ x ∈ halfBO S (per A N N') c, ∀ y ∈ halfBO S (per A N N') c, ∃ n : ℤ, coc A x y = n :=
    fun x hx y hy => coc_int_twO A hX hδ hL hc (expS_conj hS) hx hy

  have hBM : (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0 := by
    intro h0
    refine hidx (c : 𝓞 X.E) (Nat.cast_ne_zero.2 hc.ne') (AddSubgroup.relIndex_eq_zero_of_le_left ?_ h0)
    rintro _ ⟨m, hm, rfl⟩
    refine (mem_twO _ _ _ _).2 fun Q => mem_loc_self Q ?_
    change _ • (((c : 𝓞 X.E) : X.E) • m) ∈ _
    rw [show ((c : 𝓞 X.E) : X.E) = (c : X.E) from map_natCast (algebraMap (𝓞 X.E) X.E) c]
    rcases expS_cases S hS Q with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ | ⟨e1, -⟩
    · rw [e1, zpow_one, inv_smul_smul₀ hc0]; exact hm
    · rw [e1, zpow_neg, inv_inv, zpow_one]; exact nat_smul_mem (nat_smul_mem hm c) c
    · rw [e1, zpow_zero, inv_one, one_smul]; exact nat_smul_mem hm c
  have hdvd := relIndex_dvd_of_le (halfBO S (per A N N') c).toAddSubgroup
    ((per A N N').toAddSubgroup ⊓ (halfAO S (per A N N') c).toAddSubgroup) (per A N N').toAddSubgroup inf_le_left
  set n := (halfBO S (per A N N') c).toAddSubgroup.relIndex
    ((per A N N').toAddSubgroup ⊓ (halfAO S (per A N N') c).toAddSubgroup) with hn
  have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hBM hdvd
  refine ⟨n, hn0, hdvd, fun x hx t ht htx R hR => ?_⟩

  obtain ⟨RA, hRA⟩ := (GlobalTheory.RepsMod.reps_facts _).1 _ _ hn0
  have hRA' := reps_map _ hinj hRA
  rw [AddSubgroup.map_inf _ _ _ hinj] at hRA'
  have hSA : IsReps (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)
      (repsOf _ _) := repsOf_spec ⟨_, hRA'⟩
  have hcard : (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c)
      (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card = n := by
    rw [(GlobalTheory.RepsMod.reps_facts _).2.1 _ _ _ hSA, hn, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.map_inf _ _ _ hinj]
    rfl
  have hR' : IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c) _ := reps_map _ hinj hR
  have hSB : IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (repsOf _ _) :=
    repsOf_spec ⟨_, hR'⟩

  have hinv : ∀ y ∈ (halfBO S (per A N N') c).toAddSubgroup, ∀ l ∈ (per A N N').toAddSubgroup,
      l ∈ (halfBO S (per A N N') c).toAddSubgroup → Wx A (y + l) (A.e a b N N') = Wx A y (A.e a b N N') := by
    intro y hy l hl hl'
    rw [← Wx_mul A (hBB y hy l hl')]
    congr 1
    funext z
    exact hfix _ ⟨l, hl, rfl⟩ z
  have hshift : ∀ u ∈ halfBO S (per A N N') c, Wx A u (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) =
      fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z := by
    intro u hu
    rw [Wx_sum]
    funext z
    rw [sum_reps_eq (fun y => Wx A y (A.e a b N N') z) hR (reps_shift hR hu)
      (fun y hy l hl hl' => by rw [hinv y hy l hl hl']), Finset.sum_map]
    exact Finset.sum_congr rfl fun y hy => by rw [Wx_mul A (hBB u hu y (hR.1 y hy))]; rfl

  have hxi : xiS (HV A.sc) (alV A.d A.sc) (volC A.AA S N N')
      (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (indL (BC (X.embC A.σ₀) A.δ A.AA S N N' c)) (A.e a b N N') =
      fun z => ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ * (((volC A.AA S N N' : ℝ) : ℂ) / (n : ℂ)) *
        ∑ y ∈ R, Wx A y (A.e a b N N') z := by
    funext z
    have e1 : ∑ y ∈ R, Wx A y (A.e a b N N') z =
        ∑ v ∈ repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c),
          alV A.d A.sc v * opU (HV A.sc) v (A.e a b N N') z := by
      rw [sum_reps_eq (fun v => alV A.d A.sc v * opU (HV A.sc) v (A.e a b N N') z) hSB hR' ?_, Finset.sum_map]
      · rfl
      · rintro _ ⟨y, hy, rfl⟩ _ ⟨l, hl, rfl⟩ ⟨l', hl', e⟩
        obtain rfl := hinj e
        rw [← map_add]
        exact congrFun (hinv y hy l' hl hl') z
    rw [e1, Finset.mul_sum, xiS, sumU]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨y, hy, rfl⟩ := hSB.1 v hv
    rw [hatS_ind _ _ hSA, hcard, mul_assoc]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨n₁, h₁⟩ := hBB u hu y hy
    obtain ⟨n₂, h₂⟩ := hBB y hy u hu
    exact ((GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.2.2.1 y u).2
      ⟨n₁ - n₂, by rw [(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.1, h₁, h₂]; push_cast; ring⟩

  have hlift : A.IsLift S N N' c x (A.liftW S N N' c x) :=
    Classical.epsilon_spec (p := A.IsLift S N N' c x) ⟨t, ⟨cA * c, Nat.mul_pos hcA hc, ht⟩, htx⟩
  obtain ⟨⟨c', hc', hs⟩, hsx⟩ := hlift
  set s := A.liftW S N N' c x with hs_def
  obtain ⟨hB, hcoc⟩ := two_lifts A hX hδ hL hS hc hc' (Nat.mul_pos hcA hc) hs ht (by
    intro P hP
    obtain ⟨h, hh, e⟩ := sub_mem htx hsx
    have e' : t - s = (c : X.E) • h := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E), ← sub_sub_sub_cancel_right t s x]
      exact e.symm
    rw [e', inv_smul_smul₀ hc0]
    exact (hloc P (hU P hP) h).2 (hh P hP))
  have hW : Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) = Wx A (-s) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) := by
    conv_lhs => rw [← hshift _ hB, Wx_mul A hcoc]
    congr 1
    abel
  rw [hW]
  funext z
  have hv := volC_pos A hFG hAA S hN hN'
  have hsq : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) * ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) = (volC A.AA S N N' : ℝ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
  have hsq0 : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hv).ne'
  have hα : alV A.d A.sc (emb A (-s)) = alV A.d A.sc (embH (X.embC A.σ₀) A.δ s) := by
    simp [emb, alV, alphaQ, Formalism.L2.Th1.H.qOf]
  have hem : emb A (-s) = -embH (X.embC A.σ₀) A.δ s := map_neg _ _
  rw [Amb.thInd, xiInd, ← hs_def, hxi, Wx]
  simp only [hα]
  rw [hem, opU, opU, ← hsq]
  field_simp

end Main

end GlobalTheory.MomT.ThShape
