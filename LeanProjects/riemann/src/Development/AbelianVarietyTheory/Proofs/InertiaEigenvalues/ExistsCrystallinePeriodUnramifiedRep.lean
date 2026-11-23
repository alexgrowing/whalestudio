import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

noncomputable section

open scoped Topology

namespace GlobalTheory.UnrPer

open GlobalTheory.UnramifiedCrys

section Abstract

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {R : Type} [CommRing R] [IsDomain R] [CharP R p]
  [PerfectRing R p] (ρ : G →* (R ≃+* R)) {n : Type} [Fintype n] [DecidableEq n]

def act (g : G) : Matrix n n (WittVector p R) →+* Matrix n n (WittVector p R) :=
  (WittVector.map (ρ g).toRingHom).mapMatrix

theorem act_apply (g : G) (M : Matrix n n (WittVector p R)) (i j : n) :
    act ρ g M i j = WittVector.map (ρ g).toRingHom (M i j) := rfl

variable (p) in

def Dv (N : ℕ) (M : Matrix n n (WittVector p R)) : Prop := ∀ i j, (p : WittVector p R) ^ N ∣ M i j

variable (p) in

def Jset : Set G := {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
  [PerfectRing R p] in
theorem act_mul_apply (g h : G) (M : Matrix n n (WittVector p R)) :
    act ρ (g * h) M = act ρ g (act ρ h M) := by
  ext i j : 1
  exact wittMap_mul ρ g h (M i j)

theorem Dv_add {N : ℕ} {M M' : Matrix n n (WittVector p R)} (h : Dv p N M) (h' : Dv p N M') :
    Dv p N (M + M') := fun i j => dvd_add (h i j) (h' i j)

theorem Dv_sub {N : ℕ} {M M' : Matrix n n (WittVector p R)} (h : Dv p N M) (h' : Dv p N M') :
    Dv p N (M - M') := fun i j => dvd_sub (h i j) (h' i j)

theorem Dv_mul_left (X : Matrix n n (WittVector p R)) {N : ℕ} {M : Matrix n n (WittVector p R)}
    (h : Dv p N M) : Dv p N (X * M) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem Dv_mul_right (X : Matrix n n (WittVector p R)) {N : ℕ} {M : Matrix n n (WittVector p R)}
    (h : Dv p N M) : Dv p N (M * X) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h i k) _

theorem Dv_mono {N N' : ℕ} (hN : N ≤ N') {M : Matrix n n (WittVector p R)} (h : Dv p N' M) :
    Dv p N M := fun i j => (pow_dvd_pow _ hN).trans (h i j)

theorem Dv_act (g : G) {N : ℕ} {M : Matrix n n (WittVector p R)} (h : Dv p N M) :
    Dv p N (act ρ g M) := fun i j => by
  have := map_dvd (WittVector.map (ρ g).toRingHom) (h i j)
  rwa [map_pow, map_natCast] at this

theorem Dv_smul (N : ℕ) (M : Matrix n n (WittVector p R)) : Dv p N ((p : WittVector p R) ^ N • M) :=
  fun i j => ⟨M i j, rfl⟩

theorem approx_step
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (A : G → Matrix n n (WittVector p R)) (hA : ∀ g h, A (g * h) = A g * act ρ g (A h))
    (h1 : ∀ g, Dv p 1 (A g - 1)) (hJ : ∀ N, ∀ᶠ g in 𝓝ˢ (Jset p ρ), Dv p N (A g - 1))
    (N : ℕ) (Q : Matrix n n (WittVector p R)) (hQ : ∀ᶠ g in 𝓝ˢ (Jset p ρ), act ρ g Q = Q)
    (hE : ∀ g, Dv p N (A g * act ρ g Q - Q)) :
    ∃ Q' : Matrix n n (WittVector p R), Dv p N (Q - Q') ∧ (∀ᶠ g in 𝓝ˢ (Jset p ρ), act ρ g Q' = Q') ∧
      ∀ g, Dv p (N + 1) (A g * act ρ g Q' - Q') := by
  have hp0 : (p : WittVector p R) ^ N ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p R)
  have cc0 : ∀ x : WittVector p R, (p : WittVector p R) ∣ x → x.coeff 0 = 0 := fun x hx =>
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero x).1 (Ideal.mem_span_singleton.2 hx)
  have ccA : ∀ g (Y : Matrix n n (WittVector p R)) i j, ((A g * Y) i j).coeff 0 = (Y i j).coeff 0 := by
    intro g Y i j
    have e : (A g * Y) i j = Y i j + ((A g - 1) * Y) i j := by rw [sub_mul, one_mul]; simp
    have h2 := Dv_mul_right Y (h1 g) i j
    rw [pow_one] at h2
    rw [e, ← WittVector.constantCoeff_apply, map_add, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, cc0 _ h2, add_zero]
  have hD : ∀ g, ∃ D : Matrix n n (WittVector p R), A g * act ρ g Q - Q = (p : WittVector p R) ^ N • D :=
    fun g => ⟨Matrix.of fun i j => (hE g i j).choose, by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      exact (hE g i j).choose_spec⟩
  choose D hD using hD
  have hact_smul : ∀ g (X : Matrix n n (WittVector p R)),
      act ρ g ((p : WittVector p R) ^ N • X) = (p : WittVector p R) ^ N • act ρ g X := by
    intro g X
    ext i j
    simp only [act_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
  have hcoc : ∀ g h, D (g * h) = D g + A g * act ρ g (D h) := by
    intro g h
    have e1 : A (g * h) * act ρ (g * h) Q - Q =
        (A g * act ρ g Q - Q) + A g * act ρ g (A h * act ρ h Q - Q) := by
      rw [hA, act_mul_apply, map_sub, map_mul]; noncomm_ring
    rw [hD, hD, hD, hact_smul, Matrix.mul_smul, ← smul_add] at e1
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun e1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hp0 this
  have hec : ∀ g h i j, (D (g * h) i j).coeff 0 = (D g i j).coeff 0 + ρ g ((D h i j).coeff 0) := by
    intro g h i j
    rw [hcoc, Matrix.add_apply, ← WittVector.constantCoeff_apply, map_add, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, ccA, act_apply, WittVector.map_coeff]
    rfl
  have hnear : ∀ᶠ g in 𝓝ˢ (Jset p ρ), ∀ i j, (D g i j).coeff 0 = 0 := by
    filter_upwards [hQ, hJ (N + 1)] with g hg hg'
    intro i j
    have e : A g * act ρ g Q - Q = (A g - 1) * Q := by rw [hg, sub_mul, one_mul]
    have h2 := Dv_mul_right Q hg' i j
    rw [← e, hD] at h2
    simp only [Matrix.smul_apply, smul_eq_mul, pow_succ] at h2
    exact cc0 _ ((mul_dvd_mul_iff_left hp0).1 h2)
  have hβ : ∀ i j, ∃ β : R, ∀ g, (D g i j).coeff 0 = ρ g β - β := fun i j =>
    exists_coboundary ρ hopen (fun g => (D g i j).coeff 0) (fun g h => hec g h i j)
      (hnear.mono fun g hg => hg i j)
  choose β hβ using hβ
  let T : Matrix n n (WittVector p R) := Matrix.of fun i j => WittVector.teichmuller p (β i j)
  refine ⟨Q - (p : WittVector p R) ^ N • T, ?_, ?_, fun g => ?_⟩
  · rw [sub_sub_cancel]; exact Dv_smul N T
  · filter_upwards [hQ, hnear] with g hg hg'
    have hT : act ρ g T = T := by
      refine Matrix.ext fun i j => ?_
      have := hβ i j g
      rw [hg' i j] at this
      simp only [act_apply, T, Matrix.of_apply, WittVector.map_teichmuller]
      rw [show (ρ g).toRingHom (β i j) = β i j from sub_eq_zero.1 this.symm]
    rw [map_sub, hact_smul, hg, hT]
  · have e : A g * act ρ g (Q - (p : WittVector p R) ^ N • T) - (Q - (p : WittVector p R) ^ N • T) =
        (p : WittVector p R) ^ N • (D g - (A g * act ρ g T - T)) := by
      rw [map_sub, hact_smul, mul_sub, Matrix.mul_smul, smul_sub, smul_sub, ← hD]; abel
    rw [e]
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, pow_succ]
    refine mul_dvd_mul_left _ ?_
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    rw [Matrix.sub_apply, Matrix.sub_apply, ← WittVector.constantCoeff_apply, map_sub, map_sub,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, ccA,
      act_apply, hβ i j g]
    simp [T, WittVector.map_teichmuller, WittVector.teichmuller_coeff_zero]

theorem exists_solution
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (A : G → Matrix n n (WittVector p R)) (hA : ∀ g h, A (g * h) = A g * act ρ g (A h))
    (h1 : ∀ g, Dv p 1 (A g - 1)) (hJ : ∀ N, ∀ᶠ g in 𝓝ˢ (Jset p ρ), Dv p N (A g - 1)) :
    ∃ Q : Matrix n n (WittVector p R), IsUnit Q.det ∧ ∀ g, A g * act ρ g Q = Q := by
  have cc0 : ∀ x : WittVector p R, (p : WittVector p R) ∣ x → x.coeff 0 = 0 := fun x hx =>
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero x).1 (Ideal.mem_span_singleton.2 hx)
  let Pn : ℕ → Matrix n n (WittVector p R) → Prop := fun N Q =>
    Dv p 1 (Q - 1) ∧ (∀ᶠ g in 𝓝ˢ (Jset p ρ), act ρ g Q = Q) ∧ ∀ g, Dv p (N + 1) (A g * act ρ g Q - Q)
  have hstep : ∀ N (Q : {Q // Pn N Q}), ∃ Q' : {Q // Pn (N + 1) Q}, Dv p (N + 1) (Q.1 - Q'.1) := by
    intro N Q
    obtain ⟨Q', h1', h2', h3'⟩ := approx_step ρ hopen A hA h1 hJ (N + 1) Q.1 Q.2.2.1 Q.2.2.2
    refine ⟨⟨Q', ?_, h2', h3'⟩, h1'⟩
    have e : Q' - 1 = (Q.1 - 1) - (Q.1 - Q') := by abel
    rw [e]
    exact Dv_sub Q.2.1 (Dv_mono (by omega) h1')
  choose F hF using hstep
  let s : ∀ N, {Q // Pn N Q} := fun N => Nat.rec (motive := fun N => {Q // Pn N Q})
    ⟨1, fun i j => by simp, Filter.Eventually.of_forall fun g => map_one _,
      fun g => by simpa using h1 g⟩ F N
  have hs : ∀ N, Dv p (N + 1) ((s N).1 - (s (N + 1)).1) := fun N => hF N (s N)
  have hsm : ∀ (N : ℕ) (x y : WittVector p R),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p R)} ^ N • ⊤ : Submodule (WittVector p R) _)] ↔
        (p : WittVector p R) ^ N ∣ x - y := fun N x y => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have hcau : ∀ i j {m k : ℕ}, m ≤ k → (p : WittVector p R) ^ m ∣ (s m).1 i j - (s k).1 i j := by
    intro i j m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have := dvd_add ih ((pow_dvd_pow _ (by omega : m ≤ k + 1)).trans (hs k i j))
      rwa [Matrix.sub_apply, sub_add_sub_cancel] at this
  have hL : ∀ i j, ∃ L : WittVector p R, ∀ N, (p : WittVector p R) ^ N ∣ (s N).1 i j - L := by
    intro i j
    obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun N => (s N).1 i j)
      (fun hmk => (hsm _ _ _).2 (hcau i j hmk))
    exact ⟨L, fun N => (hsm _ _ _).1 (hL N)⟩
  choose L hL using hL
  let Q : Matrix n n (WittVector p R) := Matrix.of L
  have hQs : ∀ N, Dv p N ((s N).1 - Q) := fun N i j => hL i j N
  refine ⟨Q, ?_, fun g => ?_⟩
  · have hQ1 : Dv p 1 (Q - 1) := by
      have e : Q - 1 = ((s 1).1 - 1) - ((s 1).1 - Q) := by abel
      rw [e]
      exact Dv_sub (s 1).2.1 (hQs 1)
    have hmap : (WittVector.constantCoeff : WittVector p R →+* R).mapMatrix Q = 1 := by
      have e : Q = (Q - 1) + 1 := by abel
      have h0 : (WittVector.constantCoeff : WittVector p R →+* R).mapMatrix (Q - 1) = 0 := by
        refine Matrix.ext fun i j => ?_
        have := hQ1 i j
        rw [pow_one] at this
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
          WittVector.constantCoeff_apply]
        exact cc0 _ this
      rw [e, map_add, h0, map_one, zero_add]
    have hdet : WittVector.constantCoeff Q.det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    have hmem : Q.det - 1 ∈ Ideal.span {(p : WittVector p R)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
        hdet, map_one, sub_self]
    have hj := IsAdicComplete.le_jacobson_bot (Ideal.span {(p : WittVector p R)}) hmem
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    simpa using this
  · refine Matrix.ext fun i j => sub_eq_zero.1 (hcomp.toIsHausdorff.haus _ fun N => ?_)
    rw [hsm, sub_zero]
    have e : A g * act ρ g Q - Q = (A g * act ρ g (s N).1 - (s N).1) -
        A g * act ρ g ((s N).1 - Q) + ((s N).1 - Q) := by
      rw [map_sub]; noncomm_ring
    have hd : Dv p N (A g * act ρ g Q - Q) := by
      rw [e]
      exact Dv_add (Dv_sub (Dv_mono (by omega) ((s N).2.2.2 g))
        (Dv_mul_left _ (Dv_act ρ g (hQs N)))) (hQs N)
    simpa [Matrix.sub_apply] using hd i j

end Abstract

end GlobalTheory.UnrPer

namespace GlobalTheory.UnrPer

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.UnramifiedCrys

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_le_inv_of_lt_one_kur (c : ↥(MaximalUnramifiedExtension l)) (hc : ‖(c : Om l)‖ < 1) :
    ‖(c : Om l)‖ ≤ (l : ℝ) ^ (-(1 : ℤ)) := by
  by_cases h0 : (c : Om l) = 0
  · rw [h0, norm_zero]; positivity
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow c.2 h0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  rw [hk] at hc ⊢
  have hk0 : k < 0 := by
    by_contra hk0
    push_neg at hk0
    exact absurd hc (not_lt.2 (one_le_zpow₀ hl1.le hk0))
  exact zpow_le_zpow_right₀ hl1.le (by omega)

theorem pow_dvd_of_lift {P : LocPrime l} (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (c : ↥(MaximalUnramifiedExtension l)) (hcK : (c : Om l) ∈ K.1) (N : ℕ) (hc : ‖(c : Om l)‖ ≤ (l : ℝ) ^ (-(N : ℤ)))
    (w : Ainf l) (hw : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) : (l : Ainf l) ^ N ∣ w := by
  have hl0 : ((l : ↥(MaximalUnramifiedExtension l)) : Om l) ≠ 0 := by
    push_cast; exact_mod_cast hl.out.ne_zero
  let d : ↥(MaximalUnramifiedExtension l) := c / (l : ↥(MaximalUnramifiedExtension l)) ^ N
  have hdK : (d : Om l) ∈ K0 K := by
    refine ⟨?_, d.2⟩
    show ((c / (l : ↥(MaximalUnramifiedExtension l)) ^ N : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1
    push_cast
    exact K.1.div_mem hcK (pow_mem (K.1.natCast_mem l) N)
  have hd1 : ‖(d : Om l)‖ ≤ 1 := by
    show ‖((c / (l : ↥(MaximalUnramifiedExtension l)) ^ N : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1
    push_cast
    rw [norm_div, norm_pow]
    have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [Padic.norm_p] at h
      rw [← h]
      congr 1
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    rw [hn, div_le_one (pow_pos (inv_pos.2 hlpos) N), inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hc
  obtain ⟨v, hv⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T K ⟨d, hdK⟩ hd1
  have hcd : c = (l : ↥(MaximalUnramifiedExtension l)) ^ N * d := by
    simp only [d]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0 : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0))]
  refine ⟨v, AI.ιA_inj ?_⟩
  rw [hw, map_mul, map_pow, map_natCast, hcd, map_mul, map_pow, map_natCast]
  congr 1
  exact hv.symm

end GlobalTheory.UnrPer

namespace GlobalTheory.UnrPer

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.UnramifiedCrys
open scoped Formalism.Per

theorem coe_one_apply {l : ℕ} [Fact l.Prime] {n : Type} [DecidableEq n] (i j : n) :
    (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) = (1 : Matrix n n (Om l)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem exists_period_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)),
    IsRat r ρ → (∀ g ∈ IK K, ρ g = 1) →
    (∀ g i j, ‖(((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1) →
    ∃ Q : GL n P.R.B, ∀ g : ↥(GK K), (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *
      (Q : Matrix n n P.R.B).map (P.actQ (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K r ρ hρ hI hn
  haveI := compactSpace_GK K
  let σ : ↥(GK K) →* (OCb l ≃+* OCb l) := AI.actT.comp (GK K).subtype
  have hopen : ∀ (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → ∀ᶠ g in 𝓝 (1 : ↥(GK K)), σ g y = y :=
    fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)

  let M : ↥(GK K) → Matrix n n ↥(MaximalUnramifiedExtension l) := fun g => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) - 1
  have hKρ : ∀ g i j, (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 :=
    fun g i j => hρ.le _ (hρ.rat g i j)
  have hK1 : ∀ i j, (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun i j => by
    rw [coe_one_apply, Matrix.one_apply]
    split_ifs
    · exact K.1.one_mem
    · exact K.1.zero_mem
  have hKM : ∀ g i j, ((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun g i j => by
    simp only [M, Matrix.sub_apply]
    push_cast
    exact K.1.sub_mem (hKρ g i j) (hK1 i j)
  have hnM : ∀ g i j, ‖((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l)‖ < 1 := fun g i j => by
    simp only [M, Matrix.sub_apply]
    push_cast
    rw [coe_one_apply]
    exact hn g i j
  have hnρ : ∀ g i j, ‖(((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := fun g i j => by
    have e : (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) =
        ((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l) + (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      simp [M]
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hnM g i j).le ?_)
    rw [coe_one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hlift : ∀ g i j, ∃ w : Ainf l, AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) :=
    fun g i j => by
      obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T K
        ⟨_, hKρ g i j, ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j).2⟩ (hnρ g i j)
      exact ⟨w, hw⟩
  choose w hw using hlift
  let A : ↥(GK K) → Matrix n n (Ainf l) := fun g => Matrix.of (w g)
  have hιA : ∀ g, AI.ιA.mapMatrix (A g) = (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) :=
    fun g => Matrix.ext fun i j => hw g i j
  have hinj : Function.Injective (AI.ιA.mapMatrix : Matrix n n (Ainf l) →+* Matrix n n P.R.B) :=
    fun X Y h => Matrix.ext fun i j => AI.ιA_inj (congrFun (congrFun h i) j)
  have hact : ∀ (g : ↥(GK K)) (X : Matrix n n (Ainf l)),
      AI.ιA.mapMatrix (act σ g X) = (AI.ιA.mapMatrix X).map (P.actQ (g : GQ l)) :=
    fun g X => Matrix.ext fun i j => AI.ιA_act (g : GQ l) (X i j)
  have hfix : ∀ g h : ↥(GK K), ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix (ρ h : Matrix n n ↥(MaximalUnramifiedExtension l))).map (P.actQ (g : GQ l)) =
      (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix (ρ h : Matrix n n ↥(MaximalUnramifiedExtension l)) :=
    fun g h => Matrix.ext fun i j => P.actQ_Kur _ _ _ (mem_GK.1 g.2 _ (hKρ h i j))
  have hA : ∀ g h, A (g * h) = A g * act σ g (A h) := by
    intro g h
    apply hinj
    rw [map_mul, hact, hιA, hιA, hιA, hfix, map_mul, Units.val_mul, map_mul]
  have hιA1 : ∀ g, AI.ιA.mapMatrix (A g - 1) = (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix (M g) := by
    intro g
    rw [map_sub, map_one, hιA, map_sub, map_one]
  have hdiv : ∀ g (N : ℕ), (∀ i j, ‖((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ (l : ℝ) ^ (-(N : ℤ))) →
      Dv l N (A g - 1) := fun g N hN i j =>
    pow_dvd_of_lift AI T K (M g i j) (hKM g i j) N (hN i j) _
      (congrFun (congrFun (hιA1 g) i) j)
  have h1 : ∀ g, Dv l 1 (A g - 1) := fun g =>
    hdiv g 1 fun i j => by exact_mod_cast norm_le_inv_of_lt_one_kur _ (hnM g i j)
  have hJ : ∀ N, ∀ᶠ g in 𝓝ˢ (Jset l σ), Dv l N (A g - 1) := by
    intro N
    let U : Set ↥(GK K) := ⋂ i, ⋂ j, {g | ‖((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l)‖ < (l : ℝ) ^ (-(N : ℤ))}
    have hU : IsOpen U := by
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      have hc : Continuous fun g : ↥(GK K) => ((M g i j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
        simp only [M, Matrix.sub_apply]
        push_cast
        exact (hρ.cont i j).sub continuous_const
      exact isOpen_lt hc.norm continuous_const
    have hJU : Jset l σ ⊆ U := by
      intro g hg
      have hgI : g ∈ IK K := Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
      intro i j
      have : M g = 0 := by simp [M, hI g hgI]
      rw [this]
      simp only [Matrix.zero_apply, ZeroMemClass.coe_zero, norm_zero]
      have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
      positivity
    filter_upwards [hU.mem_nhdsSet.2 hJU] with g hg
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hg
    exact hdiv g N fun i j => (hg i j).le
  obtain ⟨Q₀, hQdet, hQ⟩ := exists_solution σ hopen A hA h1 hJ
  have hQu : IsUnit (AI.ιA.mapMatrix Q₀) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
    exact hQdet.map _
  refine ⟨hQu.unit, fun g => ?_⟩
  rw [IsUnit.unit_spec, ← hact, ← RingHom.mapMatrix_apply, ← hιA, ← map_mul, hQ]

end GlobalTheory.UnrPer
