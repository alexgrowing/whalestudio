import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHcParamCodeWord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelevelCoprimeOfModOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModulusBbDisjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNonnegOfImagQuadratic
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Development.AutomorphicArithmetic.PrimeDiscriminants.MuParallel

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

def NormPrimes : Prop :=
  ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M → ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
    (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧ p ≡ a ^ 2 [MOD M]

def SpacesExist : Prop :=
  ∀ (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (_ : CMData F E)
    (T : ℕ) (_ : T.Prime) (pz : E) (_ : star pz * pz = T),
    ∃ S : Spaces R F E, S.T = T ∧ (∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) ∧
      (∀ j, 0 < j → j < R.m → HasHyperbolicAuxiliaryFrame S j) ∧ (∀ j, 1 ≤ j → j ≤ R.m → S.Vneg j = false) ∧
      (S.X R.m).hT S.z S.z = (S.T : E)

theorem spacesExist : SpacesExist := by
  intro R F E _ _ _ _ _ _ cm T hT pz hpz
  exact ⟨spacesNorm R cm T hT pz hpz, rfl, fun j _ τ => spacesNorm_Y_sig R cm T hT pz hpz j τ,
    fun j _ hj => auxiliary_frame_normalized_spaces R cm T hT pz hpz j hj, fun _ _ _ => rfl, spacesNorm_z_norm R cm T hT pz hpz⟩

theorem mod_of_modEq {p c M : ℕ} (hc : 1 < c) (hcM : c ∣ M) (h : p ≡ 1 [MOD M]) : p % c = 1 := by
  have h1 : p ≡ 1 [MOD c] := h.of_dvd hcM
  unfold Nat.ModEq at h1
  rw [h1, Nat.mod_eq_of_lt hc]

private theorem coprime_of_mod_one {x a b c : ℕ} (h : x % (a * b * c) = 1) : Nat.Coprime x a := by
  have h1 : Nat.Coprime x (a * b * c) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h]; exact Nat.gcd_one_left _
  exact h1.coprime_dvd_right ((dvd_mul_right a b).mul_right c)

theorem win_eq (T : ℝ) (hT : 0 < T) (n : ℝ) (hn : 0 < n) :
    (T ^ n * 4 / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / n) * (2 : ℝ) ^ (-(2 : ℝ) / n) = T := by
  have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT.le, h4,
    ← Real.rpow_mul (by norm_num), mul_assoc, ← Real.rpow_add (by norm_num)]
  have h1 : n * (1 / n) = 1 := by field_simp
  have h2 : 2 * (1 / n) + -2 / n = 0 := by ring
  rw [h1, h2, Real.rpow_one, Real.rpow_zero, mul_one]

theorem exists_primes (hP : NormPrimes) (R : Ranks) (H : Host R) :
    ∃ (g : Fin 2 → ℕ) (π : Fin 2 → 𝓞 H.E) (p p' : ℕ), (∀ i, (g i).Prime) ∧ g 0 < g 1 ∧ g 1 < p ∧ p < p' ∧ p.Prime ∧ p'.Prime ∧
      p % 15 = 1 ∧ p' % 15 = 1 ∧ p % (H.QS * H.q * H.d) = 1 ∧ p' % (H.QS * H.q * H.d) = 1 ∧
      (∀ i, g i % (H.QS * H.q * H.d) = 1) ∧ (∀ i, (π i : H.E) ∈ H.K) ∧
      (∀ i, (π i : H.E) * H.conj (π i : H.E) = (g i : H.E)) ∧
      (∀ i, ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π i - 1) ∧ 2 * R.f * R.k + 1 < g 0 ∧
      Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) ∧ 1 < H.QS * H.q * H.d := by
  set c := H.QS * H.q * H.d with hc
  have hc1 : 1 < c := by
    have h1 := H.QS_pos
    have h2 := H.hyp.1.pos
    have h3 := H.hyp.2.1.one_lt
    have : 0 < H.QS * H.q := by positivity
    rw [hc]; nlinarith
  have hc0 : c ≠ 0 := by omega
  obtain ⟨π0, g0, hg0, hg0N, hK0, hn0, hcg0, hm0⟩ := hP R H c 1 (2 * R.f * R.k + 1) hc0 (Nat.coprime_one_left _)
  obtain ⟨M, N, hM0, hcM, hBB⟩ := exists_modulus_bb_disjoint R.r g0 c hg0 hc0
  have hcop : Nat.Coprime (1 + M) (M ^ 2) := Nat.Coprime.pow_right _ (by simp)
  obtain ⟨π1, g1, hg1, hg1N, hK1, hn1, hcg1, hm1⟩ := hP R H (M ^ 2) (1 + M) (N + g0) (pow_ne_zero _ hM0) hcop
  obtain ⟨p, hp, hpN, hpm⟩ := Nat.exists_prime_gt_modEq_one g1 (k := 15 * c) (by omega)
  obtain ⟨p', hp', hpN', hpm'⟩ := Nat.exists_prime_gt_modEq_one p (k := 15 * c) (by omega)
  refine ⟨![g0, g1], ![π0, π1], p, p', ?_, ?_, hpN, hpN', hp, hp', mod_of_modEq (by norm_num) (dvd_mul_right _ _) hpm,
    mod_of_modEq (by norm_num) (dvd_mul_right _ _) hpm', mod_of_modEq hc1 (dvd_mul_left _ _) hpm,
    mod_of_modEq hc1 (dvd_mul_left _ _) hpm', ?_, ?_, ?_, ?_, hg0N, hBB g1 hg1 (by omega) hm1, hc1⟩
  · intro i; fin_cases i; exacts [hg0, hg1]
  · show g0 < g1; omega
  · intro i; fin_cases i
    · exact mod_of_modEq hc1 dvd_rfl (by simpa using hm0)
    · refine mod_of_modEq hc1 hcM ?_
      have h1 : g1 ≡ (1 + M) ^ 2 [MOD M] := hm1.of_dvd (dvd_pow_self _ two_ne_zero)
      refine h1.trans ?_
      have h2 : 1 + M ≡ 1 [MOD M] := by simp [Nat.ModEq]
      simpa using h2.pow 2
  · intro i; fin_cases i; exacts [hK0, hK1]
  · intro i; fin_cases i; exacts [hn0, hn1]
  · intro i; fin_cases i
    · simpa using Ideal.mem_span_singleton.1 hcg0
    · have h1 := Ideal.mem_span_singleton.1 hcg1
      have h2 : (c : 𝓞 H.E) ∣ (M : 𝓞 H.E) := Nat.cast_dvd_cast hcM
      have h3 : (M : 𝓞 H.E) ∣ ((M ^ 2 : ℕ) : 𝓞 H.E) := Nat.cast_dvd_cast (dvd_pow_self _ two_ne_zero)
      have h4 : π1 - 1 = (π1 - ((1 + M : ℕ) : 𝓞 H.E)) + (M : 𝓞 H.E) := by push_cast; ring
      show (c : 𝓞 H.E) ∣ π1 - 1
      rw [h4]
      exact dvd_add (h2.trans (h3.trans h1)) h2

theorem exists_preX_host (hP : NormPrimes) (hS : SpacesExist) (R : Ranks) (H₀ : Host R) :
    ∃ B : Pre, B.R = R ∧ HEq B.host.toHostAx H₀.toHostAx ∧ Nontrivial B.Word ∧ Nonempty (PreX B) := by
  obtain ⟨H, hcc, hH⟩ : ∃ H : Host R, H.ccK = ⊤ ∧ H.toHostAx = H₀.toHostAx := ⟨UpperTheory.Host.withTop H₀, rfl, rfl⟩
  obtain ⟨g, π, p, p', hg, hg01, hg1p, hpp', hp, hp', hp15, hp15', hpc, hpc', hgc, hπK, hπn, hπc, hgbig, hBB, hc1⟩ :=
    exists_primes hP R H
  obtain ⟨P, hPv, hPb, hPe, hPu⟩ := GlobalTheory.exists_hcParam_codeWord R 2 0 (R.t + 3) le_rfl le_rfl

  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ u : Bool, ∀ j, j ≤ R.m → ((Formalism.BasicNotions.Examples₂.lamOf (P fun _ => u) j).spread : ℝ) ≤ A := by
    have hfin : (Set.range fun x : Bool × Fin (R.m + 1) => ((Formalism.BasicNotions.Examples₂.lamOf (P fun _ => x.1) x.2).spread : ℝ)).Finite :=
      Set.finite_range _
    obtain ⟨b, hb⟩ := hfin.bddAbove
    obtain ⟨A, hA⟩ := exists_nat_ge b
    exact ⟨A, fun u j hj => (hb ⟨(u, ⟨j, by omega⟩), rfl⟩).trans hA⟩
  set a : ℕ := A + (2 * R.f * R.N R.m + 1) with ha
  have hM0 : H.QS * H.q * H.d * (g 0 * g 1) ^ 2 ≠ 0 :=
    mul_ne_zero (by omega) (pow_ne_zero _ (mul_ne_zero (hg 0).ne_zero (hg 1).ne_zero))
  obtain ⟨πT, T, hT, hTN, hTK, hTn, hTc, hTm⟩ := hP R H _ 1 (4 * a + p') hM0 (Nat.coprime_one_left _)
  have hTcond : T % (H.QS * H.q * H.d) = 1 := mod_of_modEq hc1 (dvd_mul_right _ _) (by simpa using hTm)
  have hpg : ∀ i, p ≠ g i ∧ p' ≠ g i := by
    intro i; fin_cases i
    · exact ⟨(by omega : p ≠ g 0), (by omega : p' ≠ g 0)⟩
    · exact ⟨(by omega : p ≠ g 1), (by omega : p' ≠ g 1)⟩
  have hQS : ∀ x ∈ insert (g 0) (insert (g 1) (insert p (insert p' ({T} : Finset ℕ)))), Nat.Coprime x H.QS := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    exacts [coprime_of_mod_one (hgc 0), coprime_of_mod_one (hgc 1), coprime_of_mod_one hpc, coprime_of_mod_one hpc',
      coprime_of_mod_one hTcond]
  obtain ⟨hg', hne, lv, hl, hp1, hp2, hpp, hpl, hm, hpg', hco, hcs, hlv, -⟩ :=
    GlobalTheory.host_relevel R H hcc g p p' {T} hg hg01.ne hp hp' hpp'.ne hp15 hp15' hpg hQS
  let H' : Host R := { H with levelPrimes := lv, g := g, g_prime := hg', g_ne := hne, g_level := hl, pde := p, pde' := p', pde_prime := hp1, pde'_prime := hp2, pde_ne := hpp, pde_level := hpl, pde_mod := hm, pde_ne_g := hpg', ccK_coprime := hco, level_coprimeS := hcs }
  have hsplit := GlobalTheory.HostSplit.split_of_one_mod R H'
  letI := H'.cmStar
  have hstar : star (πT : H'.E) * (πT : H'.E) = (T : H'.E) := by
    have h1 : star (πT : H'.E) = H'.conj (πT : H'.E) := bridge_star_holds R H' _
    rw [h1, mul_comm]; exact hTn
  obtain ⟨S, hST, hSY, hSA, hSV, hSz⟩ := hS R H'.F H'.E (host_cmData R H') T hT (πT : H'.E) hstar
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hf : 0 < R.f := by unfold Ranks.f Ranks.n; positivity
  have hfk : (0 : ℝ) < (R.f : ℝ) * R.k := by
    have : 0 < R.k := by omega
    positivity
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT.pos
  have hTc' : πT - 1 ∈ Ideal.span {((H.QS * H.q * H.d * (g 0 * g 1) ^ 2 : ℕ) : 𝓞 H.E)} := by simpa using hTc
  let B : Pre :=
    { R := R
      host := H'
      sp := S
      Y_sigval := hSY
      auxiliaryFrame := hSA
      V_pos := hSV
      z_norm := hSz
      ccK_top := hcc
      BB_disj := hBB
      level_cond := by
        intro x hx
        have hx' : x ∈ insert (g 0) (insert (g 1) (insert p (insert p' ({T} : Finset ℕ)))) := hlv ▸ hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with h | h | h | h | h <;> rw [h]
        exacts [⟨hg 0, hgc 0⟩, ⟨hg 1, hgc 1⟩, ⟨hp, hpc⟩, ⟨hp', hpc'⟩, ⟨hT, hTcond⟩]
      Word := Bool
      u₀ := false
      hc := fun _ => P fun _ => false
      hcW := fun u _ => P fun _ => u
      hcW_base := rfl
      hcW_v := fun u _ => funext fun i => by rw [hPv, hPv]
      hcW_b := fun u _ => funext fun i => by rw [hPb, hPb]
      hcW_e := fun u _ => funext fun i => by rw [hPe, hPe]
      hcW_first := fun u _ h => by rw [hPu, hPu]; simp
      hcW_last := fun u _ h => by
        rw [hPu, hPu]
        have : ¬ (R.k - 1 = 0) := by omega
        simp [this]
      T := fun _ => T
      T_level := fun _ => by
        show T ∈ lv
        rw [hlv]; simp
      T_norm := fun _ => ⟨πT, hTK, hTn, hTc'⟩
      sp_T := hST
      cOf := fun _ => 1
      cOf_ne := fun _ => one_ne_zero
      cOf_eq := fun _ => by simp
      T_ne_pde := fun _ => ⟨(by omega : T ≠ p), (by omega : T ≠ p')⟩
      duStar := fun _ => 1
      duStar_pos := fun _ => one_pos
      Dstar := (T : ℝ) ^ ((R.f : ℝ) * R.k) * 4
      Dstar_pos := by positivity
      GamP := 2
      one_lt_gammaP := by norm_num
      T_win := fun _ => by
        rw [win_eq _ hT0 _ hfk]
        refine ⟨le_rfl, ?_⟩
        have : (0 : ℝ) ≤ 1 / ((R.f : ℝ) * R.k) * T := by positivity
        linarith }
  refine ⟨B, rfl, heq_of_eq hH, inferInstanceAs (Nontrivial Bool), ⟨?_⟩⟩
  exact
    { piG := π
      piG_K := hπK
      piG_norm := hπn
      piG_cong := hπc
      piT := fun _ => πT
      piT_K := fun _ => hTK
      piT_norm := fun _ => hTn
      piT_cong := fun _ => Ideal.mem_span_singleton.1 hTc'
      pde_split := ⟨(GlobalTheory.HostSplit.ncard_placesOver H'.E hp).symm.trans (hsplit _ hp hpc).1,
        (GlobalTheory.HostSplit.ncard_placesOver H'.E hp').symm.trans (hsplit _ hp' hpc').1⟩
      ccK_top := hcc
      e_even := fun j => UpperTheory.Host.muQ_const H' fun _ => ((P fun _ => false).e_int j).choose_spec
      hcW_inj := by
        have hne : Nonempty (Tau R) := Fintype.card_pos_iff.1 (by rw [card_Tau H']; exact hf)
        obtain ⟨τ⟩ := hne
        intro u u' h
        have h1 : (P fun _ => u).u ⟨1, by omega⟩ = (P fun _ => u').u ⟨1, by omega⟩ := by
          have h0 : (P fun _ => u) = (P fun _ => u') := congrFun h τ
          rw [h0]
        rw [hPu, hPu] at h1
        have h2 : ¬ (1 = R.k - 1) := by omega
        change u = u'
        cases u <;> cases u' <;> simp [h2] at h1 ⊢ <;> linarith
      a := a
      g_big := fun i => by
        show 2 * R.f * R.k < g i - 1
        fin_cases i
        · show _ < g 0 - 1; omega
        · show _ < g 1 - 1; omega
      T_gt := fun _ => by
        show 4 * (a : ℝ) < T
        exact_mod_cast (by omega : 4 * a < T)
      a_gt := by
        show ((2 * R.f * R.N R.m + 1 : ℕ) : ℝ) < 4 * (a : ℝ)
        exact_mod_cast (by omega : 2 * R.f * R.N R.m + 1 < 4 * a)
      spread_le := fun u j hj _ => by
        refine (hA u j hj).trans ?_
        show (A : ℝ) ≤ 2 * (a : ℝ)
        exact_mod_cast (by omega : A ≤ 2 * a) }

theorem exists_preX (hP : NormPrimes) (hS : SpacesExist) (R : Ranks) (hR : Nonempty (Host R)) :
    ∃ B : Pre, B.R = R ∧ Nontrivial B.Word ∧ Nonempty (PreX B) := by
  obtain ⟨H⟩ := hR
  obtain ⟨B, h1, -, h2⟩ := exists_preX_host hP hS R H
  exact ⟨B, h1, h2⟩

theorem exists_preX_some (hP : NormPrimes) (hS : SpacesExist) : ∃ B : Pre, Nontrivial B.Word ∧ Nonempty (PreX B) := by
  obtain ⟨B, -, h⟩ := exists_preX hP hS Formalism.BasicNotions.Examples₂.R0 (UpperTheory.Host.nonempty_host_over_cyclic_two_power _ rfl le_rfl)
  exact ⟨B, h⟩

theorem exists_preX_ranks (hP : NormPrimes) (R : Ranks) (hR : Nonempty (Host R)) :
    ∃ B : Pre, B.R = R ∧ Nontrivial B.Word ∧ Nonempty (PreX B) :=
  exists_preX hP spacesExist R hR

theorem exists_preX_two_words (hP : NormPrimes) : ∃ B : Pre, Nontrivial B.Word ∧ Nonempty (PreX B) :=
  exists_preX_some hP spacesExist

theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

theorem T_big (B : Pre) (X : PreX B) (u : B.Word) : 2 * B.R.f * B.R.N B.R.m + 1 < B.T u := by
  exact_mod_cast X.a_gt.trans (X.T_gt u)

theorem T_ne_g (B : Pre) (X : PreX B) (u : B.Word) (i : Fin 2) : B.T u ≠ B.host.g i := by
  intro h
  have h0 : B.host.g i ∣ B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (dvd_pow_self _ two_ne_zero)) _
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]
  obtain ⟨y, hy⟩ := (Nat.cast_dvd_cast (α := 𝓞 B.host.E) h0).trans (X.piT_cong u)
  let yb : 𝓞 B.host.E := RingOfIntegers.mapRingHom (B.host.conj : B.host.E →+* B.host.E) y
  have hyE : (X.piT u : B.host.E) = 1 + (B.host.g i : B.host.E) * (y : B.host.E) := by
    have h1 := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (sub_eq_iff_eq_add'.1 hy)
    simpa using h1
  have hn := X.piT_norm u
  rw [hyE, h, map_add, map_one, map_mul, map_natCast] at hn
  have hyb : (yb : B.host.E) = B.host.conj (y : B.host.E) := rfl
  have h2 : ((B.host.g i : ℕ) : 𝓞 B.host.E) ∣ ((1 : ℤ) : 𝓞 B.host.E) := by
    refine ⟨1 - y - yb - (B.host.g i : 𝓞 B.host.E) * y * yb, RingOfIntegers.ext ?_⟩
    push_cast
    rw [← hyb] at hn
    show (1 : B.host.E) = (B.host.g i : B.host.E) * (1 - (y : B.host.E) - (yb : B.host.E) - (B.host.g i : B.host.E) * (y : B.host.E) * (yb : B.host.E))
    linear_combination hn
  have h3 := Formalism.L2.Col.Primes.natCast_dvd_intCast h2
  have h4 : B.host.g i ∣ 1 := by exact_mod_cast h3
  exact (B.host.g_prime i).one_lt.ne' (Nat.dvd_one.1 h4)

theorem normPrimes : NormPrimes := GlobalTheory.Mem.ImaginaryQuadraticNorm.exists_norm_prime

theorem exists_preX_all_ranks (R : Ranks) (hR : Nonempty (Host R)) :
    ∃ B : Pre, B.R = R ∧ Nontrivial B.Word ∧ Nonempty (PreX B) :=
  exists_preX_ranks normPrimes R hR

theorem exists_preData_dyadicFrame (R : Ranks) (hφ : R.toFrame = Formalism.HC.cyclicFrame R.e) (he : 2 ≤ R.e) :
    ∃ B : Pre, B.R = R ∧ Nontrivial B.Word ∧ Nonempty (PreX B) :=
  exists_preX_all_ranks R (UpperTheory.Host.nonempty_host_over_cyclic_two_power R hφ he)

theorem tauLL_injective (B : Base) : Function.Injective B.tauLL := by
  intro τ τ' h
  have h1 : B.host.sigmaOf (τ : B.R.GG) = B.host.sigmaOf (τ' : B.R.GG) := by
    ext x
    have h2 := RingHom.congr_fun h x
    have h3 := B.embE.injective h2
    exact h3
  exact Subtype.ext ((B.host.gal).symm.injective h1)

theorem piG_ne_one (B : Pre) (X : PreX B) (i : Fin 2) : (X.piG i : B.host.E) ≠ 1 := by
  intro h
  have hn := X.piG_norm i
  rw [h, map_one, one_mul] at hn
  have : B.host.g i = 1 := by exact_mod_cast hn.symm
  exact (B.host.g_prime i).one_lt.ne' this

theorem sizes_nondeg (B : Pre) (X : PreX B) : 0 < X.a ∧ ∀ i, 2 * B.R.f * B.R.k + 1 < B.host.g i := by
  refine ⟨?_, fun i => by have := X.g_big i; omega⟩
  have h1 := X.a_gt
  have h2 : (0 : ℝ) ≤ ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalTheory.Mem.PreXModel

end
