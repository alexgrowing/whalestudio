import Mathlib
import Formalism.LocalToGlobal.Columns.ChainInst
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AtTypeClosed
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

def ranksFour : Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 4
  t := 17
  k_even := by decide
  m_even := by decide
  t_odd := by decide
  two_le_m := by decide
  m_add_three_le_k := by decide
  rank_add_five_le := by decide
  three_m_lt_t := by decide
  m_le_f := (by norm_num : 4 ≤ 2 * 2 ^ 2)
  f_le_k := (by norm_num : 2 * 2 ^ 2 ≤ 8)
  m_sq_le_N := by decide

section Gen
variable {X : Fields} {Pr : Primes X}

def powChars {m₀ : ℕ} (Ch : Chars X Pr (m₀ + 1)) (m : ℕ) : Chars X Pr m where
  psi0 := Ch.psi0
  chi j w := Ch.chi 0 w ^ (j.1 + 1)
  muVal _ := Ch.muVal 0
  etaVal := Ch.etaVal

theorem exists_unit (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) (a : (ZMod (Pr.g i))ˣ) :
    ∃ x : (𝓞 X.E ⧸ w.asIdeal)ˣ, (x : 𝓞 X.E ⧸ w.asIdeal) = (((a : ZMod (Pr.g i)).val : ℕ) : 𝓞 X.E ⧸ w.asIdeal) := by
  have hp := hPr.g_prime i
  haveI : NeZero (Pr.g i) := ⟨hp.ne_zero⟩
  have hq : qOf w = Pr.g i := ciQOf_eq hPr hw
  haveI : Finite (𝓞 X.E ⧸ w.asIdeal) := ciFinite (by rw [hq]; exact hp.ne_zero)
  haveI : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  let e : ZMod (Pr.g i) ≃+* (𝓞 X.E ⧸ w.asIdeal) :=
    ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, ciCard, hq])
  refine ⟨Units.map (e : ZMod (Pr.g i) →* (𝓞 X.E ⧸ w.asIdeal)) a, ?_⟩
  change e (a : ZMod (Pr.g i)) = _
  rw [← map_natCast e, ZMod.natCast_zmod_val]

theorem powChars_ok (hPr : Pr.Ok) {m₀ : ℕ} {Ch : Chars X Pr (m₀ + 1)} (hCh : Ch.Ok) {m : ℕ} (hm : ∀ i, 2 * m + 1 < Pr.g i) :
    (powChars Ch m).Ok := by
  have hom : ∀ i : Fin 2, ∃ om : (ZMod (Pr.g i))ˣ →* X.Kˣ, Function.Injective om ∧
      ∀ w : {w // w ∈ Pr.vGs}, w.1 ∈ Pr.vG i → ∀ (j : Fin m) (a : (ZMod (Pr.g i))ˣ) (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
        (x : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g i)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) →
        (powChars Ch m).chi j w x = om a ^ (2 * (j.1 + 1)) := by
    intro i
    obtain ⟨om, hi, h⟩ := hCh.chi_om i
    refine ⟨om, hi, fun w hw j a x hx => ?_⟩
    change (Ch.chi 0 w ^ (j.1 + 1)) x = _
    rw [MonoidHom.pow_apply, h w hw 0 a x hx, ← pow_mul]
    simp
  refine ⟨hCh.psi_zero_nontrivial_character, fun w j j' hjj => ?_, fun i w w' hw hw' j a x x' hx hx' => ?_, hCh.characterAgreesOnPlaces, hom⟩
  · obtain ⟨i, hi⟩ := ciVGs_cases w.2
    obtain ⟨om, hinj, h⟩ := hom i
    haveI : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
    obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (Pr.g i))ˣ)
    obtain ⟨x, hx⟩ := exists_unit hPr hi a
    have h1 : om a ^ (2 * (j.1 + 1)) = om a ^ (2 * (j'.1 + 1)) := by
      rw [← h w hi j a x hx, ← h w hi j' a x hx]
      exact DFunLike.congr_fun hjj x
    have ho : orderOf (om a) = Pr.g i - 1 := by
      rw [orderOf_injective om hinj, ha, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmi := hm i
    have hj := j.2
    have hj' := j'.2
    have h2 := pow_injOn_Iio_orderOf (x := om a) (by rw [ho, Set.mem_Iio]; omega) (by rw [ho, Set.mem_Iio]; omega) h1
    exact Fin.ext (by omega)
  · change (Ch.chi 0 w ^ (j.1 + 1)) x = (Ch.chi 0 w' ^ (j.1 + 1)) x'
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, hCh.chi_same i w w' hw hw' 0 a x x' hx hx']

theorem powChars_ne_one {m₀ m : ℕ} {Ch : Chars X Pr (m₀ + 1)} (h : (powChars Ch (m + 2)).Ok) (w : {w // w ∈ Pr.vGs}) :
    (powChars Ch (m + 2)).chi 0 w ≠ 1 := by
  intro h1
  have h2 : Ch.chi 0 w = 1 := by simpa [powChars] using h1
  have h3 : (0 : Fin (m + 2)) = 1 := h.chi_inj w (by simp [powChars, h2])
  simp at h3

def cstSym {R : Ranks} (Ch : Chars X Pr R.m) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) : LocCst X SB :=
  { ciCst Ch SB (fun _ _ => 1) with sharp := true, A := R.m }

theorem atType_of_ok (hX : X.Ok) (hPr : Pr.Ok) {R : Ranks} {Ch : Chars X Pr R.m} (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (σ₀ : X.K →+* ℂ)
    (P : rowSG Pr sel (mu0 X.F X.E X.K S₀)) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : X.E →+* k)
      (S : SymData k (R.m - 2) R.k), AtType Ch sel (mu0 X.F X.E X.K S₀) (cstSym Ch _) σ₀ P ι S := by
  have hP := ciMemG sel S₀ P
  have h2 := R.two_le_m
  have hc : (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S₀)) (fun _ _ => 1)).Ok :=
    ciCst_ok hPr hCh (fun Q hQ => ciMemG sel S₀ ⟨Q, hQ⟩) (fun Q hQ => h4 Q (ciMemG sel S₀ ⟨Q, hQ⟩))
  refine GlobalTheory.AtTypeExists.exists_atType X Pr R Ch sel S₀ _ _ σ₀ P _ hP (by omega)
    ⟨hc.psi_add, hc.psi_int, hc.psi_ne, hc.D_pos, hc.sq_sq, hc.M_pos, ?_, hc.M_le_B, hc.B_pos⟩ rfl le_rfl (fun a ha => ?_)
    (ciQ_notMem_sq hX hPr hP)
  · change 1 ≤ R.m
    omega
  · have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr hP).ne_zero
    change ciPsi Ch P _ = _
    unfold ciPsi
    rw [mul_div_cancel₀ _ hq0, if_pos ha]

end Gen

open Formalism.L2.Host in

theorem exists_closed_ok : ∃ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) (_ : Field k) (_ : ValuativeRel k)
    (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k),
    X.Ok ∧ Pr.Ok ∧ Ch.Ok ∧ X.f = R.f ∧ chiP Ch P.1 0 ≠ 1 ∧ 4 ≤ R.m ∧ AtType Ch sel mu cst σ₀ P ι S := by
  have hX := exampleFields_ok (cycQ nd2N) le_rfl
  have hPr := examplePrimes_ok (cycQ nd2N) le_rfl
  have hf : (nd2X (cycQ nd2N) le_rfl).f = ranksFour.f := exampleFields_degree _ _
  have h4 := primes_over_one_mod_four (cycQ nd2N) le_rfl
  have hg : ∀ i, 2 * 4 + 1 < (toyPrimes (cycQ nd2N) le_rfl).g i :=
    Fin.forall_fin_two.2 ⟨lt_trans (by norm_num) example_primes_gt_sixteen.1, lt_trans (by norm_num) example_primes_gt_sixteen.2⟩
  have h0 : ∃ Ch : Chars (nd2X (cycQ nd2N) le_rfl) (toyPrimes (cycQ nd2N) le_rfl) (1 + 1), Ch.Ok := exampleCharacters_exist _ _
  have σ₀ := toyComplexEmbedding (cycQ nd2N) le_rfl
  revert hX hPr hf h4 hg h0 σ₀
  generalize toyPrimes (cycQ nd2N) le_rfl = Pr
  revert Pr
  generalize nd2X (cycQ nd2N) le_rfl = X
  intro Pr hX hPr hf h4 hg h0 σ₀
  obtain ⟨Ch₀, hCh₀⟩ := h0
  have hCh : (powChars Ch₀ (2 + 2)).Ok := powChars_ok hPr hCh₀ hg
  obtain ⟨w, hw⟩ : (Pr.vG 0).Nonempty := Finset.card_pos.1 (by rw [hPr.vG_card 0, hf]; decide)
  have hw' : w ∈ Pr.vGs := by
    classical
    exact Finset.mem_union.2 (Or.inl hw)
  let P : rowSG Pr (fun _ => w) (mu0 X.F X.E X.K ∅) := ⟨w, by rw [ciRowSG]; exact hw'⟩
  obtain ⟨k, i1, i2, i3, i4, ι, S, hS⟩ := atType_of_ok hX hPr (R := ranksFour) (Ch := powChars Ch₀ (2 + 2)) hCh h4 (fun _ => w) ∅ σ₀ P
  refine ⟨X, Pr, ranksFour, powChars Ch₀ (2 + 2), _, _, _, _, σ₀, P, k, i1, i2, i3, i4, ι, _, S, hX, hPr, hCh, hf, ?_, le_rfl, hS⟩
  unfold chiP
  rw [dif_pos hw']
  exact powChars_ne_one hCh ⟨w, hw'⟩

end GlobalTheory.AtTypeClosed
