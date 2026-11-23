import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainDataGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfInvariant

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

theorem psi_add (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) * a)) (hb : IntAt P.1 ((qOf P.1 : X.E) * b)) :
    c.psi P (a + b) = c.psi P a * c.psi P b := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (hc.D_pos P)
  refine hc.psi_add P a b ?_ ?_ <;> rw [hk, pow_succ, mul_assoc]
  · exact (intAt_pow (intAt_nat _) _).mul ha
  · exact (intAt_pow (intAt_nat _) _).mul hb

theorem psi_add_int (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [psi_add hc P ha ((intAt_nat _).mul hb), hc.psi_int P b hb, mul_one]

theorem psi_mem (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) * a)) : c.psi P a ∈ Zmu X.K (qOf P.1) := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, psi_add hc P _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  exact mem_Zmu_of_pow (by rw [h, hc.psi_int P _ ha])

end Psi

section Til

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_tilH (hN : N = n + 1) (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal)
    (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) (v : Sp E N) :
    v ∈ localization₂ Q.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      prH E hN v ∈ localization₂ Q.asIdeal d.1.N ∧ IntAt Q (v (Br.iL hN)) := by
  subst hN
  have e : (DecoSet.tilH (ST := ST) rfl pi d).1 = d.1.til pi := DecoSet.til_val d hT hG
  rw [e]
  exact mem_localization_tilN Q d.1.N v

theorem comp_funLeft_mem {P : HeightOneSpectrum (𝓞 E)} {a c b : ℕ} (hc : c = 0) (ex : ℕ → ℕ) (B : Submodule (𝓞 E) (Sp E b))
    (x : HomE E a b) :
    x ∘ₗ LinearMap.funLeft E E (Fin.castAdd c) ∈ homS (LocE.lamY P (qOf P) a c ex) B ↔ x ∈ homS (stdAt E a P) B := by
  subst hc
  rw [lamY_zero]
  rfl

end Til

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem atNL_last (v : Sp X.E (R.N R.m)) : atNL X.E (R.N R.m) (R.N R.m - 1) v = v (Br.iL (N_m_succ R)) := by
  have h : R.N R.m - 1 < R.N R.m := (Br.iL (N_m_succ R)).2
  unfold atNL
  rw [dif_pos h]
  rfl

theorem good_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {n : ℕ} {y : Sp X.E n}
    (hy : (qOf P.1 : X.E) • y ∈ stdAt X.E n P.1) :
    Good P.1 {ξ : Sp X.E n →ₗ[X.E] X.E | InDual P.1 ξ} fun η => ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have h1 : ∀ η : Sp X.E n →ₗ[X.E] X.E, (∀ i, IntAt P.1 (η (Pi.single i 1))) →
      IntAt P.1 ((qOf P.1 : X.E) * ((epsSg : X.E) * η y)) := fun η h => by
    have := (inDual_iff η).2 h _ hy
    rw [map_smul, smul_eq_mul] at this
    rw [mul_left_comm]
    exact he.mul this
  unfold ftY
  simp only [if_pos hP]
  refine ⟨fun η h => (inDual_iff η).2 (ne_of_ite h), fun η z hz => ?_, fun η => ?_⟩
  · have hz' := (inDual_iff z).1 hz
    refine ite_eq_ite_zero (forall_congr' fun i => intAt_add_q (hz' i)) fun h => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add, mul_left_comm]
    exact psi_add_int hc P (h1 η h) (h1 z hz')
  · dsimp only
    split_ifs with h
    · exact psi_mem hc P (h1 η h)
    · exact zero_mem _

theorem good_fhat (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {n : ℕ} {f : Sp X.E n → X.K} (hf : ColFn P.1 f) :
    Good P.1 {ξ : Sp X.E n →ₗ[X.E] X.E | InDual P.1 ξ} (fhat sel mu cst P f) := by
  classical
  refine Good.sum _ fun y hy => (good_ftY sel mu cst hc P hP (mem_stdAt.2 fun i => ?_)).const_mul (hf.2.2 y)
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (Fintype.mem_piFinset.1 hy i)
  rw [Pi.smul_apply, ← hk, smul_eq_mul, pow_one, mul_div_cancel₀ _ qOf_ne_zero]
  exact intAt_nat k

theorem good_PhiTop {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    Good P (homS (LocE.lamY P (qOf P) (R.N (m2 + 1)) (cOf R (m2 + 1)) fun i => i + 1) (stdAt X.E (R.N R.m - 1) P))
      (PhiTop Ch mu sharp m2 P) := by
  have h1 : R.k ≤ R.N (m2 + 1) := Nat.le_add_right _ _
  have h3 : R.r + (R.m - 1) * R.t = R.N (m2 + 1) + cOf R (m2 + 1) := by
    unfold Ranks.r Ranks.N cOf
    rw [hm, show m2 + 2 - 1 = m2 + 1 from rfl, mul_add (m2 + 1)]
    omega
  have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
    unfold Ranks.N cOf
    rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
    omega
  rw [← lamY_zero fun i => i + 1]
  unfold PhiTop
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 (by omega) h3 h4
  · exact good_PhiG _ _ h1 (by omega) h3 h4

theorem good_omPhi {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {hal : AutY X R m2}
    (hh : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N m2) (cOf R m2) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (m2 + 1)) (cOf R (m2 + 1)) fun i => i + 1)) (omPhi Ch sel mu cst m2 P hal 1) := by
  have h1 : R.k ≤ R.N m2 := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (m2 + 1) := Nat.le_add_right _ _
  have h3 : R.r + (m2 + 1 - 1) * R.t = R.N m2 + cOf R m2 := by
    unfold Ranks.r Ranks.N cOf
    rw [hm, Nat.add_sub_cancel, mul_add m2]
    omega
  have h4 : R.N m2 + cOf R m2 ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
    unfold Ranks.N cOf
    rw [hm, add_mul m2]
    omega
  unfold lamYat at hh
  rw [if_pos hP] at hh
  refine good_om ?_ _ _ _ hh
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

theorem cOf_pen {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R m2 = 1 := by
  unfold cOf
  omega

theorem cOf_top {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

theorem good_PsiAt {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {hal : AutY X R m2}
    (hh : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1)) (y : Sp X.E (R.N (m2 + 1))) :
    Good P.1 (homS (stdAt X.E (R.N m2) P.1) (stdAt X.E (R.N (m2 + 1)) P.1)) fun x₀ => PsiAt Ch sel mu cst m2 P hal x₀ y := by
  have h := good_omPhi Ch sel mu cst hm P hP hh
  refine ⟨fun x hx => ((joinCol_mem (cOf_pen hm) (cOf_top hm) _ _).1 (h.1 _ hx)).1, fun x z hz => ?_, fun x => h.2.2 _⟩
  have := h.2.1 (joinCol x y) (joinCol z 0) ((joinCol_mem (cOf_pen hm) (cOf_top hm) _ _).2 ⟨hz, by simp⟩)
  rw [← joinCol_add, smul_zero, add_zero] at this
  exact this

theorem splitAt {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {hal : AutY X R m2}
    (hh : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1)) : SplitAt Ch sel mu cst m2 P hal := by
  have h := good_omPhi Ch sel mu cst hm P hP hh
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  refine ⟨fun x => by rw [PsiAt, joinCol_restr (cOf_pen hm) (cOf_top hm)], ?_⟩
  obtain ⟨ι, _, a, f, hf, hs⟩ := exists_split (P := P.1) (PsiAt Ch sel mu cst m2 P hal)
    (fun x y hx => ((joinCol_mem (cOf_pen hm) (cOf_top hm) _ _).1 (h.1 _ hx)).2) fun x y z hz => by
      have := h.2.1 (joinCol x y) (joinCol 0 ((qOf P.1 : X.E)⁻¹ • z)) ((joinCol_mem (cOf_pen hm) (cOf_top hm) _ _).2
        ⟨fun _ _ => zero_mem _, by rwa [smul_inv_smul₀ hq]⟩)
      rw [← joinCol_add, smul_zero, add_zero, smul_inv_smul₀ hq] at this
      exact this
  exact ⟨ι, inferInstance, fun i x₀ => PsiAt Ch sel mu cst m2 P hal x₀ (a i), f,
    fun i => (fnModAt_iff _ _ _).2 (good_PsiAt Ch sel mu cst hm P hP hh _), hf, hs⟩

theorem fnMod_topDatum (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    {f : Sp X.E (R.N (m2 + 1)) → X.K} (hf : ColFn P.1 f) : FnMod P.1 (topDatum Ch sel mu cst m2 P f) := by
  refine (fnModAt_iff _ _ _).2 ((good_PhiTop Ch mu hm cst.sharp hP).mul (good_fhat sel mu cst hc P hP hf)
    (fun x => prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))
    (fun x => atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x) (fun x z => ?_) (fun x z => ?_) fun w => ?_)
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · rw [LinearMap.comp_add, LinearMap.comp_smul]
  · rw [← LinearMap.comp_assoc, comp_funLeft_mem (cOf_top hm)]
    have key : ∀ v : Sp X.E (R.N R.m), v ∈ stdAt X.E _ P.1 ↔
        prXp X.E R v ∈ stdAt X.E (R.N R.m - 1) P.1 ∧ IntAt P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) v) := fun v => by
      rw [atNL_last]
      exact mem_stdAt_succ (N_m_succ R)
    exact ⟨fun h => ⟨fun y hy => ((key _).1 (h y hy)).1, fun y hy => ((key _).1 (h y hy)).2⟩,
      fun h y hy => (key _).2 ⟨h.1 y hy, h.2 y hy⟩⟩

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  rw [dif_pos hP]
  exact (liftFr_spec p.deco.2 ⟨P.1, hP⟩).1 x

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (x : Sp X.E (R.N j)) : (frsF sel mu p P).symm x ∈ stdAt X.E (R.N j) P.1 ↔ x ∈ localization₂ P.1.asIdeal p.deco.1.N := by
  rw [← frsF_mem sel mu p P hP, LinearEquiv.apply_symm_apply]

theorem fnModAt_facPen {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2)
    (hh : L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1)) {u : Pr.Word} (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) :
    FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P) := by
  refine (fnModAt_iff _ _ _).2 ((good_PsiAt Ch sel mu cst hm P hP hh _).comp (inFr (frsF sel mu p₀ P) (frsF sel mu p P))
    (fun x z => ?_) fun w => ⟨fun h y hy => ?_, fun h y hy => ?_⟩)
  · unfold inFr
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · exact (frsF_symm_mem sel mu p P hP _).2 (h _ ((frsF_mem sel mu p₀ P hP y).2 hy))
  · have := (frsF_symm_mem sel mu p P hP _).1 (h _ ((frsF_symm_mem sel mu p₀ P hP y).2 hy))
    simpa using this

theorem q_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) : (qOf P.1 : X.E) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_pos hP] at h1 h2
  simp only [zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul] at h1 h2
  have h3 := add_mem (smul_mem_locP (intAt_nat (qOf P.1)) h2) h1
  rwa [← smul_add, sub_add_cancel] at h3

theorem fnModAt_facTop (hPr : Pr.Ok) (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    {u : Pr.Word} (hu : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) (p : ChPt (R := R) sel mu u (m2 + 1))
    (d : RowPt Pr R sel mu) {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) :
    FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P) := by
  have hy : (qOf P.1 : X.E) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, frsF_symm_mem sel mu p P hP]
    exact q_smul_repY sel mu cst hY P hP
  refine (fnModAt_iff _ _ _).2 ((good_PhiTop Ch mu hm cst.sharp hP).mul (good_ftY sel mu cst hc P hP hy)
    (fun x => (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))
    (fun x => (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
    (fun x z => ?_) (fun x z => ?_) fun w => ?_)
  · simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp (qOf P.1 : X.E), LinearMap.comp_smul]
  · rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, comp_funLeft_mem (cOf_top hm)]
    have h0 : ((Pr.piT u : 𝓞 X.E) : X.E) ≠ 0 := fun h => hu P (by
      rw [show Pr.piT u = 0 from RingOfIntegers.ext h]
      exact zero_mem _)
    have key : ∀ v : Sp X.E (R.N R.m), v ∈ localization₂ P.1.asIdeal (tilQ sel mu u d).1.N ↔
        (d.1.liftFr P).symm (prXp X.E R v) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) v) := fun v => by
      rw [atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply]
      refine (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 v).trans (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
      · rw [inv_mul_eq_div]
        exact h.div_of_notMem (hu P)
      · have := (IntAt.coe P.1 (Pr.piT u)).mul h
        rwa [← mul_assoc, show algebraMap (𝓞 X.E) X.E (Pr.piT u) = ((Pr.piT u : 𝓞 X.E) : X.E) from rfl,
          mul_inv_cancel₀ h0, one_mul] at this
    refine ⟨fun h => ⟨fun y hy => ((key _).1 (h _ ((frsF_mem sel mu p P hP y).2 hy))).1,
      fun y hy => ((key _).1 (h _ ((frsF_mem sel mu p P hP y).2 hy))).2⟩, fun h y hy => ?_⟩
    have hy' := (frsF_symm_mem sel mu p P hP y).2 hy
    rw [← (frsF sel mu p P).apply_symm_apply y]
    exact (key _).2 ⟨h.1 _ hy', h.2 _ hy'⟩

end Chain

theorem chainDataGuarded : ChainDataGuarded := fun _ _ _ Ch sel _ mu cst _ hPr hc hm P hP =>
  ⟨fun _ hh => splitAt Ch sel mu cst hm P hP hh, fun _ hf => good_fhat sel mu cst hc P hP hf,
    fun _ hf => fnMod_topDatum Ch sel mu cst hc hm P hP hf,
    fun L al hh _ p₀ p Y _ => fnModAt_facPen Ch sel mu cst hm P hP L al hh p₀ p Y,
    fun _ hu p d _ hY => fnModAt_facTop Ch sel mu cst hPr hc hm P hP hu p d hY⟩

end GlobalTheory.LastSteps
