import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharC

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppFwdPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.RowDictPf
  PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW
  Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx Formalism.L2.SG.Pf.KppLoc Formalism.L2.SG.Pf.KppChar Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

theorem n_pos : 0 < X.B.I.n := by
  rw [X.n_eq, hrD D]
  omega

theorem Wq_of_smul {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hn : 0 < I.n) {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ IntAf I.F I.E)
    (h : ∀ y ∈ I.Lf, t • y ∈ Lq I w) : t ∈ Wq I w := by
  obtain ⟨m, c, -, hc⟩ := congW_exists hp hcard ht
  have hcy : ∀ y ∈ I.Lf, ((c : ℤ) : I.E ⊗[I.F] Af I.F) • y ∈ Lq I w := by
    intro y hy
    have h1 := (Lq I w).sub_mem (h y hy) (Wq_smul hc hy)
    rwa [sub_smul, sub_sub_cancel] at h1
  obtain ⟨b, hb⟩ := Formalism.L2.SG.Pf.RedBasicsPf.exists_redBasis I w hp hcard
  set i0 : Fin I.n := ⟨0, hn⟩
  have hv : iv I (∑ j, (((Pi.single i0 c : Fin I.n → ℤ) j : ℤ) : I.E) • b j) ∈ lamAf (F := I.F) (wLat0 I w) := by
    rw [iv_sum_int]
    have hs : ∑ j, (((Pi.single i0 c : Fin I.n → ℤ) j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
        ((c : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b i0) := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    rw [hs]
    exact hcy _ (Submodule.subset_span ⟨⟨b i0, hb.1 i0⟩, rfl⟩)
  have hdvd : (p : ℤ) ∣ c := by
    have := Formalism.L2.SG.Pf.RedBasicsPf.redBasis_indep I w hp hcard hb (Pi.single i0 c : Fin I.n → ℤ)
      (Formalism.L2.SG.Pf.RedBasicsPf.inter I w hv) i0
    simpa using this
  obtain ⟨k, rfl⟩ := hdvd
  have hcW : ((p * k : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_int k)
  have := (Wq I w).add_mem hc hcW
  simpa using this

private theorem congW_sub_mem_of_prime_residue_card {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} {c : ℕ}
    (h : CongW (w := w) p t (c : ZMod p)) : t - (c : I.E ⊗[I.F] Af I.F) ∈ Wq I w :=
  Wq_of_congW_zero hp hcard (by simpa using congW_sub h (congW_natCast (w := w) (p := p) c))

theorem ew_res (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) ∧
      sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I (wK X kv) := by
  have hp := D.host.g_prime kv.1
  have hcard := card_wK X kv
  have hn := n_pos X
  have : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  have hsI : sg X.B.I X.ew ∈ IntAf X.B.I.F X.B.I.E := by
    obtain ⟨m0, c, -, hc⟩ := congW_exists (w := wc X.B.I (wK X kv)) hp (card_wKc X kv) X.ew_int
    have h1 := sg_Wq hc
    rw [wc_wc, map_sub, sg_intCast] at h1
    have h2 := (IntAf X.B.I.F X.B.I.E).add_mem (Wq_int h1) (intCast_int c)
    simpa using h2
  have hA : 1 - X.ew - sg X.B.I X.ew ∈ Wq X.B.I (wK X kv) := by
    refine Wq_of_smul hp hcard hn ?_ ?_
    · exact (IntAf X.B.I.F X.B.I.E).sub_mem
        ((IntAf X.B.I.F X.B.I.E).sub_mem (IntAf X.B.I.F X.B.I.E).one_mem X.ew_int) hsI
    · intro y hy
      exact mL_le (level_mem_wB' X kv) (X.ew_full y hy)
  have key : ∀ ob : Bool, sg X.B.I X.ew - (if ob then 0 else 1) =
      -(1 - X.ew - sg X.B.I X.ew) - (X.ew - (if ob then 1 else 0)) := by
    intro ob
    cases ob <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  obtain ⟨m, hm⟩ := congW_exists (w := wK X kv) hp hcard X.ew_int
  have hmm : m * m = m := by
    have h1 := congW_mul X.ew_int hm hm
    rw [X.ew_idem] at h1
    exact congW_unique hp hcard hn h1 hm
  have h01 : m = 0 ∨ m = 1 := by
    have h1 : m * (m - 1) = 0 := by rw [mul_sub, mul_one, hmm, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hfin : ∀ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) →
      ∃ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) ∧
        sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I (wK X kv) := by
    intro ob hob
    refine ⟨ob, hob, ?_⟩
    rw [key ob]
    exact (Wq X.B.I (wK X kv)).sub_mem ((Wq X.B.I (wK X kv)).neg_mem hA) hob
  rcases h01 with h0 | h1
  · refine hfin false ?_
    have := congW_sub_mem_of_prime_residue_card hp hcard (c := 0) (by simpa [h0] using hm)
    simpa using this
  · refine hfin true ?_
    have := congW_sub_mem_of_prime_residue_card hp hcard (c := 1) (by simpa [h1] using hm)
    simpa using this

private theorem exists_conj_rhoX_JPred_of_mem_K2 (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      JPred D.R.k D.R.rS ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧
      ∃ t1 t2 : ZMod (D.host.g kv.1), CongW (w := wK X kv) (D.host.g kv.1) (argC X x) t1 ∧
        CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) (argC X x) t2 ∧
        t1 + t2 = phiJ D.R.k D.R.rS ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  have hp := D.host.g_prime kv.1
  have hcard := card_wK X kv
  have hn := n_pos X
  have hg := level_mem_wB' X kv
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩
  obtain ⟨ob, hew, hsew⟩ := ew_res X kv
  have hgr := gram X ob hg hew hsew
  obtain ⟨c, hc⟩ := exists_lifts hp hcard (fr_L X ob)
  have hcL : ∀ j, c j ∈ X.B.I.L := fun j => (hc j).1
  have hcq : ∀ j, fr X ob j - iv X.B.I (c j) ∈ Lq X.B.I (wK X kv) := fun j => (hc j).2
  have hgc := gram_lift (frd_L X ob) hgr hcq
  have hbc : IsRedBasis0 X.B.I (wK X kv) c :=
    isRedBasis_of_gram hp hcard X.n_eq.symm (frd_L X ob) hcL hgc
  obtain ⟨P0, Q0, hPQ, hQP, hconj⟩ := conj_basis hp hcard X.n_eq.symm (redBX X kv).hb hbc
  have hdd : (dM D.R.rS D.R.k ob : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      dM D.R.rS D.R.k ob = 1 := dM_sq ob
  have hPm : ∃ Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Pm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = P0 * dM D.R.rS D.R.k ob ∧
      ((Pm⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) =
        dM D.R.rS D.R.k ob * Q0 := by
    refine ⟨⟨P0 * dM D.R.rS D.R.k ob, dM D.R.rS D.R.k ob * Q0, ?_, ?_⟩, rfl, rfl⟩
    · rw [mul_assoc, ← mul_assoc (dM D.R.rS D.R.k ob), hdd, one_mul, hPQ]
    · rw [mul_assoc, ← mul_assoc Q0, hQP, one_mul, hdd]
  obtain ⟨Pm, hPm1, hPm2⟩ := hPm
  refine ⟨Pm, fun x hx => ?_⟩
  have hxK : (x : X.B.I.Gf) ∈ X.B.I.Kset := hx.1
  have hxi : (x : X.B.I.Gf)⁻¹ ∈ X.K2 := (Formalism.L2.SG.Closed.level_subgroup_is_group X).2.2.1 _ hx
  have hxiK : (x : X.B.I.Gf)⁻¹ ∈ X.B.I.Kset := hxi.1
  have hM : RedMatB X.B.I (wK X kv) (D.host.g kv.1) (redBX X kv).b (x : X.B.I.Gf)
      ((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [rhoX_apply]
    exact rhoB_spec (redBX X kv) x
  obtain ⟨N, hN⟩ := redMatB_exists X.B.I (wK X kv) hp hcard hbc hxK
  obtain ⟨N', hN'⟩ := redMatB_exists X.B.I (wK X kv) hp hcard hbc hxiK
  have hMN := hconj _ hxK _ N hM hN
  have hval : ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) =
      dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob := by
    rw [Units.val_mul, Units.val_mul, hPm1, hPm2]
    calc dM D.R.rS D.R.k ob * Q0 * ((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) * (P0 * dM D.R.rS D.R.k ob)
        = dM D.R.rS D.R.k ob * Q0 * (((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) * P0) * dM D.R.rS D.R.k ob := by
          simp only [mul_assoc]
      _ = dM D.R.rS D.R.k ob * (Q0 * P0) * N * dM D.R.rS D.R.k ob := by
          rw [hMN]
          simp only [mul_assoc]
      _ = dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob := by
          rw [hQP, mul_one]
  have hW := entry (frd_L X ob) hcL hcq hgc hxK hN
  have hW' := entry (frd_L X ob) hcL hcq hgc hxiK hN'
  have hJ := shape X ob hg hew hsew hp hcard hn hx hW
  have hJ' := shape X ob hg hew hsew hp hcard hn hxi hW'
  have hmul : N * N' = 1 := by
    have h1 := redMatB_mul X.B.I (wK X kv) hp hcard hcL hxK hN hN'
    rw [mul_inv_cancel] at h1
    exact redMatB_unique X.B.I (wK X kv) hp hcard X.n_eq.symm hbc h1 (redMatB_one X.B.I (wK X kv) hp c)
  have hinv := inv_super hJ hJ' hmul
  rw [hval]
  exact ⟨jPred_conj (hrD D) ob hJ, tW (D := D) ob N, tWc (D := D) ob N', congC X ob hew hxK hW,
    congCc X ob hsew hxK hW', sum_eq ob hinv⟩

theorem kppFwd_holds : KppFwd X := by
  have hs : D.R.m / 2 - 1 = D.R.rS := by
    have h1 := r_eq D
    have h2 := hrD D
    omega
  choose Pm hPm using exists_conj_rhoX_JPred_of_mem_K2 X
  choose ε hε1 hεP using exists_eps X
  have hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)} :=
    fun kv => eps_other X kv (hεP kv) (1 - kv.1) (other_ne kv.1)
  unfold KppFwd
  refine ⟨Pm, fun kv => psiK X (ε kv) (hε kv), fun kv => psiK_ne X (hε1 kv) (hεP kv) (hε kv), ?_⟩
  intro x hx
  rw [hs]
  choose t1 t2 h1 h2 h12 using fun kv => (hPm kv x hx).2
  refine ⟨fun kv => (hPm kv x hx).1, ?_⟩
  rw [quadratic_character_eq_additive X (x : X.B.I.Gf), chi_split X ε hε1 hεP hε (n_pos X) (argC_int X hx.1) t1 t2 h1 h2]
  exact Finset.prod_congr rfl fun kv _ => by rw [h12 kv]

end Formalism.L2.SG.Pf.KppFwdPf
