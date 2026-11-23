import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEqAevalProd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K1V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SingleSmulFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem strictAnti_of_adjacent {f : Fin n → ℝ} (h : ∀ a b : Fin n, a.val + 1 = b.val → f b < f a) :
    StrictAnti f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m => exact Fin.strictAnti_iff_succ_lt.2 fun i => h _ _ (by simp)

theorem sub_le_abs_add {h c x y : ℝ} (hx : h ≤ |x|) (hy1 : -c ≤ y) (hy2 : y ≤ c) : h - c ≤ |x + y| := by
  have h1 := abs_sub_abs_le_abs_sub x (-y)
  rw [sub_neg_eq_add, abs_neg] at h1
  have h2 : |y| ≤ c := abs_le.2 ⟨hy1, hy2⟩
  linarith

theorem single_entry_int (s a : Fin n) : ∃ z : ℤ, (Pi.single s 1 : Fin n → ℝ) a = z := by
  rw [Pi.single_apply]; split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem three_add_le_gapBound (ε : Fin n → Bool) : 3 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ hNeed ε := by
  have h1 := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  have h2 : 2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε :=
    le_max_left _ _
  linarith

theorem shifted_weight_parameter {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {s c0 : Fin n} {ν : Fin n → ℝ}
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hGL : GapLap ε lam h)
    (hcone : InRootCone (ν - lowK ε (lam + Pi.single s 1)))
    (hbd : ∀ k, kirrPs k ν ≤ kirrPs k (lowK ε lam + Pi.single c0 1))
    (hdom : ∀ a b : Fin n, a < b → ε a = ε b → ν b ≤ ν a) :
    (∀ a, ∃ m : ℤ, (ν + rhoC ε - rhoN ε) a - ((n : ℝ) - 1) / 2 = (m : ℝ)) ∧
      StrictAnti (ν + rhoC ε - rhoN ε) ∧ GapAtLeast ε (ν + rhoC ε - rhoN ε) (h - 2) ∧
      hNeed ε < h - 2 + 2 ∧ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h - 2 ∧
      ν + rhoC ε - rhoN ε = (lam + Pi.single s 1) + (ν - lowK ε (lam + Pi.single s 1)) := by
  obtain ⟨hmono, hh, hN⟩ := hGL
  set γ := ν - lowK ε lam with hγ
  have hγβ : γ = Pi.single s 1 + (ν - lowK ε (lam + Pi.single s 1)) := by
    rw [hγ, lowestKType_add_single]; abel
  have heq' : ν + rhoC ε - rhoN ε = lam + γ := by rw [hγ]; unfold lowK; abel
  have heq : ν + rhoC ε - rhoN ε = (lam + Pi.single s 1) + (ν - lowK ε (lam + Pi.single s 1)) := by
    rw [heq', hγβ]; abel
  have hb0 : ∀ k, 0 ≤ kirrPs k γ := by
    intro k; rw [hγβ, rootCone_entry_int]
    linarith [(highestWeightVector_lift k s).1, partialSum_single_bounds hcone k]
  have hb1 : ∀ k, kirrPs k γ ≤ 1 := by
    intro k; rw [hγ, partialSum_sub]
    have := hbd k; rw [rootCone_entry_int] at this
    linarith [(highestWeightVector_lift k c0).2]
  have hent := aux_statement_19 hb0 hb1
  have hN1 := three_add_le_gapBound ε
  have hg0 : 0 ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  refine ⟨fun a => ?_, ?_, ?_, by linarith, by linarith, heq⟩
  · obtain ⟨m, hm⟩ := hint a
    obtain ⟨z1, hz1⟩ := single_entry_int s a
    obtain ⟨z2, hz2⟩ := rootCone_unitWeightSum_nat hcone a
    refine ⟨m + z1 + z2, ?_⟩
    rw [heq', hγβ]
    simp only [Pi.add_apply]
    rw [hz1, hz2]
    push_cast
    linarith
  · refine strictAnti_of_adjacent fun a b hab => ?_
    have hlt : a < b := Fin.lt_def.2 (by omega)
    by_cases hε : ε a = ε b
    · obtain ⟨h1, h2⟩ := rho_adjacent_same_sign hab hε
      have := hdom a b hlt hε
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith
    · have hl := hmono hlt
      have hg := hh a b hε
      rw [abs_of_pos (by linarith)] at hg
      rw [heq']
      simp only [Pi.add_apply]
      linarith [(hent a).1, (hent b).2]
  · intro a b hε
    rw [heq']
    simp only [Pi.add_apply]
    have := sub_le_abs_add (hh a b hε) (y := γ a - γ b) (c := 2)
      (by linarith [(hent a).1, (hent b).2]) (by linarith [(hent a).2, (hent b).1])
    convert this using 2
    ring

theorem k3V (n : ℕ) : QuotientHighestWeightTensorStandard n := by
  intro ε lam h H _ _ _ σ D E V s N _ _ EN φ x hσ hD hV hc hVK hint hmono hGL hp hq hmono' hEN hUN
    hφ hx hφx
  classical
  have hE : IsGlRep E := hD.glRep
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hKN : IsKUnitary ε EN := isKUnitary_of_isInfUnitary hUN
  have hK1 := k1V n ε lam h H σ D E V hσ hD hV hc hVK hint hmono hGL hp hq
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).1
  have hgen := (gen_statement n ε D E V hE hV.2.1).1
  have hT := tens_statement n D E hE
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = Xs (eeV E) (genSub E V) (thV lam s) := ⟨_, rfl⟩
  have hX0mem : ∀ f, f ∈ X0 ↔ (∀ c, f c ∈ genSub E V) ∧ eeV E f = ((thV lam s : ℝ) : ℂ) • f := by
    intro f; rw [hX0]; exact mem_eigenTensorSpace_gen_iff
  have hX0st : ∀ a b f, f ∈ X0 → tensV E a b f ∈ X0 := by
    rw [hX0]; exact fun a b f hf => eigenTensorSpace_stable hE a b hf
  rw [← hX0] at hx hK2
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ (Fin n → D), P = aeval (eeV E) (k3bP (thV lam) s) := ⟨_, rfl⟩
  have hPcomm : ∀ a b f, P (tensV E a b f) = tensV E a b (P f) := by
    rw [hP]; exact fun a b f => aeval_tensorAction_comm hE _ a b f
  have hPmem : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V := by
    rw [hP]; exact fun f hf => lagrange_mem_generated _ hf
  have hPX : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → P f ∈ X0 := by
    rw [hP, hX0]; exact fun f hf => lagrange_mem_eigenTensorSpace hK1 s hf
  have hPon : ∀ y ∈ X0, P y = (k3bP (thV lam) s).eval ((thV lam s : ℝ) : ℂ) • y := by
    rw [hP, hX0]; exact fun y hy => lagrange_on_eigenTensorSpace _ s hy
  have hθinj : Function.Injective (thV lam) := fun a b hab => hmono.injective (by unfold thV at hab; linarith)
  have hPne := lagrangeFactor_eval_ne_zero_of_injective hθinj s

  have hstart : ∃ u : Fin n → D, (∀ c, u c ∈ V) ∧ φ (P u) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : φ (P x) = 0 := generated_eigenspace_annihilate EN φ hφ P hPcomm hPmem hne (hgen x ((hX0mem x).1 hx).1)
    rw [hPon x hx, map_smul] at h0
    exact hφx ((smul_eq_zero.1 h0).resolve_left hPne)
  obtain ⟨u0, hu0V, hu0φ⟩ := hstart
  obtain ⟨piV, hpiV⟩ : ∃ piV : Submodule ℂ (Fin n → D), piV = Submodule.pi Set.univ (fun _ => V) :=
    ⟨_, rfl⟩
  have hpiV_mem : ∀ u, u ∈ piV ↔ ∀ c, u c ∈ V := fun u => by rw [hpiV]; simp [Submodule.mem_pi]
  have hpiVfd : FiniteDimensional ℂ piV := by rw [hpiV]; exact finiteDimensional_pi_submodule hV.1
  have hpiVst : IsKStableSub ε (tensV E) piV := by
    intro a b hab u hu
    rw [hpiV_mem] at hu ⊢
    intro c
    rw [entry_bounds_of_partialSum]
    refine V.add_mem (hV.2.1 a b hab _ (hu c)) ?_
    split_ifs
    · exact hu b
    · exact V.zero_mem
  have hpiVG : ∀ u ∈ piV, ∀ c, u c ∈ genSub E V := fun u hu c => le_generatedSubmodule ((hpiV_mem u).1 hu c)
  have hS0fd : FiniteDimensional ℂ (piV.map P) := inferInstance
  have hS0X : piV.map P ≤ X0 := by rintro _ ⟨u, hu, rfl⟩; exact hPX u (hpiVG u hu)
  have hS0st : IsKStableSub ε (tensV E) (piV.map P) := by
    rintro a b hab _ ⟨u, hu, rfl⟩
    rw [← hPcomm]
    exact Submodule.mem_map_of_mem (hpiVst a b hab u hu)

  have himg : ∀ S : Submodule ℂ (Fin n → D), S ≤ X0 → IsKStableSub ε (tensV E) S →
      IsKStableSub ε EN (S.map φ) := by
    rintro S hSX hSst a b hab _ ⟨f, hf, rfl⟩
    rw [← hφ a b f ((hX0mem f).1 (hSX hf)).1]
    exact Submodule.mem_map_of_mem (hSst a b hab f hf)
  have hcone : ∀ S : Submodule ℂ (Fin n → D), FiniteDimensional ℂ S → S ≤ X0 →
      IsKStableSub ε (tensV E) S → ∀ (W : Submodule ℂ N) (ν : Fin n → ℝ), W ≤ S.map φ →
      IsKIrrHW ε EN ν W → InRootCone (ν - lowK ε (lam + Pi.single s 1)) := by
    intro S hfd hSX hSst W ν hWS hW
    obtain ⟨w, hwW, hw0, hwK⟩ := hW.2.2.2
    obtain ⟨f0, hf0, hf0eq⟩ := Submodule.mem_map.1 (hWS hwW)
    obtain ⟨f, hfS, hfK, hff⟩ := partialSum_succ_alt hKD φ hfd hSst
      (fun a b _ g hg => hφ a b g ((hX0mem g).1 (hSX hg)).1) hf0 (by rw [hf0eq]; exact hwK)
    refine hK2 ν f (hSX hfS) ?_ hfK
    rintro rfl
    rw [map_zero, hf0eq] at hff
    exact hw0 hff.symm

  have hS0ne : (piV.map P).map φ ≠ ⊥ := by
    intro h0
    have : φ (P u0) ∈ (piV.map P).map φ :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem ((hpiV_mem u0).2 hu0V))
    rw [h0, Submodule.mem_bot] at this
    exact hu0φ this
  obtain ⟨W1, hW1S, ν1, hW1⟩ := exists_kIrreducible_highestWeight hEN hKN inferInstance (himg _ hS0X hS0st) hS0ne
  obtain ⟨w1, hw1W, hw10, hw1K⟩ := hW1.2.2.2
  obtain ⟨v1, hv1, hv1eq⟩ := Submodule.mem_map.1 (hW1S hw1W)
  obtain ⟨u1, hu1, rfl⟩ := Submodule.mem_map.1 hv1
  have hgP : ∀ a b, ε a = ε b → ∀ g ∈ piV, (φ ∘ₗ P) (tensV E a b g) = EN a b ((φ ∘ₗ P) g) := by
    intro a b _ g hg
    show φ (P (tensV E a b g)) = EN a b (φ (P g))
    rw [hPcomm]
    exact hφ a b _ (hPmem g (hpiVG g hg))
  have hyP : IsKHWVec ε EN ν1 ((φ ∘ₗ P) u1) := by
    show IsKHWVec ε EN ν1 (φ (P u1))
    rw [hv1eq]; exact hw1K
  obtain ⟨y, hyV, hyK, hyeq⟩ := partialSum_succ_alt hKD (φ ∘ₗ P) hpiVfd hpiVst hgP hu1 hyP
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : (φ ∘ₗ P) 0 = 0 := map_zero _
    rw [h0] at hyeq
    change 0 = φ (P u1) at hyeq
    rw [hv1eq] at hyeq
    exact hw10 hyeq.symm
  obtain ⟨c0, hc0⟩ := Function.ne_iff.1 hy0
  have hwt : ∀ a, E a a (y c0) = (((ν1 - Pi.single c0 1 : Fin n → ℝ) a : ℝ) : ℂ) • y c0 := by
    intro a
    have h1 := congrFun (hyK.1 a) c0
    rw [entry_bounds_of_partialSum, Pi.smul_apply] at h1
    by_cases hac : c0 = a
    · subst hac
      rw [if_pos rfl] at h1
      rw [Pi.sub_apply, Pi.single_eq_same, Complex.ofReal_sub, Complex.ofReal_one, sub_smul,
        one_smul, ← h1]
      abel
    · rw [if_neg hac, add_zero] at h1
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hac), sub_zero, h1]
  obtain ⟨u, huV, hu0, huK⟩ := hV.2.2.2
  have hbd1 : ∀ k, kirrPs k ν1 ≤ kirrPs k (lowK ε lam + Pi.single c0 1) := by
    intro k
    have := kirrPs_le hE hV huV hu0 huK (((hpiV_mem y).1 hyV) c0) hc0 hwt k
    rw [partialSum_sub] at this
    rw [rootCone_entry_int]; linarith

  let good : (Fin n → ℝ) → Prop := fun ν =>
    (∃ S : Submodule ℂ (Fin n → D), FiniteDimensional ℂ S ∧ S ≤ X0 ∧ IsKStableSub ε (tensV E) S ∧
      ∃ W ≤ S.map φ, IsKIrrHW ε EN ν W) ∧ ∀ k, kirrPs k ν ≤ kirrPs k (lowK ε lam + Pi.single c0 1)
  have hgoodL : ∀ ν, good ν →
      ∃ M : ℕ, kUnitWtLin ν = kUnitWtLin (lowK ε (lam + Pi.single s 1)) + M := by
    rintro ν ⟨⟨S, hfd, hSX, hSst, W, hWS, hW⟩, -⟩
    obtain ⟨M, hM⟩ := tensorAction_ofLp (hcone S hfd hSX hSst W ν hWS hW)
    exact ⟨M, by rw [unitWeightSum_sub] at hM; linarith⟩
  have hex : ∃ M : ℕ, ∃ ν, good ν ∧ kUnitWtLin ν = kUnitWtLin (lowK ε (lam + Pi.single s 1)) + M := by
    have hg1 : good ν1 := ⟨⟨piV.map P, hS0fd, hS0X, hS0st, W1, hW1S, hW1⟩, hbd1⟩
    obtain ⟨M, hM⟩ := hgoodL ν1 hg1
    exact ⟨M, ν1, hg1, hM⟩
  obtain ⟨ν0, ⟨⟨S1, hS1fd, hS1X, hS1st, W0, hW0S, hW0⟩, hbd0⟩, hL0⟩ := Nat.find_spec hex
  have hmin : ∀ ν, good ν → kUnitWtLin ν0 ≤ kUnitWtLin ν := by
    intro ν hg
    obtain ⟨M, hM⟩ := hgoodL ν hg
    have h1 := Nat.find_min' hex ⟨ν, hg, hM⟩
    have h2 : ((Nat.find hex : ℕ) : ℝ) ≤ M := by exact_mod_cast h1
    rw [hL0, hM]; linarith

  have hcone0 := hcone S1 hS1fd hS1X hS1st W0 ν0 hW0S hW0
  obtain ⟨w0, hw0W, hw00, hw0K⟩ := hW0.2.2.2
  have hdom : ∀ a b : Fin n, a < b → ε a = ε b → ν0 b ≤ ν0 a :=
    fun a b hab hε => highestWeight_dominant hEN hKN hw00 hw0K hab hε
  obtain ⟨hint'', hSA, hGap, hgN, hbig, heq⟩ := shifted_weight_parameter hint hGL hcone0 hbd0 hdom
  have hW0' : IsKIrrHW ε EN (lowK ε (ν0 + rhoC ε - rhoN ε)) W0 := by rw [lowestKType_shift_inv]; exact hW0

  have hsch : ∀ z ∈ Wm ε EN W0, phi EN 1 z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨z0', hz0W, hz00⟩ := hne
    have : FiniteDimensional ℂ (ncV ε W0 1) := finiteDimensional_ncV hW0.1 1
    have hfdW : FiniteDimensional ℂ (Wm ε EN W0) := Submodule.finiteDimensional_of_le Wm_le_ncV
    have hWst : IsKStableSub ε (bAct EN 1) (Wm ε EN W0) := Wm_kStable hEN hUN hW0'
    have hT'st : IsKStableSub ε EN ((Wm ε EN W0).map (phi EN 1)) := by
      rintro a b hab _ ⟨z, hz, rfl⟩
      rw [← phi_bAct hEN 1 hab z]
      exact Submodule.mem_map_of_mem (hWst a b hab z hz)
    have hT'ne : (Wm ε EN W0).map (phi EN 1) ≠ ⊥ := by
      intro h0
      have : phi EN 1 z0' ∈ (Wm ε EN W0).map (phi EN 1) := Submodule.mem_map_of_mem hz0W
      rw [h0, Submodule.mem_bot] at this
      exact hz00 this
    obtain ⟨W', hW'T, ν', hW'⟩ := exists_kIrreducible_highestWeight hEN hKN inferInstance hT'st hT'ne
    obtain ⟨w', hw'W, hw'0, hw'K⟩ := hW'.2.2.2
    obtain ⟨z0, hz0, hz0eq⟩ := Submodule.mem_map.1 (hW'T hw'W)
    obtain ⟨z1, hz1, -, hkhw1, hfz1⟩ := lift_khw (A := bAct EN 1) (bAct_isKUnitary hUN 1) (phi EN 1)
      (fun a b hab z => phi_bAct hEN 1 hab z) hfdW hWst hz0 (by rw [hz0eq]; exact hw'K)
    have hz10 : z1 ≠ 0 := by
      rintro rfl
      rw [map_zero, hz0eq] at hfz1
      exact hw'0 hfz1.symm
    obtain ⟨a, b, hab, -, hν'⟩ := Wm_khw hEN hUN hW0' hSA hGap hbig hz1 hz10 hkhw1
    rw [lowestKType_shift_inv] at hν'
    let S2 : Submodule ℂ (Fin n → D) := S1 ⊔ ⨆ a : Fin n, ⨆ b : Fin n, S1.map (tensV E a b)
    have hmapmem : ∀ a b z, z ∈ S1 → tensV E a b z ∈ S2 := fun a b z hz =>
      Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
        (Submodule.mem_map_of_mem hz)))
    have hS2fd : FiniteDimensional ℂ S2 := inferInstance
    have hS2X : S2 ≤ X0 := sup_le hS1X (iSup_le fun a => iSup_le fun b => by
      rintro _ ⟨z, hz, rfl⟩
      exact hX0st a b z (hS1X hz))
    have hS2st : IsKStableSub ε (tensV E) S2 := by
      intro c d hcd v hv
      have hle : S2 ≤ S2.comap (tensV E c d) := by
        refine sup_le (fun z hz => Submodule.mem_sup_left (hS1st c d hcd z hz))
          (iSup_le fun a => iSup_le fun b => ?_)
        rintro _ ⟨z, hz, rfl⟩
        show tensV E c d (tensV E a b z) ∈ S2
        have hcm := LinearMap.congr_fun (hT.1 c d a b) z
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hcm
        rw [sub_eq_iff_eq_add] at hcm
        rw [hcm]
        refine S2.add_mem (S2.sub_mem ?_ ?_) (hmapmem a b _ (hS1st c d hcd z hz))
        · split_ifs
          · exact hmapmem _ _ z hz
          · exact S2.zero_mem
        · split_ifs
          · exact hmapmem _ _ z hz
          · exact S2.zero_mem
      exact hle hv
    have hT'le : (Wm ε EN W0).map (phi EN 1) ≤ S2.map φ := by
      rintro _ ⟨z, hz, rfl⟩
      rw [sch_phi_one_apply]
      refine Submodule.sum_mem _ fun p _ => ?_
      have hzp : z (fun _ => p) ∈ W0 := mem_V_of_mem_ncV (Wm_le_ncV hz) _
      obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.1 (hW0S hzp)
      rw [← hfeq, ← hφ p.1 p.2 f ((hX0mem f).1 (hS1X hf)).1]
      exact Submodule.mem_map_of_mem (hmapmem _ _ f hf)
    have hgood' : good ν' := ⟨⟨S2, hS2fd, hS2X, hS2st, W', hW'T.trans hT'le, hW'⟩, fun k => by
      rw [hν', partialSum_sub]; linarith [partialSum_root_nonneg hab k, hbd0 k]⟩
    have hlt : kUnitWtLin ν' < kUnitWtLin ν0 := by
      rw [hν', unitWeightSum_sub, unitWeightSum_finset_sum hab]
      have hab' : (a : ℕ) < b := hab
      have : (0 : ℝ) < (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (b : ℕ) - (a : ℕ))
      linarith
    exact absurd (hmin ν' hgood') (not_le.2 hlt)

  have hcX : ∀ f ∈ X0, casimir (tensV E) f = ((casVal (lam + Pi.single s 1) : ℝ) : ℂ) • f := by
    intro f hf
    obtain ⟨hfG, hfe⟩ := (hX0mem f).1 hf
    have h1 : (fun c => casimir E (f c)) = ((casVal lam : ℝ) : ℂ) • f :=
      funext fun c => casimir_genSub hE hc (f c) (hfG c)
    rw [hT.2.2.1 f, hfe, h1, casimirValue_add_single]
    push_cast
    rw [add_smul, add_smul, mul_smul]
  have hcas0 : ∀ v ∈ W0, casimir EN v = ((casVal (lam + Pi.single s 1) : ℝ) : ℂ) • v := by
    intro v hv
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 (hW0S hv)
    rw [casimir_map_intertwiner EN φ hφ ((hX0mem f).1 (hS1X hf)).1, hcX f (hS1X hf), map_smul]

  have hsc := schmid_casimir n ε ν0 (h - 2) _ N EN W0 hEN hUN hW0 hsch hcas0 hint'' hSA hGap hgN hp hq
  have hreal : casVal (lam + Pi.single s 1) = casVal (ν0 + rhoC ε - rhoN ε) := by exact_mod_cast hsc
  have hβ0 := cone_norm n (lam + Pi.single s 1) (ν0 - lowK ε (lam + Pi.single s 1)) hmono'.antitone
    hcone0 (by rw [← heq]; unfold casVal at hreal; linarith)
  have hν0 : ν0 = lowK ε (lam + Pi.single s 1) := sub_eq_zero.1 hβ0
  refine ⟨W0, ?_, by rw [← hν0]; exact hW0, hcas0⟩
  rw [← hX0]
  exact hW0S.trans (Submodule.map_mono hS1X)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
