import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReduction

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx.TwLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_mul (P : HeightOneSpectrum (𝓞 E)) (c : E) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e * c) := by
  by_cases hc : c = 0
  · refine ⟨0, fun e _ => ?_⟩
    rw [hc, mul_zero]
    simpa using Formalism.L2.Col.IntAt.coe P 0
  have h0 : P.valuation E c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  refine ⟨(WithZero.log (P.valuation E c)).toNat, fun e he => ?_⟩
  have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
  have hv : P.valuation E (algebraMap (𝓞 E) E e * c) ≤ 1 := by
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
    have hK := Int.self_le_toNat (WithZero.log (P.valuation E c))
    calc P.intValuation e * P.valuation E c
        ≤ WithZero.exp (-((WithZero.log (P.valuation E c)).toNat : ℤ)) * P.valuation E c := by gcongr
      _ = WithZero.exp (-((WithZero.log (P.valuation E c)).toNat : ℤ) + WithZero.log (P.valuation E c)) := by
          rw [WithZero.exp_add, WithZero.exp_log h0]
      _ ≤ 1 := by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          omega
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

variable [StarRing E] {n : ℕ}

theorem exists_smul_of_mem_locP {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {v : Sp E n}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : ∃ l : E, ∃ x ∈ N, v = l • x := by
  obtain ⟨s, hs, h⟩ := (mem_locP P N v).1 hv
  have hs0 : s ≠ 0 := fun e => hs (e ▸ P.asIdeal.zero_mem)
  have hs1 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hs0
  refine ⟨(algebraMap (𝓞 E) E s)⁻¹, s • v, h, ?_⟩
  rw [← algebraMap_smul E s v, inv_smul_smul₀ hs1]

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (c : T → E) (a : T → Sp E n)
    (ha : ∀ P, ∃ l : E, ∃ x ∈ N, a P = l • x) :
    ∃ y : Sp E n, ∀ P : T, c P • (y - a P) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  classical
  choose l x hx hax using ha
  choose K hK using fun P P' : T => exists_pow_intAt_mul P'.1 (c P' * l P)
  have he : ∀ P : T, ∃ e : 𝓞 E, ∀ P' : T, e - (if P = P' then 1 else 0) ∈ P'.1.asIdeal ^ (∑ P'' : T, K P'' P') := by
    intro P
    obtain ⟨e, he⟩ := exists_forall_sub_mem_ideal (s := (Finset.univ : Finset T)) (fun Q : T => Q.1.asIdeal)
      (fun Q : T => ∑ P'' : T, K P'' Q) (fun Q _ => Q.1.prime)
      (fun Q _ Q' _ hne h => hne (Subtype.ext (HeightOneSpectrum.ext h))) (fun Q => if P = Q.1 then 1 else 0)
    exact ⟨e, fun P' => he P' (Finset.mem_univ _)⟩
  choose e he using he
  refine ⟨∑ P, (algebraMap (𝓞 E) E (e P) * l P) • x P, fun P0 => ?_⟩
  have hsum : (∑ P, (algebraMap (𝓞 E) E (e P) * l P) • x P) - a P0 =
      ∑ P, (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) • x P := by
    symm
    have h1 : ∀ P, (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) • x P =
        (algebraMap (𝓞 E) E (e P) * l P) • x P - (if P = P0 then l P0 • x P0 else 0) := by
      intro P
      split_ifs with hP
      · subst hP
        rw [map_sub, map_one, _root_.sub_mul, one_mul, sub_smul]
      · rw [sub_zero, sub_zero]
    rw [Finset.sum_congr rfl (fun P _ => h1 P), Finset.sum_sub_distrib, hax P0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun P _ => ?_
  rw [smul_smul]
  have e1 : c P0 * (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) =
      algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * (c P0 * l P) := by ring
  rw [e1]
  exact GlobalTheory.TopStep.smul_mem_locP (hK P P0 _ (Ideal.pow_le_pow_right
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ P)) (he P P0)))
    (Formalism.L2.Col.le_locP _ _ (hx P))

end Local

end GlobalTheory.Mem.Col2.ChEx.TwLift

namespace GlobalTheory.Mem.Col2.ChEx.TwLift

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {u : Pr.Word} {j : ℕ}

open Classical in

theorem frsF_mem (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  rw [dif_neg hP]
  exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x

theorem frsF_symm_mem (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (v : Sp X.E (R.N j)) :
    (frsF sel mu p P).symm v ∈ stdAt X.E (R.N j) P.1 ↔ v ∈ p.deco.1.at P.1 := by
  rw [← frsF_mem p P hP, LinearEquiv.apply_symm_apply]

open Classical in

theorem cosetIn_eq {cst : LocCst X (rowSG Pr sel mu)} (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : q.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))})
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    cosetIn q P = {z | ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1} := by
  ext z
  simp only [cosetIn, if_neg hP, hY, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y0, hy0, hz⟩
    have h1 := (mem_locLat _ _ _ _).1 hy0 P
    rw [if_neg hP, zpow_natCast] at h1
    have h2 := (frsF_symm_mem q.1.1 P hP _).2 h1
    rw [map_smul, map_sub] at h2
    have e : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y) =
        ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y0) +
          ((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu q.1.1 P).symm y0 - (frsF sel mu q.1.1 P).symm y) := by
      rw [← smul_add]
      congr 1
      abel
    rw [e]
    exact add_mem hz h2
  · intro hz
    exact ⟨y, by rw [sub_self]; exact zero_mem _, hz⟩

end Pt

theorem exists_ptAt_bar_cq_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (p : ChPt (R := R) sel mu u j), ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r' = GlobalTheory.Mem.Col2.ChEx.cqOf r := by
  intro X Pr R sel S mu cst u j hQ r p
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := r.mem_ybSet h
    have hyG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : X.E) • y ∈ r.1.1.deco.1.at P.1 := fun P hP => by
      have h1 := (mem_locLat _ _ _ _).1 hy P
      rwa [if_pos hP, _root_.zpow_neg_one, inv_inv] at h1
    have hyQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M) • y ∈ r.1.1.deco.1.at P.1 := fun P hP => by
      have h1 := (mem_locLat _ _ _ _).1 hy P
      rwa [if_neg hP, _root_.zpow_neg, inv_inv, zpow_natCast] at h1
    choose xw hxN hxv using fun w : Pr.vGs => p.deco.2.be_surj w (r.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y))
    let a : rowSG Pr sel mu → Sp X.E (R.N j) := fun P =>
      if hP : P.1 ∈ Pr.vGs then (((qOf P.1 : ℕ) : X.E))⁻¹ • xw ⟨P.1, hP⟩ else frsF sel mu p P ((frsF sel mu r.1.1 P).symm y)
    let c : rowSG Pr sel mu → X.E := fun P => ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹
    have haG : ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), a P = (((qOf P.1 : ℕ) : X.E))⁻¹ • xw ⟨P.1, hP⟩ := fun P hP => dif_pos hP
    have haQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → a P = frsF sel mu p P ((frsF sel mu r.1.1 P).symm y) := fun P hP => dif_neg hP
    have hQa : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M) • a P ∈ p.deco.1.at P.1 := fun P hP => by
      rw [haQ P hP, ← map_smul, frsF_mem p P hP, ← map_smul, frsF_symm_mem r.1.1 P hP]
      exact hyQ P hP
    have ha : ∀ P, ∃ l : X.E, ∃ x ∈ p.deco.1.N, a P = l • x := fun P => by
      by_cases hP : P.1 ∈ Pr.vGs
      · exact ⟨_, _, hxN _, haG P hP⟩
      · obtain ⟨l, x, hx, e⟩ := exists_smul_of_mem_locP (hQa P hP)
        refine ⟨((qOf P.1 : X.E) ^ cst.M)⁻¹ * l, x, hx, ?_⟩
        rw [mul_smul, ← e, inv_smul_smul₀ (pow_ne_zero _ GlobalTheory.TopStep.qOf_ne_zero)]
    obtain ⟨y', hy'⟩ := exists_approx (rowSG Pr sel mu) p.deco.1.N c a ha
    have hy'G : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → y' - a P ∈ p.deco.1.at P.1 := fun P hP => by
      have h1 := hy' P
      simp only [c, if_pos hP, pow_zero, inv_one, one_smul] at h1
      exact h1
    have hy'Q : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y' - a P) ∈ p.deco.1.at P.1 := fun P hP => by
      have h1 := hy' P
      simp only [c, if_neg hP] at h1
      exact h1
    have eG : ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), ((qOf P.1 : ℕ) : X.E) • y' =
        xw ⟨P.1, hP⟩ + ((qOf P.1 : ℕ) : X.E) • (y' - a P) := fun P hP => by
      rw [haG P hP, smul_sub, smul_inv_smul₀ GlobalTheory.TopStep.qOf_ne_zero, add_sub_cancel]
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    refine ⟨⟨(p, {z | z - y' ∈ locLat (rowSG Pr sel mu) p.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩,
      rfl, ?_, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (mem_locLat _ _ _ _).2 fun P => ?_, rfl⟩
      by_cases hP : P.1 ∈ Pr.vGs
      · rw [if_pos hP, _root_.zpow_neg_one, inv_inv]
        show _ ∈ p.deco.1.at P.1
        rw [eG P hP]
        exact add_mem (Formalism.L2.Col.le_locP _ _ (hxN _)) (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G P hP))
      · rw [if_neg hP, _root_.zpow_neg, inv_inv, zpow_natCast]
        show _ ∈ p.deco.1.at P.1
        have e : ((qOf P.1 : X.E) ^ cst.M) • y' = ((qOf P.1 : X.E) ^ cst.M) • a P +
            ((qOf P.1 : X.E) ^ cst.M * (qOf P.1 : X.E) ^ cst.M) • (((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y' - a P)) := by
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ GlobalTheory.TopStep.qOf_ne_zero), mul_one, smul_sub, add_sub_cancel]
        rw [e]
        exact add_mem (hQa P hP) (GlobalTheory.TopStep.smul_mem_locP
          ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _)) (hy'Q P hP))
    · funext w
      have hw := hG w
      have hmem : ((qOf w.1 : ℕ) : X.E) • y' ∈ p.deco.1.at w.1 := by
        rw [eG ⟨w.1, hw⟩ w.2]
        exact add_mem (Formalism.L2.Col.le_locP _ _ (hxN _))
          (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2))
      have key : p.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y') = r.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) := by
        rw [eG ⟨w.1, hw⟩ w.2, p.deco.2.be_add w _ (Formalism.L2.Col.le_locP _ _ (hxN _)) _
          (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2)),
          GlobalTheory.TopStep.be_smul_int p.deco.2 w (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2), GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul,
          add_zero]
        exact hxv w
      refine (MemChart.CosetLift.coset_be p.deco _ w hw _ (if_pos w.2) hmem).trans ?_
      rw [key, MemChart.bar, hY]
      exact (MemChart.CosetLift.coset_be r.1.1.deco _ w hw _ (if_pos w.2) (hyG ⟨w.1, hw⟩ w.2)).symm
    · funext P
      have hP : (⟨P.1, Finset.mem_union_right _ P.2⟩ : rowSG Pr sel mu).1 ∉ Pr.vGs := hQ P.1 P.2
      unfold GlobalTheory.Mem.Col2.ChEx.cqOf
      rw [cosetIn_eq r hY _ hP]
      refine (cosetIn_eq _ (y := y') ?_ _ hP).trans ?_
      · rfl
      set P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
      set cM : X.E := ((qOf P'.1 : X.E) ^ cst.M)⁻¹
      have key : cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) ∈ stdAt X.E (R.N j) P'.1 := by
        have e1 : (frsF sel mu r.1.1 P').symm y = (frsF sel mu p P').symm (a P') := by
          rw [haQ P' hP, LinearEquiv.symm_apply_apply]
        rw [e1, ← map_sub, ← map_smul, frsF_symm_mem p P' hP]
        exact hy'Q P' hP
      ext z
      simp only [Set.mem_setOf_eq]
      have e : cM • (z - (frsF sel mu r.1.1 P').symm y) =
          cM • (z - (frsF sel mu p P').symm y') + cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) := by
        rw [← smul_add]
        congr 1
        abel
      constructor
      · intro hz
        change cM • (z - (frsF sel mu r.1.1 P').symm y) ∈ stdAt X.E (R.N j) P'.1
        rw [e]
        exact add_mem hz key
      · intro hz
        change cM • (z - (frsF sel mu p P').symm y') ∈ stdAt X.E (R.N j) P'.1
        have e2 : cM • (z - (frsF sel mu p P').symm y') = cM • (z - (frsF sel mu r.1.1 P').symm y) -
            cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) := by
          rw [e, add_sub_cancel_right]
        rw [e2]
        exact sub_mem hz key
  · have hY : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(p, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_, ?_⟩
    · funext w
      simp [MemChart.bar, hY]
    · funext P
      simp [GlobalTheory.Mem.Col2.ChEx.cqOf, cosetIn, hY]

end GlobalTheory.Mem.Col2.ChEx.TwLift
