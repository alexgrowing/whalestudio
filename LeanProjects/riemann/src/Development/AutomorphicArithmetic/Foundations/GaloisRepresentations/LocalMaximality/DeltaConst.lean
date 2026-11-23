import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem delta_const' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) :
    deltaL ℂ ι E (fun J => if J.card = 1 then v else 0) = 0 := by
  funext t
  change ∑ i ∈ t, GlobalTheory.cubeSign t i • (if (t.erase i).card = 1 then v else 0) = 0
  by_cases h2 : t.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact le_rfl
        · exact h.le)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = -1 := by
        have : ({a, b} : Finset ι).filter (· < b) = {a} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · rfl
            · exact absurd h' (lt_irrefl _)
          · rintro rfl; exact ⟨Or.inl rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact h.le
        · exact le_rfl)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = -1 := by
        have : ({a, b} : Finset ι).filter (· < a) = {b} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · exact absurd h' (lt_irrefl _)
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : (t.erase i).card ≠ 1 := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i; simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i; simp [rgt, uni]

private theorem omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono (by
    rintro y ⟨b, hb, v, hv, rfl⟩
    exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩)

private theorem omB_smul' {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {q : ℕ} {r : L} (hr : r ∈ B)
    {m : DR ℂ L} (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [smul_smul]
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
  | smul z a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ z ha

private theorem mem_acxC' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left]

private theorem pk_zero {d : ℕ} {I : Finset (Fin (d + 1))} (h : 0 ∈ I) : pk I = 0 := by
  have hn : I.Nonempty := ⟨0, h⟩
  rw [pk, dif_pos hn]
  exact le_antisymm (I.min'_le 0 h) (Fin.zero_le _)

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem inv_mem_rB (I : Finset (Fin (d + 1))) {m : Fin (d + 1)} (hm : m ∈ I) :
    algebraMap F K' ((x 0 : F) / x m) ∈ rB ℂ K' (xv x) I :=
  (integralClosure (rA ℂ (xv x) I) K').algebraMap_mem ⟨(x 0 : F) / x m, Algebra.subset_adjoin ⟨m, hm, 0, rfl⟩⟩

private theorem prod_tt :
    ∏ l, tt K' x l = ∏ m : Fin (d + 1), algebraMap F K' ((x m : F) / x 0) := by
  rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, map_one, one_mul]
  rfl

private theorem prod_compl (I : Finset (Fin (d + 1))) :
    (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) * ∏ l, tt K' x l =
      ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0) := by
  rw [prod_tt, ← Finset.prod_mul_prod_compl I, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one, one_mul]
  intro m _
  rw [← map_mul, div_mul_div_comm, mul_comm (x 0 : F), div_self (mul_ne_zero (x m).ne_zero (x 0).ne_zero), map_one]

private theorem prod_X (I : Finset (Fin (d + 1))) :
    ∏ m ∈ I, algebraMap F K' (x m : F) =
      algebraMap F K' (x 0 : F) ^ I.card * ∏ m ∈ I, algebraMap F K' ((x m : F) / x 0) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

private theorem prod_tt_X :
    ∏ l : Fin d, algebraMap F K' (x l.succ : F) = algebraMap F K' (x 0 : F) ^ d * ∏ l, tt K' x l := by
  have : algebraMap F K' (x 0 : F) ^ d = ∏ _l : Fin d, algebraMap F K' (x 0 : F) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [tt, ← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

end

theorem yXi_of :
    MJ → ThT → DtBasic → SysBasic → RYBasic → OmLoc → YXi := by
  intro hMJ hTh hDt hSB hRY _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY h
  obtain ⟨hw, h1, h0, hL⟩ := hTh d K' (DR ℂ K') (sysY x j2 d)
  obtain ⟨τ, hτ⟩ := hY.covY.exists_isTop
  obtain ⟨-, hdt, hvol, hom, -⟩ := hDt F K' d x hY.covY τ hτ
  obtain ⟨hR0, -, hmono, -, -⟩ := hRY F K K' d x j2 hY
  obtain ⟨v, hv⟩ : ∃ v : DR ℂ K', v = (h : K') • vol0 ℂ K' (xv x) := ⟨_, rfl⟩
  let b : Finset (Fin (d + 1)) → DR ℂ K' := fun J => if J.card = 1 then v else 0
  let θ := detC (sysY x j2 d).rowT
  have hval : ∀ I J L, (sysY x j2 d).mj 0 θ b (uni (uni I J) L) =
      ((-1 : ℤ) ^ ((0 + 1) * L.card)) • (θ (uni I L) • b J) := by
    intro I J L
    simp only [Sys.mj, lft_uni', rgt_uni']
    rfl
  have hcore : ∀ (I : Finset (Fin (d + 1))) (j : Fin (d + 1)), 0 ∈ I →
      (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
    intro I j h0I
    have hle : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 I {j} := by
      have := hmono {0} I ∅ {j} (Finset.singleton_subset_iff.2 h0I) (Finset.empty_subset _)
      rwa [hR0] at this
    have hwm : (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) ∈ RY (xv x) j2 I {j} :=
      (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I {j})
        (Subalgebra.prod_mem _ fun m hm => inv_mem_rB x I hm)
    have hd : dtS K' x Finset.univ ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
      have := omB_mono' hle _ (hdt Finset.univ)
      simpa using this
    have e : (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v =
        (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) • (h : K') • dtS K' x Finset.univ := by
      rw [hvol, hom, hv, smul_smul, smul_smul, smul_smul, ← prod_compl]
      congr 1
      ring
    rw [e]
    exact omB_smul' hwm (omB_smul' (hle h.2) hd)
  refine ⟨(sysY x j2 d).mj 0 θ b, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [(hSB d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) (d + 2)).2.1]
    intro I J
    split_ifs with hIJ
    · refine (mem_acxC' _ _ _ _).2 fun L => ?_
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) ∈ _
      rw [hval]
      by_cases hJ : J.card = 1
      · rcases hL I L with hz | ⟨h0I, hc, ε, hε⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hJ
          have hcard : ((L.card : ℤ) = (d : ℤ) + 2 - I.card - ({j} : Finset (Fin (d + 1))).card) := by
            simp only [Finset.card_singleton]
            omega
          rw [if_pos hcard, pk_zero h0I]
          refine ⟨(((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v),
            Submodule.smul_of_tower_mem _ _ (hcore I j h0I), ?_⟩
          have hU : (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') = algebraMap F K' (x 0 : F) ^ L.card := by
            rw [Units.coe_prod, Finset.prod_congr rfl (g := fun _ => algebraMap F K' (x 0 : F))
              (fun l _ => by simp [Sys.u, n10, sysY]), Finset.prod_const]
          have hθ : θ (uni I L) = ε • (algebraMap F K' (x 0 : F) ^ L.card * ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) := by
            have hcc : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            rw [← hcc, ← prod_X]
            exact hε
          have hb : b {j} = v := if_pos (Finset.card_singleton j)
          change (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') • ((((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v)) = _
          rw [hU, hθ, hb, Units.smul_def, smul_assoc]
          simp only [mul_smul]
          rw [smul_comm (algebraMap F K' (x 0 : F) ^ L.card) ((-1 : ℤ) ^ ((0 + 1) * L.card)),
            smul_comm (algebraMap F K' (x 0 : F) ^ L.card) (ε : ℤ)]
      · have : b J = 0 := if_neg hJ
        simp [this]
    · refine (Submodule.mem_bot _).2 (funext fun L => ?_)
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) = 0
      rw [hval]
      by_cases hJ : J.card = 1
      · have hI : ¬ I.Nonempty := fun hI => hIJ ⟨hI, Finset.card_pos.1 (by omega)⟩
        rcases hL I L with hz | ⟨h0I, -⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · exact absurd ⟨0, h0I⟩ hI
      · have : b J = 0 := if_neg hJ
        simp [this]
  · exact hMJ d K' (DR ℂ K') (sysY x j2 d) (Fin d) (gT x j2) 0 θ b hw (delta_const' v) (fun J hJ => if_neg hJ)
  · funext s
    change (sysY x j2 d).mj 0 θ b (uni s ∅) = edge1 (locCoch ℂ K' (xv x) h) s
    simp only [Sys.mj, lft_uni', rgt_uni', edge1, Finset.card_empty, mul_zero, pow_zero, one_smul]
    by_cases hc : (rgt s).card = 1
    · rw [if_pos hc]
      have hb : b (rgt s) = v := if_pos hc
      rw [hb]
      by_cases hu : lft s = Finset.univ
      · have hθ : θ (uni Finset.univ ∅) = 1 := h1
        rw [hu, hθ, locCoch, if_pos rfl, hv]
        simp [sysY]
      · rw [locCoch, if_neg hu]
        rcases hL (lft s) ∅ with hz | ⟨-, hc', -⟩
        · have : θ (uni (lft s) ∅) = 0 := hz
          rw [this]
          simp [sysY]
        · exfalso
          apply hu
          apply Finset.eq_univ_of_card
          simpa using hc'
    · rw [if_neg hc]
      have hb : b (rgt s) = 0 := if_neg hc
      rw [hb, map_zero]
  · intro j
    rw [hval]
    have hb : b {j} = v := if_pos (Finset.card_singleton j)
    have hθ : θ (uni {0} Finset.univ) = ∏ l : Fin d, algebraMap F K' (x l.succ : F) := h0
    rw [hb, hθ, prod_tt_X, hv, hvol, hom, Finset.card_univ, Fintype.card_fin, zero_add, one_mul,
      ← Int.cast_smul_eq_zsmul K', smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

end UpperTheory.Gal.productCup_of_system
