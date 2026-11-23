import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerTimesMonomial

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_isSt_Ican {N r : ℕ} [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt ν (Ican ν) := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  have hlast : ν (Fin.last N) 0 = be := by
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [Ican_eq H, if_neg]
    intro h
    exact hc (mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) (by rw [hlast]; exact h.2))
  · intro c
    rw [Ican_eq H, pEnd_eq]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2, Finset.card_univ, Fintype.card_fin]
      · rw [if_neg fun h => h2 h.2, colH_none fun m => by rw [H.fin]; omega, Finset.card_empty]
    · rw [if_neg h1, if_neg fun h => h1 h.1, colH_all fun m => by rw [H.fin]; omega, Finset.card_empty]
      omega
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Ican_eq H, Ican_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Ican ν c = ∅ := by rw [Ican_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

section Ctx

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem exists_path_decomposition (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ)
    (q : X.Idx p K j (X.restr j b)) :
    ∃ (dd b' b'' : Fin (segN X.F j) → ℕ) (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd)
      (P1 : PPath r (segN X.F j) (segLL X.F j) b') (P2 : PPath K (segN X.F j) (segLL X.F j) b''),
      P.mu = q.1.1 ∧ P1.mu = plPart q.1.1 ∧ P2.mu = tanPart q.1.1 ∧ (∀ i, b' i + b'' i = dd i) ∧
      (∀ i, Formalism.MainNotions.CovariantDegrees.CondC (segLL X.F j) (plPart q.1.1) (tanPart q.1.1) i) ∧
      X.IsPATH p K j (X.restr j b) q.1.1 dd ∧ X.IsGood p K j (X.restr j b) q.1.1 ∧
      IsSt (tanPart q.1.1) q.1.2.1 ∧
      (∀ v, q.1.2.2 v + 2 * X.beS p K j (X.restr j b) < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.1.2.2 (i', c) = X.restr j b (X.F.fr j i'.val) := by
  obtain ⟨dd, hP, hG, hSt, hu, hd⟩ := q.2
  obtain ⟨P, hPμ⟩ := hP.path
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b', b'', hsum, ⟨P1, h1⟩, ⟨P2, h2⟩, hC⟩ :=
    (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp ⟨P, by rw [hPμ, joinPT_parts]⟩
  exact ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hP, hG, hSt, hu, hd⟩

theorem mem_W_vec (hX : X.Hyp p K) (j : ℤ) (l : Fin (segN X.F j)) (hl : l.val < r) :
    (segLL X.F j).vec l = true := by
  have hW : X.F.IsW j (segE X.F j l) := (TE.dict_w hX.valid l).mpr hl
  rw [comb_vec]
  exact comb_W_even X.F j hX.valid _ (segE_mem X.F j l) hW

theorem mem_tan_zero (hX : X.Hyp p K) (j : ℤ) {dd : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (s : Fin (segN X.F j + 1)) (hs : s.val ≤ r) (c : Fin K) :
    tanPart P.mu s c = 0 := by
  apply le_antisymm
  · exact T.mu_nonpos P s.val s.isLt (Fin.natAdd r c) (by simp only [Fin.val_natAdd]; omega)
  · exact comb_nonneg_of_vec P s (fun l hl => mem_W_vec hX j l (by omega)) _

theorem tangent_degree_zero_at_w (hX : X.Hyp p K) (j : ℤ) {dd b'' : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (P2 : PPath K (segN X.F j) (segLL X.F j) b'')
    (h2 : P2.mu = tanPart P.mu) (i : Fin (segN X.F j)) (hW : X.F.IsW j (segE X.F j i)) : b'' i = 0 := by
  have hi : i.val < r := (TE.dict_w hX.valid i).mp hW
  have hs := T.step_vec P2 i (mem_W_vec hX j i hi)
  have h3 := hs.2.2
  rw [h2] at h3
  have : ∑ a, (tanPart P.mu i.succ a - tanPart P.mu i.castSucc a) = 0 :=
    Finset.sum_eq_zero fun a _ => by
      rw [mem_tan_zero hX j P i.succ (by simp only [Fin.val_succ]; omega) a,
        mem_tan_zero hX j P i.castSucc (by simp only [Fin.val_castSucc]; omega) a, sub_zero]
  rw [this] at h3
  exact_mod_cast h3.symm

theorem mem_thc_restr (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    X.thc p K j (X.restr j b) x = X.thc p K j b x := by
  classical
  obtain ⟨ho1, ho2⟩ := oldest_letter_in_segment p n' r K X hX j x hx
  unfold Dat.thc
  split_ifs with hW
  · rfl
  · have hl : X.F.oldest j x ∈ X.toLate j := (mem_late X j _).mpr ⟨ho1, hW⟩
    unfold Dat.restr
    rw [if_pos hl]

theorem mem_det_supported (R : Type) [CommRing R] {n : ℕ} (y : Fin n → ℤ) (s : Set (ℤ × Fin n))
    (h : ∀ a c, (y a, c) ∈ s) :
    Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R)) ∈
      supported R s := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)
  exact Algebra.subset_adjoin ⟨_, h (σ i) i, rfl⟩

theorem disc_power_monomial_mem_supported (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr (j - 1) a.val, c) ∈ s) : X.discPowerTimesMonomial p K O j b ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.discPowerTimesMonomial Dat.Dw
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (mem_det_supported O _ s h) _)
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (hXm _ (h i 0)) _)

theorem mem_Mu_supported (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr j a.val, c) ∈ s) : X.memMu O j u ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.memMu
  exact Subalgebra.prod_mem _ fun v _ => Subalgebra.pow_mem _ (hXm _ (h v.1 v.2)) _

theorem mem_vg_A (D : Formalism.BasicNotions.D7) (hB2 : admB2 D) (hX : X.Hyp p K) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (S : Set ℤ) (hS : ∀ a : Fin r, X.F.fr (j - 1) a.val ∈ S) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (X.memPl K O j q.1)) :
    (((X.m0 K : ℤ) + a : ℤ) : WithTop ℤ) ≤ valS LZ S (X.memA p K O j b q) := by
  have hV := hX.valid
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hD : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.Dw O j) := by
    unfold Dat.Dw
    rw [(hB2 O ℤ r LZ S).2.2 (fun a => X.F.fr (j - 1) a.val) (fr_injective X.F hV (j - 1))
      (fun a => ⟨hS a, by simp [LZ, hevW a]⟩)]
    exact le_rfl
  have h1 := mem_vg_pow D hB2 S hD (X.m0 K)
  have h2 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun i : Fin r => (X.F.fr (j - 1) i.val, (0 : Fin r)))
    (fun i => ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) (fun i _ => hevW i)
  have h3 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun v : Fin r × Fin r => (X.F.fr j v.1.val, v.2))
    q.2.2 (fun v _ => hevT v.1)
  have h4 := mem_vg_mul D hB2 S (mem_vg_mul D hB2 S (mem_vg_mul D hB2 S h1 h2) h3) ha
  unfold Dat.memA Dat.discPowerTimesMonomial Dat.memMu
  have e : (X.m0 K : ℤ) * 1 + 0 + 0 + a = (X.m0 K : ℤ) + a := by ring
  rw [e] at h4
  exact h4

end Ctx

theorem restMemA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemA C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hB2 : admB2 D := hAdm.2.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI''
  rw [h1] at u1
  rw [h2] at u2
  refine ⟨?_, ?_, ?_⟩
  · unfold Dat.memA
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact disc_power_monomial_mem_supported O j b _ fun a _ => TE.frp_mem hV j a.val a.isLt
    · exact mem_Mu_supported O j _ _ fun a _ => k_fr_mem_letters X.F hV j a.isLt
    · unfold Dat.memPl
      refine mem_supported.mpr fun v hv => ?_
      obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
      exact segE_mem X.F j u.1
  · unfold Dat.memG
    refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, hu', rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact ⟨segE_mem X.F j u.1, fun hW => pol_vars_deg u2.1 hu'
      (tangent_degree_zero_at_w hX j P P2 (by rw [h2, hPμ]) u.1 hW)⟩
  · intro x hx hW
    obtain ⟨i, rfl⟩ := segE_surj X.F j hx
    obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi O (plPart q.1.1) (Ican (plPart q.1.1))) i
    obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi O (tanPart q.1.1) q.1.2.1) i
    have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
    have hM : X.memM K j q.1.1 (segE X.F j i) =
        (if Even (segE X.F j i) then tanPart q.1.1 i.succ 0 else tanPart q.1.1 i.castSucc 0) :=
      (segE_strictMono X.F j).injective.extend_apply _ _ i
    have hWlt : ∀ a : Fin r, X.F.fr (j - 1) a.val < segE X.F j i := by
      intro a
      have h3 : ¬ segE X.F j i ≤ X.F.fr (j - 1) (r - 1) := hW
      have h4 := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by have := a.isLt; omega)
      omega
    have vlt := mem_vg_A D hB2 hX O j b q.1 {y | y < segE X.F j i} hWlt (plPart q.1.1 i.castSucc (lastIdx r))
      (by unfold Dat.memPl; rw [sA2]; exact (u1.2 i.castSucc).1)
    have vle := mem_vg_A D hB2 hX O j b q.1 {y | y ≤ segE X.F j i} (fun a => (hWlt a).le)
      (plPart q.1.1 i.succ (lastIdx r)) (by unfold Dat.memPl; rw [sA1]; exact (u1.2 i.succ).1)
    have hCi := hC i
    unfold Formalism.MainNotions.CovariantDegrees.CondC at hCi
    refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
    · rw [hM, if_pos he]
      unfold Dat.memG
      rw [sG3]; exact (u2.2 i.succ).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
      rw [hM, if_pos he]
      rw [if_pos ((comb_vec X.F j i).mpr he)] at hCi
      omega
    · rw [hM, if_neg he]
      unfold Dat.memG
      rw [sG4]; exact (u2.2 i.castSucc).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
      rw [hM, if_neg he]
      rw [if_neg (fun h => he ((comb_vec X.F j i).mp h))] at hCi
      omega
    · refine geR_of_le vlt ?_
      rw [← mem_thc_restr hX j b _ hxl]
      have := (hGood i hW).1
      push_cast
      have hm : (0 : ℝ) ≤ (X.m0 K : ℝ) := Nat.cast_nonneg _
      linarith

end Formalism.MainNotions.SelectionLemmas.Pf
