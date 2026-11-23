import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.HomCompRename

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem isNormal_pl {n' r K : ℕ} (s : Fin n') (a : Fin r) :
    IsNormal r ((s, Fin.castAdd K a) : TV n' (r + K)) ↔ ¬ Even s.val := by
  unfold IsNormal
  by_cases h : Even s.val <;> simp [h, a.isLt]

theorem isNormal_no {n' r K : ℕ} (s : Fin n') (b : Fin K) :
    IsNormal r ((s, Fin.natAdd r b) : TV n' (r + K)) ↔ Even s.val := by
  unfold IsNormal
  by_cases h : Even s.val <;> simp [h]

section ND

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def oOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  ∑ x : TL J nL r, if Even (posOf n' (posTL Fr x)).val then
    ∑ b : Fin K, rho (x, Fin.natAdd r b) + lowP Fr p x * dNo x
    else ∑ a : Fin r, rho (x, Fin.castAdd K a) + lowP Fr p x * dPl x

theorem normDeg_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (h1 : ∀ x, multideg bp x = dPl x)
    (h2 : ∀ x, multideg bn x = dNo x) (mm : TV n' (r + K) →₀ ℕ)
    (hmm : ∀ v, mm v = bigM Fr p hk nL rho bp bn (castVK hk v)) :
    normDeg r mm = oOf Fr p nL rho dPl dNo := by
  have hpl : ∀ (x : TL J nL r) (a : Fin r), mm (posOf n' (posTL Fr x), Fin.castAdd K a)
      = rho (x, Fin.castAdd K a) + lowP Fr p x * bp (x, a) := by
    intro x a
    rw [hmm]
    exact bigM_pl hinj rho bp bn x a
  have hno : ∀ (x : TL J nL r) (b : Fin K), mm (posOf n' (posTL Fr x), Fin.natAdd r b)
      = rho (x, Fin.natAdd r b) + lowP Fr p x * bn (x, b) := by
    intro x b
    rw [hmm]
    exact bigM_no hinj rho bp bn x b
  have hoff : ∀ s : Fin n', s ∉ Set.range (fun x : TL J nL r => posOf n' (posTL Fr x)) →
      ∀ c : Fin (r + K), mm (s, c) = 0 := by
    intro s hs c
    rw [hmm]
    exact bigM_off Fr p hk nL htop rho bp bn s hs _
  have h0 : normDeg r mm = ∑ v : TV n' (r + K), (if IsNormal r v then mm v else 0) := by
    unfold normDeg
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hz : mm v = 0 := by simpa [Finsupp.mem_support_iff] using hv
    simp [hz]
  have hprod : ∑ v : TV n' (r + K), (if IsNormal r v then mm v else 0)
      = ∑ s : Fin n', ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0) :=
    Fintype.sum_prod_type _
  have hsub : ∑ s ∈ Finset.univ.image (fun x : TL J nL r => posOf n' (posTL Fr x)),
        ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0)
      = ∑ s : Fin n', ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    have hs' : s ∉ Set.range (fun x : TL J nL r => posOf n' (posTL Fr x)) := by
      rintro ⟨x, rfl⟩
      exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    apply Finset.sum_eq_zero
    intro c _
    simp [hoff s hs' c]
  have himg := Finset.sum_image (s := Finset.univ) (g := fun x : TL J nL r => posOf n' (posTL Fr x))
    (f := fun s : Fin n' => ∑ c : Fin (r + K), (if IsNormal r ((s, c) : TV n' (r + K)) then mm (s, c) else 0))
    (fun x _ y _ h => hinj h)
  rw [h0, hprod, ← hsub, himg]
  unfold oOf
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.sum_univ_add]
  by_cases he : Even (posOf n' (posTL Fr x)).val
  · simp only [isNormal_pl, isNormal_no, he, not_true_eq_false, if_false, if_true, Finset.sum_const_zero,
      zero_add, hno, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← h2 x]
    rfl
  · simp only [isNormal_pl, isNormal_no, he, not_false_eq_true, if_false, if_true, Finset.sum_const_zero,
      add_zero, hpl, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← h1 x]
    rfl

end ND

theorem castVK_inj {n' k r K : ℕ} (hk : k = r + K) : Function.Injective (castVK (n' := n') hk) := by
  intro v w h
  simp only [castVK, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.ext (by simpa using congrArg Fin.val h.2))

theorem toKK_support {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K))
    (mm : Fin n' × Fin (r + K) →₀ ℕ) (h : mm ∈ P.support) :
    Finsupp.mapDomain (castVK hk) mm ∈ (toKK hk P).support := by
  rw [MvPolynomial.mem_support_iff] at h ⊢
  unfold toKK
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_rename_mapDomain _ (castVK_inj hk)]
  intro h0
  apply h
  exact (IsFractionRing.injective O (KK O)) (by simpa using h0)

theorem restDegG : RestDegG := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH δ _
  have hV : Fr.Valid L₁ N₁ := hM.frames.2.1
  have hr : 1 ≤ r := le_trans (by norm_num) hM.two_le_r
  have hJ : J = Fr.J := hMH.1.1.1
  have hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card := hMH.1.1.2.1
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hsurj := posTL_surj Fr hV hr hJ hnL
  have htop : ∀ x : TL J Dt.nL r, posOf n' (posTL Fr x) ∈ Fr.TT := fun x => (posTL_seg Fr hV hr hnL x).2.2
  obtain ⟨Go', hsub, hren⟩ := homComp_rename (fun v : ML J Dt.nL r × Fin r => (mlPos Fr Dt.nL v.1, v.2)) δ Go
  have e : homComp δ (xiPl Fr O Dt.nL Go) = xiPl Fr O Dt.nL Go' := hren.symm
  rw [e]
  have hid : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go') * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go'))
      (MvPolynomial.map (algebraMap O (KK O)) No) :=
    alg_identity p O hk Fr Dt hV hr hJ hMH.1.1.2.2.2.2.1 rho No Go'
  have hA : Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go') ∈ Pol (KK O) r dPl := by
    rw [← hMH.1.1.2.2.2.1]
    refine ph_mem_pol Dt _ fun mo hmo => hMH.2.2.2.2 mo (hsub ?_)
    rwa [support_of_map] at hmo
  have hN : MvPolynomial.map (algebraMap O (KK O)) No ∈ Pol (KK O) K dNo := hMH.2.2.1.2.1
  have hAd := (mem_restrictSupport_iff (KK O)).1 hA
  have hNd := (mem_restrictSupport_iff (KK O)).1 hN
  refine ⟨?_, oOf Fr p Dt.nL rho dPl dNo, ?_⟩
  · rw [hid]
    unfold HasMultideg Pol
    rw [mem_restrictSupport_iff]
    intro mm hmm
    obtain ⟨bp, hbp, bn, hbn, rfl⟩ := asm_support Fr p O hk Dt.nL rho _ _ mm hmm
    exact multideg_bigM Fr p hk Dt.nL hinj hsurj htop d hM.d_off rho dPl dNo hMH.2.1 bp bn (hAd hbp) (hNd hbn)
  · intro mm hmm
    have h1 := toKK_support hk _ mm hmm
    rw [hid] at h1
    obtain ⟨bp, hbp, bn, hbn, h2⟩ := asm_support Fr p O hk Dt.nL rho _ _ _ h1
    refine normDeg_bigM Fr p hk Dt.nL hinj htop rho dPl dNo bp bn (hAd hbp) (hNd hbn) mm fun v => ?_
    rw [← h2, Finsupp.mapDomain_apply (castVK_inj hk)]

end Formalism.MainNotions.Proposition5Numerics
