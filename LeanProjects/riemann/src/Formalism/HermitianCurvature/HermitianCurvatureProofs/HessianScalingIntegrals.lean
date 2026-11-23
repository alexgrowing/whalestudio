import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals

variable {K : Type} [CommRing K]

theorem out_mk_sub (Λ : AddSubgroup K) (x : K) :
    (Quotient.out (x : K ⧸ Λ) : K) - x ∈ Λ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add Λ x
  rw [hh]; simp

theorem fin_supp [TopologicalSpace K] [IsTopologicalRing K] (Λ L : AddSubgroup K)
    (hΛ : IsOpen (Λ : Set K)) (hL : IsCompact (L : Set K)) (d : ℕ) :
    {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : ((QuotientAddGroup.mk : K → K ⧸ Λ) '' (L : Set K)).Finite :=
    (hL.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine (Set.Finite.pi' (fun _ : Fin d => h1)).subset ?_
  intro y hy i
  exact ⟨_, hy i, QuotientAddGroup.out_eq' _⟩

theorem intK_eq_sum (R : Subring K) (Λ L : AddSubgroup K) (d : ℕ)
    (hfin : {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite)
    (g : (Fin d → K) → ℂ) (hg : ∀ x, g x ≠ 0 → ∀ i, x i ∈ L) :
    intK R Λ d g = (volL R Λ : ℂ) ^ d * ∑ y ∈ hfin.toFinset, g (fun i => Quotient.out (y i)) := by
  unfold intK
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro y hy
  simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  exact hg _ hy

theorem ball_piece (R : Subring K) (m : ℕ) (B Λ : AddSubgroup K) (hΛB : Λ ≤ B) (z : K)
    (φ : (Fin m → K) → (Fin m → K))
    (hbij : Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B})
    (hcos : ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
      ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ))
    (G G' : (Fin m → K) → ℂ) (hG : LatInvN Λ G)
    (hG0 : ∀ x, (¬ ∀ k, x k - z ∈ B) → G x = 0)
    (hG'0 : ∀ ξ, (¬ ∀ k, ξ k ∈ B) → G' ξ = 0)
    (hGG' : ∀ ξ, (∀ k, ξ k ∈ B) → G (fun k => z + φ ξ k) = G' ξ) :
    LatInvN Λ G' ∧ intK R Λ m G = intK R Λ m G' := by
  classical
  have hinv : ∀ x x' : Fin m → K, (∀ k, x k - x' k ∈ Λ) → G x = G x' := by
    intro x x' h
    have := hG x' (fun k => x k - x' k) h
    rw [← this]; congr 1; ext k; simp
  constructor
  · intro ξ l hl
    by_cases hξ : ∀ k, ξ k ∈ B
    · have hξl : ∀ k, (ξ + l) k ∈ B := fun k => B.add_mem (hξ k) (hΛB (hl k))
      rw [← hGG' _ hξl, ← hGG' _ hξ]
      apply hinv
      intro k
      have := (hcos (ξ + l) ξ hξl hξ).2 (fun k => by simpa using hl k) k
      simpa using this
    · have hξl : ¬ ∀ k, (ξ + l) k ∈ B := fun h => hξ fun k => by
        have := B.sub_mem (h k) (hΛB (hl k)); simpa using this
      rw [hG'0 _ hξl, hG'0 _ hξ]
  · unfold intK
    congr 1
    let o : (Fin m → K ⧸ Λ) → (Fin m → K) := fun y i => Quotient.out (y i)
    let e : (Fin m → K ⧸ Λ) → (Fin m → K ⧸ Λ) := fun y k => ((z + φ (o y) k : K) : K ⧸ Λ)
    have hoe : ∀ y k, o (e y) k - (z + φ (o y) k) ∈ Λ := fun y k => out_mk_sub Λ _
    have h1 : ∑ᶠ y, G (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k - z ∈ B}, G (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG0 _ h
    have h2 : ∑ᶠ y, G' (o y) = ∑ᶠ y ∈ {y | ∀ k, o y k ∈ B}, G' (o y) := by
      refine finsum_congr fun y => ?_
      rw [finsum_eq_if]
      split_ifs with h
      · rfl
      · exact hG'0 _ h
    change ∑ᶠ y, G (o y) = ∑ᶠ y, G' (o y)
    rw [h1, h2]
    symm
    refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
    · intro y hy k
      have h3 : φ (o y) k ∈ B := hbij.mapsTo hy k
      have h4 := B.add_mem (hΛB (hoe y k)) h3
      have : o (e y) k - z = o (e y) k - (z + φ (o y) k) + φ (o y) k := by ring
      rw [this]; exact h4
    · intro y hy y' hy' hyy
      have h3 : ∀ k, φ (o y) k - φ (o y') k ∈ Λ := by
        intro k
        have := congrFun hyy k
        have h5 : ((z + φ (o y) k : K) : K ⧸ Λ) = ((z + φ (o y') k : K) : K ⧸ Λ) := this
        rw [QuotientAddGroup.eq] at h5
        have h6 := Λ.neg_mem h5
        have : φ (o y) k - φ (o y') k = -(-(z + φ (o y) k) + (z + φ (o y') k)) := by ring
        rw [this]; exact h6
      have h4 := (hcos _ _ hy hy').1 h3
      funext k
      have h5 : ((o y k : K) : K ⧸ Λ) = ((o y' k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h6 := Λ.neg_mem (h4 k)
        have : -o y k + o y' k = -(o y k - o y' k) := by ring
        rw [this]; exact h6
      simpa [o] using h5
    · intro y hy
      have hmem : (fun k => o y k - z) ∈ {ξ : Fin m → K | ∀ k, ξ k ∈ B} := hy
      obtain ⟨ξ, hξ, hξy⟩ := hbij.surjOn hmem
      let y' : Fin m → K ⧸ Λ := fun k => ((ξ k : K) : K ⧸ Λ)
      have h3 : ∀ k, o y' k - ξ k ∈ Λ := fun k => out_mk_sub Λ _
      have h4 : ∀ k, o y' k ∈ B := fun k => by
        have := B.add_mem (hΛB (h3 k)) (hξ k); simpa using this
      refine ⟨y', h4, ?_⟩
      funext k
      have h5 := (hcos _ _ h4 hξ).2 h3 k
      have h6 : ((z + φ (o y') k : K) : K ⧸ Λ) = ((o y k : K) : K ⧸ Λ) := by
        rw [QuotientAddGroup.eq]
        have h7 : φ ξ k = o y k - z := congrFun hξy k
        have : -(z + φ (o y') k) + o y k = -(φ (o y') k - φ ξ k) := by rw [h7]; ring
        rw [this]; exact Λ.neg_mem h5
      have h8 : ((o y k : K) : K ⧸ Λ) = y k := QuotientAddGroup.out_eq' _
      exact h6.trans h8
    · intro y hy
      rw [← hGG' _ hy]
      symm
      exact hinv _ _ (hoe y)

theorem hess_scale (m : ℕ) (z t : Kˣ) :
    hessM m (z * t) = ((t⁻¹ : Kˣ) : K) • hessM m z := by
  unfold hessM
  rw [smul_smul, mul_inv, Units.val_mul, mul_comm]

theorem psi_ne_zero (ψ : AddChar K ℂ) (a : K) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ (a + -a) = 1 := by simp
  rw [AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem amp_const (Λ₁ : AddSubgroup K) {m : ℕ} (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (z : K)
    (x : Fin m → K) (hx : ∀ k, x k - z ∈ Λ₁) : A x = A (fun _ => z) := by
  have := hA (fun _ => z) (fun k => x k - z) hx
  rw [← this]; congr 1; ext k; simp

open Classical in

theorem root_piece [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
    (hγ : IsGamma R ψ m γ) (Λ₁ : AddSubgroup K) (B Λ : Submodule R K)
    (hB : IsLat B.toAddSubgroup) (hΛ : IsLat Λ.toAddSubgroup) (hΛB : Λ ≤ B)
    (hBΛ₁ : ∀ b ∈ B, b ∈ Λ₁)
    (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (t z : Kˣ) (D : K) (hD : (z : K) ^ (m + 1) = D)
    (hmod : 0 < modK R (z : K) ∧ 0 < modK R (t : K) ∧
      modK R ((z : K) * (t : K)) = modK R (z : K) * modK R (t : K))
    (hadm : GaussAdm ψ B.toAddSubgroup (hessM m (z * t)))
    (hmorse : ∃ φ : (Fin m → K) → (Fin m → K),
        Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
        (∀ Λ : Submodule R K, Λ ≤ B → ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
          ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
        ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
          (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
          g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
            ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)))
    (hinv : LatInvN Λ.toAddSubgroup (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0)) :
    intK R Λ.toAddSubgroup m (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0) =
      ((modK R (t : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K))) := by
  subst hD
  by_cases hA0 : A (fun _ => (z : K)) = 0
  · have h0 : (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
        A x * ψ (g0 ((z : K) ^ (m + 1)) x * ((t⁻¹ : Kˣ) : K)) else 0) = fun _ => 0 := by
      funext x
      split_ifs with h
      · rw [amp_const Λ₁ A hA z x (fun k => hBΛ₁ _ (h k)), hA0, zero_mul]
      · rfl
    rw [h0, hA0]
    simp [intK]
  · obtain ⟨φ, hbij, hcos, hval⟩ := hmorse
    set c : ℂ := A (fun _ => (z : K)) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) with hc
    have hc0 : c ≠ 0 := mul_ne_zero hA0 (psi_ne_zero ψ _)
    obtain ⟨hi, he⟩ := ball_piece R m B.toAddSubgroup Λ.toAddSubgroup hΛB (z : K) φ hbij
      (hcos Λ hΛB) _ (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) hinv
      (fun x hx => if_neg hx)
      (fun ξ hξ => by
        have : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ = 0 := if_neg hξ
        rw [this, mul_zero])
      (fun ξ hξ => by
        have h1 : ∀ k, (z : K) + φ ξ k - (z : K) ∈ B := fun k => by
          have : φ ξ k ∈ B := hbij.mapsTo hξ k
          simpa using this
        have h2 : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ =
            ψ (Ring.inverse 2 * (ξ ⬝ᵥ (hessM m (z * t) *ᵥ ξ))) := if_pos hξ
        rw [h2]
        simp only []
        rw [if_pos h1, amp_const Λ₁ A hA z _ (fun k => hBΛ₁ _ (h1 k)), (hval ξ hξ).2, hc, mul_assoc,
          ← AddChar.map_add_eq_mul, hess_scale, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        congr 2
        ring)
    have hi' : LatInvN Λ.toAddSubgroup (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      intro ξ l hl
      exact mul_left_cancel₀ hc0 (hi ξ l hl)
    rw [he]
    have h3 : intK R Λ.toAddSubgroup m (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) =
        c * intK R Λ.toAddSubgroup m (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      unfold intK
      rw [mul_left_comm]
      congr 1
      have := smul_finsum c (fun y : Fin m → K ⧸ Λ.toAddSubgroup =>
        gaussF ψ B.toAddSubgroup (hessM m (z * t)) (fun i => Quotient.out (y i)))
      simpa [smul_eq_mul] using this.symm
    rw [h3, hγ.2.2 (z * t) _ _ hB hΛ hadm hi', Units.val_mul, hmod.2.2,
      Real.mul_rpow hmod.1.le hmod.2.1.le, hc]
    push_cast
    ring

theorem ball_iff (B : AddSubgroup K) {m : ℕ} (x l : Fin m → K) (z : K) (hl : ∀ k, l k ∈ B) :
    (∀ k, (x + l) k - z ∈ B) ↔ ∀ k, x k - z ∈ B := by
  refine forall_congr' fun k => ?_
  have h1 : (x + l) k - z = x k - z + l k := by simp only [Pi.add_apply]; ring
  rw [h1]
  exact B.add_mem_cancel_right (hl k)

end Formalism.FourierDecayAlt.P.HessianScalingIntegrals

open Formalism.FourierDecayAlt.P.HessianScalingIntegrals in
open Classical in

theorem Formalism.FourierDecayAlt.P.stationaryPhaseOfSteps : Formalism.FourierDecayAlt.A6.StationaryAssemble := by
  intro hNS hMorse hRef hMod hRF _ _ _ _ _ hRS hSM hGA _ K _ _ _ R ψ hD hn m hm γ hγ L₀ Λ₁ Q hL₀ hΛ₁
    hQ hQu
  obtain ⟨VM, hVM, hM⟩ := hMorse K R ψ hD hn m hm Q hQ hQu
  obtain ⟨VS, hVS, hS⟩ := hRS K R ψ hD hn (m + 1) (by omega) Q hQ hQu
  have hΛ₁n : (Λ₁ : Set K) ∈ 𝓝 (0 : K) := hΛ₁.1.mem_nhds Λ₁.zero_mem
  obtain ⟨B, hB, hBV⟩ := hSM K R ψ hD hn (VM ∩ VS ∩ (Λ₁ : Set K))
    (inter_mem (inter_mem hVM hVS) hΛ₁n)
  obtain ⟨VN, hVN, hN⟩ := hNS K R ψ hD hn m hm L₀ Λ₁ B.toAddSubgroup Q hL₀ hΛ₁ hB hQ hQu
  obtain ⟨VG, hVG, hG⟩ := hGA K R ψ hD hn m B.toAddSubgroup Q hB hQ hQu
  refine ⟨VN ∩ VG, inter_mem hVN hVG, ?_⟩
  intro t D' A ht hD' hA Λ hΛ hF

  have hΛn : (Λ : Set K) ∈ 𝓝 (0 : K) := hΛ.1.mem_nhds Λ.zero_mem
  have hBn : (B : Set K) ∈ 𝓝 (0 : K) := hB.1.mem_nhds B.zero_mem
  obtain ⟨Λ', hΛ', hΛ'V⟩ := hSM K R ψ hD hn ((Λ : Set K) ∩ (B : Set K)) (inter_mem hΛn hBn)
  have hΛ'Λ : Λ'.toAddSubgroup ≤ Λ := fun x hx => (hΛ'V hx).1
  have hΛ'B : Λ' ≤ B := fun x hx => (hΛ'V hx).2
  set F : (Fin m → K) → ℂ := fun x => A x * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hFdef
  have hFsupp : ∀ x, F x ≠ 0 → ∀ i, x i ∈ L₀ := fun x hx i =>
    (hA.1 x (left_ne_zero_of_mul hx) i).1
  have hF' : LatInvN Λ'.toAddSubgroup F := fun x l hl => hF x l fun i => hΛ'Λ (hl i)
  rw [← hRef K R ψ hD Λ Λ'.toAddSubgroup L₀ m F hΛ hΛ' hL₀ hΛ'Λ hFsupp hF]

  have hfin : {z : Kˣ | z ^ (m + 1) = D'}.Finite :=
    @hRF K _ hD.artin hD.red (m + 1) (by omega) D'
  have hzQ : ∀ z : Kˣ, z ^ (m + 1) = D' → (z : K) ^ (m + 1) = (D' : K) := fun z hz => by
    rw [← hz, Units.val_pow_eq_pow_val]
  have hsep : ∀ z z' : Kˣ, z ^ (m + 1) = D' → z' ^ (m + 1) = D' → ∀ x : Fin m → K,
      (∀ k, x k - (z : K) ∈ B) → (∀ k, x k - (z' : K) ∈ B) → z = z' := by
    intro z z' hz hz' x hx hx'
    refine hS z z' (by rw [hzQ z hz]; exact hD') (hz.trans hz'.symm) ?_
    have h1 := B.sub_mem (hx' ⟨0, hm⟩) (hx ⟨0, hm⟩)
    have h2 : (z : K) - (z' : K) = x ⟨0, hm⟩ - (z' : K) - (x ⟨0, hm⟩ - (z : K)) := by ring
    rw [h2]
    exact (hBV h1).1.2
  set Foff : (Fin m → K) → ℂ := fun x =>
    if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup then 0 else F x with hFoff
  set Fz : Kˣ → (Fin m → K) → ℂ := fun z x => if ∀ k, x k - (z : K) ∈ B then F x else 0 with hFz
  have hdec : ∀ x, F x = Foff x + ∑ z ∈ hfin.toFinset, Fz z x := by
    intro x
    by_cases h : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup
    · obtain ⟨z0, hz0, hx0⟩ := h
      have h1 : Foff x = 0 := if_pos ⟨z0, hz0, hx0⟩
      rw [h1, zero_add, Finset.sum_eq_single z0]
      · exact (if_pos hx0).symm
      · intro z hz hne
        refine if_neg fun hx => hne ?_
        exact hsep z z0 (by simpa using hz) hz0 x hx hx0
      · intro hz
        exact absurd (by simpa using hz0) hz
    · have h1 : Foff x = F x := if_neg h
      rw [h1, Finset.sum_eq_zero, add_zero]
      intro z hz
      exact if_neg fun hx => h ⟨z, by simpa using hz, hx⟩
  have hFoffInv : LatInvN Λ'.toAddSubgroup Foff := by
    intro x l hl
    have h1 : (∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + l) k - (z : K) ∈ B.toAddSubgroup) ↔
        ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B.toAddSubgroup :=
      exists_congr fun z => and_congr_right fun _ =>
        ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFoff]
    rw [if_congr h1 rfl (hF' x l hl)]
  have hFzInv : ∀ z : Kˣ, LatInvN Λ'.toAddSubgroup (Fz z) := by
    intro z x l hl
    have h1 : (∀ k, (x + l) k - (z : K) ∈ B) ↔ ∀ k, x k - (z : K) ∈ B :=
      ball_iff B.toAddSubgroup x l z fun k => hΛ'B (hl k)
    simp only [hFz]
    rw [if_congr h1 (hF' x l hl) rfl]
  have hFoffSupp : ∀ x, Foff x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFoff, h0, ite_self]
  have hFzSupp : ∀ z x, Fz z x ≠ 0 → ∀ i, x i ∈ L₀ := by
    intro z x hx
    apply hFsupp
    intro h0
    apply hx
    simp only [hFz, h0, ite_self]
  have hS0 := fin_supp Λ'.toAddSubgroup L₀ hΛ'.1 hL₀.2 m
  have hsplit : intK R Λ'.toAddSubgroup m F = intK R Λ'.toAddSubgroup m Foff +
      ∑ z ∈ hfin.toFinset, intK R Λ'.toAddSubgroup m (Fz z) := by
    rw [intK_eq_sum R _ L₀ m hS0 F hFsupp, intK_eq_sum R _ L₀ m hS0 Foff hFoffSupp]
    simp_rw [fun z => intK_eq_sum R _ L₀ m hS0 (Fz z) (hFzSupp z)]
    rw [← Finset.mul_sum, ← mul_add, Finset.sum_comm, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun y _ => hdec _
  have hoff : intK R Λ'.toAddSubgroup m Foff = 0 :=
    hN t D' A ht.1 hD' hA Λ'.toAddSubgroup hΛ' hFoffInv
  rw [hsplit, hoff, zero_add]
  have hrhs : (∑ᶠ z : Kˣ, if z ^ (m + 1) = D' then
          γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) else 0) =
      ∑ z ∈ hfin.toFinset, γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K)) := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => if_pos (by simpa using hz)
    · intro z hz
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      by_contra h
      exact hz (if_neg h)
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' : z ^ (m + 1) = D' := by simpa using hz
  have hzq : (z : K) ^ (m + 1) ∈ Q := by rw [hzQ z hz']; exact hD'
  exact root_piece R ψ m γ hγ Λ₁ B Λ' hB hΛ' hΛ'B (fun b hb => (hBV hb).2) A hA.2 t z (D' : K)
    (hzQ z hz') ⟨(hMod K R ψ hD z t).1, (hMod K R ψ hD t z).1, (hMod K R ψ hD z t).2⟩
    (hG t z ht.2 hzq) (hM B hB (fun b hb => (hBV hb).1.1) z hzq) (hFzInv z)
