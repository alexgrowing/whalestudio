import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def P1 (m al be j : ℕ) : ℝ := (dimHar m al be : ℝ) / ((dimPol m (al + j) : ℝ) * dimPol m (be + j))

structure DensityNumericalFacts (K : Cst) (X : Dat) : Prop where
  m1 : 1 ≤ X.m
  cardP : 0 < (X.WaP K).card ∧ 0 < (X.WbP K).card
  dens : ∃ δ : ℝ, 0 ≤ δ ∧
    (∀ τ ≤ X.ccl, ∀ al ∈ X.Wa τ, ∀ be ∈ X.Wb τ, δ ≤ ∑ j ∈ Finset.range (X.Jn K + 1), P1 X.m al be j) ∧
    ((X.WaP K).card : ℝ) ^ X.N * ((X.WbP K).card : ℝ) ^ X.N ≤
      2 * δ ^ X.N * (((X.Wa 0).card : ℝ) ^ X.N * ((X.Wb 0).card : ℝ) ^ X.N)

open Classical in
theorem sum_map_le {α β : Type*} (S : Finset α) (S' : Finset β) (φ : α → β) (hinj : Set.InjOn φ S)
    (hmap : ∀ x ∈ S, φ x ∈ S') (g : β → ℝ) (hg : ∀ y ∈ S', 0 ≤ g y) :
    ∑ x ∈ S, g (φ x) ≤ ∑ y ∈ S', g y := by
  calc ∑ x ∈ S, g (φ x) = ∑ y ∈ S.image φ, g y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ S', g y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.2 hmap) (fun y hy _ => hg y hy)

theorem dimPol_pos (m A : ℕ) : 0 < dimPol m A := Nat.choose_pos (Nat.le_add_left _ _)

theorem Ne_pos {p n' : ℕ} (R : RS p n') (k : ℕ) : 0 < gaussianNumber (p ^ n') (k + 1) := by
  have hp : 5 ≤ p := R.std.1.five_le
  have hn : 2 ≤ n' := R.std.1.two_le
  have hq : (1 : ℝ) < ((p ^ n' : ℕ) : ℝ) := by
    have : 1 < p ^ n' := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  unfold gaussianNumber
  apply div_pos
  · have := one_lt_pow₀ hq (by omega : k + 1 ≠ 0)
    linarith
  · linarith

theorem card_Wa (X : Dat) (τ : ℕ) : (X.Wa τ).card = (X.Wa 0).card := by
  simp only [Dat.Wa, Nat.card_Icc]; omega

theorem card_Wb (X : Dat) (τ : ℕ) : (X.Wb τ).card = (X.Wb 0).card := by
  simp only [Dat.Wb, Nat.card_Icc]; omega

theorem sum_kF_mul_prod_le_kx (hD : RestDims) (K : Cst) (X : Dat) (hm : 1 ≤ X.m) (R : RS X.p X.n') (hK : KeyIneq K X R)
    (A : X.TT → ℕ) (hA : A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K))
    (B : X.TT → ℕ) (hB : B ∈ Fintype.piFinset (fun _ : X.TT => X.WbP K)) :
    ∑ j ∈ Fintype.piFinset (fun _ : X.TT => Finset.range (X.Jn K + 1)),
        X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          ∏ s, ((dimHar X.m (A s - j s) (B s - j s) : ℝ) / ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) ≤
      X.kx K R A B := by
  have h := hK A hA B hB
  have hNe := Ne_pos R X.m
  have hHH : ((dimHH (m := X.m) R.Kf X.TT (ex A) (ex B) : ℕ) : ℝ) =
      ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s)) := by
    rw [(hD X.p X.n' R X.m hm X.TT A B).1]; push_cast; rfl
  have hPpos : 0 < ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s)) :=
    Finset.prod_pos fun s _ => mul_pos (by exact_mod_cast dimPol_pos _ _) (by exact_mod_cast dimPol_pos _ _)
  rw [hHH] at h
  have hterm : ∀ j : X.TT → ℕ,
      X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          ∏ s, ((dimHar X.m (A s - j s) (B s - j s) : ℝ) / ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) =
      (X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s))) *
        (gaussianNumber (X.p ^ X.n') (X.m + 1) / ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) := by
    intro j
    unfold dL
    rw [(hD X.p X.n' R X.m hm X.TT (fun s => A s - j s) (fun s => B s - j s)).2, Finset.prod_div_distrib]
    push_cast
    field_simp
  simp only [hterm]
  rw [← Finset.sum_mul]
  calc _ ≤ (X.kx K R A B * ((∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) / gaussianNumber (X.p ^ X.n') (X.m + 1))) *
        (gaussianNumber (X.p ^ X.n') (X.m + 1) / ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) :=
        mul_le_mul_of_nonneg_right h (le_of_lt (div_pos hNe hPpos))
    _ = X.kx K R A B := by field_simp

theorem avg_abs {ι : Type} [Fintype ι] [DecidableEq ι] (SaP SbP Sa Sb : Finset ℕ) (J : ℕ)
    (kf kx : (ι → ℕ) → (ι → ℕ) → ℝ) (q : ℕ → ℕ → ℕ → ℝ) (hq : ∀ A B j, 0 ≤ q A B j) (hkf : ∀ A B, 0 ≤ kf A B)
    (hkey : ∀ A ∈ Fintype.piFinset (fun _ : ι => SaP), ∀ B ∈ Fintype.piFinset (fun _ : ι => SbP),
      ∑ j ∈ Fintype.piFinset (fun _ : ι => Finset.range (J + 1)),
        kf (fun s => A s - j s) (fun s => B s - j s) * ∏ s, q (A s) (B s) (j s) ≤ kx A B)
    (hsa : ∀ a ∈ Sa, ∀ j ≤ J, a + j ∈ SaP) (hsb : ∀ b ∈ Sb, ∀ j ≤ J, b + j ∈ SbP)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ al ∈ Sa, ∀ be ∈ Sb, δ ≤ ∑ j ∈ Finset.range (J + 1), q (al + j) (be + j) j)
    (hcard : (SaP.card : ℝ) ^ Fintype.card ι * (SbP.card : ℝ) ^ Fintype.card ι ≤
      2 * δ ^ Fintype.card ι * ((Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι))
    (hpa : 0 < SaP.card) (hpb : 0 < SbP.card) :
    meanN Sa Sb kf ≤ 2 * meanN SaP SbP kx := by
  set SJ := Fintype.piFinset (fun _ : ι => Finset.range (J + 1)) with hSJ
  set SA := Fintype.piFinset (fun _ : ι => SaP) with hSA
  set SB := Fintype.piFinset (fun _ : ι => SbP) with hSB
  set Ta := Fintype.piFinset (fun _ : ι => Sa) with hTa
  set Tb := Fintype.piFinset (fun _ : ι => Sb) with hTb
  let F : (ι → ℕ) → (ι → ℕ) → (ι → ℕ) → ℝ := fun A B j =>
    kf (fun s => A s - j s) (fun s => B s - j s) * ∏ s, q (A s) (B s) (j s)
  have hFnn : ∀ A B j, 0 ≤ F A B j := fun A B j =>
    mul_nonneg (hkf _ _) (Finset.prod_nonneg fun s _ => hq _ _ _)
  have h1 : ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j ≤ ∑ A ∈ SA, ∑ B ∈ SB, kx A B :=
    Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun B hB => hkey A hA B hB
  have h2 : ∑ al ∈ Ta, ∑ be ∈ Tb, ∑ j ∈ SJ, F (al + j) (be + j) j ≤ ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j := by
    have e1 : ∑ al ∈ Ta, ∑ be ∈ Tb, ∑ j ∈ SJ, F (al + j) (be + j) j =
        ∑ j ∈ SJ, ∑ al ∈ Ta, ∑ be ∈ Tb, F (al + j) (be + j) j := by
      calc _ = ∑ al ∈ Ta, ∑ j ∈ SJ, ∑ be ∈ Tb, F (al + j) (be + j) j :=
            Finset.sum_congr rfl fun al _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have e2 : ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j = ∑ j ∈ SJ, ∑ A ∈ SA, ∑ B ∈ SB, F A B j := by
      calc _ = ∑ A ∈ SA, ∑ j ∈ SJ, ∑ B ∈ SB, F A B j := Finset.sum_congr rfl fun A _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [e1, e2]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : ∀ s, j s ≤ J := fun s => by
      have := (Fintype.mem_piFinset.1 hj) s
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 this)
    have hmapA : ∀ al ∈ Ta, al + j ∈ SA := fun al hal =>
      Fintype.mem_piFinset.2 fun s => hsa _ ((Fintype.mem_piFinset.1 hal) s) _ (hj' s)
    have hmapB : ∀ be ∈ Tb, be + j ∈ SB := fun be hbe =>
      Fintype.mem_piFinset.2 fun s => hsb _ ((Fintype.mem_piFinset.1 hbe) s) _ (hj' s)
    calc ∑ al ∈ Ta, ∑ be ∈ Tb, F (al + j) (be + j) j
        ≤ ∑ al ∈ Ta, ∑ B ∈ SB, F (al + j) B j := Finset.sum_le_sum fun al _ =>
          sum_map_le Tb SB (fun be => be + j) (fun x _ y _ h => add_right_cancel h) hmapB
            (fun B => F (al + j) B j) (fun _ _ => hFnn _ _ _)
      _ ≤ ∑ A ∈ SA, ∑ B ∈ SB, F A B j :=
          sum_map_le Ta SA (fun al => al + j) (fun x _ y _ h => add_right_cancel h) hmapA
            (fun A => ∑ B ∈ SB, F A B j) (fun _ _ => Finset.sum_nonneg fun _ _ => hFnn _ _ _)
  have h3 : ∀ al ∈ Ta, ∀ be ∈ Tb, δ ^ Fintype.card ι * kf al be ≤ ∑ j ∈ SJ, F (al + j) (be + j) j := by
    intro al hal be hbe
    have e : ∀ j : ι → ℕ, F (al + j) (be + j) j = kf al be * ∏ s, q (al s + j s) (be s + j s) (j s) := by
      intro j
      simp only [F, Pi.add_apply, Nat.add_sub_cancel]
    simp only [e]
    rw [← Finset.mul_sum, hSJ,
      ← Finset.prod_univ_sum (fun _ : ι => Finset.range (J + 1)) (fun s j => q (al s + j) (be s + j) j), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hkf _ _)
    calc δ ^ Fintype.card ι = ∏ _s : ι, δ := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hδ0) fun s _ =>
        hδ (al s) ((Fintype.mem_piFinset.1 hal) s) (be s) ((Fintype.mem_piFinset.1 hbe) s)
  have h4 : δ ^ Fintype.card ι * ∑ al ∈ Ta, ∑ be ∈ Tb, kf al be ≤ ∑ A ∈ SA, ∑ B ∈ SB, kx A B := by
    refine le_trans ?_ (le_trans h2 h1)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun al hal => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun be hbe => h3 al hal be hbe
  unfold meanN
  set s := ∑ al ∈ Ta, ∑ be ∈ Tb, kf al be with hs
  set x := ∑ A ∈ SA, ∑ B ∈ SB, kx A B with hx
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hkf _ _
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (pow_nonneg hδ0 _) hs0) h4
  set u := (Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι with hu
  set v := (SaP.card : ℝ) ^ Fintype.card ι * (SbP.card : ℝ) ^ Fintype.card ι with hv
  have hv0 : 0 < v := mul_pos (pow_pos (by exact_mod_cast hpa) _) (pow_pos (by exact_mod_cast hpb) _)
  have hu0 : 0 ≤ u := by positivity
  rcases eq_or_lt_of_le hu0 with hu' | hu'
  · rw [← hu', div_zero]; positivity
  · rw [div_le_iff₀ hu', ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hv0]
    calc s * v ≤ s * (2 * δ ^ Fintype.card ι * u) := mul_le_mul_of_nonneg_left hcard hs0
      _ = 2 * (δ ^ Fintype.card ι * s) * u := by ring
      _ ≤ 2 * x * u := by gcongr

theorem avg_of (hD : RestDims) (K : Cst) (X : Dat) (hF : DensityNumericalFacts K X) (R : RS X.p X.n') (hK : KeyIneq K X R)
    (τ : ℕ) (hτ : τ ≤ X.ccl) : Avg K X R τ := by
  obtain ⟨δ, hδ0, hδ, hcard⟩ := hF.dens
  refine avg_abs (X.WaP K) (X.WbP K) (X.Wa τ) (X.Wb τ) (X.Jn K) (X.kF K R) (X.kx K R)
    (fun A B j => (dimHar X.m (A - j) (B - j) : ℝ) / ((dimPol X.m A : ℝ) * dimPol X.m B))
    (fun A B j => by positivity) (fun _ _ => Real.sInf_nonneg fun _ h => h.1)
    (fun A hA B hB => sum_kF_mul_prod_le_kx hD K X hF.m1 R hK A hA B hB) ?_ ?_ δ hδ0 ?_ ?_ hF.cardP.1 hF.cardP.2
  · intro a ha j hj
    have := Finset.mem_Icc.1 ha
    simp only [Dat.WaP, Finset.mem_Icc]
    omega
  · intro b hb j hj
    have := Finset.mem_Icc.1 hb
    simp only [Dat.WbP, Finset.mem_Icc]
    omega
  · intro al hal be hbe
    have := hδ τ hτ al hal be hbe
    simpa only [P1, Nat.add_sub_cancel] using this
  · rw [card_Wa, card_Wb, Fintype.card_coe]
    exact hcard

end Formalism.MainNotions.flipOneThree.Pf

end
