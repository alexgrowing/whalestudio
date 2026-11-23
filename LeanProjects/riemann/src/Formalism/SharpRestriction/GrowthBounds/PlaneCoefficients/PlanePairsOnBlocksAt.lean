import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Block

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def BlockDeg (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : Prop :=
  ∀ x : TL J nL r, ∑ c, rho (x, c) + lowP Fr p x * (dPl x + dNo x) = dd (posOf n' (posTL Fr x))

theorem blockDeg_of (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (mo : TV n' (m + 1) →₀ ℕ) (h1 : InLow Fr p hk nL rho mo) (h2 : InBlock Fr p hk nL dPl dNo mo)
    (h3 : ∀ t, ∑ c, mo (t, c) = dd t) : BlockDeg Fr p nL dd rho dPl dNo := by
  intro x
  rw [← h3, ← h2.1 x, ← h2.2 x]
  have e : ∑ c : Fin (m + 1), mo (posOf n' (posTL Fr x), c) =
      ∑ c : Fin (r + K), mo (posOf n' (posTL Fr x), Fin.cast hk.symm c) :=
    (Fintype.sum_equiv (finCongr hk.symm) _ _ (fun c => rfl)).symm
  rw [e, Fin.sum_univ_add, Fin.sum_univ_add]
  simp_rw [← h1.1 x, ← h1.2 x]
  have hA : ∑ a, mo (plVar Fr hk nL x a) = ∑ a, mo (plVar Fr hk nL x a) % lowP Fr p x +
      ∑ a, lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  have hB : ∑ b, mo (noVar Fr hk nL x b) = ∑ b, mo (noVar Fr hk nL x b) % lowP Fr p x +
      ∑ b, lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  change _ = ∑ a, mo (plVar Fr hk nL x a) + ∑ b, mo (noVar Fr hk nL x b)
  rw [hA, hB, mul_add, Finset.mul_sum, Finset.mul_sum]
  ring

end Block

def MemAtB (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (dd : Fin n' → ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ), BlockDeg Fr p Dt.nL dd rho dPl dNo →
    ∀ (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

section MemLin

variable (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (dd : Fin n' → ℕ)

def memSubB : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O)) where
  carrier := {F | MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F}
  add_mem' := by
    intro F G hF hG J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_add, oneT_add, planeCoeff_add]
    exact XX_add Dt (hF J Dt dPl dNo ka hT rho hb e he nu) (hG J Dt dPl dNo ka hT rho hb e he nu)
  zero_mem' := by
    intro J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_zero, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt
  smul_mem' := by
    intro c F hF J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_smul, oneT_smul, planeCoeff_smul]
    exact XX_smul Dt c (hF J Dt dPl dNo ka hT rho hb e he nu)

theorem memAtG_of_B (F : MvPolynomial (TV n' (m + 1)) (KK O)) (hdeg : ∀ mo ∈ F.support, ∀ t, ∑ c, mo (t, c) = dd t)
    (h : MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  by_cases hb : BlockDeg Fr p Dt.nL dd rho dPl dNo
  · exact h J Dt dPl dNo ka hT rho hb e he nu
  · have h0 : levImg Fr p hk Dt.nL rho dPl dNo F = 0 := by
      unfold levImg
      apply Finset.sum_eq_zero
      intro mo hmo
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hmo
      exact absurd (blockDeg_of Fr p hk Dt.nL dd rho dPl dNo mo h2 h3 (hdeg mo h1)) hb
    rw [h0, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt

end MemLin

def topDeg {n' k : ℕ} (ga : TV n' k →₀ ℕ) (t : Fin n') : ℕ := ∑ c, ga (t, c)

theorem castV_inj {n' m r K : ℕ} (hk : m + 1 = r + K) : Function.Injective (castV (n' := n') hk) := by
  intro u v huv
  have h1 : (castV hk u).1 = (castV hk v).1 := congrArg Prod.fst huv
  have h2 : (castV hk u).2 = (castV hk v).2 := congrArg Prod.snd huv
  exact Prod.ext h1 (Fin.cast_injective hk.symm h2)

theorem topDeg_castV {n' m r K : ℕ} (hk : m + 1 = r + K) (b : Fin n' × Fin (r + K) →₀ ℕ) (t : Fin n') :
    topDeg (b.mapDomain (castV hk)) t = ∑ c, b (t, c) := by
  unfold topDeg
  have hinj := castV_inj (n' := n') hk
  rw [← Fintype.sum_equiv (finCongr hk.symm) (fun c => (b.mapDomain (castV hk)) (t, Fin.cast hk.symm c)) _
    (fun c => rfl)]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finsupp.mapDomain_apply hinj b (t, c)

def PlanePairsOnBlocksAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ (E' : Fin n' → ℕ) (xs : ℤ → SegRing O r K),
      (∀ i : ℕ, i < F.J → xs i ∈ pairSet O r K F (i : ℤ)
        (g2mg p n' r K F (flatDeg lam0) (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x)
          (cPrime n' r TT.card c0 cpp cStar)) Y (i : ℤ)) (g2th p n' F (flatDeg lam0) (i : ℤ))) →
    ∀ l : Fin n' × Fin (r + K) →₀ ℕ, IsLabel p F l →
    ∀ ga ∈ (SPR O p F hrk (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)).support,
      MemAtB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
        (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t) (symG p O hk F l ga xs)

theorem rest5aMonoStep_of_B (C CLa : ℝ) (h : PlanePairsOnBlocksAt C CLa) : Lemma5aMonomialAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD b ga hga
  have hGen := hD.2.2.2.1.choose_spec.2 b
  set E' := hD.2.2.2.1.choose with hE'
  obtain ⟨xs, hxs, l, hl, hB, hdeg⟩ := hGen
  have e1 : MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (B b) * monomial ga 1) =
      symG p O hk F l ga xs := by rw [hB]; rfl
  apply memAtG_of_B 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)
  · intro mo hmo t
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ hmo
    obtain ⟨d, hd, g, hg, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ h1)
    have hg' := MvPolynomial.support_monomial_subset hg
    rw [Finset.mem_singleton] at hg'
    subst hg'
    have hd' := hd
    rw [MvPolynomial.support_rename_of_injective (castV_inj hk)] at hd'
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hd'
    have h2 : ∑ c, b' (t, c) = G2d F (flatDeg lam0) E' t :=
      ((MvPolynomial.mem_restrictSupport_iff O).1 hdeg) hb' t
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    rw [← h2, ← topDeg_castV hk b' t]
    rfl
  rw [e1]
  let mS : ℕ := mStar p F (r + K) (orbitWindowCount r de h' x) (p ^ goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar)
  let Sj : ℤ → Set (SegRing O r K) := fun jj =>
    pairSet O r K F jj (g2mg p n' r K F (flatDeg lam0) mS Y jj) (g2th p n' F (flatDeg lam0) jj)
  have hspan : ∀ i : ℕ, i < F.J → xs i ∈ Submodule.span O (Sj i) := fun i _ =>
    symbol_spaces_le_pair_span CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h' x) (2 * TT.card)) mS a Y (i : ℤ) (hxs i)
  exact symG_span p O hk F (memSubB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)) Sj l ga
    (fun xs' hxs' => h p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
      E' xs' hxs' l hl ga hga)
    xs hspan

def PlanePairsOnBlocks (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PlanePairsOnBlocksAt C CLa

theorem rest5aMono_of_B (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : PlanePairsOnBlocks D CLa Ck Crk Cdeg) :
    Lemma5aMonomial D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h2⟩ := h hA
  exact ⟨C₁, h1, fun C hC => rest5aMonoStep_of_B C CLa (h2 C hC)⟩

end Formalism.MainNotions.PairMembershipBlocks
