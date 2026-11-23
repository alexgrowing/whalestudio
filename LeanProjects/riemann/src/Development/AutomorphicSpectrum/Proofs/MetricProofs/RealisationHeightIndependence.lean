import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBaseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormIntegralVerticalInvarianceStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CoeffWord

theorem abs_le_expand {Λ : Type*} {m : ℕ} (T : Λ → Λ) (H : Λ) (Good : Λ → Prop) (G : (Fin m → Λ) → ℝ)
    (hadd : ∀ (L : Fin m → Λ) (i : Fin m) (C : Λ), (∀ j, Good (L j)) → Good C →
      G (Function.update L i (T C)) = G (Function.update L i C) + G (Function.update L i H))
    (hT : ∀ C, Good C → Good (T C)) (hH : Good H) (E : Fin m → Λ) (hE : ∀ i, Good (E i)) (M : ℝ)
    (hM : ∀ L : Fin m → Λ, (∀ i, L i = H ∨ L i = T (E i)) → |G L| ≤ M) :
    |G E| ≤ 2 ^ m * M := by
  classical
  have key : ∀ s : Finset (Fin m), ∀ L : Fin m → Λ, (∀ i ∈ s, L i = E i) →
      (∀ i, i ∉ s → L i = H ∨ L i = T (E i)) → |G L| ≤ 2 ^ s.card * M := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro L _ h
      simpa using hM L fun i => h i (by simp)
    | insert i s hi ih =>
      intro L h1 h2
      have hLi : L i = E i := h1 i (Finset.mem_insert_self _ _)
      have hgood : ∀ j, Good (L j) := by
        intro j
        by_cases hj : j ∈ insert i s
        · rw [h1 j hj]; exact hE j
        · rcases h2 j hj with h | h
          · rw [h]; exact hH
          · rw [h]; exact hT _ (hE j)
      have hs := hadd L i (E i) hgood (hE i)
      have hself : Function.update L i (E i) = L := by
        rw [← hLi]; exact Function.update_eq_self i L
      rw [hself] at hs
      have b : ∀ Y, (Y = H ∨ Y = T (E i)) → |G (Function.update L i Y)| ≤ 2 ^ s.card * M := by
        intro Y hY
        refine ih _ (fun j hj => ?_) (fun j hj => ?_)
        · have hji : j ≠ i := fun e => hi (e ▸ hj)
          rw [Function.update_of_ne hji]
          exact h1 j (Finset.mem_insert_of_mem hj)
        · by_cases hji : j = i
          · subst hji
            simpa using hY
          · rw [Function.update_of_ne hji]
            exact h2 j (by simp [hji, hj])
      obtain ⟨a1, a2⟩ := abs_le.1 (b _ (Or.inr rfl))
      obtain ⟨c1, c2⟩ := abs_le.1 (b _ (Or.inl rfl))
      have e : (2 : ℝ) ^ (insert i s).card * M = 2 * (2 ^ s.card * M) := by
        rw [Finset.card_insert_of_notMem hi, pow_succ]; ring
      rw [e]
      exact abs_le.2 ⟨by linarith, by linarith⟩
  simpa using key Finset.univ E (fun i _ => rfl) (fun i hi => absurd (Finset.mem_univ i) hi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem abs_sub_le_telescope (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) (A B : Fin (D + 1) → HermLine ι)
    (hA : ∀ j, IsSmoothHerm (A j)) (hB : ∀ j, IsSmoothHerm (B j)) (M : ℝ)
    (h : ∀ (k : Fin (D + 1)) (E : Fin D → HermLine ι), (∀ i, ∃ r, E i = A r ∨ E i = B r) →
      |II K ι P (D + 1) (Fin.snoc E (A k)) - II K ι P (D + 1) (Fin.snoc E (B k))| ≤ M) :
    |II K ι P (D + 1) A - II K ι P (D + 1) B| ≤ ((D : ℝ) + 1) * M := by
  classical
  let X : ℕ → Fin (D + 1) → HermLine ι := fun k i => if (i : ℕ) < k then B i else A i
  have hX : ∀ k j, IsSmoothHerm (X k j) := by
    intro k j
    simp only [X]
    split_ifs
    · exact hB j
    · exact hA j
  have hsym := (hII.1 K ι).1
  have step : ∀ k (hk : k < D + 1), |II K ι P (D + 1) (X k) - II K ι P (D + 1) (X (k + 1))| ≤ M := by
    intro k hk
    let kk : Fin (D + 1) := ⟨k, hk⟩
    let τ : Equiv.Perm (Fin (D + 1)) := Equiv.swap kk (Fin.last D)
    let E : Fin D → HermLine ι := fun i => X k (τ i.castSucc)
    have hτl : τ (Fin.last D) = kk := Equiv.swap_apply_right _ _
    have e1 : X k ∘ τ = Fin.snoc E (A kk) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [hτl, X, kk]
      · simp [E]
    have e2 : X (k + 1) ∘ τ = Fin.snoc E (B kk) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [hτl, X, kk]
      · have hne : τ i.castSucc ≠ kk := fun e => by
          have : τ i.castSucc = τ (Fin.last D) := e.trans hτl.symm
          exact (Fin.castSucc_lt_last i).ne (τ.injective this)
        have hne' : ((τ i.castSucc : Fin (D + 1)) : ℕ) ≠ k := fun e => hne (Fin.ext e)
        simp only [Function.comp, Fin.snoc_castSucc, E, X]
        by_cases h1 : ((τ i.castSucc : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [← hsym P _ (X k) τ hP (hX k), ← hsym P _ (X (k + 1)) τ hP (hX (k + 1)), e1, e2]
    refine h kk E fun i => ⟨τ i.castSucc, ?_⟩
    simp only [E, X]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have ind : ∀ k, k ≤ D + 1 → |II K ι P (D + 1) (X 0) - II K ι P (D + 1) (X k)| ≤ (k : ℝ) * M := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨a1, a2⟩ := abs_le.1 (ih (by omega))
      obtain ⟨c1, c2⟩ := abs_le.1 (step k (by omega))
      push_cast
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have h0 : X 0 = A := by
    funext i
    simp [X]
  have h1 : X (D + 1) = B := by
    funext i
    simp [X, i.isLt]
  have := ind (D + 1) le_rfl
  rw [h0, h1] at this
  simpa using this

theorem vertClose_tensor {P : Ideal (MRing ι)} {T : Finset ℕ} {α : ℕ → ℝ} {A B : HermLine ι}
    (h : VertClose P T α A B) (H : HermLine ι) : VertClose P T α (A.tensor H) (B.tensor H) := by
  obtain ⟨f, g, df, dg, hf, hg, hfP, hgP, hd, hn, h1, h2⟩ := h
  refine ⟨f, g, df, dg, hf, hg, hfP, hgP, fun k => ?_, fun z hz => ?_, h1, h2⟩
  · have := hd k
    simp only [HermLine.tensor, Pi.add_apply]
    linarith
  · have := hn z hz
    simp only [HermLine.tensor]
    rw [← mul_assoc, this, mul_assoc]

theorem holoOn_sub_set {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ}
    (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g := fun j =>
  (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem samePot_tensor {P J : Ideal (MRing ι)} {D : ℕ} (R : AnLogRes P J D) {Y : Type} [TopologicalSpace Y]
    {π : R.X → Y} (hπ : Continuous π) {A B : HermLine ι} {Q Q' W : LocPot Y}
    (hA : SamePot R.A Set.univ (potOf R A) (Q.pullback π hπ))
    (hB : SamePot R.A Set.univ (potOf R B) (Q'.pullback π hπ))
    (hW : ∀ x y, W.φ x y = Q.φ x y + Q'.φ x y) :
    SamePot R.A Set.univ (potOf R (A.tensor B)) (W.pullback π hπ) := by
  intro x _
  obtain ⟨V₁, o₁, m₁, G₁, h₁, e₁⟩ := hA x trivial
  obtain ⟨V₂, o₂, m₂, G₂, h₂, e₂⟩ := hB x trivial
  refine ⟨(V₁ ∩ V₂) ∩ R.U x, (o₁.inter o₂).inter (R.isOpen_U x), ⟨⟨m₁, m₂⟩, R.mem_U x⟩, fun z => G₁ z + G₂ z,
    holoOn_sub_set (holoOn_add R.A h₁ h₂) Set.inter_subset_left, ?_⟩
  rintro y ⟨⟨y1, y2⟩, y3⟩
  have hz := (R.mem x y y3).1
  have a1 := e₁ y y1
  have a2 := e₂ y y2
  simp only [potOf, LocPot.pullback, HermLine.tensor] at a1 a2 ⊢
  rw [Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne', hW, Complex.add_re]
  linarith

theorem samePot_congr {P J : Ideal (MRing ι)} {D : ℕ} (R : AnLogRes P J D) {Y : Type} [TopologicalSpace Y]
    {π : R.X → Y} (hπ : Continuous π) {A : HermLine ι} {Q W : LocPot Y}
    (hA : SamePot R.A Set.univ (potOf R A) (Q.pullback π hπ)) (hW : ∀ x y, W.φ x y = Q.φ x y) :
    SamePot R.A Set.univ (potOf R A) (W.pullback π hπ) := by
  intro x hx
  obtain ⟨V, o, m, G, h, e⟩ := hA x hx
  refine ⟨V, o, m, G, h, fun y hy => ?_⟩
  have := e y hy
  simp only [LocPot.pullback] at this ⊢
  rw [hW]
  exact this

variable {D : ℕ} {σ : Type}

def wordPot (S : AnSys D σ) (thH : LocPot S.X) (v : Option σ) : LocPot S.X :=
  v.elim thH fun a => S.th a + thH

def wordU (S : AnSys D σ) (t : ℝ) (v : Option σ) : S.X → ℝ :=
  v.elim (fun _ => 0) fun a => S.phT a t

def wordNum (S : AnSys D σ) (thH : LocPot S.X) (v : Fin D → Option σ) : ℝ :=
  mInt S.A (fun j => wordPot S thH (v j)) fun _ => 1

def wordBound [Fintype σ] (S : AnSys D σ) (thH : LocPot S.X) : ℝ :=
  ∑ v : Fin D → Option σ, |wordNum S thH v|

def wLine {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (H : HermLine ι) (t : ℝ) (v : Option σ) :
    HermLine ι :=
  v.elim H fun a => (Re.line a t).tensor H

theorem pts_wLine (hE : ResExistsStatement) {S : AnSys D σ} [Fintype σ] {P : Ideal (MRing ι)} (Re : Realis S P)
    {thH : LocPot S.X} (hth : IsPotential S.A thH) {H : HermLine ι} (hHs : IsSmoothHerm H)
    (hHp : SamePot Re.R.A Set.univ (potOf Re.R H) (thH.pullback Re.π Re.holo.1))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ S.t₀) (v : Fin D → Option σ) :
    ptsIntegral P (pot fun i => wLine Re H t (v i)) (fun _ => 1) = Re.deg * wordNum S thH v := by
  have hΦ0 : ∀ i, IsPotential S.A (wordPot S thH (v i)) := by
    intro i
    cases v i with
    | none => exact hth
    | some a => exact isPotentialAdd _ _ _ (S.sing a).1 hth
  have hu : ∀ i, S.A.Smooth (wordU S t (v i)) := by
    intro i
    cases v i with
    | none => exact fun _ => contDiffOn_const
    | some a => exact ((S.reg a).2.2 t ht0 ht1).1
  have hΦ : ∀ i, IsPotential S.A (wordPot S thH (v i) + LocPot.ofFun (wordU S t (v i))) := fun i =>
    isPotentialAdd _ _ _ (hΦ0 i) (isPotential_ofFun _ _ (hu i))
  have hsm : ∀ i, IsSmoothHerm (wLine Re H t (v i)) := by
    intro i
    cases v i with
    | none => exact hHs
    | some a => exact isSmoothHerm_tensor (Re.line_smooth a t ht0 ht1) hHs
  have hpot : ∀ i, SamePot Re.R.A Set.univ (potOf Re.R (wLine Re H t (v i)))
      ((wordPot S thH (v i) + LocPot.ofFun (wordU S t (v i))).pullback Re.π Re.holo.1) := by
    intro i
    cases v i with
    | none =>
      refine samePot_congr Re.R Re.holo.1 hHp fun x y => ?_
      show thH.φ x y + 0 = thH.φ x y
      ring
    | some a =>
      refine samePot_tensor Re.R Re.holo.1
        ((GlobalTheory.T.realisation_potential_degree_compatibility hE K ι D σ S P Re).1 a t ht0 ht1) hHp fun x y => ?_
      show (S.th a).φ x y + thH.φ x y + S.phT a t y = (S.th a).φ x y + S.phT a t y + thH.φ x y
      ring
  have h1P : (1 : MRing ι) ∉ P := fun h => Re.arith.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hrat : IsRatSectionOn P (oneLine (ι := ι)) 1 1 := by
    obtain ⟨a, ha, hs, hP⟩ := isSectionOn_one (P := P) Re.arith.2.1.1 (B := oneLine (ι := ι)) rfl
    exact ⟨a, a, hs, hs, hP, hP, fun k => by rw [sub_self]; rfl⟩
  have e1 : (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) = logNormRat (oneLine (ι := ι)) 1 1 := by
    funext z
    have := logNorm_oneLine (ι := ι) z
    unfold logNorm at this
    unfold logNormRat
    simpa using this.symm
  have key := GlobalTheory.T.intersection_number_pullback_degree_alt hE K ι P Re.J D Re.R S.X S.A Re.π Re.holo Re.deg Re.br Re.arith Re.degree
    (fun i => wLine Re H t (v i)) (fun i => wordPot S thH (v i) + LocPot.ofFun (wordU S t (v i))) hsm hΦ hpot
    (oneLine (ι := ι)) 1 1 (fun _ => 1) ∅ isSmoothHerm_oneLine hrat (fun j => by simp)
    (fun x _ => congrFun e1.symm _) (mIntegrableCont _ _ hΦ _ continuous_const)
  rw [e1, key, massIndep S.A _ _ hΦ0 hu]
  rfl

theorem abs_pts_le (hE : ResExistsStatement) {S : AnSys D σ} [Fintype σ] {P : Ideal (MRing ι)}
    (Re Re' : Realis S P) {thH : LocPot S.X} (hth : IsPotential S.A thH) {T : Finset ℕ} {α : ℕ → ℝ}
    {H : HermLine ι} (hHs : IsSmoothHerm H)
    (hHp : SamePot Re.R.A Set.univ (potOf Re.R H) (thH.pullback Re.π Re.holo.1))
    (hV : ∀ a t, 0 < t → t ≤ S.t₀ → VertClose P T α (Re.line a t) (Re'.line a t))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ S.t₀) (L : Fin D → HermLine ι)
    (hL : ∀ i, L i = H ∨ ∃ a, L i = (Re.line a t).tensor H ∨ L i = (Re'.line a t).tensor H) :
    |ptsIntegral P (pot L) fun _ => 1| ≤ Re.deg * wordBound S thH := by
  have hv : ∀ i, ∃ v : Option σ, L i = wLine Re H t v ∨ VertClose P T α (wLine Re H t v) (L i) := by
    intro i
    rcases hL i with h | ⟨a, h | h⟩
    · exact ⟨none, Or.inl h⟩
    · exact ⟨some a, Or.inl h⟩
    · refine ⟨some a, Or.inr ?_⟩
      rw [h]
      exact vertClose_tensor (hV a t ht0 ht1) H
  choose v hv using hv
  have hsm0 : ∀ i, IsSmoothHerm (wLine Re H t (v i)) := by
    intro i
    cases v i with
    | none => exact hHs
    | some a => exact isSmoothHerm_tensor (Re.line_smooth a t ht0 ht1) hHs
  have hsm : ∀ i, IsSmoothHerm (L i) := by
    intro i
    rcases hL i with h | ⟨a, h | h⟩ <;> rw [h]
    · exact hHs
    · exact isSmoothHerm_tensor (Re.line_smooth a t ht0 ht1) hHs
    · exact isSmoothHerm_tensor (Re'.line_smooth a t ht0 ht1) hHs
  have e1 : (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) = logNorm (oneLine (ι := ι)) 1 :=
    funext fun z => (logNorm_oneLine z).symm
  have hsame : ptsIntegral P (pot L) (fun _ => 1) =
      ptsIntegral P (pot fun i => wLine Re H t (v i)) (fun _ => 1) := by
    rw [e1]
    exact (GlobalTheory.T.log_norm_integral_vertical_invariance hE K ι P D _ L T α Re.arith hsm0 hsm
      (fun j => (hv j).imp Eq.symm id) oneLine 1 isSmoothHerm_oneLine
      (isSectionOn_one Re.arith.2.1.1 rfl)).symm
  rw [hsame, pts_wLine hE Re hth hHs hHp ht0 ht1 v, abs_mul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Finset.single_le_sum (f := fun v => |wordNum S thH v|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)

end GlobalTheory.CompanionTheory.Ar.PB.CoeffWord

namespace GlobalTheory.CompanionTheory.Ar.PB

open CoeffWord

theorem abs_num_sub_num_le : Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (thH : LocPot S.X),
    IsPotential S.A thH → ∃ C₂ : ℝ, ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re Re' : Realis S P)
      (T : Finset ℕ) (α : ℕ → ℝ) (H : HermLine ι), Re'.deg = Re.deg → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) →
      IsSmoothHerm H → SamePot Re.R.A Set.univ (potOf Re.R H) (thH.pullback Re.π Re.holo.1) →
      (∀ a t, 0 < t → t ≤ S.t₀ → VertClose P T α (Re.line a t) (Re'.line a t)) →
      (∀ p ∈ T, NefAt P p H.a ∧ ∀ a, NefAt P p ((Re.ref a).a + H.a) ∧ NefAt P p ((Re'.ref a).a + H.a)) →
      ∀ t, 0 < t → t ≤ S.t₀ → ∀ w, |Re.num II t w - Re'.num II t w| ≤ C₂ * ∑ p ∈ T, α p * Real.log p := by
  intro hI D σ _ S thH hth
  refine ⟨((D : ℝ) + 1) * 2 ^ D * wordBound S thH, ?_⟩
  intro II hII K _ ι _ P Re Re' T α H hdeg hTp hHs hHp hV hN t ht0 ht1 w
  have hP := Re.arith
  have hE : ResExistsStatement := hI.resExists
  have hSg0 : 0 ≤ ∑ p ∈ T, α p * Real.log p :=
    Finset.sum_nonneg fun p hp => mul_nonneg (hTp p hp).2 (Real.log_natCast_nonneg p)
  have hA : ∀ j, IsSmoothHerm (Re.line (w j) t) := fun j => Re.line_smooth _ _ ht0 ht1
  have hB : ∀ j, IsSmoothHerm (Re'.line (w j) t) := fun j => Re'.line_smooth _ _ ht0 ht1
  have main : |II K ι P (D + 1) (fun j => Re.line (w j) t) - II K ι P (D + 1) (fun j => Re'.line (w j) t)| ≤
      ((D : ℝ) + 1) * (2 ^ D * ((∑ p ∈ T, α p * Real.log p) * (Re.deg * wordBound S thH))) := by
    refine abs_sub_le_telescope II hII hP _ _ hA hB _ fun k E hEE => ?_
    have hEs : ∀ i, IsSmoothHerm (E i) := by
      intro i
      obtain ⟨r, h | h⟩ := hEE i <;> rw [h]
      · exact hA r
      · exact hB r
    refine abs_le_expand (fun C => C.tensor H) H IsSmoothHerm
      (fun L => II K ι P (D + 1) (Fin.snoc L (Re.line (w k) t)) -
        II K ι P (D + 1) (Fin.snoc L (Re'.line (w k) t))) ?_
      (fun C hC => isSmoothHerm_tensor hC hHs) hHs E hEs _ ?_
    · intro L i C hL hC
      have hs : ∀ (Z : HermLine ι), IsSmoothHerm Z →
          ∀ j, IsSmoothHerm ((Fin.snoc L Z : Fin (D + 1) → HermLine ι) j) := by
        intro Z hZ j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using hZ
        · simpa using hL i
      have m1 := hII.2.1 K ι P (D + 1) (Fin.snoc L (Re.line (w k) t)) i.castSucc C H hP (hs _ (hA k)) hC hHs
      have m2 := hII.2.1 K ι P (D + 1) (Fin.snoc L (Re'.line (w k) t)) i.castSucc C H hP (hs _ (hB k)) hC hHs
      simp only [Fin.snoc_update]
      rw [m1, m2]
      ring
    · intro L hL
      have hE' : ∀ i, L i = H ∨ ∃ a, L i = (Re.line a t).tensor H ∨ L i = (Re'.line a t).tensor H := by
        intro i
        rcases hL i with h | h
        · exact Or.inl h
        · obtain ⟨r, e | e⟩ := hEE i
          · exact Or.inr ⟨w r, Or.inl (by rw [h, e])⟩
          · exact Or.inr ⟨w r, Or.inr (by rw [h, e])⟩
      have hLs : ∀ j, IsSmoothHerm (L j) := by
        intro j
        rcases hL j with h | h <;> rw [h]
        · exact hHs
        · exact isSmoothHerm_tensor (hEs j) hHs
      have hnef : ∀ p ∈ T, ∀ j, NefAt P p (L j).a := by
        intro p hp j
        rcases hE' j with h | ⟨a, h | h⟩ <;> rw [h]
        · exact (hN p hp).1
        · show NefAt P p ((Re.line a t).a + H.a)
          rw [Re.line_deg]
          exact ((hN p hp).2 a).1
        · show NefAt P p ((Re'.line a t).a + H.a)
          rw [Re'.line_deg]
          exact ((hN p hp).2 a).2
      refine (GlobalTheory.T.intersection_vertical_perturbation_bound hI II hII K ι P D L _ _ T α hP hLs (hA k) (hB k) hTp (hV _ t ht0 ht1) hnef).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hSg0
      exact (le_abs_self _).trans (abs_pts_le hE Re Re' hth hHs hHp hV ht0 ht1 L hE')
  have hd : (0 : ℝ) < Re.deg := Nat.cast_pos.2 Re.deg_pos
  rw [Realis.num, Realis.num, hdeg, ← sub_div, abs_div, Nat.abs_cast, div_le_iff₀ hd]
  refine main.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.Ar.PB
