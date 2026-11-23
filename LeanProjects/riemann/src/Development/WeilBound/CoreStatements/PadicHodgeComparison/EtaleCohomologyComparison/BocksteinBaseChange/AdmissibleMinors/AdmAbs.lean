import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailAlt

noncomputable section

open Matrix

namespace CrystallineSemistableComparison.AdmAbs

variable {F : Type*} [Field F] {Γ : Type*} (σ : Γ → F →+* F) (S : Subring F) {X : Type*}

def Indep {r : ℕ} (w : Fin r → X → F) : Prop :=
  ∀ μ : Fin r → F, (∀ i, μ i ∈ S) → (∀ i g, σ g (μ i) = μ i) → (∀ x, ∑ i, μ i * w i x = 0) → μ = 0

theorem reduce (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S) :
    ∀ (r : ℕ) (w : Fin r → X → F), (∀ i x g, σ g (w i x) = w i x) →
    ∃ (r' : ℕ) (w' : Fin r' → X → F), (∀ i x g, σ g (w' i x) = w' i x) ∧ Indep σ S w' ∧
      ∀ β : Fin r → F, (∀ i, β i ∈ S) → ∃ β' : Fin r' → F, (∀ i, β' i ∈ S) ∧
        ∀ x, ∑ i, β i * w i x = ∑ i, β' i * w' i x := by
  intro r
  induction r with
  | zero =>
    intro w hw
    exact ⟨0, w, hw, fun μ _ _ _ => funext fun i => i.elim0, fun β hβ => ⟨β, hβ, fun _ => rfl⟩⟩
  | succ r ih =>
    intro w hw
    by_cases hI : Indep σ S w
    · exact ⟨r + 1, w, hw, hI, fun β hβ => ⟨β, hβ, fun _ => rfl⟩⟩
    · simp only [Indep, not_forall] at hI
      obtain ⟨μ, hμS, hμσ, hμw, hμ0⟩ := hI
      obtain ⟨i0, hi0⟩ : ∃ i0, μ i0 ≠ 0 := by
        by_contra h
        push Not at h
        exact hμ0 (funext h)
      obtain ⟨lam, hlamS, hw0⟩ : ∃ lam : Fin r → F, (∀ i, lam i ∈ S) ∧
          ∀ x, w i0 x = ∑ i, lam i * w (i0.succAbove i) x := by
        refine ⟨fun i => -μ (i0.succAbove i) / μ i0, fun i => ?_, fun x => ?_⟩
        · refine hfrac (-μ (i0.succAbove i)) (S.neg_mem (hμS _)) (μ i0) (hμS i0) _ ?_ hi0 ?_
          · exact div_mul_cancel₀ _ hi0
          · intro g
            rw [map_div₀, map_neg, hμσ, hμσ]
        · have h := hμw x
          rw [Fin.sum_univ_succAbove _ i0] at h
          have h' : μ i0 * w i0 x = -∑ i, μ (i0.succAbove i) * w (i0.succAbove i) x :=
            eq_neg_of_add_eq_zero_left h
          apply mul_left_cancel₀ hi0
          rw [h', Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
      obtain ⟨r', w', hw', hI', hmap⟩ := ih (fun i => w (i0.succAbove i)) (fun i x g => hw _ x g)
      refine ⟨r', w', hw', hI', fun β hβ => ?_⟩
      obtain ⟨β', hβ', heq⟩ := hmap (fun i => β (i0.succAbove i) + β i0 * lam i)
        (fun i => S.add_mem (hβ _) (S.mul_mem (hβ _) (hlamS i)))
      have heq' : ∀ x, ∑ i, (β (i0.succAbove i) + β i0 * lam i) * w (i0.succAbove i) x =
          ∑ i, β' i * w' i x := heq
      refine ⟨β', hβ', fun x => ?_⟩
      rw [← heq' x, Fin.sum_univ_succAbove _ i0, hw0 x, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem indep_S (hstab : ∀ g, ∀ x ∈ S, σ g x ∈ S)
    (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S)
    {r : ℕ} (w : Fin r → X → F) (hw : ∀ i x g, σ g (w i x) = w i x) (hI : Indep σ S w) :
    ∀ s : Fin r → F, (∀ i, s i ∈ S) → (∀ x, ∑ i, s i * w i x = 0) → s = 0 := by
  suffices h : ∀ T : Finset (Fin r), ∀ s : Fin r → F, (∀ i, s i ∈ S) → (∀ i ∉ T, s i = 0) →
      (∀ x, ∑ i, s i * w i x = 0) → s = 0 from
    fun s hs hsw => h Finset.univ s hs (fun i hi => absurd (Finset.mem_univ i) hi) hsw
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro s hs hT hsw
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i0, s i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hi0T : i0 ∈ T := by
    by_contra h
    exact hi0 (hT i0 h)
  have key : ∀ g i, σ g (s i0) * s i = s i0 * σ g (s i) := by
    intro g
    have hsupp : ∀ i ∉ T.erase i0, σ g (s i0) * s i - s i0 * σ g (s i) = 0 := by
      intro i hi
      rcases eq_or_ne i i0 with rfl | h
      · ring
      · have h0 : s i = 0 := hT i fun hiT => hi (Finset.mem_erase.2 ⟨h, hiT⟩)
        rw [h0, map_zero]
        ring
    have hrel : ∀ x, ∑ i, (σ g (s i0) * s i - s i0 * σ g (s i)) * w i x = 0 := by
      intro x
      have h1 := hsw x
      have h2 : ∑ i, σ g (s i) * w i x = 0 := by
        have h3 := congrArg (σ g) h1
        rw [map_sum, map_zero] at h3
        simpa only [map_mul, hw] using h3
      calc ∑ i, (σ g (s i0) * s i - s i0 * σ g (s i)) * w i x
          = σ g (s i0) * ∑ i, s i * w i x - s i0 * ∑ i, σ g (s i) * w i x := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h1, h2]; ring
    have := ih (T.erase i0) (Finset.erase_ssubset hi0T) (fun i => σ g (s i0) * s i - s i0 * σ g (s i))
      (fun i => S.sub_mem (S.mul_mem (hstab g _ (hs i0)) (hs i)) (S.mul_mem (hs i0) (hstab g _ (hs i))))
      hsupp hrel
    intro i
    exact sub_eq_zero.1 (congr_fun this i)
  have hlam := hI (fun i => s i / s i0) (fun i => ?_) (fun i g => ?_) (fun x => ?_)
  · have h1 := congr_fun hlam i0
    simp only [div_self hi0, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · refine hfrac (s i) (hs i) (s i0) (hs i0) _ (div_mul_cancel₀ _ hi0) hi0 fun g => ?_
    have hne' : σ g (s i0) ≠ 0 := (map_ne_zero (σ g)).2 hi0
    rw [map_div₀, div_eq_div_iff hne' hi0]
    linear_combination (-1 : F) * key g i
  · have hne' : σ g (s i0) ≠ 0 := (map_ne_zero (σ g)).2 hi0
    rw [map_div₀, div_eq_div_iff hne' hi0]
    linear_combination (-1 : F) * key g i
  · have : ∑ i, s i / s i0 * w i x = (∑ i, s i * w i x) / s i0 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsw x, zero_div]

theorem exists_minor {r a : ℕ} (M : Matrix (Fin r) (Fin a) F) (hM : ∀ z : Fin a → F, M *ᵥ z = 0 → z = 0) :
    ∃ e : Fin a → Fin r, (M.submatrix e id).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Yra1.main M hM

omit [Field F] in
theorem det_mem' [Field F] (S : Subring F) {a : ℕ} (A : Matrix (Fin a) (Fin a) F) (hA : ∀ i j, A i j ∈ S) :
    A.det ∈ S ∧ ∀ i j, A.adjugate i j ∈ S := by
  have h : A = S.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hA i j⟩ : S)) := by
    ext i j
    rfl
  refine ⟨?_, fun i j => ?_⟩
  · rw [h, ← RingHom.map_det]
    exact SetLike.coe_mem _
  · rw [h, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _

theorem admissible_of_absolute (hstab : ∀ g, ∀ x ∈ S, σ g x ∈ S)
    (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S)
    {a r : ℕ} (ρ : Γ → Matrix (Fin a) (Fin a) F) (hρS : ∀ g i j, ρ g i j ∈ S)
    (heig : ∀ x ∈ S, x ≠ 0 → (∀ g, σ g x = (ρ g).det * x) → ∃ y ∈ S, x * y = 1)
    (c : Fin a → X → F) (hcσ : ∀ g j x, σ g (c j x) = ∑ k, ρ g k j * c k x)
    (hcinj : ∀ z : Fin a → F, (∀ x, ∑ j, z j * c j x = 0) → z = 0)
    (w : Fin r → X → F) (hw : ∀ i x g, σ g (w i x) = w i x)
    (hspan : ∀ j, ∃ β : Fin r → F, (∀ i, β i ∈ S) ∧ ∀ x, c j x = ∑ i, β i * w i x) :
    ∃ P Q : Matrix (Fin a) (Fin a) F, (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
      ∀ g, ρ g * P.map (σ g) = P := by
  obtain ⟨r', w', hw', hI', hmap⟩ := reduce σ S hfrac r w hw
  have hsp' : ∀ j, ∃ β : Fin r' → F, (∀ i, β i ∈ S) ∧ ∀ x, c j x = ∑ i, β i * w' i x := by
    intro j
    obtain ⟨β, hβ, hc⟩ := hspan j
    obtain ⟨β', hβ', he⟩ := hmap β hβ
    exact ⟨β', hβ', fun x => (hc x).trans (he x)⟩
  choose β hβS hβc using hsp'
  have hβσ : ∀ g i j, σ g (β j i) = ∑ k, β k i * ρ g k j := by
    intro g i j
    have h := indep_S σ S hstab hfrac w' hw' hI' (fun i => σ g (β j i) - ∑ k, β k i * ρ g k j)
      (fun i => S.sub_mem (hstab g _ (hβS j i)) (sum_mem fun k _ => S.mul_mem (hβS k i) (hρS g k j)))
      (fun x => by
        have e1 : σ g (c j x) = ∑ i, σ g (β j i) * w' i x := by
          rw [hβc j x, map_sum]
          simp only [map_mul, hw']
        have e2 : ∑ k, ρ g k j * c k x = ∑ i, (∑ k, β k i * ρ g k j) * w' i x := by
          simp only [hβc _ x, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← e1, ← e2, hcσ, sub_self])
    exact sub_eq_zero.1 (congr_fun h i)
  obtain ⟨e, he⟩ := exists_minor (Matrix.of fun i j => β j i) fun z hz => hcinj z fun x => by
    have h0 : ∀ i, ∑ j, β j i * z j = 0 := fun i => by
      have := congr_fun hz i
      simpa [Matrix.mulVec, dotProduct] using this
    calc ∑ j, z j * c j x = ∑ i, (∑ j, β j i * z j) * w' i x := by
          simp only [hβc _ x, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [h0]
  let Q : Matrix (Fin a) (Fin a) F := Matrix.of fun k j => β j (e k)
  have hQS : ∀ i j, Q i j ∈ S := fun i j => hβS _ _
  have hQ : Q.det ≠ 0 := he
  have hQσ : ∀ g, Q.map (σ g) = Q * ρ g := by
    intro g
    ext k j
    simp only [Matrix.map_apply, Matrix.mul_apply, Q, Matrix.of_apply]
    exact hβσ g (e k) j
  obtain ⟨hdS, hadjS⟩ := det_mem' S Q hQS
  obtain ⟨y, hyS, hy⟩ := heig Q.det hdS hQ fun g => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hQσ g, Matrix.det_mul, mul_comm]
  let P : Matrix (Fin a) (Fin a) F := y • Q.adjugate
  have hPQ : P * Q = 1 := by
    simp only [P, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hy, one_smul]
  have hQP : Q * P = 1 := by
    simp only [P, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm y, hy, one_smul]
  refine ⟨P, Q, fun i j => ⟨?_, hQS i j⟩, hPQ, fun g => ?_⟩
  · simp only [P, Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hyS (hadjS i j)
  · have h1 : Q.map (σ g) * P.map (σ g) = 1 := by
      rw [← Matrix.map_mul, hQP]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    calc ρ g * P.map (σ g) = (P * Q) * (ρ g * P.map (σ g)) := by rw [hPQ, Matrix.one_mul]
      _ = P * ((Q * ρ g) * P.map (σ g)) := by simp only [Matrix.mul_assoc]
      _ = P * (Q.map (σ g) * P.map (σ g)) := by rw [hQσ g]
      _ = P := by rw [h1, Matrix.mul_one]

end CrystallineSemistableComparison.AdmAbs
