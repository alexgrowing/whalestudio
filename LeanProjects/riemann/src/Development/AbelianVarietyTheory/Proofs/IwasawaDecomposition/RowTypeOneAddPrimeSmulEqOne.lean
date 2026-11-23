import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.Cong

open GlobalTheory.LastSteps

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h : IsUnit (redP P (1 : E)) := by
    rw [GlobalTheory.TopStep.reduction_one₂]
    exact isUnit_one
  have h1 : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, GlobalTheory.TopStep.reduction_one₂, Units.val_one])
  unfold LocE.unitV
  rw [dif_pos h, h1, map_one, Units.val_one]

omit [StarRing E] in
theorem unitV_det_delta (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A : Fin t → Fin t → E}
    (hA : ∀ s s', A s s' = if s = s' then 1 else 0) : LocE.unitV χ (Matrix.det (Matrix.of fun s s' => A s s')) = 1 := by
  have : (Matrix.of fun s s' => A s s') = 1 := by
    ext s s'
    rw [Matrix.of_apply, hA, Matrix.one_apply]
  rw [this, Matrix.det_one, unitV_one]

omit [NumberField E] [StarRing E] in

theorem entB_id (q : ℕ) {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    LocE.entB q k₀ c n c n ex ex (LinearMap.id : HomE E (n + c) (n + c)) p p' = if p = p' then 1 else 0 := by
  have h1 : LocE.fIdx k₀ c n p < n + c := by
    unfold LocE.fIdx
    split_ifs <;> omega
  have h2 : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' ↔ p = p' := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    unfold LocE.fIdx at h
    split_ifs at h <;> omega
  unfold LocE.entB Loc.atN
  rw [dif_pos h1, LinearMap.id_apply]
  unfold Loc.eN
  by_cases h : p = p'
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h')), zero_mul]

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i)
      (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => unitV_det_delta _ fun s s' => ?_
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  rw [hM _ _ (h1 s) (h1 s')]
  simp [Fin.ext_iff]

omit [StarRing E] in
theorem int_delta {N : ℕ} {M : ℕ → ℕ → E} (hM : ∀ p p', p < N → p' < N → M p p' = if p = p' then 1 else 0)
    (p p' : ℕ) (h : p < N) (h' : p' < N) : IntAt P (M p p') := by
  rw [hM _ _ h h']
  split_ifs
  · exact GlobalTheory.TopStep.intAt_one
  · exact GlobalTheory.TopStep.intAt_zero

omit [StarRing E] in
theorem lamGv_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, GlobalTheory.TopStep.reduction_zero, AddChar.map_zero_eq_one]
  intro i hi
  have := Finset.mem_range.1 hi
  rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

omit [StarRing E] in
theorem lamGvS_delta {k₀ r t j : ℕ} (hk : k₀ ≤ r) {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, GlobalTheory.TopStep.reduction_zero,
    AddChar.map_zero_eq_one]
  all_goals
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

theorem lamQB_cong (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {y : HomE E (n + c) (n + c)}
    (hy : y ∈ homS (LocE.lamY P (qOf P) n c 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.lamQB ξ kj n (LinearMap.id + (qOf P : E) • y) = 1 := by
  unfold LocE.lamQB
  have hl : ∀ s : Fin (n - kj), kj + s.1 < n + c := fun s => by
    have := s.2
    omega
  have e : (fun s t : Fin (n - kj) => Loc.atN ((LinearMap.id + (qOf P : E) • y : HomE E (n + c) (n + c))
      (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
      fun s t : Fin (n - kj) => (if s = t then 1 else 0) + (qOf P : E) * y (Pi.single ⟨_, hl t⟩ 1) ⟨_, hl s⟩ := by
    funext s t
    unfold Loc.atN
    rw [dif_pos (hl s), eN_eq (hl t)]
    simp [Pi.single_apply, Fin.ext_iff]
  rw [e, unitV_congr ξ (redP_det_add_q (A := fun s t => if s = t then 1 else 0) (fun s t => ?_) fun s t => ?_),
    unitV_det_delta ξ fun _ _ => rfl, inv_one]
  · split_ifs
    · exact GlobalTheory.TopStep.intAt_one
    · exact GlobalTheory.TopStep.intAt_zero
  · simpa [LocE.scE] using mem_homS_sclLat.1 hy ⟨_, hl s⟩ ⟨_, hl t⟩

end Loc

theorem lamRow_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hj y hy
  have hN : R.N j + cOf R j = R.r + j * R.t := by
    unfold Ranks.N cOf Ranks.r
    rw [mul_add, mul_one]
    omega
  have hk : R.k ≤ R.N j := Nat.le_add_right _ _
  have hr : R.k ≤ R.r := by
    unfold Ranks.r
    omega
  unfold lamYat at hy
  unfold lamRow
  by_cases hP : P ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    have hZ := entB_int R.k (x := y) hy
    have hM : ∀ p p', p < R.r + j * R.t → p' < R.r + j * R.t →
        LocE.entB (qOf P) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1)
          (LinearMap.id : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) p p' = if p = p' then 1 else 0 :=
      fun p p' h h' => entB_id _ hk _ (hN ▸ h) (hN ▸ h')
    split_ifs
    · unfold LocE.lamGBS
      rw [entB_add_smul, lamGvS_congr _ _ (int_delta hM) hZ, lamGvS_delta _ _ hr hM]
    · unfold LocE.lamGB
      rw [entB_add_smul, lamGv_congr _ _ (int_delta hM) hZ, lamGv_delta _ _ hM]
  · rw [if_neg hP] at hy ⊢
    exact lamQB_cong _ _ _ _ hy

end GlobalTheory.Mem.Col2.IdxEx.Cong

end
