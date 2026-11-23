import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FreeN
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.StabRef

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_zero : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  rwa [map_zero] at this

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (intAt_zero (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_locP' {n : ℕ} (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L := Iff.rfl

theorem mem_stdLat' {n : ℕ} (x : Sp E n) : x ∈ stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem mem_locStd {n : ℕ} (x : Sp E n) : x ∈ localization₂ P.asIdeal (stdLat E n) ↔ ∀ i, IntAt P (x i) := by
  constructor
  · intro hx i
    obtain ⟨s, hs, h⟩ := (mem_locP' _ x).1 hx
    obtain ⟨r, hr⟩ := (mem_stdLat' _).1 h i
    exact ⟨r, s, hs, by rw [hr, Pi.smul_apply, Algebra.smul_def]⟩
  · intro H
    have : x = ∑ i, (Pi.single i (x i) : Sp E n) := (Finset.univ_sum_single x).symm
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, h⟩ := H i
    refine (mem_locP' _ _).2 ⟨s, hs, ?_⟩
    have e : s • (Pi.single i (x i) : Sp E n) = Pi.single i (algebraMap (𝓞 E) E r) := by
      rw [← Pi.single_smul, Algebra.smul_def, ← h]
    rw [e]
    rw [mem_stdLat']
    intro j
    by_cases hj : j = i
    · subst hj
      exact ⟨r, by simp⟩
    · exact ⟨0, by simp [hj]⟩

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_locStd]
  simp [LinearMap.pi_apply, smul_eq_mul]

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

theorem fPos_lt {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fPos
  split_ifs <;> omega

theorem eN_eq {N i : ℕ} (hi : i < N) : Loc.eN E N i = Pi.single (⟨i, hi⟩ : Fin N) (1 : E) := by
  funext l
  unfold Loc.eN
  by_cases h : l = ⟨i, hi⟩
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg (fun h' => h (Fin.ext h'))]

theorem apply_sum {N : ℕ} (φ : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (l : Fin N) :
    φ v l = ∑ l' : Fin N, φ (Pi.single l' 1) l * v l' := by
  have hv : v = ∑ l' : Fin N, v l' • (Pi.single l' (1 : E) : Sp E N) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem entB_eq {k₀ n c p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p' =
      κ (Pi.single (⟨LocE.fIdx k₀ c n p', fIdx_lt hk hp'⟩ : Fin (n + c)) 1) ⟨LocE.fIdx k₀ c n p, fIdx_lt hk hp⟩ *
        (q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') - LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) := by
  unfold LocE.entB
  rw [eN_eq (fIdx_lt hk hp')]
  unfold Loc.atN
  rw [dif_pos (fIdx_lt hk hp)]
  rfl

theorem bas_mem (hq0 : (q : E) ≠ 0) {n c : ℕ} (l' : Fin (n + c)) :
    ((q : E) ^ LocE.scE n (fun i => i + 1) l'.1) • (Pi.single l' (1 : E) : Sp E (n + c)) ∈
      LocE.lamY P q n c (fun i => i + 1) := by
  unfold LocE.lamY
  rw [mem_sclLat]
  intro l
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h : l = l'
  · subst h
    rw [Pi.single_eq_same, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
    have := IntAt.coe P 1
    rwa [map_one] at this
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]
    exact intAt_zero

theorem coord_int (hq0 : (q : E) ≠ 0) {n c : ℕ} {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hκ : κ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) (l l' : Fin (n + c)) :
    IntAt P (κ (Pi.single l' 1) l * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) := by
  have h1 := (hκ _).2 (bas_mem (P := P) hq0 l')
  unfold LocE.lamY at h1
  rw [mem_sclLat] at h1
  have h2 := h1 l
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  have e : ((q : E) ^ LocE.scE n (fun i => i + 1) l.1)⁻¹ * ((q : E) ^ LocE.scE n (fun i => i + 1) l'.1 * κ (Pi.single l' 1) l) =
      κ (Pi.single l' 1) l * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1) := by
    rw [zpow_sub₀ hq0]
    ring
  rwa [e] at h2

theorem map_mem (hq0 : (q : E) ≠ 0) {n c : ℕ} (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hκ : ∀ l l' : Fin (n + c),
      IntAt P (κ (Pi.single l' 1) l * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)))
    {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c (fun i => i + 1)) : κ v ∈ LocE.lamY P q n c (fun i => i + 1) := by
  unfold LocE.lamY at hv ⊢
  rw [mem_sclLat] at hv ⊢
  intro l
  rw [apply_sum κ v l, Finset.mul_sum]
  refine intAt_sum _ _ fun l' _ => ?_
  have e : ((q : E) ^ LocE.scE n (fun i => i + 1) l.1)⁻¹ * (κ (Pi.single l' 1) l * v l') =
      (κ (Pi.single l' 1) l * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) *
        (((q : E) ^ LocE.scE n (fun i => i + 1) l'.1)⁻¹ * v l') := by
    rw [zpow_sub₀ hq0]
    have h1 : (q : E) ^ LocE.scE n (fun i => i + 1) l'.1 ≠ 0 := zpow_ne_zero _ hq0
    field_simp
  rw [e]
  exact (hκ l l').mul (hv l')

theorem coord_of_entB {k₀ n c : ℕ} (hk : k₀ ≤ n) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ p p', p < n + c → p' < n + c →
      IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p')) (l l' : Fin (n + c)) :
    IntAt P (κ (Pi.single l' 1) l * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) := by
  have h1 := h _ _ (fPos_lt hk l.2) (fPos_lt hk l'.2)
  rw [entB_eq hk (fPos_lt hk l.2) (fPos_lt hk l'.2)] at h1
  have e1 : (⟨LocE.fIdx k₀ c n (LocE.fPos k₀ c n l.1), fIdx_lt hk (fPos_lt hk l.2)⟩ : Fin (n + c)) = l :=
    Fin.ext (fIdx_fPos hk l.2)
  have e2 : (⟨LocE.fIdx k₀ c n (LocE.fPos k₀ c n l'.1), fIdx_lt hk (fPos_lt hk l'.2)⟩ : Fin (n + c)) = l' :=
    Fin.ext (fIdx_fPos hk l'.2)
  rw [e1, e2, fIdx_fPos hk l.2, fIdx_fPos hk l'.2] at h1
  exact h1

theorem mem_stabL_iff : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), (q : E) ≠ 0 →
    ∀ (κ n c : ℕ), κ ≤ n → ∀ (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)),
    γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) ↔
      (∀ p p', p < n + c → p' < n + c →
        IntAt P (LocE.entB q κ c n c n (fun i => i + 1) (fun i => i + 1) γ.toLinearMap p p')) ∧
      (∀ p p', p < n + c → p' < n + c →
        IntAt P (LocE.entB q κ c n c n (fun i => i + 1) (fun i => i + 1) (γ⁻¹ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap p p')) := by
  intro E _ _ P q hq0 κ n c hk γ
  constructor
  · intro hγ
    have hγi : γ⁻¹ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) := Subgroup.inv_mem _ hγ
    refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' => ?_⟩
    · rw [entB_eq hk hp hp']
      exact coord_int hq0 hγ _ _
    · rw [entB_eq hk hp hp']
      exact coord_int hq0 hγi _ _
  · rintro ⟨h1, h2⟩
    intro x
    constructor
    · intro hx
      have e : (γ⁻¹ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (γ x) = x := LinearEquiv.symm_apply_apply γ x
      rw [← e]
      exact map_mem hq0 _ (coord_of_entB hk _ h2) hx
    · intro hx
      exact map_mem hq0 γ (coord_of_entB hk γ h1) hx

end GlobalTheory.StabRef
