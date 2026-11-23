import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Lemmata.GeneralBFactThirdTer.Imports

noncomputable section

namespace Formalism.L2.Ker

open Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv

section Formal

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hatS_lin (H : Sesq V) (vol : ℝ) (SA : Finset V) (a : ℂ) (Φ Φ' : V → ℂ) (y : V) :
    hatS H vol SA (fun t => a * Φ t + Φ' t) y = a * hatS H vol SA Φ y + hatS H vol SA Φ' y := by
  simp only [hatS, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem opU_lin (H : Sesq V) (x : V) (a : ℂ) (e e' : V → ℂ) (z : V) :
    opU H x (fun v => a * e v + e' v) z = a * opU H x e z + opU H x e' z := by
  simp only [opU]; ring

theorem xiS_lin_datum (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SA SB : Finset V) (a : ℂ) (Φ Φ' e : V → ℂ) (z : V) :
    xiS H α vol SA SB (fun t => a * Φ t + Φ' t) e z = a * xiS H α vol SA SB Φ e z + xiS H α vol SA SB Φ' e z := by
  simp only [xiS, sumU, hatS_lin, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem xiS_lin_vec (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SA SB : Finset V) (a : ℂ) (Φ e e' : V → ℂ) (z : V) :
    xiS H α vol SA SB Φ (fun v => a * e v + e' v) z = a * xiS H α vol SA SB Φ e z + xiS H α vol SA SB Φ e' z := by
  simp only [xiS, sumU, opU_lin, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem twist_linear : XiLinear := by
  intro V _ _ H α vol SX SA SB a Φ Φ' e e' z
  refine ⟨xiS_lin_datum H α vol SA SB a Φ Φ' e z, xiS_lin_vec H α vol SA SB a Φ e e' z, ?_, ?_⟩
  · simp only [xiL, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h : xiS H α vol SA SB (fun s => a * Φ (s - x) + Φ' (s - x)) e
        = fun v => a * xiS H α vol SA SB (fun s => Φ (s - x)) e v + xiS H α vol SA SB (fun s => Φ' (s - x)) e v :=
      funext fun v => xiS_lin_datum H α vol SA SB a (fun s => Φ (s - x)) (fun s => Φ' (s - x)) e v
    rw [h, opU_lin]; ring
  · simp only [xiL, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h : xiS H α vol SA SB (fun s => Φ (s - x)) (fun v => a * e v + e' v)
        = fun v => a * xiS H α vol SA SB (fun s => Φ (s - x)) e v + xiS H α vol SA SB (fun s => Φ (s - x)) e' v :=
      funext fun v => xiS_lin_vec H α vol SA SB a (fun s => Φ (s - x)) e e' v
    rw [h, opU_lin]; ring

theorem bracket_commutation : BrkComm := by
  intro V _ _ H hH
  exact ⟨fun y t F z => (heisenbergComm V H hH F z).2 t y, fun _ _ _ _ => rfl⟩

end Formal

section Inj

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_reps_eq {Λ₁ Λ₂ : AddSubgroup V} {S S' : Finset V} (hS : IsReps Λ₁ Λ₂ S) (hS' : IsReps Λ₁ Λ₂ S') (g : V → ℂ)
    (hg : ∀ x ∈ Λ₂, ∀ m ∈ Λ₂, m ∈ Λ₁ → g (x + m) = g x) : ∑ x ∈ S, g x = ∑ x ∈ S', g x := by
  classical
  have hex : ∀ x ∈ S, ∃ x' ∈ S', x - x' ∈ Λ₁ := fun x hx => hS'.2.2 x (hS.1 x hx)
  choose! f hf hfd using hex
  refine Finset.sum_bij (fun x _ => f x) (fun x hx => hf x hx) ?_ ?_ ?_
  · intro x hx y hy hxy
    apply hS.2.1 x hx y hy
    have hxy' : f x = f y := hxy
    have : x - y = (x - f x) - (y - f y) := by rw [hxy']; abel
    rw [this]; exact Λ₁.sub_mem (hfd x hx) (hfd y hy)
  · intro x' hx'
    obtain ⟨x, hx, hd⟩ := hS.2.2 x' (hS'.1 x' hx')
    refine ⟨x, hx, ?_⟩
    apply hS'.2.1 (f x) (hf x hx) x' hx'
    have : f x - x' = -((x - f x) + (x' - x)) := by abel
    rw [this]; exact Λ₁.neg_mem (Λ₁.add_mem (hfd x hx) hd)
  · intro x hx
    have h1 : g x = g (f x + (x - f x)) := by congr 1; abel
    rw [h1]
    exact hg (f x) (hS'.1 _ (hf x hx)) (x - f x) (Λ₂.sub_mem (hS.1 x hx) (hS'.1 _ (hf x hx))) (hfd x hx)

theorem sum_reps_shift {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (g : V → ℂ)
    (hg : ∀ x ∈ Λ₂, ∀ m ∈ Λ₂, m ∈ Λ₁ → g (x + m) = g x) {x₀ : V} (hx₀ : x₀ ∈ Λ₂) :
    ∑ x ∈ S, g (x₀ + x) = ∑ x ∈ S, g x := by
  classical
  rw [← sum_reps_eq (reps_translate hS hx₀) hS g hg, Finset.sum_image]
  intro a _ b _ h
  exact add_left_cancel h

theorem char_sum_zero {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (χ : V → ℂ)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (htriv : ∀ m ∈ Λ₂, m ∈ Λ₁ → χ m = 1) {x₀ : V} (hx₀ : x₀ ∈ Λ₂) (hne : χ x₀ ≠ 1) :
    ∑ x ∈ S, χ x = 0 := by
  have h := sum_reps_shift hS χ (fun x _ m hm hm1 => by rw [hadd, htriv m hm hm1, mul_one]) hx₀
  simp only [hadd, ← Finset.mul_sum] at h
  have h2 : (χ x₀ - 1) * ∑ x ∈ S, χ x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hne
  · exact h0

theorem brk_ne_zero (H : Sesq V) (y t : V) : brk H y t ≠ 0 := Complex.exp_ne_zero _

theorem brk_add_right (H : Sesq V) (y t t' : V) : brk H y (t + t') = brk H y t * brk H y t' := by
  simp only [brk, altE, map_add, LinearMap.add_apply, Complex.add_im]
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem brk_add_left (H : Sesq V) (y y' t : V) : brk H (y + y') t = brk H y t * brk H y' t := by
  simp only [brk, altE, map_add, Complex.add_im]
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem brk_sub_right (H : Sesq V) (y t t' : V) : brk H y (t - t') = brk H y t * (brk H y t')⁻¹ := by
  have h := brk_add_right H y (t - t') t'
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv_cancel₀ (brk_ne_zero H y t'), mul_one]

theorem brk_sub_left (H : Sesq V) (y y' t : V) : brk H (y - y') t = brk H y t * (brk H y' t)⁻¹ := by
  have h := brk_add_left H (y - y') y' t
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv_cancel₀ (brk_ne_zero H y' t), mul_one]

theorem brk_one_of_int (H : Sesq V) {y t : V} (h : ∃ m : ℤ, altE H t y = (m : ℝ)) : brk H y t = 1 := by
  obtain ⟨m, hm⟩ := h
  simp only [brk, hm]; exact Inv.exp_two_pi_int m

theorem int_of_brk_one (H : Sesq V) {y t : V} (h : brk H y t = 1) : ∃ m : ℤ, altE H t y = (m : ℝ) :=
  Inv.int_of_exp_two_pi h

theorem step_translate (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (Λ : AddSubgroup V) (vol : ℝ) (SA SB : Finset V) (Φ θ : V → ℂ)
    (hθ : θ ∈ fixedBy H α Λ) {x : V} (hx : x ∈ Λ) (z : V) :
    α x * opU H x (xiS H α vol SA SB Φ θ) z = ∑ y ∈ SB, brk H y x * (hatS H vol SA Φ y * α y * opU H y θ z) := by
  have h0 : xiS H α vol SA SB Φ θ = fun v => ∑ y ∈ SB, (fun w => (hatS H vol SA Φ y * α y) * opU H y θ w) v := rfl
  rw [h0, Inv.opU_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Inv.opU_const_mul, (bracket_commutation V H hH).1 y x θ z]
  have h1 : α x * opU H y (opU H x θ) z = opU H y θ z := by
    rw [← Inv.opU_const_mul]
    have : (fun v => α x * opU H x θ v) = θ := funext fun v => hθ x hx v
    rw [this]
  rw [← h1]; ring

theorem twist_projection : XiProject := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol θ hθ Φ y hy z
  obtain ⟨hH, -, hB, -, -, -, -, -, -, h5⟩ := hyp
  have hBint := (semicharacterBasic V H hH B α hB).2.2
  have e1 : ∀ x ∈ SA, (brk H y x)⁻¹ * (α x * opU H x (xiS H α vol SA SB Φ θ) z)
      = ∑ y' ∈ SB, ((brk H y x)⁻¹ * brk H y' x) * (hatS H vol SA Φ y' * α y' * opU H y' θ z) := by
    intro x hx
    rw [step_translate H hH α Λ vol SA SB Φ θ hθ (hSA.1 x hx).1 z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rw [Finset.sum_eq_single y]
  · have : ∑ x ∈ SA, (brk H y x)⁻¹ * brk H y x = (SA.card : ℂ) := by
      rw [Finset.sum_congr rfl fun x _ => inv_mul_cancel₀ (brk_ne_zero H y x)]; simp
    rw [this]
  · intro y' hy' hne
    have hz : ∑ x ∈ SA, (brk H y x)⁻¹ * brk H y' x = 0 := by
      by_contra hne0
      apply hne
      apply hSB.2.1 y' hy' y hy
      apply h5 (y' - y) (B.sub_mem (hSB.1 y' hy') (hSB.1 y hy))
      intro a haA haΛ
      by_contra hno
      refine hne0 (char_sum_zero hSA (fun x => (brk H y x)⁻¹ * brk H y' x) ?_ ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro u v; simp only [brk_add_right, mul_inv]; ring
      · intro m _ hmB
        rw [brk_one_of_int H (hBint hmB y (hSB.1 y hy)), brk_one_of_int H (hBint hmB y' (hSB.1 y' hy'))]; simp
      · intro h1
        apply hno
        apply int_of_brk_one H
        rw [brk_sub_left, mul_comm]; exact h1
    rw [hz, zero_mul]
  · intro h; exact absurd hy h

theorem twist_injective_bis : XiInjective := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol hvol θ hθ hθ0 Φ hΦ hzero t ht
  have hproj := twist_projection V H α A B Λ hyp SA SB hSA hSB vol θ hθ Φ
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, -⟩ := hyp
  have hΛint := (semicharacterBasic V H hH Λ α hΛ).2.2
  have hcardA : (SA.card : ℂ) ≠ 0 := by
    obtain ⟨x, hx, -⟩ := hSA.2.2 0 (AddSubgroup.zero_mem _)
    exact_mod_cast (Finset.card_pos.2 ⟨x, hx⟩).ne'
  have hcardB : (SB.card : ℂ) ≠ 0 := by
    obtain ⟨x, hx, -⟩ := hSB.2.2 0 (AddSubgroup.zero_mem _)
    exact_mod_cast (Finset.card_pos.2 ⟨x, hx⟩).ne'
  have hfun : xiS H α vol SA SB Φ θ = fun _ => 0 := funext hzero
  obtain ⟨w, hw⟩ : ∃ w, θ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hθ0 (funext hcon)

  have hhat : ∀ y ∈ SB, hatS H vol SA Φ y = 0 := by
    intro y hy
    have h1 := hproj y hy (w - y)
    rw [hfun] at h1
    simp only [opU, zero_mul, mul_zero, Finset.sum_const_zero, sub_add_cancel] at h1
    have hα : α y ≠ 0 := by
      rcases hB.1 y (hSB.1 y hy) with h | h <;> rw [h] <;> norm_num
    have h2 := h1.symm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hcardA
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · exact h5
        · exact absurd h5 hα
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · exact absurd h5 hw
        · exact absurd h5 (Complex.exp_ne_zero _)
  have hsq : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hvolc : ((vol : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  have hS : ∀ y ∈ SB, ∑ s ∈ SA, Φ s * (brk H y s)⁻¹ = 0 := by
    intro y hy
    have h1 := hhat y hy
    simp only [hatS] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (inv_ne_zero hsq)
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 (div_ne_zero hvolc hcardA)
      · exact h3

  have hSA0 : ∀ t₀ ∈ SA, Φ t₀ = 0 := by
    intro t₀ ht₀
    have h1 : ∑ y ∈ SB, brk H y t₀ * ∑ s ∈ SA, Φ s * (brk H y s)⁻¹ = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [hS y hy, mul_zero]
    simp only [Finset.mul_sum] at h1
    rw [Finset.sum_comm] at h1
    have h2 : ∀ s ∈ SA, ∑ y ∈ SB, brk H y t₀ * (Φ s * (brk H y s)⁻¹) = Φ s * ∑ y ∈ SB, brk H y t₀ * (brk H y s)⁻¹ := by
      intro s _
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl h2, Finset.sum_eq_single t₀] at h1
    · have h3 : ∑ y ∈ SB, brk H y t₀ * (brk H y t₀)⁻¹ = (SB.card : ℂ) := by
        rw [Finset.sum_congr rfl fun y _ => mul_inv_cancel₀ (brk_ne_zero H y t₀)]; simp
      rw [h3] at h1
      exact (mul_eq_zero.1 h1).resolve_right hcardB
    · intro s hs hne
      have hz : ∑ y ∈ SB, brk H y t₀ * (brk H y s)⁻¹ = 0 := by
        by_contra hne0
        apply hne
        apply hSA.2.1 s hs t₀ ht₀
        have hmem : t₀ - s ∈ dualLat H B := by
          intro y hyB
          by_contra hno
          refine hne0 (char_sum_zero hSB (fun y => brk H y t₀ * (brk H y s)⁻¹) ?_ ?_ (x₀ := y) hyB ?_)
          · intro u v; simp only [brk_add_left, mul_inv]; ring
          · intro m _ hmΛ
            rw [brk_one_of_int H (hΛint (hSA.1 t₀ ht₀).1 m hmΛ), brk_one_of_int H (hΛint (hSA.1 s hs).1 m hmΛ)]; simp
          · intro h1
            apply hno
            apply int_of_brk_one H
            rw [brk_sub_right]; exact h1
        rw [sdB] at hmem
        have : s - t₀ = -(t₀ - s) := by abel
        rw [this]; exact B.neg_mem hmem
      rw [hz, mul_zero]
    · intro h; exact absurd ht₀ h
  obtain ⟨x, hx, hd⟩ := hSA.2.2 t ht
  have h1 : Φ t = Φ (x + (t - x)) := by congr 1; abel
  rw [h1, hΦ x (hSA.1 x hx).2 (t - x) (A.sub_mem ht.2 (hSA.1 x hx).2) hd]
  exact hSA0 x hx

end Inj

section Halves

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  rw [mem_conjP, mem_conjP, cO_cO]

section Mod

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (x : W) :
    x ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • x ∈ localization₂ Q.asIdeal M := by
  simp only [twist₂, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_coe, id_eq]

theorem le_locP' (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem nat_smul_mem (L : Submodule (𝓞 E) W) (c : ℕ) {x : W} (hx : x ∈ L) : (c : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx c

theorem mem_of_forall_locP (M : Submodule (𝓞 E) W) {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  let I : Ideal (𝓞 E) :=
    { carrier := {r | r • x ∈ M}
      add_mem' := fun {r s} hr hs => by
        show (r + s) • x ∈ M
        rw [add_smul]; exact M.add_mem hr hs
      zero_mem' := by
        show (0 : 𝓞 E) • x ∈ M
        rw [zero_smul]; exact M.zero_mem
      smul_mem' := fun r s hs => by
        show (r • s) • x ∈ M
        rw [smul_eq_mul, mul_smul]; exact M.smul_mem r hs }
  by_cases hI : I = ⊤
  · have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; trivial
    have h2 : (1 : 𝓞 E) • x ∈ M := h1
    rwa [one_smul] at h2
  · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    exact absurd (hIm hsx) hs

theorem tw_mem_of (M : Submodule (𝓞 E) W) (c : ℕ) (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ) {x : W} (hx : x ∈ M) (ε : 𝓞 E)
    (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) (h : ∀ Q, e Q = 1 → ∃ s, s ∉ Q.asIdeal ∧ (c : 𝓞 E) ∣ s * ε) : ε • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [mem_twO]
  intro Q
  rcases he Q with h1 | h1 | h1
  · obtain ⟨s, hs, r, hr⟩ := h Q h1
    rw [h1, zpow_one]
    refine ⟨s, hs, ?_⟩
    have e1 : s • ((c : E)⁻¹ • (ε • x)) = r • x := by
      rw [← IsScalarTower.algebraMap_smul E s, ← IsScalarTower.algebraMap_smul E ε x, ← IsScalarTower.algebraMap_smul E r x, smul_smul,
        smul_smul]
      congr 1
      have h2 := congrArg (algebraMap (𝓞 E) E) hr
      simp only [map_mul, map_natCast] at h2
      field_simp
      linear_combination h2
    rw [e1]; exact M.smul_mem r hx
  · rw [h1, zpow_zero, inv_one, one_smul]; exact le_locP' M Q (M.smul_mem ε hx)
  · rw [h1, zpow_neg_one, inv_inv]; exact nat_smul_mem _ c (le_locP' M Q (M.smul_mem ε hx))

theorem tw_split (M : Submodule (𝓞 E) W) (c : ℕ) (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ)
    (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) {a₀ b₀ : W} (ha : a₀ ∈ twist₂ M c fun Q => -e Q) (hb : b₀ ∈ twist₂ M c e) (hab : a₀ + b₀ ∈ M) :
    a₀ ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [mem_twO] at ha hb
  apply mem_of_forall_locP
  intro Q
  have hA := ha Q
  have hB := hb Q
  rcases he Q with h1 | h1 | h1
  · rw [h1, zpow_one] at hB
    have h2 := nat_smul_mem _ c hB
    rw [smul_smul, mul_inv_cancel₀ hcE, one_smul] at h2
    have h3 : a₀ = (a₀ + b₀) - b₀ := by abel
    rw [h3]; exact Submodule.sub_mem _ (le_locP' M Q hab) h2
  · simp only [h1, neg_zero, zpow_zero, inv_one, one_smul] at hA; exact hA
  · simp only [h1, neg_neg, zpow_one] at hA
    have h2 := nat_smul_mem _ c hA
    rwa [smul_smul, mul_inv_cancel₀ hcE, one_smul] at h2

end Mod

theorem primary_pow (Q : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) :
    ∃ k : ℕ, ∀ r ∈ Q.asIdeal ^ k, ∃ s, s ∉ Q.asIdeal ∧ c ∣ s * r := by
  have hI : Ideal.span {c} ≠ (0 : Ideal (𝓞 E)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc
  have hQ : ¬ IsUnit Q.asIdeal := by
    rw [Ideal.isUnit_iff]; exact Q.isPrime.ne_top
  obtain ⟨J, hJ, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hQ hI).exists_eq_pow_mul_and_not_dvd
  refine ⟨multiplicity Q.asIdeal (Ideal.span {c}), fun r hr => ?_⟩
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨s, hsJ, hsQ⟩ := SetLike.not_le_iff_exists.1 hnd
  refine ⟨s, hsQ, ?_⟩
  rw [← Ideal.mem_span_singleton, hJ, mul_comm s r]
  exact Ideal.mul_mem_mul hr hsJ

theorem exists_idem (SS : Finset (HeightOneSpectrum (𝓞 E))) (hSS : ∀ P ∈ SS, conjPrime₂ P ∉ SS) (c : ℕ) (hc : 0 < c) :
    ∃ ε : 𝓞 E, (∀ Q ∈ SS, ∃ s, s ∉ Q.asIdeal ∧ (c : 𝓞 E) ∣ s * (1 - ε)) ∧
      ∀ Q, conjPrime₂ Q ∈ SS → ∃ s, s ∉ Q.asIdeal ∧ (c : 𝓞 E) ∣ s * ε := by
  classical
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  choose k hk using fun Q : HeightOneSpectrum (𝓞 E) => primary_pow Q (c : 𝓞 E) hc0
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ SS.image conjPrime₂) (fun Q => Q.asIdeal) k
    (fun Q _ => Q.prime) (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h')) (fun Q => if Q.1 ∈ SS then 1 else 0)
  refine ⟨y, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · have h1 := hy Q (Finset.mem_union_left _ hQ)
    simp only [hQ, if_true] at h1
    have h2 : 1 - y ∈ Q.asIdeal ^ k Q := by
      have : 1 - y = -(y - 1) := by ring
      rw [this]; exact neg_mem h1
    exact hk Q _ h2
  · have hQ' : Q ∉ SS := fun h => hSS Q h hQ
    have h1 := hy Q (Finset.mem_union_right _ (Finset.mem_image.2 ⟨conjPrime₂ Q, hQ, conjP_conjP' Q⟩))
    simp only [hQ', if_false, sub_zero] at h1
    exact hk Q _ h1

theorem expS_cases (SS : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := by
  unfold expS; split_ifs <;> simp

theorem expS_eq_one (SS : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) (h : expS SS Q = 1) : Q ∈ SS := by
  by_contra hn
  have h0 : expS SS Q = 0 ∨ expS SS Q = -1 := by
    unfold expS; rw [if_neg hn]; split_ifs <;> simp
  omega

theorem expS_eq_neg_one (SS : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) (h : -expS SS Q = 1) : conjPrime₂ Q ∈ SS := by
  by_contra hn
  have h0 : expS SS Q = 1 ∨ expS SS Q = 0 := by
    unfold expS; rw [if_neg hn]; split_ifs <;> simp
  omega

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem herm_HV (sc : ℝ) : IsHerm (HV sc : Sesq (VV ι a b)) := by
  intro x y
  show (sc : ℂ) * ∑ τ, ∑ i, ∑ j, y τ i j * (starRingEnd ℂ) (x τ i j) =
    (starRingEnd ℂ) ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j))
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem embH_inj [Nonempty ι] (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH emb δ : HomE E a b → VV ι a b) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  apply LinearMap.pi_ext'
  intro j
  apply LinearMap.ext_ring
  funext i
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  have h2 : δ * emb τ (x (Pi.single j 1) i) = δ * emb τ (y (Pi.single j 1) i) := h1
  exact (emb τ).injective (mul_left_cancel₀ hδ h2)

theorem half_periods_complex : HalvesC := by
  intro E _ _ _ ι _ _ a b emb δ d sc AA0 SS N N' c hδ hc hSS sdΛ sdA sdB scΛ scA scB
  have hH : IsHerm (HV sc : Sesq (VV ι a b)) := herm_HV sc
  have hAint := (semicharacterBasic _ _ hH _ _ scA).2.2
  have hBint := (semicharacterBasic _ _ hH _ _ scB).2.2
  have hinj := embH_inj (a := a) (b := b) emb hδ

  have hsum : LamC emb δ AA0 N N' ≤ (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c) ⊔ (LamC emb δ AA0 N N' ⊓ BC emb δ AA0 SS N N' c) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ε, h1, h2⟩ := exists_idem SS hSS c hc
    rw [AddSubgroup.mem_sup]
    refine ⟨embH emb δ (ε • x), ⟨⟨ε • x, Submodule.smul_mem _ ε hx, rfl⟩, ⟨ε • x, ?_, rfl⟩⟩,
      embH emb δ ((1 - ε) • x), ⟨⟨(1 - ε) • x, Submodule.smul_mem _ _ hx, rfl⟩, ⟨(1 - ε) • x, ?_, rfl⟩⟩, ?_⟩
    · refine tw_mem_of _ c hc _ hx ε (fun Q => ?_) (fun Q hQ => h2 Q (expS_eq_neg_one SS Q hQ))
      rcases expS_cases SS Q with h | h | h <;> simp [h]
    · exact tw_mem_of _ c hc _ hx (1 - ε) (expS_cases SS) (fun Q hQ => h1 Q (expS_eq_one SS Q hQ))
    · rw [← map_add, ← add_smul]; simp
  have h3 : ∀ u ∈ AC emb δ AA0 SS N N' c, ∀ v ∈ BC emb δ AA0 SS N N' c, u + v ∈ LamC emb δ AA0 N N' → u ∈ LamC emb δ AA0 N N' := by
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩ ⟨m, hm, hme⟩
    rw [← map_add] at hme
    have hm' : a₀ + b₀ ∈ perO AA0 N N' := by rw [← hinj hme]; exact hm
    exact ⟨a₀, tw_split _ c hc _ (expS_cases SS) ha₀ hb₀ hm', rfl⟩
  refine ⟨hH, scA, scB, sdA, sdB, scΛ, hsum, h3, ?_, ?_⟩
  · intro u hu h
    rw [← sdΛ]
    intro l hl
    obtain ⟨lA, hlA, lB, hlB, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hl)
    obtain ⟨m1, hm1⟩ := hAint hu lA hlA.2
    obtain ⟨m2, hm2⟩ := h lB hlB.2 hlB.1
    refine ⟨m1 + m2, ?_⟩
    have : altE (HV sc) u (lA + lB) = altE (HV sc) u lA + altE (HV sc) u lB := by simp [altE]
    rw [this, hm1, hm2]; push_cast; ring
  · intro v hv h
    rw [← sdΛ]
    intro l hl
    obtain ⟨lA, hlA, lB, hlB, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hl)
    obtain ⟨m1, hm1⟩ := h lA hlA.2 hlA.1
    obtain ⟨m2, hm2⟩ := hBint hv lB hlB.2
    refine ⟨-m1 + m2, ?_⟩
    have : altE (HV sc) v (lA + lB) = altE (HV sc) v lA + altE (HV sc) v lB := by simp [altE]
    rw [this, Inv.altE_swap hH lA v, hm1, hm2]; push_cast; ring

end Halves

section Lifts

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem loc_of_dvd (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) {c n : ℕ} (hc : (c : E) ≠ 0) {x : W} (hn : (n : E) • x ∈ M)
    {t ε r : 𝓞 E} (ht : t ∉ Q.asIdeal) (hr : t * ε = ((c : 𝓞 E) * (n : 𝓞 E)) * r) : (c : E)⁻¹ • (ε • x) ∈ localization₂ Q.asIdeal M := by
  refine ⟨t, ht, ?_⟩
  have e1 : t • ((c : E)⁻¹ • (ε • x)) = r • ((n : E) • x) := by
    rw [← IsScalarTower.algebraMap_smul E t, ← IsScalarTower.algebraMap_smul E ε x, ← IsScalarTower.algebraMap_smul E r, smul_smul,
      smul_smul, smul_smul]
    congr 1
    have h2 := congrArg (algebraMap (𝓞 E) E) hr
    simp only [map_mul, map_natCast] at h2
    field_simp
    linear_combination h2
  rw [e1]; exact M.smul_mem r hn

theorem loc_of_dvd_sq (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) {c : ℕ} (hc : (c : E) ≠ 0) {x : W}
    (hx : (c : E) • x ∈ localization₂ Q.asIdeal M) {t ε r : 𝓞 E} (ht : t ∉ Q.asIdeal) (hr : t * (1 - ε) = ((c : 𝓞 E) * (c : 𝓞 E)) * r) :
    (c : E)⁻¹ • (ε • x - x) ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s', hs', hm⟩ := hx
  refine ⟨t * s', Q.asIdeal.primeCompl.mul_mem ht hs', ?_⟩
  have e1 : (t * s') • ((c : E)⁻¹ • (ε • x - x)) = (-r) • (s' • ((c : E) • x)) := by
    have e2 : ε • x - x = (algebraMap (𝓞 E) E ε - 1) • x := by
      rw [sub_smul, one_smul, IsScalarTower.algebraMap_smul]
    rw [e2, ← IsScalarTower.algebraMap_smul E (t * s'), ← IsScalarTower.algebraMap_smul E (-r), ← IsScalarTower.algebraMap_smul E s',
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    have h2 := congrArg (algebraMap (𝓞 E) E) hr
    simp only [map_mul, map_natCast, map_sub, map_one] at h2
    simp only [map_mul, map_neg]
    field_simp
    linear_combination (-(algebraMap (𝓞 E) E s')) * h2
  rw [e1]; exact M.smul_mem _ hm

theorem exists_lift (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) (c n : ℕ) (hc : 0 < c) (hn0 : 0 < n) {x : W}
    (hn : (n : E) • x ∈ M) (hx : ∀ P ∈ SS, (c : E) • x ∈ localization₂ P.asIdeal M) :
    ∃ s : W, (s ∈ twist₂ M c fun Q => -expS SS Q) ∧ ∀ P ∈ SS, ((c : E)⁻¹ • (s - x)) ∈ localization₂ P.asIdeal M := by
  classical
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcc : ((c : 𝓞 E) * (c : 𝓞 E)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hc hc).ne'
  have hcn : ((c : 𝓞 E) * (n : 𝓞 E)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hc hn0).ne'
  choose k1 hk1 using fun Q : HeightOneSpectrum (𝓞 E) => primary_pow Q _ hcc
  choose k2 hk2 using fun Q : HeightOneSpectrum (𝓞 E) => primary_pow Q _ hcn
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(c : 𝓞 E) * (n : 𝓞 E)}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hcn)
  obtain ⟨ε, hε⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hfin.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then k1 Q else k2 Q)
    (fun Q _ => Q.prime) (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h')) (fun Q => if Q.1 ∈ SS then 1 else 0)
  have hin : ∀ Q ∈ SS, ∃ t, t ∉ Q.asIdeal ∧ ((c : 𝓞 E) * (c : 𝓞 E)) ∣ t * (1 - ε) := by
    intro Q hQ
    have h1 := hε Q (Finset.mem_union_left _ hQ)
    simp only [hQ, if_true] at h1
    have h2 : 1 - ε ∈ Q.asIdeal ^ k1 Q := by
      have : 1 - ε = -(ε - 1) := by ring
      rw [this]; exact neg_mem h1
    exact hk1 Q _ h2
  have hout : ∀ Q, Q ∉ SS → (c : E)⁻¹ • (ε • x) ∈ localization₂ Q.asIdeal M := by
    intro Q hQ
    by_cases hd : ((c : 𝓞 E) * (n : 𝓞 E)) ∈ Q.asIdeal
    · have hQT : Q ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        show Q.asIdeal ∣ _
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hd
      have h1 := hε Q (Finset.mem_union_right _ hQT)
      simp only [hQ, if_false, sub_zero] at h1
      obtain ⟨t, ht, r, hr⟩ := hk2 Q _ h1
      exact loc_of_dvd M Q hcE hn ht hr
    · exact loc_of_dvd M Q hcE hn hd rfl
  refine ⟨ε • x, ?_, fun P hP => ?_⟩
  · rw [mem_twO]
    intro Q
    by_cases hQ : Q ∈ SS
    · have h1 : expS SS Q = 1 := by unfold expS; rw [if_pos hQ]
      rw [h1, zpow_neg_one, inv_inv, smul_comm]
      exact Submodule.smul_mem _ ε (hx Q hQ)
    · rcases expS_cases SS Q with h | h | h
      · exact absurd (expS_eq_one SS Q h) hQ
      · rw [h, neg_zero, zpow_zero, inv_one, one_smul]
        have h2 := nat_smul_mem _ c (hout Q hQ)
        rwa [smul_smul, mul_inv_cancel₀ hcE, one_smul] at h2
      · rw [h, neg_neg, zpow_one]; exact hout Q hQ
  · obtain ⟨t, ht, r, hr⟩ := hin P hP
    exact loc_of_dvd_sq M P hcE (hx P hP) ht hr

theorem lift_exists_alt : LiftExists := by
  intro E _ _ _ a b SS M c hc _ hspan x hx
  obtain ⟨n, hn0, hn⟩ := hspan x
  exact Classical.epsilon_spec (p := fun s => IsLiftS SS M c x s) (exists_lift SS M c n hc hn0 hn hx)

theorem repsOf_spec {V : Type} [AddCommGroup V] [Module ℂ V] (Λ₁ Λ₂ : AddSubgroup V) (h : relIdx Λ₁ Λ₂ ≠ 0) : IsReps Λ₁ Λ₂ (repsOf Λ₁ Λ₂) :=
  Classical.epsilon_spec (p := fun S => IsReps Λ₁ Λ₂ S) (cosetRepsExist V Λ₁ Λ₂ h).1

theorem XiIndCClass_of (h : XiIndClass) : XiIndCClass := by
  intro E _ _ _ ι _ _ a b emb δ d sc AA0 SS N N' c hyp hr1 hr2 θ hθ x x' hl hl' hxx vol
  set s := liftS SS (perO AA0 N N') c x with hs
  set s' := liftS SS (perO AA0 N N') c x' with hs'
  have hA : s - s' ∈ halfAO SS (perO AA0 N N') c := Submodule.sub_mem _ hl.1 hl'.1
  have hB : s - s' ∈ halfBO SS (perO AA0 N N') c := by
    have hA' := (mem_twO _ _ _ _).1 hA
    refine (mem_twO _ _ _ _).2 fun Q => ?_
    have hAQ := hA' Q
    rcases expS_cases SS Q with h1 | h1 | h1
    · have hQ := expS_eq_one SS Q h1
      rw [h1, zpow_one]
      have e1 : (c : E)⁻¹ • (s - s') = (c : E)⁻¹ • (s - x) - (c : E)⁻¹ • (s' - x') + (c : E)⁻¹ • (x - x') := by
        rw [← smul_sub, ← smul_add]; congr 1; abel
      rw [e1]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (hl.2 Q hQ) (hl'.2 Q hQ)) (hxx Q hQ)
    · simp only [h1, neg_zero] at hAQ
      rw [h1]; exact hAQ
    · simp only [h1, neg_neg, zpow_one] at hAQ
      rw [h1, zpow_neg_one, inv_inv]
      by_cases hc : (c : E) = 0
      · rw [hc, zero_smul]; exact Submodule.zero_mem _
      · have h2 := nat_smul_mem _ c (nat_smul_mem _ c hAQ)
        rwa [smul_smul (c : E) (c : E)⁻¹, mul_inv_cancel₀ hc, one_smul] at h2
  funext z
  have e0 : embH emb δ s = embH emb δ s' + embH emb δ (s - s') := by rw [← map_add]; congr 1; abel
  show xiInd _ _ _ _ _ _ θ (embH emb δ s) z = xiInd _ _ _ _ _ _ θ (embH emb δ s') z
  rw [e0]
  exact h _ _ _ _ _ _ hyp _ _ (repsOf_spec _ _ hr1) (repsOf_spec _ _ hr2) _ θ hθ _ ⟨s', hl'.1, rfl⟩ _ ⟨s - s', hA, rfl⟩ ⟨s - s', hB, rfl⟩ z

end Lifts

section TwHomS

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem loc_of_scal {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (Q : HeightOneSpectrum (𝓞 E)) {l : E} {v ρ : 𝓞 E} (hv : v ∉ Q.asIdeal) (h : algebraMap (𝓞 E) E v * l = algebraMap (𝓞 E) E ρ) {y : W}
    (hy : y ∈ L) : l • y ∈ localization₂ Q.asIdeal L := by
  refine ⟨v, hv, ?_⟩
  rw [← IsScalarTower.algebraMap_smul E v, smul_smul, h, IsScalarTower.algebraMap_smul]
  exact L.smul_mem ρ hy

theorem exists_mult (c : ℕ) (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ) (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ t : 𝓞 E, t ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ∃ v ρ : 𝓞 E, v ∉ Q'.asIdeal ∧
      algebraMap (𝓞 E) E v * (((c : E) ^ e Q')⁻¹ * (algebraMap (𝓞 E) E t * (c : E) ^ e Q)) = algebraMap (𝓞 E) E ρ := by
  classical
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  choose K hK using fun Q' : HeightOneSpectrum (𝓞 E) => primary_pow Q' ((c : 𝓞 E) ^ (e Q' - e Q).toNat) (pow_ne_zero _ hc0)
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(c : 𝓞 E)}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc0)
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert Q hfin.toFinset) (fun Q' => Q'.asIdeal)
    (fun Q' => if Q' = Q then 1 else K Q')
    (fun Q' _ => Q'.prime) (fun Q' _ Q'' _ h h' => h (HeightOneSpectrum.ext h')) (fun Q' => if Q'.1 = Q then 1 else 0)
  refine ⟨t, fun htQ => ?_, fun Q' => ?_⟩
  · have h1 := ht Q (Finset.mem_insert_self _ _)
    simp only [if_true, pow_one] at h1
    have h2 : (1 : 𝓞 E) ∈ Q.asIdeal := by
      have : (1 : 𝓞 E) = t - (t - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ htQ h1
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · have hz : ((c : E) ^ e Q')⁻¹ * (algebraMap (𝓞 E) E t * (c : E) ^ e Q) = algebraMap (𝓞 E) E t * (c : E) ^ (e Q - e Q') := by
      rw [zpow_sub₀ hcE]; field_simp
    rw [hz]
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (e Q - e Q')
    · refine ⟨1, t * (c : 𝓞 E) ^ m, fun h => Q'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
      rw [hm, zpow_natCast]; simp
    · have hm' : (e Q' - e Q).toNat = m := by omega
      rw [hm, zpow_neg, zpow_natCast]
      by_cases hd : (c : 𝓞 E) ∈ Q'.asIdeal
      · by_cases hQQ : Q' = Q
        · subst hQQ
          have : m = 0 := by omega
          subst this
          refine ⟨1, t, fun h => Q'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
        · have hQT : Q' ∈ insert Q hfin.toFinset := by
            apply Finset.mem_insert_of_mem
            rw [Set.Finite.mem_toFinset]
            show Q'.asIdeal ∣ _
            rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hd
          have h1 := ht Q' hQT
          simp only [hQQ, if_false, sub_zero] at h1
          obtain ⟨v, hv, ρ, hρ⟩ := hK Q' _ h1
          rw [hm'] at hρ
          refine ⟨v, ρ, hv, ?_⟩
          have h2 := congrArg (algebraMap (𝓞 E) E) hρ
          simp only [map_mul, map_pow, map_natCast] at h2
          field_simp
          linear_combination h2
      · refine ⟨(c : 𝓞 E) ^ m, t, fun h => hd (Q'.isPrime.mem_of_pow_mem _ h), ?_⟩
        simp only [map_pow, map_natCast]
        field_simp

theorem twist_homomorphism : TwHom := by
  intro E _ _ _ a b AA0 N N' c e hN hc
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  apply le_antisymm
  · intro z hz
    rw [mem_twO] at hz
    apply mem_of_forall_locP
    intro Q
    obtain ⟨s, hs, hsz⟩ := hz Q
    obtain ⟨t, ht, hmul⟩ := exists_mult c hc e Q
    have hcl : perO AA0 N N' ≤ (perO AA0 N (twist₂ N' c e)).comap
        (((algebraMap (𝓞 E) E t * (c : E) ^ e Q) • (LinearMap.id : HomE E a b →ₗ[E] HomE E a b)).restrictScalars (𝓞 E)) := by
      apply Submodule.span_le.2
      rintro _ ⟨r, hr, x, hx, rfl⟩
      show (algebraMap (𝓞 E) E t * (c : E) ^ e Q) • (r • x) ∈ perO AA0 N (twist₂ N' c e)
      rw [smul_comm]
      refine Submodule.subset_span ⟨r, hr, _, ?_, rfl⟩
      intro y hy
      show (algebraMap (𝓞 E) E t * (c : E) ^ e Q) • x y ∈ twist₂ N' c e
      rw [mem_twO]
      intro Q'
      obtain ⟨v, ρ, hv, hρ⟩ := hmul Q'
      rw [smul_smul]
      exact loc_of_scal N' Q' hv hρ (hx y hy)
    have h1 := hcl hsz
    refine ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
    have h2 : (t * s) • z = (algebraMap (𝓞 E) E t * (c : E) ^ e Q) • (s • (((c : E) ^ e Q)⁻¹ • z)) := by
      rw [← IsScalarTower.algebraMap_smul E (t * s), ← IsScalarTower.algebraMap_smul E s, smul_smul, smul_smul, map_mul]
      congr 1
      have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
      field_simp
    rw [h2]; exact h1
  · apply Submodule.span_le.2
    rintro _ ⟨r, hr, x, hx, rfl⟩
    show r • x ∈ twist₂ (perO AA0 N N') c e
    rw [mem_twO]
    intro Q
    obtain ⟨G, hG⟩ := hN
    have hex : ∀ g ∈ G, ∃ s : 𝓞 E, s ∈ Q.asIdeal.primeCompl ∧ s • (((c : E) ^ e Q)⁻¹ • x g) ∈ N' := by
      intro g hg
      have h1 : x g ∈ twist₂ N' c e := hx g (by rw [← hG]; exact Submodule.subset_span hg)
      exact (mem_twO _ _ _ _).1 h1 Q
    choose! sg hsg hsg' using hex
    refine ⟨∏ g ∈ G, sg g, Submonoid.prod_mem _ hsg, ?_⟩
    have hx' : (∏ g ∈ G, sg g) • (((c : E) ^ e Q)⁻¹ • x) ∈ homO N N' := by
      have hle : N ≤ N'.comap (((∏ g ∈ G, sg g) • (((c : E) ^ e Q)⁻¹ • x)).restrictScalars (𝓞 E)) := by
        rw [← hG]
        apply Submodule.span_le.2
        intro g hg
        show (∏ g ∈ G, sg g) • (((c : E) ^ e Q)⁻¹ • x g) ∈ N'
        obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem sg hg
        rw [hq, mul_comm, mul_smul]
        exact N'.smul_mem q (hsg' g hg)
      exact fun y hy => hle hy
    have e1 : (∏ g ∈ G, sg g) • (((c : E) ^ e Q)⁻¹ • (r • x)) = r • ((∏ g ∈ G, sg g) • (((c : E) ^ e Q)⁻¹ • x)) := by
      rw [smul_comm _ r x, smul_comm _ r]
    rw [e1]
    exact Submodule.subset_span ⟨r, hr, _, hx', rfl⟩

end TwHomS

section Norm

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

theorem half_periods_of_lattice : HalvesOfLa := by
  intro E _ _ _ ι _ _ a b emb δ d sc AA0 SS N N' c hδ hc hSS hN h0 hB hA
  have eA : AC emb δ AA0 SS N N' c = LamC emb δ AA0 N (twist₂ N' c fun Q => -expS SS Q) := by
    unfold AC LamC halfAO; rw [twist_homomorphism E a b AA0 N N' c _ hN hc]
  have eB : BC emb δ AA0 SS N N' c = LamC emb δ AA0 N (twist₂ N' c (expS SS)) := by
    unfold BC LamC halfBO; rw [twist_homomorphism E a b AA0 N N' c _ hN hc]
  exact half_periods_complex E ι a b emb δ d sc AA0 SS N N' c hδ hc hSS h0.1 (by rw [eA]; exact hA.1) (by rw [eB]; exact hB.1) h0.2
    (by rw [eA]; exact hA.2) (by rw [eB]; exact hB.2)

theorem exponent_set_conjugate : ExpSConj := by
  intro E _ _ _ SS hSS Q
  unfold expS
  rw [conjP_conjP']
  by_cases h1 : Q ∈ SS
  · have h2 : conjPrime₂ Q ∉ SS := hSS Q h1
    simp [h1, h2]
  · by_cases h2 : conjPrime₂ Q ∈ SS <;> simp [h1, h2]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hatS_one (H : Sesq V) {vol : ℝ} (hvol : 0 < vol) (SA : Finset V) (Φ : V → ℂ) (y : V) :
    hatS H 1 SA Φ y = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * hatS H vol SA Φ y := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) = ((vol : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt hvol.le
  have hs0 : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have h1 : ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ) = 1 := by rw [← hs]; field_simp
  simp only [hatS, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, div_eq_mul_inv]
  linear_combination (-((SA.card : ℂ)⁻¹ * ∑ t ∈ SA, Φ t * (brk H y t)⁻¹)) * h1

theorem xiS_one (H : Sesq V) (α : V → ℂ) {vol : ℝ} (hvol : 0 < vol) (SA SB : Finset V) (Φ e : V → ℂ) (z : V) :
    xiS H α 1 SA SB Φ e z = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiS H α vol SA SB Φ e z := by
  simp only [xiS, sumU, hatS_one H hvol, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem xiS_scale (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiS H α vol SA SB (fun t => k * Φ t) e z = k * xiS H α vol SA SB Φ e z := by
  have h := xiS_lin_datum H α vol SA SB k Φ (fun _ => 0) e z
  have h0 : xiS H α vol SA SB (fun _ => 0) e z = 0 := by simp [xiS, sumU, hatS]
  simpa [h0] using h

theorem xiL_one (H : Sesq V) (α : V → ℂ) {vol : ℝ} (hvol : 0 < vol) (SX SA SB : Finset V) (Φ e : V → ℂ) :
    xiL H α 1 SX SA SB Φ e = xiL H α vol SX SA SB (fun t => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * Φ t) e := by
  funext z
  simp only [xiL]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : xiS H α 1 SA SB (fun s => Φ (s - x)) e = xiS H α vol SA SB (fun s => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * Φ (s - x)) e := by
    funext v
    rw [xiS_one H α hvol, xiS_scale]
  rw [h]

theorem theta_coset_moved : ThCMoved := by
  intro E _ _ _ ι _ a b emb δ d sc AA0 SS N N' c hvol θ
  refine ⟨fun Ξ => ?_, fun x z => ?_⟩
  · have h : onV emb δ (fun x => ((Real.sqrt (volC AA0 SS N N') : ℝ) : ℂ)⁻¹ * Ξ x)
        = fun t => ((Real.sqrt (volC AA0 SS N N') : ℝ) : ℂ)⁻¹ * onV emb δ Ξ t := by
      funext v
      unfold onV
      split_ifs <;> simp
    unfold thC xiC xiV
    rw [h, xiL_one _ _ hvol]
  · unfold thIndC xiIndC xiIndV xiInd
    have h : xiS (HV sc) (alV d sc) 1 (repsOf (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c))
        (repsOf (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c)) (indL (BC emb δ AA0 SS N N' c)) θ
        = fun v => ((Real.sqrt (volC AA0 SS N N') : ℝ) : ℂ)⁻¹ * xiS (HV sc) (alV d sc) (volC AA0 SS N N')
          (repsOf (BC emb δ AA0 SS N N' c) (LamC emb δ AA0 N N' ⊓ AC emb δ AA0 SS N N' c))
          (repsOf (LamC emb δ AA0 N N') (BC emb δ AA0 SS N N' c)) (indL (BC emb δ AA0 SS N N' c)) θ v :=
      funext fun v => xiS_one _ _ hvol _ _ _ _ v
    rw [h, Inv.opU_const_mul]; ring

theorem volS_pos_of {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (M₀ M : Submodule (𝓞 E) (HomE E a b))
    (h : ∀ P ∈ SS, (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 ∧
      (localization₂ P.asIdeal M).toAddSubgroup.relIndex (localization₂ P.asIdeal M₀).toAddSubgroup ≠ 0) : 0 < volS SS M₀ M :=
  Finset.prod_pos fun P hP => div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (h P hP).1)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (h P hP).2))

end Norm

section TwDual

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

theorem twist_selfDual : TwSelfDual := by
  intro E _ _ _ b N' c e _ hc he hU
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hU' : dual (hStd E b) N' = N' := hU
  have hint : ∀ y ∈ N', ∀ x ∈ N', hStd E b y x ∈ (1 : Submodule (𝓞 E) E) := fun y hy x hx =>
    (mem_dual N' x).1 (by rw [hU']; exact hx) y hy
  show dual (hStd E b) (twist₂ N' c e) = twist₂ N' c e
  apply le_antisymm
  · intro x hx
    rw [mem_dual] at hx
    rw [mem_twO]
    intro Q
    obtain ⟨t, ht, hmul⟩ := exists_mult c hc e (conjPrime₂ Q)
    refine ⟨cO E t, fun h => ht ((mem_conjP Q t).2 h), ?_⟩
    rw [← hU', mem_dual]
    intro y hy
    have hy' : (algebraMap (𝓞 E) E t * (c : E) ^ e (conjPrime₂ Q)) • y ∈ twist₂ N' c e := by
      rw [mem_twO]
      intro Q'
      obtain ⟨v, ρ, hv, hρ⟩ := hmul Q'
      rw [smul_smul]
      exact loc_of_scal N' Q' hv hρ hy
    have h1 := hx _ hy'
    have h2 : hStd E b y (cO E t • (((c : E) ^ e Q)⁻¹ • x)) = hStd E b ((algebraMap (𝓞 E) E t * (c : E) ^ e (conjPrime₂ Q)) • y) x := by
      rw [← IsScalarTower.algebraMap_smul E (cO E t), algebraMap_cO, he Q]
      simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul', star_inv₀, star_zpow₀, star_natCast,
        zpow_neg]
      ring
    rw [h2]; exact h1
  · intro x hx
    rw [mem_dual]
    intro y hy
    apply mem_of_forall_locP (W := E)
    intro Q
    obtain ⟨s, hs, hsx⟩ := (mem_twO _ _ _ _).1 hx Q
    obtain ⟨s', hs', hsy⟩ := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    have h1 := hint _ hsy _ hsx
    refine ⟨cO E s' * s, Q.asIdeal.primeCompl.mul_mem (fun h => hs' ((mem_conjP Q s').2 h)) hs, ?_⟩
    have h2 : (cO E s' * s) • hStd E b y x = hStd E b (s' • (((c : E) ^ e (conjPrime₂ Q))⁻¹ • y)) (s • (((c : E) ^ e Q)⁻¹ • x)) := by
      rw [Algebra.smul_def, map_mul, algebraMap_cO, ← IsScalarTower.algebraMap_smul E s', ← IsScalarTower.algebraMap_smul E s, he Q]
      simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_zpow₀, star_natCast,
        zpow_neg, inv_inv]
      have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
      field_simp
    rw [h2]; exact h1

end TwDual

section Vol

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain
open scoped Pointwise

theorem relIndex_ne_zero_of_cover {G : Type} [AddCommGroup G] (H K : AddSubgroup G) (R : Set G) (hR : R.Finite)
    (h : ∀ x ∈ K, ∃ ρ ∈ R, x - ρ ∈ H) : H.relIndex K ≠ 0 := by
  classical
  have : Finite R := hR.to_subtype
  choose! ρ hρ hρH using h
  let f : K ⧸ H.addSubgroupOf K → R := fun q => ⟨ρ (Quotient.out q : K), hρ _ (Quotient.out q : K).2⟩
  have hf : Function.Injective f := by
    intro q q' hqq
    have h1 : ρ (Quotient.out q : K) = ρ (Quotient.out q' : K) := congrArg Subtype.val hqq
    have h2 := hρH _ (Quotient.out q : K).2
    have h3 := hρH _ (Quotient.out q' : K).2
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have h4 : ((-(Quotient.out q : K) + (Quotient.out q' : K) : K) : G)
        = ((Quotient.out q' : K) - ρ (Quotient.out q' : K)) - ((Quotient.out q : K) - ρ (Quotient.out q : K)) := by
      rw [h1]; push_cast; abel
    rw [h4]; exact H.sub_mem h3 h2
  have : Finite (K ⧸ H.addSubgroupOf K) := Finite.of_injective f hf
  exact AddSubgroup.index_ne_zero_of_finite

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem loc_approx (P : HeightOneSpectrum (𝓞 E)) (M M₀ : Submodule (𝓞 E) W) (ν : 𝓞 E) (hν : ν ≠ 0) (h : ∀ x ∈ M, ν • x ∈ M₀) {x : W}
    (hx : x ∈ localization₂ P.asIdeal M) : ∃ m ∈ M, x - m ∈ localization₂ P.asIdeal M₀ := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨k, hk⟩ := primary_pow P ν hν
  have hcop : IsCoprime (Ideal.span {s}) (P.asIdeal ^ k) := by
    apply IsCoprime.pow_right
    obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hs
    exact Ideal.isCoprime_iff_exists.2 ⟨y * s, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s), i, hi, hyi⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨s', rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine ⟨s' • (s • x), M.smul_mem s' hsx, ?_⟩
  have e0 : s' • (s • x) + j • x = x := by rw [← mul_smul, ← add_smul, hij, one_smul]
  have e1 : x - s' • (s • x) = j • x := sub_eq_of_eq_add (by rw [add_comm]; exact e0.symm)
  rw [e1]
  obtain ⟨u, hu, r, hr⟩ := hk j hj
  refine ⟨u * s, P.asIdeal.primeCompl.mul_mem hu hs, ?_⟩
  have e2 : (u * s) • (j • x) = ν • (r • (s • x)) := by
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    linear_combination s * hr
  rw [e2]; exact h _ (M.smul_mem r hsx)

theorem relIndex_loc_ne_zero (P : HeightOneSpectrum (𝓞 E)) (M M₀ : Submodule (𝓞 E) W) (hM : M.FG) (ν : 𝓞 E) (hν : ν ≠ 0)
    (h : ∀ x ∈ M, ν • x ∈ M₀) : (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 := by
  have : Finite (𝓞 E ⧸ Ideal.span {ν}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM
  have : Subsingleton (M ⧸ (⊤ : Submodule (𝓞 E) M)) :=
    ⟨fun p q => Quotient.inductionOn₂' p q fun x y => (Submodule.Quotient.eq ⊤).2 Submodule.mem_top⟩
  have hfin : Finite (M ⧸ (Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M))) :=
    Submodule.finite_quotient_smul (Ideal.span {ν}) Module.Finite.fg_top
  let out : M ⧸ (Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M)) → M := Function.surjInv (Submodule.Quotient.mk_surjective _)
  refine relIndex_ne_zero_of_cover _ _ (Set.range fun q => ((out q : M) : W)) (Set.finite_range _) ?_
  intro x hx
  obtain ⟨m, hm, hxm⟩ := loc_approx P M M₀ ν hν h hx
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩, ?_⟩
  have h1 : Submodule.Quotient.mk (p := Ideal.span {ν} • (⊤ : Submodule (𝓞 E) M)) (out (Submodule.Quotient.mk ⟨m, hm⟩))
      = Submodule.Quotient.mk ⟨m, hm⟩ := Function.surjInv_eq _ _
  have h2 := (Submodule.Quotient.eq _).1 h1
  have h2' : out (Submodule.Quotient.mk ⟨m, hm⟩) - ⟨m, hm⟩ ∈ ν • (⊤ : Submodule (𝓞 E) M) := by
    rw [← Submodule.ideal_span_singleton_smul]; exact h2
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h2'
  have h3 : ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M) : W) - m = ν • (y : W) := by
    have := congrArg (Subtype.val) hy
    simpa using this.symm
  have h4 : x - ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M) : W) = (x - m) - ν • (y : W) := by rw [← h3]; abel
  show x - ((out (Submodule.Quotient.mk ⟨m, hm⟩) : M) : W) ∈ localization₂ P.asIdeal M₀
  rw [h4]
  exact Submodule.sub_mem _ hxm (le_locP' M₀ P (h _ y.2))

end Vol

section VolumeCarry

open Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem exists_int_mul_integral (a : E) : ∃ e : ℤ, e ≠ 0 ∧ IsIntegral ℤ ((e : E) * a) := by
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ a)
  obtain ⟨e, he, hea⟩ := halg.exists_integral_multiple
  exact ⟨e, he, by rwa [zsmul_eq_mul] at hea⟩

theorem exists_smul_mem (L : Submodule (𝓞 E) W) (hL : Submodule.span E (L : Set W) = ⊤) (y : W) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first | exact Bl.general_b_fact_third_ter.goal1 .. | (apply Bl.general_b_fact_third_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_ter.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_ter.goal1 <;> first | assumption | infer_instance)

theorem exists_smul_le (L₁ L : Submodule (𝓞 E) W) (h₁ : L₁.FG) (hL : Submodule.span E (L : Set W) = ⊤) :
    ∃ ν : 𝓞 E, ν ≠ 0 ∧ ∀ x ∈ L₁, ν • x ∈ L := by
  classical
  obtain ⟨G, hG⟩ := h₁
  choose cg hcg hcg' using fun y => exists_smul_mem L hL y
  refine ⟨∏ g ∈ G, cg g, Finset.prod_ne_zero_iff.2 (fun g _ => hcg g), ?_⟩
  have hle : L₁ ≤ L.comap ((∏ g ∈ G, cg g) • (LinearMap.id : W →ₗ[𝓞 E] W)) := by
    rw [← hG]
    apply Submodule.span_le.2
    intro g hg
    show (∏ g ∈ G, cg g) • g ∈ L
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem cg hg
    rw [hq, mul_comm, mul_smul]; exact L.smul_mem q (hcg' g)
  exact fun x hx => hle hx

theorem fg_of_scale (M L : Submodule (𝓞 E) W) (hL : L.FG) (ν : 𝓞 E) (hν : ν ≠ 0) (h : ∀ x ∈ M, ν • x ∈ L) : M.FG := by
  have hno : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (M.map (ν • (LinearMap.id : W →ₗ[𝓞 E] W))).FG :=
    isNoetherian_submodule.1 hno _ (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
  refine Submodule.fg_of_fg_map_injective _ ?_ h1
  intro x y hxy
  have h2 : ν • x = ν • y := hxy
  rw [← IsScalarTower.algebraMap_smul E ν x, ← IsScalarTower.algebraMap_smul E ν y] at h2
  exact smul_right_injective W (fun h0 => hν ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))) h2

variable {a b : ℕ}

theorem homO_scale (N N₁ : Submodule (𝓞 E) (Sp E a)) (N' N₁' : Submodule (𝓞 E) (Sp E b)) (νa νb : 𝓞 E) (ha : ∀ y ∈ N₁, νa • y ∈ N)
    (hb : ∀ y ∈ N', νb • y ∈ N₁') {x : HomE E a b} (hx : x ∈ homO N N') : (νa * νb) • x ∈ homO N₁ N₁' := by
  intro y hy
  show (νa * νb) • x y ∈ N₁'
  rw [mul_comm, mul_smul, ← LinearMap.map_smul_of_tower]
  exact hb _ (hx _ (ha y hy))

theorem perO_scale (AA0 : Submodule (𝓞 E) E) (N N₁ : Submodule (𝓞 E) (Sp E a)) (N' N₁' : Submodule (𝓞 E) (Sp E b)) (νa νb : 𝓞 E)
    (ha : ∀ y ∈ N₁, νa • y ∈ N) (hb : ∀ y ∈ N', νb • y ∈ N₁') : ∀ x ∈ perO AA0 N N', (νa * νb) • x ∈ perO AA0 N₁ N₁' := by
  have hle : perO AA0 N N' ≤ (perO AA0 N₁ N₁').comap ((νa * νb) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) := by
    apply Submodule.span_le.2
    rintro _ ⟨r, hr, x, hx, rfl⟩
    show (νa * νb) • (r • x) ∈ perO AA0 N₁ N₁'
    rw [smul_comm]
    exact Submodule.subset_span ⟨r, hr, _, homO_scale N N₁ N' N₁' νa νb ha hb hx, rfl⟩
  exact fun x hx => hle hx

theorem homO_std_fg : (homO (stdLat E a) (stdLat E b)).FG := by
  let Ψ : HomE E a b →ₗ[𝓞 E] (Fin a → Sp E b) :=
    { toFun := fun x j => x (Pi.single j 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Ψ := by
    intro x y h
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    exact congrFun h j
  have hpi : (Submodule.pi Set.univ fun _ : Fin a => stdLat E b).FG := Submodule.fg_pi fun _ => (stdLat_lattice (E := E) (n := b)).fg
  have hno : IsNoetherian (𝓞 E) (Submodule.pi Set.univ fun _ : Fin a => stdLat E b) := isNoetherian_of_fg_of_noetherian _ hpi
  refine Submodule.fg_of_fg_map_injective Ψ hinj (isNoetherian_submodule.1 hno _ ?_)
  rintro _ ⟨x, hx, rfl⟩ j _
  refine hx _ ?_
  have := single_mem_stdLat (E := E) (n := a) j 1
  simpa using this

theorem smul_smul_eq_of {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
    [IsScalarTower (𝓞 E) E W] (ν : 𝓞 E) (r : E) (x : W) (ρ : 𝓞 E) (h : algebraMap (𝓞 E) E ρ = ν • r) : ν • (r • x) = ρ • x := by
  rw [← IsScalarTower.algebraMap_smul E ρ x, h, smul_assoc]

theorem covolume_positive : VolCPos := by
  intro E _ _ _ a b AA0 SS N N' hN hN' hsN hsN' hAA _
  have sa := stdLat_lattice (E := E) (n := a)
  have sb := stdLat_lattice (E := E) (n := b)
  obtain ⟨νa₁, ha₁0, ha₁⟩ := exists_smul_le (stdLat E a) N sa.fg hsN
  obtain ⟨νb₁, hb₁0, hb₁⟩ := exists_smul_le N' (stdLat E b) hN' sb.span_eq_top
  obtain ⟨νa₂, ha₂0, ha₂⟩ := exists_smul_le N (stdLat E a) hN sa.span_eq_top
  obtain ⟨νb₂, hb₂0, hb₂⟩ := exists_smul_le (stdLat E b) N' sb.fg hsN'
  have h1 := perO_scale AA0 N (stdLat E a) N' (stdLat E b) νa₁ νb₁ ha₁ hb₁
  have h2 := perO_scale AA0 (stdLat E a) N (stdLat E b) N' νa₂ νb₂ ha₂ hb₂
  have hone : Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : E) ∈ Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) :=
      Submodule.subset_span (Submodule.one_le.1 le_rfl)
    have := Submodule.smul_mem _ x h1
    simpa using this
  obtain ⟨ν₀, h00, h0⟩ := exists_smul_le AA0 (1 : Submodule (𝓞 E) E) hAA hone
  have hM₀ : (perO AA0 (stdLat E a) (stdLat E b)).FG := by
    refine fg_of_scale _ _ (homO_std_fg (E := E) (a := a) (b := b)) ν₀ h00 ?_
    have hle : perO AA0 (stdLat E a) (stdLat E b) ≤ (homO (stdLat E a) (stdLat E b)).comap
        (ν₀ • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) := by
      apply Submodule.span_le.2
      rintro _ ⟨r, hr, x, hx, rfl⟩
      show ν₀ • (r • x) ∈ homO (stdLat E a) (stdLat E b)
      obtain ⟨ρ, hρ⟩ := Submodule.mem_one.1 (h0 r hr)
      rw [smul_smul_eq_of (ν₀) r x ρ hρ]
      exact Submodule.smul_mem _ ρ hx
    exact fun x hx => hle hx
  have hM : (perO AA0 N N').FG := fg_of_scale _ _ hM₀ _ (mul_ne_zero ha₁0 hb₁0) h1
  exact volS_pos_of SS _ _ fun P _ =>
    ⟨relIndex_loc_ne_zero P _ _ hM _ (mul_ne_zero ha₁0 hb₁0) h1, relIndex_loc_ne_zero P _ _ hM₀ _ (mul_ne_zero ha₂0 hb₂0) h2⟩

end VolumeCarry

section Direct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem brk_zero_right (H : Sesq V) (y : V) : brk H y 0 = 1 := by simp [brk, altE]

theorem brk_neg_right (H : Sesq V) (y s : V) : brk H y (-s) = (brk H y s)⁻¹ := by
  have h := brk_sub_right H y 0 s
  rwa [zero_sub, brk_zero_right, one_mul] at h

theorem hatS_ind (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (B L : AddSubgroup V) (hB : IsSemiChar H B α) (vol : ℝ) (SA : Finset V)
    (hSA : IsReps B L SA) {y : V} (hy : y ∈ B) :
    hatS H vol SA (indL B) y = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) := by
  have hBint := (semicharacterBasic V H hH B α hB).2.2
  have h1 : ∑ t ∈ SA, indL B t * (brk H y t)⁻¹ = 1 := by
    obtain ⟨t0, _, ht0B, hsum⟩ := Inv.sum_reps hSA (fun t => indL B t * (brk H y t)⁻¹) (fun t _ htB => by simp [indL, htB])
    rw [hsum, brk_one_of_int H (hBint ht0B y hy)]; simp [indL, ht0B]
  simp only [hatS, h1, mul_one]

theorem twist_induced_vanish : XiIndZero := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol θ z
  obtain ⟨hH, -, hB, -, -, -⟩ := hyp
  simp only [xiS, sumU]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]; ring

theorem sumU_fixed (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (B Λ : AddSubgroup V) (hB : IsSemiChar H B α) (SB : Finset V)
    (hSB : IsReps Λ B SB) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ) {m : V} (hm : m ∈ B) (z : V) :
    α m * opU H m (sumU H α SB θ) z = sumU H α SB θ z := by
  have h0 : sumU H α SB θ = fun v => ∑ y ∈ SB, (fun w => α y * opU H y θ w) v := rfl
  rw [h0, Inv.opU_finset_sum, Finset.mul_sum]
  have h1 : ∀ y ∈ SB, α m * opU H m (fun w => α y * opU H y θ w) z = α (m + y) * opU H (m + y) θ z :=
    fun y hy => semicharacterHom V H hH B α hB m hm y (hSB.1 y hy) θ z
  rw [Finset.sum_congr rfl h1]
  exact sum_reps_shift hSB (fun y => α y * opU H y θ z)
    (fun x hx y hy hyΛ => InterClass_of semicharacterHom V H hH Λ B α hB θ hθ x hx y hy hyΛ z) hm

theorem twist_induced_class : XiIndClass := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol θ hθ s hs m hm hmB z
  have hz := twist_induced_vanish V H α A B Λ hyp SA SB hSA hSB vol θ
  obtain ⟨hH, hA, hB, -, -, -⟩ := hyp
  have hneg := (semicharacterBasic V H hH A α hA).2.1
  have hnegB := (semicharacterBasic V H hH B α hB).2.1
  set G := xiS H α vol SA SB (indL B) θ with hG
  have hfix : (fun v => α (-m) * opU H (-m) G v) = G := by
    funext v
    have hG' : G = fun w => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * sumU H α SB θ w := funext hz
    rw [hG', Inv.opU_const_mul, mul_left_comm, sumU_fixed H hH α B Λ hB SB hSB θ hθ (B.neg_mem hmB)]
  have h1 := semicharacterHom V H hH A α hA (-s) (A.neg_mem hs) (-m) (A.neg_mem hm) G z
  rw [hfix] at h1
  show α (s + m) * opU H (-(s + m)) G z = α s * opU H (-s) G z
  rw [← hneg (s + m) (A.add_mem hs hm), neg_add, ← h1, hneg s hs]

theorem twist_expand_series : XiExpandS := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol θ hθ Φ z
  obtain ⟨hH, -, hB, -, -, hΛ, -⟩ := hyp
  have hneg := (semicharacterBasic V H hH Λ α hΛ).2.1
  have h1 : ∀ s ∈ SA, Φ s * xiInd H α vol B SA SB θ s z
      = ∑ y ∈ SB, Φ s * ((brk H y s)⁻¹ * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * α y * opU H y θ z)) := by
    intro s hs
    have hsΛ : s ∈ Λ := (hSA.1 s hs).1
    show Φ s * (α s * opU H (-s) (xiS H α vol SA SB (indL B) θ) z) = _
    rw [← hneg s hsΛ, step_translate H hH α Λ vol SA SB (indL B) θ hθ (Λ.neg_mem hsΛ) z, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [brk_neg_right, hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  simp only [xiS, sumU, hatS]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem twist_vacuum : XiVacuum := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB vol hvol θ hθ z
  obtain ⟨hH, -, hB, -, -, hΛ, -, -, -, h5⟩ := hyp
  have hΛint := (semicharacterBasic V H hH Λ α hΛ).2.2
  have hBint := (semicharacterBasic V H hH B α hB).2.2
  have hcardA : (SA.card : ℂ) ≠ 0 := by
    obtain ⟨x, hx, -⟩ := hSA.2.2 0 (AddSubgroup.zero_mem _)
    exact_mod_cast (Finset.card_pos.2 ⟨x, hx⟩).ne'
  have hs : ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) = ((vol : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt hvol.le
  have hs0 : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hout : ∀ y ∈ SB, y ∉ Λ → hatS H vol SA (fun _ => ((Real.sqrt vol : ℝ) : ℂ)⁻¹) y * α y * opU H y θ z = 0 := by
    intro y hy hyΛ
    have hz : ∑ t ∈ SA, (brk H y t)⁻¹ = 0 := by
      by_contra hne0
      apply hyΛ
      apply h5 y (hSB.1 y hy)
      intro a haA haΛ
      by_contra hno
      refine hne0 (char_sum_zero hSA (fun t => (brk H y t)⁻¹) ?_ ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro u v; simp only [brk_add_right, mul_inv]
      · intro m _ hmB
        rw [brk_one_of_int H (hBint hmB y (hSB.1 y hy))]; simp
      · intro h1
        apply hno
        apply int_of_brk_one H
        exact inv_eq_one.1 h1
    simp only [hatS, ← Finset.mul_sum, hz, mul_zero, zero_mul]
  obtain ⟨y0, hy0, hy0Λ, hsum⟩ := Inv.sum_reps hSB
    (fun y => hatS H vol SA (fun _ => ((Real.sqrt vol : ℝ) : ℂ)⁻¹) y * α y * opU H y θ z) hout
  show ∑ y ∈ SB, hatS H vol SA (fun _ => ((Real.sqrt vol : ℝ) : ℂ)⁻¹) y * α y * opU H y θ z = θ z
  rw [hsum]
  have hone : ∑ t ∈ SA, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (brk H y0 t)⁻¹ = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (SA.card : ℂ) := by
    rw [Finset.sum_congr rfl fun t ht => by rw [brk_one_of_int H (hΛint (hSA.1 t ht).1 y0 hy0Λ), inv_one, mul_one]]
    simp [mul_comm]
  have hhat : hatS H vol SA (fun _ => ((Real.sqrt vol : ℝ) : ℂ)⁻¹) y0 = 1 := by
    simp only [hatS, hone]
    rw [← hs]; field_simp
  rw [hhat, one_mul]
  exact hθ y0 hy0Λ z

theorem twist_induced_coset_class : XiIndCClass := XiIndCClass_of twist_induced_class

end Direct

section DirectL

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xiInd_shift (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (A : AddSubgroup V) (hA : IsSemiChar H A α) (vol : ℝ) (M : AddSubgroup V)
    (SA SB : Finset V) (θ : V → ℂ) {x s : V} (hx : x ∈ A) (hs : s ∈ A) (z : V) :
    α x * opU H x (xiInd H α vol M SA SB θ s) z = xiInd H α vol M SA SB θ (s - x) z := by
  have hneg := (semicharacterBasic V H hH A α hA).2.1
  have h1 := semicharacterHom V H hH A α hA x hx (-s) (A.neg_mem hs) (xiS H α vol SA SB (indL M) θ) z
  have h2 : xiInd H α vol M SA SB θ s = fun v => α (-s) * opU H (-s) (xiS H α vol SA SB (indL M) θ) v := by
    funext v; rw [hneg s hs]; rfl
  rw [h2, h1]
  show _ = α (s - x) * opU H (-(s - x)) (xiS H α vol SA SB (indL M) θ) z
  have h3 : -(s - x) = x + -s := by abel
  rw [← hneg (s - x) (A.sub_mem hs hx), h3]

theorem inter_le (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (hyp : SplitHyp H α A B Λ) {m : V} (hmA : m ∈ A) (hmB : m ∈ B) : m ∈ Λ := by
  obtain ⟨hH, -, hB, -, -, -, -, -, h4, -⟩ := hyp
  exact h4 m hmA fun b hb _ => (semicharacterBasic V H hH B α hB).2.2 hmB b hb

theorem twist_expand_lattice : XiExpandL := by
  classical
  intro V _ _ H α A B Λ hyp S SX SA SB hS hSX hSA hSB vol θ hθ Φ hΦ z
  have hES := twist_expand_series V H α A B Λ hyp SA SB hSA hSB vol θ hθ
  have hcl := twist_induced_class V H α A B Λ hyp SA SB hSA hSB vol θ hθ
  have hAB : ∀ m ∈ A, m ∈ B → m ∈ Λ := fun m h1 h2 => inter_le H α A B Λ hyp h1 h2
  obtain ⟨hH, hA, -, -, -, -⟩ := hyp
  let g : V → ℂ := fun s => Φ s * xiInd H α vol B SA SB θ s z
  have hg : ∀ s ∈ A, ∀ m ∈ A, m ∈ B → g (s + m) = g s := by
    intro s hs m hm hmB
    show Φ (s + m) * _ = Φ s * _
    rw [hΦ s hs m hm hmB, hcl s hs m hm hmB z]
  have h1 : ∀ x ∈ SX, α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) z = ∑ t ∈ SA, g (t - x) := by
    intro x hx
    have h2 : xiS H α vol SA SB (fun s => Φ (s - x)) θ = fun v => ∑ t ∈ SA, (fun w => Φ (t - x) * xiInd H α vol B SA SB θ t w) v :=
      funext fun v => hES (fun s => Φ (s - x)) v
    rw [h2, Inv.opU_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Inv.opU_const_mul, mul_left_comm, xiInd_shift H hH α A hA vol B SA SB θ (hSX.1 x hx) (hSA.1 t ht).2 z]
  show ∑ x ∈ SX, α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) z = ∑ s ∈ S, g s
  rw [Finset.sum_congr rfl h1, ← Finset.sum_product']
  have hinj : ∀ p ∈ SX ×ˢ SA, ∀ p' ∈ SX ×ˢ SA, (p.2 - p.1) - (p'.2 - p'.1) ∈ B → p = p' := by
    rintro ⟨x, t⟩ hp ⟨x', t'⟩ hp' hd
    obtain ⟨hx, ht⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', ht'⟩ := Finset.mem_product.1 hp'
    simp only at hd hx ht hx' ht'
    have hdA : (t - x) - (t' - x') ∈ A :=
      A.sub_mem (A.sub_mem (hSA.1 t ht).2 (hSX.1 x hx)) (A.sub_mem (hSA.1 t' ht').2 (hSX.1 x' hx'))
    have hdΛ := hAB _ hdA hd
    have hxx : x - x' ∈ Λ := by
      have : x - x' = (t - t') - ((t - x) - (t' - x')) := by abel
      rw [this]; exact Λ.sub_mem (Λ.sub_mem (hSA.1 t ht).1 (hSA.1 t' ht').1) hdΛ
    have hxe : x = x' := hSX.2.1 x hx x' hx' hxx
    subst hxe
    have htt : t - t' ∈ B := by
      have : t - t' = (t - x) - (t' - x) := by abel
      rw [this]; exact hd
    rw [hSA.2.1 t ht t' ht' htt]
  have hT : IsReps B A ((SX ×ˢ SA).image fun p => p.2 - p.1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨hx, ht⟩ := Finset.mem_product.1 hp
      exact A.sub_mem (hSA.1 _ ht).2 (hSX.1 _ hx)
    · intro w hw w' hw' hd
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hw'
      rw [hinj p hp p' hp' hd]
    · intro y hy
      obtain ⟨x, hx, hxd⟩ := hSX.2.2 (-y) (A.neg_mem hy)
      have h3 : y + x ∈ Λ ⊓ A := by
        refine ⟨?_, A.add_mem hy (hSX.1 x hx)⟩
        have : y + x = -(-y - x) := by abel
        rw [this]; exact Λ.neg_mem hxd
      obtain ⟨t, ht, htd⟩ := hSA.2.2 _ h3
      refine ⟨t - x, Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩, ?_⟩
      have : y - (t - x) = y + x - t := by abel
      rw [this]; exact htd
  rw [← sum_reps_eq hT hS g hg, Finset.sum_image]
  intro p hp p' hp' h
  apply hinj p hp p' hp'
  have h' : p.2 - p.1 = p'.2 - p'.1 := h
  rw [h', sub_self]; exact B.zero_mem

theorem exists_reps_AB (A B Λ : AddSubgroup V) (SX SA : Finset V) (hSX : IsReps Λ A SX) (hSA : IsReps B (Λ ⊓ A) SA) :
    ∃ S : Finset V, IsReps B A S := by
  classical
  have hidx : relIdx B A ≠ 0 := by
    refine relIndex_ne_zero_of_cover B A (((SX ×ˢ SA).image fun p => p.2 - p.1 : Finset V) : Set V) (Finset.finite_toSet _) ?_
    intro y hy
    obtain ⟨x', hx', hxd⟩ := hSX.2.2 (-y) (A.neg_mem hy)
    have h3 : y + x' ∈ Λ ⊓ A := by
      refine ⟨?_, A.add_mem hy (hSX.1 x' hx')⟩
      have : y + x' = -(-y - x') := by abel
      rw [this]; exact Λ.neg_mem hxd
    obtain ⟨t, ht, htd⟩ := hSA.2.2 _ h3
    refine ⟨t - x', Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x', t), Finset.mem_product.2 ⟨hx', ht⟩, rfl⟩), ?_⟩
    have : y - (t - x') = y + x' - t := by abel
    rw [this]; exact htd
  exact (cosetRepsExist V B A hidx).1

theorem twist_translate : XiTranslate := by
  intro V _ _ H α A B Λ hyp SX SA SB hSX hSA hSB vol θ hθ Φ hΦ x hx z
  classical
  have hcl := twist_induced_class V H α A B Λ hyp SA SB hSA hSB vol θ hθ
  have hEL := twist_expand_lattice V H α A B Λ hyp
  have hH := hyp.1
  have hA := hyp.2.1
  obtain ⟨S, hS⟩ := exists_reps_AB A B Λ SX SA hSX hSA
  have hΦ' : InvOn A B fun t => Φ (t + x) := by
    intro t ht m hm hmB
    show Φ (t + m + x) = Φ (t + x)
    have : t + m + x = (t + x) + m := by abel
    rw [this]; exact hΦ _ (A.add_mem ht hx) m hm hmB
  rw [hEL S SX SA SB hS hSX hSA hSB vol θ hθ _ hΦ' z]
  have h2 : xiL H α vol SX SA SB Φ θ = fun v => ∑ s ∈ S, (fun w => Φ s * xiInd H α vol B SA SB θ s w) v :=
    funext fun v => hEL S SX SA SB hS hSX hSA hSB vol θ hθ Φ hΦ v
  rw [h2, Inv.opU_finset_sum, Finset.mul_sum]
  have h3 : ∀ s ∈ S, α x * opU H x (fun w => Φ s * xiInd H α vol B SA SB θ s w) z = Φ s * xiInd H α vol B SA SB θ (s - x) z := by
    intro s hs
    rw [Inv.opU_const_mul, mul_left_comm, xiInd_shift H hH α A hA vol B SA SB θ hx (hS.1 s hs) z]
  rw [Finset.sum_congr rfl h3]
  have hg : ∀ s ∈ A, ∀ m ∈ A, m ∈ B → (fun s => Φ (s + x) * xiInd H α vol B SA SB θ s z) (s + m)
      = (fun s => Φ (s + x) * xiInd H α vol B SA SB θ s z) s := by
    intro s hs m hm hmB
    show Φ (s + m + x) * _ = Φ (s + x) * _
    have e' : Φ (s + m + x) = Φ (s + x) := hΦ' s hs m hm hmB
    rw [e', hcl s hs m hm hmB z]
  rw [← sum_reps_shift hS _ hg (A.neg_mem hx)]
  refine Finset.sum_congr rfl fun s _ => ?_
  show Φ (-x + s + x) * xiInd H α vol B SA SB θ (-x + s) z = _
  have e1 : -x + s + x = s := by abel
  have e2 : -x + s = s - x := by abel
  rw [e1, e2]

theorem G_fixed (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (hyp : SplitHyp H α A B Λ) (SA SB : Finset V) (hSA : IsReps B (Λ ⊓ A) SA)
    (hSB : IsReps Λ B SB) (vol : ℝ) (θ : V → ℂ) (hθ : θ ∈ fixedBy H α Λ) {m : V} (hm : m ∈ B) :
    (fun v => α m * opU H m (xiS H α vol SA SB (indL B) θ) v) = xiS H α vol SA SB (indL B) θ := by
  have hz := twist_induced_vanish V H α A B Λ hyp SA SB hSA hSB vol θ
  obtain ⟨hH, -, hB, -, -, -⟩ := hyp
  funext v
  have hG' : xiS H α vol SA SB (indL B) θ
      = fun w => ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * sumU H α SB θ w := funext hz
  rw [hG', Inv.opU_const_mul, mul_left_comm, sumU_fixed H hH α B Λ hB SB hSB θ hθ hm]

theorem twist_modulate : XiModulate := by
  intro V _ _ H α A B Λ hyp SX SA SB hSX hSA hSB vol θ hθ Φ hΦ y hy z
  have hEL := twist_expand_lattice V H α A B Λ hyp
  have hfix := G_fixed H α A B Λ hyp SA SB hSA hSB vol θ hθ hy
  have hH := hyp.1
  have hBint := (semicharacterBasic V H hH B α hyp.2.2.1).2.2
  obtain ⟨S, hS⟩ := exists_reps_AB A B Λ SX SA hSX hSA
  have hΦ' : InvOn A B fun t => brk H y t * Φ t := by
    intro t ht m hm hmB
    show brk H y (t + m) * Φ (t + m) = brk H y t * Φ t
    rw [brk_add_right, brk_one_of_int H (hBint hmB y hy), mul_one, hΦ t ht m hm hmB]
  rw [hEL S SX SA SB hS hSX hSA hSB vol θ hθ _ hΦ' z]
  have h2 : xiL H α vol SX SA SB Φ θ = fun v => ∑ s ∈ S, (fun w => Φ s * xiInd H α vol B SA SB θ s w) v :=
    funext fun v => hEL S SX SA SB hS hSX hSA hSB vol θ hθ Φ hΦ v
  rw [h2, Inv.opU_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Inv.opU_const_mul]
  have h3 : xiInd H α vol B SA SB θ s = fun v => α s * opU H (-s) (xiS H α vol SA SB (indL B) θ) v := rfl
  have h4 : brk H (-s) y = brk H y s := by
    simp only [brk]
    rw [Inv.altE_neg_right, ← Inv.altE_swap hH y s]
  have h5 : α y * opU H (-s) (opU H y (xiS H α vol SA SB (indL B) θ)) z = opU H (-s) (xiS H α vol SA SB (indL B) θ) z := by
    rw [← Inv.opU_const_mul, hfix]
  rw [h3, Inv.opU_const_mul, (bracket_commutation V H hH).1 (-s) y, h4]
  show brk H y s * Φ s * (α s * opU H (-s) (xiS H α vol SA SB (indL B) θ) z) = _
  rw [← h5]; ring

theorem twist_representatives : XiReps := by
  intro V _ _ H α A B Λ hyp SX SA SB SX' SA' SB' hSX hSA hSB hSX' hSA' hSB' vol θ hθ Φ hΦ z
  have hEL := twist_expand_lattice V H α A B Λ hyp
  have hz := twist_induced_vanish V H α A B Λ hyp
  have hH := hyp.1
  have hB := hyp.2.2.1
  obtain ⟨S, hS⟩ := exists_reps_AB A B Λ SX SA hSX hSA
  rw [hEL S SX' SA' SB' hS hSX' hSA' hSB' vol θ hθ Φ hΦ z, hEL S SX SA SB hS hSX hSA hSB vol θ hθ Φ hΦ z]
  have hcard : (SA'.card : ℂ) = (SA.card : ℂ) := by
    have := sum_reps_eq hSA' hSA (fun _ => (1 : ℂ)) (fun _ _ _ _ _ => rfl)
    simpa using this
  have hG : xiS H α vol SA' SB' (indL B) θ = xiS H α vol SA SB (indL B) θ := by
    funext v
    rw [hz SA' SB' hSA' hSB' vol θ v, hz SA SB hSA hSB vol θ v, hcard]
    congr 1
    exact sum_reps_eq hSB' hSB (fun y => α y * opU H y θ v)
      (fun x hx y hy hyΛ => InterClass_of semicharacterHom V H hH Λ B α hB θ hθ x hx y hy hyΛ v)
  refine Finset.sum_congr rfl fun s _ => ?_
  show Φ s * (α s * opU H (-s) (xiS H α vol SA' SB' (indL B) θ) z) = Φ s * (α s * opU H (-s) (xiS H α vol SA SB (indL B) θ) z)
  rw [hG]

end DirectL

open NumberField in

theorem twO_one {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
    [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (e : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → ℤ) : twist₂ M 1 e = M := by
  apply le_antisymm
  · intro x hx
    rw [mem_twO] at hx
    apply mem_of_forall_locP
    intro Q
    simpa using hx Q
  · intro x hx
    rw [mem_twO]
    intro Q
    simpa using le_locP' M Q hx

namespace Test

def H1 : Sesq ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => z * (starRingEnd ℂ) w)
    (by intro x y w; ring) (by intro c x w; simp only [smul_eq_mul, RingHom.id_apply]; ring)
    (by intro x y w; simp only [map_add]; ring) (by intro c x w; simp only [smul_eq_mul, map_mul]; ring)

theorem standard_hermitian_apply (z w : ℂ) : H1 z w = z * (starRingEnd ℂ) w := rfl

theorem alternating_form_standard_hermitian (x y : ℂ) : altE H1 x y = x.im * y.re - x.re * y.im := by
  simp only [altE, standard_hermitian_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem isHermitian_standard_form : IsHerm H1 := by
  intro x y
  simp only [standard_hermitian_apply, map_mul, Complex.conj_conj]; ring

def Lp (p : ℝ) : AddSubgroup ℂ where
  carrier := {z | (∃ m : ℤ, z.re = p * m) ∧ ∃ n : ℤ, z.im = n / p}
  zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  add_mem' := by
    rintro x y ⟨⟨m, hm⟩, n, hn⟩ ⟨⟨m', hm'⟩, n', hn'⟩
    exact ⟨⟨m + m', by rw [Complex.add_re, hm, hm']; push_cast; ring⟩, ⟨n + n', by rw [Complex.add_im, hn, hn']; push_cast; ring⟩⟩
  neg_mem' := by
    rintro x ⟨⟨m, hm⟩, n, hn⟩
    exact ⟨⟨-m, by rw [Complex.neg_re, hm]; push_cast; ring⟩, ⟨-n, by rw [Complex.neg_im, hn]; push_cast; ring⟩⟩

theorem mem_Lp {p : ℝ} {z : ℂ} : z ∈ Lp p ↔ (∃ m : ℤ, z.re = p * m) ∧ ∃ n : ℤ, z.im = n / p := Iff.rfl

def α1 (z : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((z.re * z.im : ℝ) : ℂ))

theorem exp_pi_int (k : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 ∨
    Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = -1 := by
  have h : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = (-1 : ℂ) ^ k := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h]
  rcases Int.even_or_odd k with hk | hk
  · left; exact hk.neg_one_zpow
  · right; exact hk.neg_one_zpow

theorem semi_Lp {p : ℝ} (hp : p ≠ 0) : IsSemiChar H1 (Lp p) α1 := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨⟨m, hm⟩, n, hn⟩
    have h : ((x.re * x.im : ℝ) : ℂ) = ((m * n : ℤ) : ℂ) := by
      have : x.re * x.im = ((m * n : ℤ) : ℝ) := by rw [hm, hn]; push_cast; field_simp
      rw [this]; push_cast; ring
    simp only [α1]; rw [h]; exact exp_pi_int _
  · rintro x ⟨⟨m, hm⟩, -⟩ y ⟨-, n', hn'⟩
    have key : x.re * y.im = ((m * n' : ℤ) : ℝ) := by rw [hm, hn']; push_cast; field_simp
    have key' : (x.re : ℂ) * (y.im : ℂ) = ((m * n' : ℤ) : ℂ) := by exact_mod_cast key
    simp only [α1]
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m * n', ?_⟩
    rw [alternating_form_standard_hermitian, Complex.add_re, Complex.add_im]
    push_cast at key' ⊢
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * key'

theorem selfDual_Lp {p : ℝ} (hp : p ≠ 0) : IsSelfDual H1 (Lp p) := by
  apply AddSubgroup.ext
  intro x
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h (p : ℂ) ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
    obtain ⟨l, hl⟩ := h ((p⁻¹ : ℝ) * Complex.I) ⟨⟨0, by simp⟩, ⟨1, by rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; push_cast; ring⟩⟩
    rw [alternating_form_standard_hermitian] at hk hl
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_sub] at hk hl
    refine ⟨⟨-l, ?_⟩, ⟨k, ?_⟩⟩
    · push_cast; rw [← hl]; field_simp
    · rw [← hk]; field_simp
  · rintro ⟨⟨m, hm⟩, n, hn⟩ y ⟨⟨m', hm'⟩, n', hn'⟩
    refine ⟨n * m' - m * n', ?_⟩
    rw [alternating_form_standard_hermitian, hm, hn, hm', hn']; push_cast; field_simp

theorem goodLat_test : GoodLat H1 α1 (Lp (1 / 3)) (Lp 3) (Lp 1) := by
  refine ⟨semi_Lp one_ne_zero, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨⟨m, hm⟩, n, hn⟩
    rw [AddSubgroup.mem_sup]
    refine ⟨(x.re : ℂ), ⟨⟨⟨m, by simpa using hm⟩, ⟨0, by simp⟩⟩, ⟨⟨3 * m, by rw [Complex.ofReal_re, hm]; push_cast; ring⟩, ⟨0, by simp⟩⟩⟩,
      (x.im : ℂ) * Complex.I, ⟨⟨⟨0, by simp⟩, ⟨n, by simpa using hn⟩⟩, ⟨⟨0, by simp⟩, ⟨3 * n, by simp [hn]⟩⟩⟩, Complex.re_add_im x⟩
  · rintro a ⟨⟨m, hm⟩, n, hn⟩ b ⟨⟨m', hm'⟩, -⟩ ⟨⟨k, hk⟩, -⟩
    refine ⟨⟨k - 3 * m', ?_⟩, ⟨3 * n, ?_⟩⟩
    · rw [Complex.add_re, hm'] at hk; push_cast; linarith
    · rw [hn]; push_cast; ring
  · rintro a ⟨⟨m, hm⟩, n, hn⟩ h
    obtain ⟨k, hk⟩ := h Complex.I ⟨⟨0, by simp⟩, ⟨3, by simp⟩⟩ ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩
    rw [alternating_form_standard_hermitian] at hk
    simp only [Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub] at hk
    refine ⟨⟨-k, by push_cast; linarith⟩, ⟨3 * n, by rw [hn]; push_cast; ring⟩⟩
  · rintro b ⟨⟨m, hm⟩, n, hn⟩ h
    obtain ⟨k, hk⟩ := h 1 ⟨⟨3, by simp⟩, ⟨0, by simp⟩⟩ ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
    rw [alternating_form_standard_hermitian] at hk
    simp only [Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_sub] at hk
    refine ⟨⟨3 * m, by rw [hm]; push_cast; ring⟩, ⟨-k, by push_cast; linarith⟩⟩

theorem splitHyp_test : SplitHyp H1 α1 (Lp (1 / 3)) (Lp 3) (Lp 1) :=
  ⟨isHermitian_standard_form, semi_Lp (by norm_num), semi_Lp (by norm_num), selfDual_Lp (by norm_num), selfDual_Lp (by norm_num), goodLat_test⟩

theorem level_test : ((1 / 3 : ℝ) : ℂ) ∈ Lp (1 / 3) ∧ ((1 / 3 : ℝ) : ℂ) ∉ Lp 1 := by
  refine ⟨⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩, ?_⟩
  rintro ⟨⟨m, hm⟩, -⟩
  rw [Complex.ofReal_re] at hm
  have h : (3 * m : ℤ) = 1 := by
    have : (3 : ℝ) * m = 1 := by linarith
    exact_mod_cast this
  omega

end Test

end Formalism.L2.Ker
