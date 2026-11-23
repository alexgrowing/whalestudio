import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.XiIndZero

open GlobalTheory.ThetaInter

variable {V : Type} [AddCommGroup V]

theorem isReps_repsOf {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) : IsReps L₁ L₂ (repsOf L₁ L₂) := by
  classical
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  refine Classical.epsilon_spec (p := fun S => IsReps L₁ L₂ S)
    ⟨Finset.univ.image fun c : L₂ ⧸ L₁.addSubgroupOf L₂ => ((Quotient.out c : L₂) : V), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out c : L₂).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    have : d = c := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [neg_add_eq_sub] using hxy
    rw [this]
  · intro y hy
    refine ⟨_, Finset.mem_image.2 ⟨((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂), Finset.mem_univ _, rfl⟩, ?_⟩
    have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [neg_add_eq_sub] using this

theorem sum_reps {M : Type*} [AddCommMonoid M] {L₁ L₂ : AddSubgroup V} [Fintype (L₂ ⧸ L₁.addSubgroupOf L₂)]
    {S : Finset V} (hS : IsReps L₁ L₂ S) (f : V → M) (hf : ∀ a ∈ L₂, ∀ s ∈ L₂, s ∈ L₁ → f (a + s) = f a) :
    ∑ x ∈ S, f x = ∑ c : L₂ ⧸ L₁.addSubgroupOf L₂, f ((Quotient.out c : L₂) : V) := by
  refine Finset.sum_bij (fun x hx => ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx y hy hxy
    have := QuotientAddGroup.eq.1 hxy.symm
    rw [AddSubgroup.mem_addSubgroupOf] at this
    exact hS.2.1 x hx y hy (by simpa [neg_add_eq_sub] using this)
  · intro c _
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hx, hxy⟩ := hS.2.2 y y.2
    refine ⟨x, hx, QuotientAddGroup.eq.2 ?_⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hxy
  · intro x hx
    set c := ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂) with hc
    have := QuotientAddGroup.eq.1 ((QuotientAddGroup.out_eq' c).trans hc)
    rw [AddSubgroup.mem_addSubgroupOf] at this
    have h2 := hf _ (Quotient.out c : L₂).2 _ (-(Quotient.out c : L₂) + ⟨x, hS.1 x hx⟩ : L₂).2 this
    simpa using h2

theorem card_reps {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) {S : Finset V} (hS : IsReps L₁ L₂ S) :
    S.card = relIdx L₁ L₂ := by
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  have h1 := sum_reps hS (fun _ => (1 : ℕ)) fun _ _ _ _ _ => rfl
  rw [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  simpa using h1

theorem xiInd_eq_inter : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (vol : ℝ) (θ : V → ℂ) (s z : V), IsHerm H → IsSelfDual H B → IsSemiChar H B α → IsSelfDual H Λ → θ ∈ fixedBy H α Λ → 0 < vol → Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) → relIdx B Λ ≠ 0 → relIdx Λ B ≠ 0 → ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B (repsOf B (Λ ⊓ A)) (repsOf Λ B) θ s z = ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ)⁻¹ * (α s * opU H (-s) (inter H α Λ B θ) z) := by
  intro V _ _ H α A B Λ vol θ s z hH hdB hsB hdΛ hθ hvol hle h1 h2
  classical
  have i1 : Fintype (Λ ⧸ B.addSubgroupOf Λ) := AddSubgroup.fintypeOfIndexNeZero h1
  have i2 : Fintype (B ⧸ Λ.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h2
  have hA : IsReps B (Λ ⊓ A) (repsOf B (Λ ⊓ A)) :=
    isReps_repsOf fun h => h1 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have hB : IsReps Λ B (repsOf Λ B) := isReps_repsOf h2
  set SA := repsOf B (Λ ⊓ A)
  set SB := repsOf Λ B
  have hA' : IsReps B Λ SA := by
    refine ⟨fun x hx => (hA.1 x hx).1, hA.2.1, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
    obtain ⟨x, hx, hxa⟩ := hA.2.2 a ha
    exact ⟨x, hx, by rw [add_sub_right_comm]; exact B.add_mem hxa hb.2⟩
  have hcard : SA.card = relIdx B Λ := card_reps h1 hA'
  have hidx : relIdx Λ B = relIdx B Λ := by
    simp only [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    exact card_eq_card hH hdB hdΛ
  obtain ⟨t₀, ht₀, ht₀B⟩ := hA'.2.2 0 Λ.zero_mem
  have ht₀B' : t₀ ∈ B := by simpa using ht₀B
  have hhat : ∀ y ∈ B, hatS H vol SA (indL B) y =
      ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℂ) / (relIdx B Λ : ℂ)) := by
    intro y hy
    rw [hatS, hcard, Finset.sum_eq_single_of_mem t₀ ht₀]
    · have : brk H y t₀ = 1 := by
        rw [← (chi_eq_one_iff t₀ y).2 (hdB.ge ht₀B' y hy), brk, chi]
        congr 1; ring
      simp [this, indL, ht₀B']
    · intro t ht hne
      have : t ∉ B := fun h => hne (hA'.2.1 t ht t₀ ht₀ (B.sub_mem h ht₀B'))
      simp [indL, this]
  have hn : (0 : ℝ) < (relIdx B Λ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h1
  set r : ℂ := ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  have hr2 : (relIdx B Λ : ℂ) = r ^ 2 := by rw [hr]; exact_mod_cast (Real.sq_sqrt hn.le).symm
  set v : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hv2 : (vol : ℂ) = v ^ 2 := by rw [hv]; exact_mod_cast (Real.sq_sqrt hvol.le).symm
  have hxi : xiS H α vol SA SB (indL B) θ = fun w => (v * r⁻¹) * inter H α Λ B θ w := by
    funext w
    rw [inter, finsum_eq_sum_of_fintype, hidx, ← hr,
      ← sum_reps hB (fun y => α y * opU H y θ w) ?_, xiS, sumU, ← mul_assoc, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [hhat y (hB.1 y hy), hr2, hv2]
      field_simp
    · intro a ha b hb hbΛ
      have e : (fun w => α b * opU H b θ w) = θ := funext (hθ b hbΛ)
      show α (a + b) * opU H (a + b) θ w = α a * opU H a θ w
      rw [alpha_opU_add hH hdB hsB ha hb, ← opU_mul, e]
  rw [xiInd, hxi]
  simp only [opU_mul]
  field_simp

end GlobalTheory.XiIndZero
