import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZeroStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.CrysCharJumps

open Classical

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l)

def HasJumps (χ : ↥(GK K) →* (↥(OL LL))ˣ) (f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) : Prop :=
  Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1)) ∧
    IsCrys (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) ∧
    ∀ τ b, multV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ b = if b = f τ then 1 else 0

variable {P K LL}

theorem charL_val (χ : ↥(GK K) →* (↥(OL LL))ˣ) (g : ↥(GK K)) :
    ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1) =
      algebraMap ↥(OL LL) ↥LL.1 ((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) := rfl

theorem isJumpV_of_multV_ne {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ) (h : multV (P.PD K) ρ τ b ≠ 0) :
    IsJumpV (P.PD K) ρ τ b := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

theorem hasJumps_one (hT : LocTied l P AI) : HasJumps P K LL 1 0 := by
  have hc : Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (1 : ↥(GK K) →* (↥(OL LL))ˣ) g : (↥LL.1)ˣ) : ↥LL.1)) := by
    simp only [charL_val, MonoidHom.one_apply, Units.val_one, map_one]
    exact continuous_const
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) 1) hc
    (fun g _ => by ext; simp [charL_val])
  exact ⟨hc, h1, fun τ b => by rw [h2]; rfl⟩

theorem hasJumps_mul (hT : LocTied l P AI) {χ ψ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f g : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (hψ : HasJumps P K LL ψ g) :
    HasJumps P K LL (χ * ψ) (f + g) := by
  have htw : IsTwistRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)
      (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) := by
    refine ⟨LinearEquiv.refl _ _, fun x y => ?_⟩
    simp [charRep, charL_val, mul_smul]
  obtain ⟨hc, hm⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI hT K LL ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) htw hχ.2.1 hψ.2.1
  refine ⟨?_, hc, fun τ b => ?_⟩
  · have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ) x : (↥LL.1)ˣ) : ↥LL.1)) =
        fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1) *
          ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ x : (↥LL.1)ˣ) : ↥LL.1) := by
      funext x
      simp [charL_val]
    rw [this]
    exact hχ.1.mul hψ.1
  · have hj : IsJumpV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ (f τ) :=
      isJumpV_of_multV_ne _ τ (f τ) (by rw [hχ.2.2]; simp)
    have := hm τ (b - f τ) (f τ) hj
    rw [sub_add_cancel] at this
    rw [this, hψ.2.2]
    simp only [Pi.add_apply]
    split_ifs <;> omega

theorem hasJumps_inv (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) :
    HasJumps P K LL χ⁻¹ (-f) := by
  have he : Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ = (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)⁻¹ := by
    refine MonoidHom.ext fun x => ?_
    simp only [Formalism.MainNotions.tableLineDegreeTwo.charL, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) f hχ.2.1 hχ.2.2
  refine ⟨?_, he ▸ h1, fun τ b => by rw [he, h2]; rfl⟩
  have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ x : (↥LL.1)ˣ) : ↥LL.1)) =
      (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1)) ∘ (fun x => x⁻¹) := by
    funext x
    simp only [Function.comp_apply, charL_val, MonoidHom.inv_apply, map_inv]
  rw [this]
  exact hχ.1.comp continuous_inv

theorem hasJumps_zpow (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (k : ℤ) :
    HasJumps P K LL (χ ^ k) (k • f) := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, zero_smul]
    exact hasJumps_one AI hT
  | succ k ih =>
    rw [zpow_add_one, add_smul, one_smul]
    exact hasJumps_mul AI hT ih hχ
  | pred k ih =>
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact hasJumps_mul AI hT ih (hasJumps_inv AI hT hχ)

theorem hasJumps_prod (hT : LocTied l P AI)
    (ψ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(GK K) →* (↥(OL LL))ˣ))
    (hψ : ∀ τ₀, HasJumps P K LL (ψ τ₀) (fun τ => if τ = τ₀ then 1 else 0))
    (c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) (s : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) :
    HasJumps P K LL (∏ τ ∈ s, ψ τ ^ c τ) (fun τ => if τ ∈ s then c τ else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    convert hasJumps_one AI hT using 1
    funext τ
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    convert hasJumps_mul AI hT (hasJumps_zpow AI hT (hψ a) (c a)) ih using 1
    funext τ
    by_cases h : τ = a
    · subst h
      simp [ha]
    · simp [h]

end GlobalTheory.CrysCharJumps

open GlobalTheory.CrysCharJumps Classical in

theorem GlobalTheory.CrysCharJumps.adm20_of_fonOf :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  intro D HW F l _ K LL hA
  refine ⟨fun a => ?_, ?_⟩
  · classical
    choose ψ hψ using fun τ₀ => GlobalTheory.T.exists_crystalline_char_jump_one_alt l (D.loc l) (D.locA l) (D.locT l) K LL hA τ₀
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    haveI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    let c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ := fun τ =>
      if h : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ then a h.choose else 0
    have hp := hasJumps_prod (D.locA l) (D.locT l) ψ (fun τ₀ => hψ τ₀) c Finset.univ
    refine ⟨∏ τ, ψ τ ^ c τ, hp.1, hp.2.1, fun i τ hi b => ?_⟩
    rw [hp.2.2]
    have hex : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ := ⟨i, hi⟩
    have hc : c τ = a i := by
      simp only [c, dif_pos hex]
      congr 1
      apply ((HW l).W K 1 LL hA.2.2).emb_bij.1
      have h1 := hex.choose_spec
      unfold Formalism.MainNotions.tableLineDegreeTwo.Over at h1 hi
      exact h1.symm.trans hi
    simp [hc]
  · intro V _ _ _ _ _ _ _ ρ ρ' μ hρc hρ hμc hμI hρ'
    obtain ⟨hμcr, hμm⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l (D.loc l) (D.locA l) (D.locT l) K LL μ hμc hμI
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ' g]⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) (D.locT l) K LL
      V ρ V ρ' μ htw hμcr hρ
    refine ⟨h1, fun τ x => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ 0 :=
      isJumpV_of_multV_ne _ τ 0 (by rw [hμm]; simp)
    simpa using h2 τ x 0 hj
