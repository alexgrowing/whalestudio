import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJumpStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

noncomputable def negPowBlock {G LL : Type} [Group G] [Field LL] (χ : G →* LLˣ) (t : ℕ) :
    Representation LL G (Fin t → LL) where
  toFun g := LinearMap.pi fun c : Fin t =>
    (((χ g)⁻¹ ^ (c : ℕ) : LLˣ) : LL) • LinearMap.proj c
  map_one' := by ext; simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun c => ?_
    simp only [map_mul, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      Module.End.mul_apply, smul_eq_mul, mul_inv, mul_pow, Units.val_mul]
    ring

noncomputable def snocSplit (LL : Type) [Field LL] (t : ℕ) :
    (Fin (t + 1) → LL) ≃ₗ[LL] ((Fin t → LL) × LL) where
  toFun v := (fun c => v c.castSucc, v (Fin.last t))
  invFun p := Fin.snoc (α := fun _ => LL) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := Fin.snoc_init_self v
  right_inv p := by
    ext <;> simp

theorem negCycBlock_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (t : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin t → ↥LL.1)), (∀ g v (c : Fin t), ρ g v c = (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * v c) → IsCrys (P.PD K) ρ ∧ IsDR (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  intro l _ P AI hT K LL t
  induction t with
  | zero =>
    intro ρ _
    refine ⟨?_, ?_, fun τ a => ?_⟩
    · unfold IsCrys
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold IsDR
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold multV
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, if_neg (by omega)]
      simp
  | succ t ih =>
    intro ρ hρ
    obtain ⟨c1, d1, m1⟩ := ih (negPowBlock (cycLL (P.PD K) ↥LL.1) t) (fun _ _ _ => rfl)
    obtain ⟨c2, d2, m2⟩ := GlobalTheory.T.cyc_zpow_crys_dR_jump_alt l P AI hT K LL (-(t : ℤ))
    obtain ⟨hd, hc, hm⟩ := GlobalTheory.T.directSum_deRham_crystalline_jumps_add l P AI hT K LL _ ρ _
      (negPowBlock (cycLL (P.PD K) ↥LL.1) t) _ (charRep (cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))))
      (snocSplit ↥LL.1 t) (by
        intro g v
        refine Prod.ext (funext fun c => ?_) ?_
        · exact hρ g v c.castSucc
        · refine (hρ g v (Fin.last t)).trans ?_
          change _ = (((cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))) g : (↥LL.1)ˣ) : ↥LL.1) * v (Fin.last t)
          rw [MonoidHom.zpow_apply, Fin.val_last, zpow_neg, zpow_natCast, inv_pow])
    refine ⟨hc.2 ⟨c1, c2⟩, hd.2 ⟨d1, d2⟩, fun τ a => ?_⟩
    rw [hm, m1, m2]
    push_cast
    split_ifs <;> omega

end GlobalTheory
