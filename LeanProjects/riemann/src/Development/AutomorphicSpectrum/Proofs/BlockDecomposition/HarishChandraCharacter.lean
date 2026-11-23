import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.FinGLChar

theorem mul_mul_eq_iff {G : Type} [Group G] (a x g : G) :
    a * (x * g) = x ↔ a⁻¹ = x * g * x⁻¹ := by
  constructor
  · intro h
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← mul_assoc, ← mul_assoc, mul_assoc a x g, h, mul_inv_cancel]
  · intro h
    have e : a = (x * g * x⁻¹)⁻¹ := by rw [← h, inv_inv]
    rw [e]
    group

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem trace_infl (p : parab K b) :
    LinearMap.trace ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) (infl K b lam p) =
      hcFun b (fun c => (lam c).character) p.1 := by
  unfold hcFun infl
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, dif_pos p.2]
  rfl

theorem character_hcRep :
    (hcRep K b lam).character = indF (parab K b) (hcFun b fun c => (lam c).character) := by
  classical
  funext g
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  let _ : Fintype (parab K b) := Fintype.ofFinite _
  have h1 : (hcRep K b lam).character g = LinearMap.trace ℂ _
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g) := rfl
  have h := GlobalTheory.BadShare.trace_coind_mul_card (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g
  rw [← h1] at h
  have hc : (Fintype.card (parab K b) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold indF
  rw [Nat.card_eq_fintype_card, eq_inv_mul_iff_mul_eq₀ hc, mul_comm, h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x * g * x⁻¹ ∈ parab K b
  · have key : ∀ γ : parab K b, (parab K b).subtype γ * (x * g) = x ↔ γ = (⟨_, hx⟩ : parab K b)⁻¹ := by
      intro γ
      rw [mul_mul_eq_iff]
      constructor
      · intro e
        refine Subtype.ext ?_
        show (γ : GL ι K) = (x * g * x⁻¹)⁻¹
        rw [← e]
        simp
      · rintro rfl
        exact inv_inv _
    simp only [key]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos hx, inv_inv]
    exact trace_infl b lam _
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun γ _ => if_neg fun e => hx ?_
    rw [← (mul_mul_eq_iff _ x g).1 e]
    exact (parab K b).inv_mem γ.2

def leviHom (c : Fin s) : parab K b →* GL {i // b i = c} K where
  toFun := levi K b c
  map_one' := PI.SerBridgeGLW.levi_one' K b c
  map_mul' := PI.SerBridgeGLW.levi_mul' K b c

theorem isClassOn_hcFun :
    IsClassOn (parab K b) (hcFun b fun c => (lam c).character) := by
  intro x hx h hh
  have hm : x * h * x⁻¹ ∈ parab K b := (parab K b).mul_mem ((parab K b).mul_mem hx hh) ((parab K b).inv_mem hx)
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, blkGL, dif_pos hm, dif_pos hh]
  have e : (⟨x * h * x⁻¹, hm⟩ : parab K b) = ⟨x, hx⟩ * ⟨h, hh⟩ * (⟨x, hx⟩ : parab K b)⁻¹ := rfl
  have e' : levi K b c ⟨x * h * x⁻¹, hm⟩ =
      leviHom b c ⟨x, hx⟩ * leviHom b c ⟨h, hh⟩ * (leviHom b c ⟨x, hx⟩)⁻¹ := by
    rw [e, ← map_inv, ← map_mul, ← map_mul]
    rfl
  beta_reduce
  rw [e', mul_assoc, FDRep.char_mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  rfl

theorem hcChar : St.HCChar := by
  intro K _ _ _ ι _ _ s b lam
  exact ⟨character_hcRep b lam, isClassOn_hcFun b lam⟩

end GlobalTheory.CompanionTheory.FinGLChar
