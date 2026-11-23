import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

noncomputable section

namespace GlobalTheory.PstRank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def sigSt (g : ↥(GK K)) : Bst P ⊗[ℚ_[l]] V →ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] V :=
  TensorProduct.map (actSt P (g : GQ l)).toLinearMap ((ρ g).restrictScalars ℚ_[l])

theorem sigSt_smul (g : ↥(GK K)) (b : Bst P) (w : Bst P ⊗[ℚ_[l]] V) :
    sigSt P ρ g (b • w) = actSt P (g : GQ l) b • sigSt P ρ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [sigSt, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem sigSt_comm (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P) :
    sigSt P ρ g (TensorProduct.comm ℚ_[l] V (Bst P) y) =
      TensorProduct.comm ℚ_[l] V (Bst P) (stRep P ρ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [sigSt]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : V ⊗[ℚ_[l]] Bst P) :
    TensorProduct.comm ℚ_[l] V (Bst P) (mulV P LL V c y) = c • TensorProduct.comm ℚ_[l] V (Bst P) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

def toB : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] Bst P ⊗[ℚ_[l]] V where
  toFun x := TensorProduct.comm ℚ_[l] V (Bst P) (((toUr P ρ).symm x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P)
  map_add' x y := by simp
  map_smul' c x := comm_mulV P c _

theorem toB_injective : Function.Injective (toB P ρ) := fun x y h =>
  (toUr P ρ).symm.injective (Subtype.ext ((TensorProduct.comm ℚ_[l] V (Bst P)).injective h))

end GlobalTheory.PstRank

namespace GlobalTheory.PstRank

theorem rank_DpstUr_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  intro l _ P hdom hreg K LL _ _ V _ _ _ _ _ ρ
  refine rank_le fun s hs => ?_
  choose F hF using fun i : ↥s => (mem_Dpst P ρ).mp ((toUr P ρ).symm (i : DpstUr P ρ)).2
  have hFd := fun i : ↥s => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let v : ↥s → Bst P ⊗[ℚ_[l]] V := fun i => toB P ρ (i : DpstUr P ρ)
  have hv : ∀ (g : ↥(GK K')) i, sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (v i) = v i := by
    intro g i
    change sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) v := hs.map' (toB P ρ) (LinearMap.ker_eq_bot.mpr (toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) v ((Finset.univ : Finset ↥s) : Set ↥s) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      v hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) v := by
    rw [← linearIndepOn_univ]; rw [Finset.coe_univ] at hB; exact hB
  simpa using LinearIndependent.fintype_card_le_finrank hB'

end GlobalTheory.PstRank
