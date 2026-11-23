import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PolMatchLin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Ext
variable {ι : Type} (P : ι → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)]

open Classical in

def extFam {S T : Finset ι} (w : ∀ v, P v) (g : ∀ v : S, P v) : ∀ v : T, P v :=
  fun v => if h : v.1 ∈ S then g ⟨v.1, h⟩ else w v.1

theorem extFam_update {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) [DecidableEq S] [DecidableEq T]
    (g : ∀ v : S, P v) (i : S) (z : P i) :
    extFam P (T := T) w (Function.update g i z) = Function.update (extFam P w g) ⟨i.1, hST i.2⟩ z := by
  funext v
  by_cases hv : v = ⟨i.1, hST i.2⟩
  · subst hv
    simp [extFam, i.2]
  · rw [Function.update_of_ne hv]
    unfold extFam
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e
      apply hv
      apply Subtype.ext
      simp [← e]
    · rfl

def extML {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    MultilinearMap ℂ (fun v : S => P v) (PiTensorProduct ℂ fun v : T => P v) where
  toFun g := PiTensorProduct.tprod ℂ (extFam P w g)
  map_update_add' g i x y := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' g i c x := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_smul _ _ _ _ _

def extL {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    (PiTensorProduct ℂ fun v : S => P v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => P v :=
  PiTensorProduct.lift (extML P hST w)

theorem extL_tprod {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) (g : ∀ v : S, P v) (g' : ∀ v : T, P v)
    (h1 : ∀ (v : T) (h : v.1 ∈ S), g' v = g ⟨v.1, h⟩) (h2 : ∀ v : T, v.1 ∉ S → g' v = w v.1) :
    extL P hST w (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ g' := by
  unfold extL
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (extFam P w g) = _
  congr 1
  funext v
  unfold extFam
  split_ifs with h
  · exact (h1 v h).symm
  · exact (h2 v h).symm

end Ext

section Main

theorem pure_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, smul_eq_mul, mul_assoc]

theorem transport {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a') (hF : IsFinMaps B G X om om' Rf)
    {T₁ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (hX : X.T ⊆ T₁) (hST : T₁ ⊆ T) {m m' : ℕ} (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (f' : Fin m' → SInf F (Fin a' × Fin (a + a')))
    (φ' : Fin m' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T₁, φ i v = G.M.vac v) (hφ' : ∀ j, ∀ v ∉ T₁, φ' j v = G.M'.vac v)
    (he : ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v))) :
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v)) := by
  set w : ∀ v, Rf.Pi v := fun v => Rf.p v (G.M.vac v)
  have k1 : ∀ i, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v) := fun i =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by simp only [w]; rw [hφ i v h])
  have k2 : ∀ j, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v) := fun j =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by
      simp only [w]; rw [hφ' j v h, (hF.sph v.1 (fun hv => h (hX hv))).1])
  have := congrArg (LinearMap.lTensor R.Pi (extL Rf.Pi hST w)) he
  simp only [map_sum, LinearMap.lTensor_tmul, k1, k2] at this
  exact this

theorem polMatch_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsFinMaps B G X om om' Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 0 ∧ ∀ (Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' Ψ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Ψ Ψ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hF
  refine ⟨?_, ?_⟩
  · refine ⟨X.T, subset_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rintro Φ Ψ Φ' Ψ' c ⟨T₁, hX₁, m₁, m₁', f₁, φ₁, f₁', φ₁', h1, h1', rfl, rfl, e1⟩
      ⟨T₂, hX₂, m₂, m₂', f₂, φ₂, f₂', φ₂', h2, h2', rfl, rfl, e2⟩
    classical
    have s1 : T₁ ⊆ T₁ ∪ T₂ := Finset.subset_union_left
    have s2 : T₂ ⊆ T₁ ∪ T₂ := Finset.subset_union_right
    refine ⟨T₁ ∪ T₂, hX₁.trans s1, m₁ + m₂, m₁' + m₂', Fin.append f₁ (fun j => c • f₂ j), Fin.append φ₁ φ₂,
      Fin.append f₁' (fun j => c • f₂' j), Fin.append φ₁' φ₂', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2 j).1, (h2 j).2.1, fun v hv => (h2 j).2.2 v (fun h => hv (s2 h))⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2' j).1, (h2' j).2.1, fun v hv => (h2' j).2.2 v (fun h => hv (s2 h))⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, map_smul, ← TensorProduct.smul_tmul', ← Finset.smul_sum]
      rw [transport B G X om om' R Rf hF hX₁ s1 f₁ φ₁ f₁' φ₁' (fun i v hv => (h1 i).2.2 v hv)
          (fun j v hv => (h1' j).2.2 v hv) e1,
        transport B G X om om' R Rf hF hX₂ s2 f₂ φ₂ f₂' φ₂' (fun i v hv => (h2 i).2.2 v hv)
          (fun j v hv => (h2' j).2.2 v hv) e2]

end Main

end GlobalTheory.PolMatchLin
