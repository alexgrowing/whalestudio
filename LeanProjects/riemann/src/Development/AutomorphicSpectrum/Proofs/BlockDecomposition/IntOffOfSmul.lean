import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgRich

variable {D : D7}

theorem hcs_mul_sep {X A B : Type} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (L : X ≃ₜ A × B) {g₁ : A → ℂ} {g₂ : B → ℂ} (h₁ : HasCompactSupport g₁) (h₂ : HasCompactSupport g₂) :
    HasCompactSupport (fun x => g₁ (L x).1 * g₂ (L x).2) := by
  have hK : IsCompact (L ⁻¹' (tsupport g₁ ×ˢ tsupport g₂)) :=
    L.isCompact_preimage.2 (h₁.isCompact.prod h₂.isCompact)
  have hC : IsClosed (L ⁻¹' (tsupport g₁ ×ˢ tsupport g₂)) :=
    ((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage L.continuous
  refine hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx => ?_) hC)
  have hx' : g₁ (L x).1 * g₂ (L x).2 ≠ 0 := hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩

def rowHomeo (Y : Type) [TopologicalSpace Y] (a : ℕ) : (Fin (a + 1) → Y) ≃ₜ (Fin a → Y) × (Fin 1 → Y) where
  toFun x := (fun i => x i.castSucc, fun _ => x (Fin.last a))
  invFun p := fun i => Fin.lastCases (motive := fun _ => Y) (p.2 0) (fun i => p.1 i) i
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i; simp
    · funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun i => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [Function.comp_def] using (continuous_apply (0 : Fin 1)).comp (continuous_snd (X := Fin a → Y) (Y := Fin 1 → Y))
    · simpa [Function.comp_def] using (continuous_apply i).comp (continuous_fst (X := Fin a → Y) (Y := Fin 1 → Y))

theorem hcs_rows {R : Type} [TopologicalSpace R] {a n : ℕ} {g₁ : Matrix (Fin a) (Fin n) R → ℂ}
    {g₂ : Matrix (Fin 1) (Fin n) R → ℂ} (h₁ : HasCompactSupport g₁) (h₂ : HasCompactSupport g₂) :
    HasCompactSupport (fun x : Matrix (Fin (a + 1)) (Fin n) R =>
      g₁ (x.submatrix Fin.castSucc id) * g₂ (x.submatrix (fun _ => Fin.last a) id)) :=
  hcs_mul_sep (rowHomeo (Fin n → R) a) h₁ h₂

def rowCLE (T : Type) [Fintype T] (a n : ℕ) :
    (T → Fin (a + 1) → Fin n → ℂ) ≃L[ℝ] (T → Fin a → Fin n → ℂ) × (T → Fin 1 → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w => (fun τ i j => w τ i.castSucc j, fun τ _ j => w τ (Fin.last a) j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p τ i j => Fin.lastCases (motive := fun _ => ℂ) (p.2 τ 0 j) (fun i => p.1 τ i j) i
      left_inv := fun w => by
        funext τ i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext τ i j; simp
        · funext τ i j
          have : i = 0 := Subsingleton.elim _ _
          subst this
          simp }

variable {a n : ℕ}

theorem fin_mul_mem (θ : InfFam D) {h : (Fin a → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hh : IsLocallyConstant h) {φ : Mx D a n → ℂ} (hφ : φ ∈ schwartzA θ a n) :
    (fun x => h (fun i j => finPart D (x i j)) * φ x) ∈ schwartzA θ a n := by
  induction hφ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm
    refine Submodule.subset_span ⟨f, fun y => h y * g y, ⟨hh.mul hg.1, hg.2.mul_left⟩, ?_⟩
    funext x
    ring
  | zero =>
    convert (schwartzA θ a n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    convert (schwartzA θ a n).add_mem h₁ h₂ using 1
    funext x
    simp [mul_add]
  | smul c Φ _ h₁ =>
    convert (schwartzA θ a n).smul_mem c h₁ using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem mul_mem (θ : InfFam D) {Φ Φ' : Mx D a n → ℂ} (hΦ : Φ ∈ schwartzA θ a n) (hΦ' : Φ' ∈ schwartzA θ a n) :
    (fun x => Φ x * Φ' x) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm
    have := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ a n f f.hasTemperateGrowth _ (fin_mul_mem θ hg.1 hΦ')
    convert this using 1
    funext x
    ring
  | zero =>
    convert (schwartzA θ a n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    convert (schwartzA θ a n).add_mem h₁ h₂ using 1
    funext x
    simp [add_mul]
  | smul c Φ _ h₁ =>
    convert (schwartzA θ a n).smul_mem c h₁ using 1
    funext x
    simp [mul_assoc]

theorem conj_mem (θ : InfFam D) {Φ : Mx D a n → ℂ} (hΦ : Φ ∈ schwartzA θ a n) :
    (fun x => conj (Φ x)) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm
    refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, fun y => conj (g y),
      ⟨hg.1.comp _, hg.2.comp_left (map_zero _)⟩, ?_⟩
    funext x
    simp
  | zero =>
    convert (schwartzA θ a n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    convert (schwartzA θ a n).add_mem h₁ h₂ using 1
    funext x
    simp
  | smul c Φ _ h₁ =>
    convert (schwartzA θ a n).smul_mem (conj c) h₁ using 1
    funext x
    simp

theorem row_mem (θ : InfFam D) {Φ : Mx D a n → ℂ} {φ : Mx D 1 n → ℂ} (hΦ : Φ ∈ schwartzA θ a n)
    (hφ : φ ∈ schwartzA θ 1 n) :
    (fun x : Mx D (a + 1) n => Φ (x.submatrix Fin.castSucc id) * φ (x.submatrix (fun _ => Fin.last a) id)) ∈
      schwartzA θ (a + 1) n := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    induction hφ using Submodule.span_induction with
    | mem φ hm' =>
      obtain ⟨f₁, g₁, hg₁, rfl⟩ := hm
      obtain ⟨f₂, g₂, hg₂, rfl⟩ := hm'
      obtain ⟨F, hF⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod f₁ f₂
      have hL := hcs_mul_sep (rowHomeo (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) a) hg₁.2 hg₂.2
      refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (rowCLE D.what₂.Tau a n) F,
        fun y => g₁ (rowHomeo _ a y).1 * g₂ (rowHomeo _ a y).2, ⟨?_, hL⟩, ?_⟩
      · exact (hg₁.1.comp_continuous (continuous_fst.comp (rowHomeo _ a).continuous)).mul
          (hg₂.1.comp_continuous (continuous_snd.comp (rowHomeo _ a).continuous))
      · funext x
        simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hF]
        have e1 : (rowCLE D.what₂.Tau a n (fun τ i j => compAt θ τ x i j)).1 =
            fun τ i j => compAt θ τ (x.submatrix Fin.castSucc id) i j := rfl
        have e2 : (rowCLE D.what₂.Tau a n (fun τ i j => compAt θ τ x i j)).2 =
            fun τ i j => compAt θ τ (x.submatrix (fun _ => Fin.last a) id) i j := rfl
        rw [e1, e2]
        have e3 : (rowHomeo (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) a fun i j => finPart D (x i j)).1 =
            fun i j => finPart D (x.submatrix Fin.castSucc id i j) := rfl
        have e4 : (rowHomeo (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) a fun i j => finPart D (x i j)).2 =
            fun i j => finPart D (x.submatrix (fun _ => Fin.last a) id i j) := rfl
        rw [e3, e4]
        ring
    | zero =>
      convert (schwartzA θ (a + 1) n).zero_mem using 1
      funext x
      simp
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      convert (schwartzA θ (a + 1) n).add_mem h₁ h₂ using 1
      funext x
      simp [mul_add]
    | smul c Φ _ h₁ =>
      convert (schwartzA θ (a + 1) n).smul_mem c h₁ using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  | zero =>
    convert (schwartzA θ (a + 1) n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    convert (schwartzA θ (a + 1) n).add_mem h₁ h₂ using 1
    funext x
    simp [add_mul]
  | smul c Φ _ h₁ =>
    convert (schwartzA θ (a + 1) n).smul_mem c h₁ using 1
    funext x
    simp [mul_assoc]

section GoodSec

variable {S : Finset (Pl D)} {e : AE D}

theorem good_zero : Good S e (fun _ : Mx D a n => (0 : ℂ)) := fun x => by simp

theorem good_add {Φ Ψ : Mx D a n → ℂ} (h₁ : Good S e Φ) (h₂ : Good S e Ψ) : Good S e (fun x => Φ x + Ψ x) := fun x => by
  by_cases h : IntOff S x
  · simp only [if_pos h]
    rw [h₁ x, h₂ x, if_pos h, if_pos h]
  · simp only [if_neg h]
    rw [h₁ x, h₂ x, if_neg h, if_neg h, add_zero]

theorem good_smul {Φ : Mx D a n → ℂ} (c : ℂ) (h₁ : Good S e Φ) : Good S e (fun x => c * Φ x) := fun x => by
  by_cases h : IntOff S x
  · simp only [if_pos h]
    rw [h₁ x, if_pos h]
  · simp only [if_neg h]
    rw [h₁ x, if_neg h, mul_zero]

theorem good_factor {M B : Mx D a n → ℂ} (hM : ∀ x, M (e • x) = M x) (h₁ : Good S e B) :
    Good S e (fun x => M x * B x) := fun x => by
  by_cases h : IntOff S x
  · simp only [if_pos h]
    rw [h₁ x, if_pos h, hM]
  · simp only [if_neg h]
    rw [h₁ x, if_neg h, mul_zero]

theorem good_mul {Φ Ψ : Mx D a n → ℂ} (h₁ : Good S e Φ) (h₂ : Good S e Ψ) : Good S e (fun x => Φ x * Ψ x) := fun x => by
  by_cases h : IntOff S x
  · simp only [if_pos h]
    rw [h₁ x, h₂ x, if_pos h, if_pos h]
  · simp only [if_neg h]
    rw [h₁ x, if_neg h, zero_mul]

theorem good_conj {Φ : Mx D a n → ℂ} (h₁ : Good S e Φ) : Good S e (fun x => conj (Φ x)) := fun x => by
  by_cases h : IntOff S x
  · simp only [if_pos h]
    rw [h₁ x, if_pos h]
  · simp only [if_neg h]
    rw [h₁ x, if_neg h, map_zero]

theorem intOff_of_smul (hid : IsIdem S e) {x : Mx D a n} (hx : e • x = x) : IntOff S x := by
  intro v hv i j
  have h0 : cv D v e = 0 := by rw [hid.2 v, if_neg hv]
  have : x i j = e * x i j := by
    conv_lhs => rw [← hx]
    rfl
  rw [this, map_mul, h0, zero_mul]
  exact zero_mem _

theorem good_row {Φ : Mx D a n → ℂ} {φ : Mx D 1 n → ℂ} (h₁ : Good S e Φ) (h₂ : Good S e φ) :
    Good S e (fun x : Mx D (a + 1) n =>
      Φ (x.submatrix Fin.castSucc id) * φ (x.submatrix (fun _ => Fin.last a) id)) := fun x => by
  by_cases h : IntOff S x
  · have a1 : IntOff S (x.submatrix Fin.castSucc id) := fun v hv i j => h v hv _ _
    have a2 : IntOff S (x.submatrix (fun _ : Fin 1 => Fin.last a) id) := fun v hv i j => h v hv _ _
    have b1 := h₁ (x.submatrix Fin.castSucc id)
    have b2 := h₂ (x.submatrix (fun _ : Fin 1 => Fin.last a) id)
    rw [if_pos a1] at b1
    rw [if_pos a2] at b2
    rw [if_pos h]
    exact congrArg₂ (· * ·) b1 b2
  · rw [if_neg h]
    simp only [IntOff, not_forall] at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    refine Fin.lastCases (motive := fun i => cv D v (x i j) ∉ intLoc D.host.F D.host.E v → _) (fun hij => ?_) (fun i hij => ?_) i hij
    · have a2 : ¬ IntOff S (x.submatrix (fun _ : Fin 1 => Fin.last a) id) := fun h' => hij (h' v hv 0 j)
      have b2 := h₂ (x.submatrix (fun _ : Fin 1 => Fin.last a) id)
      rw [if_neg a2] at b2
      show _ * φ _ = 0
      rw [b2, mul_zero]
    · have a1 : ¬ IntOff S (x.submatrix Fin.castSucc id) := fun h' => hij (h' v hv i j)
      have b1 := h₁ (x.submatrix Fin.castSucc id)
      rw [if_neg a1] at b1
      show Φ _ * _ = 0
      rw [b1, zero_mul]

theorem row_prod {θ : InfFam D} : ∀ (a : ℕ) (η : Fin a → Mx D 1 n → ℂ),
    (∀ i, η i ∈ schwartzA θ 1 n ∧ HasCompactSupport (η i) ∧ Good S e (η i)) →
    (fun x : Mx D a n => ∏ i, η i (x.submatrix (fun _ => i) id)) ∈ schwartzA θ a n ∧
      Good S e (fun x : Mx D a n => ∏ i, η i (x.submatrix (fun _ => i) id)) ∧
      HasCompactSupport (fun x : Mx D a n => ∏ i, η i (x.submatrix (fun _ => i) id)) := by
  intro a
  induction a with
  | zero =>
    intro η _
    have e1 : (fun x : Mx D 0 n => ∏ i, η i (x.submatrix (fun _ => i) id)) = fun _ => 1 := by
      funext x
      simp
    rw [e1]
    refine ⟨GlobalTheory.CompanionTheory.ThTot.one_mem_schwartzA_zero θ, fun x => ?_, ?_⟩
    · have : IntOff S x := fun v _ i => i.elim0
      rw [if_pos this]
    · haveI : Subsingleton (Mx D 0 n) := GlobalTheory.CompanionTheory.ThTot.mx_zero_subsingleton
      exact (Set.subsingleton_of_subsingleton).isCompact
  | succ a ih =>
    intro η hη
    obtain ⟨h1, h2, h3⟩ := ih (fun i => η i.castSucc) fun i => hη _
    obtain ⟨l1, l3, l2⟩ := hη (Fin.last a)
    have e1 : (fun x : Mx D (a + 1) n => ∏ i, η i (x.submatrix (fun _ => i) id)) = fun x =>
        (∏ i : Fin a, η i.castSucc ((x.submatrix Fin.castSucc id).submatrix (fun _ => i) id)) *
          η (Fin.last a) (x.submatrix (fun _ => Fin.last a) id) := by
      funext x
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [e1]
    refine ⟨row_mem θ h1 l1, fun x => ?_, ?_⟩
    · exact good_row h2 l2 x
    · have key := hcs_rows (R := AE D) h3 l3
      exact key

end GoodSec

end GlobalTheory.CompanionTheory.AlgRich

end
