import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalvesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemHomLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMapsBesselLineLatticeIffSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.LineVanish

variable {D : D7}

theorem mxAt_mul_right' {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem fin_of_mxAt' {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem isHalf_mul_right {e : AE D} {m n r : ℕ} {u : Mx D m n} (hu : IsHalf e u) (N : Mx D n r) :
    IsHalf e (u * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hu i k]

theorem isHalf_mul_left {e : AE D} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (N * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hu k j]

theorem contr_smul_left' {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem step3 : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V T : HSp D) (LV : Lat V) (LT : Lat T), IsSelfDualC V LV → IsSelfDualC T LT → ∀ y : WO V T, MxAt P y → y ∉ latO V T (LV : Set _) (LT : Set _) P → ∃ u ∈ latO V T (LV : Set _) (LT : Set _) P, (∃ e, IsSplitIdem D e ∧ IsHalf e u) ∧ ψ (symplO V T u y) ≠ 1 := by
  intro D k _ _ _ _ ι p I P hP ψ hψ V T LV LT hLV hLT y hy hout
  by_contra hno
  push_neg at hno
  apply hout
  have hadd : ∀ a b : WO V T, symplO V T (a + b) y = symplO V T a y + symplO V T b y := by
    intro a b
    have h := GlobalTheory.SplitScalar.symplO_sub_left V T (a + b) b y
    rw [add_sub_cancel_right] at h
    rw [h]; ring
  have hneg : ∀ a : AF D.host.F, ψ a = 1 → ψ (-a) = 1 := by
    intro a ha
    calc ψ (-a) = ψ (-a) * ψ a := by rw [ha, mul_one]
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let K : AddSubgroup (WO V T) :=
    { carrier := {u | ψ (symplO V T u y) = 1}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, GlobalTheory.SplitScalar.symplO_zero_left, AddChar.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hadd, AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h0 : symplO V T (-a) y = -symplO V T a y := by
          have := hadd (-a) a
          rw [neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_left] at this
          exact eq_neg_of_add_eq_zero_left this.symm
        rw [h0]; exact hneg _ ha }
  rw [GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V T LV LT hLV hLT P y hy]
  intro u' hu'
  have hK : u' ∈ K := (AddSubgroup.closure_le K).2 (fun u hu => hno u hu.1 hu.2)
    (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP V T _ _ u' hu')
  rw [GlobalTheory.SplitScalar.symplO_skew]
  exact hneg _ hK

set_option maxHeartbeats 2000000 in

theorem vanish : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr y hy hout f₁ f₂ h₁ h₂
  classical

  have hyM : MxAt P ((B.o.resS S).symm (0, y)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right' hy _
  obtain ⟨u, hu, ⟨e, he, heu⟩, hψu⟩ := step3 D k ι p I P hP ψ hψ B.V₀ S M LS hM hLS _ hyM hout
  set h := (B.o.resS S u).2 with hh
  have hhN : (B.o.resS S).symm (0, h) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    GlobalTheory.T.lineProjection_mem_homLatticeCompletion D k ι p I P hP n' ρ B S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) u hu
  have hhalf : IsHalf e h := isHalf_mul_right heu _
  have hhmx : MxAt P h := by
    have := ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P _).1 hhN).1
    have h2 : (B.o.resS S ((B.o.resS S).symm (0, h))).2 = h := by rw [AddEquiv.apply_symm_apply]
    rw [← h2]; exact mxAt_mul_right' this _
  have hpair : symplO B.V₀ S ((B.o.resS S).symm (0, h)) ((B.o.resS S).symm (0, y)) =
      symplO B.V₀ S u ((B.o.resS S).symm (0, y)) := by
    rw [B.o.symplO_resS, B.o.symplO_resS S u, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.SplitScalar.symplO_zero_right, GlobalTheory.SplitScalar.symplO_zero_right]

  obtain ⟨x', hkx, hxmx, hxhalf⟩ := GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf D ρ B B'.L B'.ζ l S P h
  have hx'N : (B'.o.resT S).symm (0, x') ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P := by
    rw [GlobalTheory.T.kappa_maps_besselLineLattice_iff_split D k ι p I P hP n' n'' ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x' (hxmx hhmx), hkx]
    exact hhN
  have hx'half : IsHalf (cA D e) ((B'.o.resT S).symm (0, x')) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (hxhalf e hhalf)
  have hf₂ : heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x')) f₂ = f₂ :=
    h₂.2.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) _ hx'N hx'half
  have hf₁ : heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x')) f₁ = f₁ := by
    rw [hkx]
    exact h₁.2.2 e he _ hhN (by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]; exact isHalf_mul_right hhalf _)
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt' hyM) h₁.1
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth h₂.1 x'
  rw [hf₂, GlobalTheory.SplitScalar.heisO_comm, hf₁, contr_smul_left', hkx, hpair] at hmove
  set C := GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂
  have : (ψ (symplO B.V₀ S u ((B.o.resS S).symm (0, y))) - 1) • C = 0 := by
    rw [sub_smul, hmove, one_smul, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψu)

end GlobalTheory.FinPl.LineVanish
