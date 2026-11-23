import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeVacuumFnApplyAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLatticeVacuumEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeVacuumFnHasCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At Acts)

theorem exists_local_vac {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (ho : IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (hk : IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (h0 : χ 0 = 1)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) :
    ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧ ∀ u ∈ Λ, GlobalTheory.WeilM.schr ψ₀ u φ = χ u • φ := by
  have hsq : ∀ u ∈ Λ, χ u * χ u = 1 := fun u hu => by
    have e := hco u hu u hu
    rw [h2 u hu, sub_self, mul_zero, AddChar.map_zero_eq_one, mul_one] at e
    exact e.symm
  have hiso : ∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1 := by
    intro u hu w hw
    have e1 := hco u hu w hw
    have e2 := hco w hw u hu
    rw [add_comm w u, e1, mul_comm (χ w) (χ u)] at e2
    have hne0 : χ u * χ w ≠ 0 :=
      mul_ne_zero (left_ne_zero_of_mul_eq_one (hsq u hu)) (left_ne_zero_of_mul_eq_one (hsq w hw))
    set a := ⅟(2 : Fv F v) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) with ha_def
    have ha : ⅟(2 : Fv F v) * (w.1 ⬝ᵥ u.2 - u.1 ⬝ᵥ w.2) = -a := by rw [ha_def]; ring
    rw [ha] at e2
    have e3 : ψ₀ a = ψ₀ (-a) := mul_left_cancel₀ hne0 e2
    have e4 : u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 = a + a := by
      rw [ha_def, ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [e4, AddChar.map_add_eq_mul]
    calc ψ₀ a * ψ₀ a = ψ₀ (-a) * ψ₀ a := congrArg (· * ψ₀ a) e3
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let L : AddSubgroup (κ → Fv F v) := Λ.comap (AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v))
  let L' : AddSubgroup (κ → Fv F v) := Λ.comap ((AddMonoidHom.inr (κ → Fv F v) (κ → Fv F v)).comp
    (DistribMulAction.toAddMonoidHom (κ → Fv F v) (⅟(2 : Fv F v))))
  have hL : IsCompact (L : Set (κ → Fv F v)) := by
    have e : (L : Set (κ → Fv F v)) = Prod.snd '' ((Λ : Set ((κ → Fv F v) × (κ → Fv F v))) ∩ {u | u.1 = 0}) := by
      ext y
      constructor
      · intro hy
        exact ⟨(0, y), ⟨hy, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
        have : u = (0, u.2) := Prod.ext hu1 rfl
        show (0, u.2) ∈ Λ
        rw [← this]; exact hu
    rw [e]
    exact (hk.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  have hL' : IsOpen (L' : Set (κ → Fv F v)) := by
    rw [AddSubgroup.coe_comap]
    exact ho.preimage (continuous_const.prodMk (continuous_const.smul continuous_id))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_dotProduct_representation_compact_character_local v ψ₀ hc hne L hL L' hL' (fun y => χ (0, y))
    (fun y hy y' hy' => by
      have e := hco _ hy _ hy'
      simp only [AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_dotProduct, sub_self, mul_zero,
        AddChar.map_zero_eq_one, mul_one] at e
      exact e)
    (fun y hy hy' => by
      have e := h2 _ hy'
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inr_apply,
        DistribMulAction.toAddMonoidHom_apply, Prod.mk_add_mk, add_zero] at e
      rwa [← add_smul, invOf_two_add_invOf_two, one_smul] at e)
  have hx : ∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y) := fun y hy => hx₀ y hy
  refine ⟨vacFn ψ₀ Λ χ x₀, ⟨GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function v ψ₀ hc Λ ho χ x₀ hco hx h2, GlobalTheory.T.heisenbergLatticeVacuumFn_hasCompactSupport v ψ₀ Λ χ x₀ hk⟩, ?_,
    GlobalTheory.T.schroedingerOperator_heisenbergLatticeVacuum_eigen ψ₀ Λ χ x₀ hco hx hiso⟩
  intro h
  have e := GlobalTheory.T.heisenbergLatticeVacuumFn_apply_add ψ₀ Λ χ x₀ hco hx 0 (zero_mem _)
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, neg_zero, mul_zero, sub_zero,
    AddChar.map_zero_eq_one, h0, mul_one, h, Pi.zero_apply] at e
  exact zero_ne_one e

end GlobalTheory.HeisLatVac

namespace GlobalTheory.HeisLatVac

theorem exists_vac_of_lattice : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), Continuous ψ → GlobalTheory.LatVac.psiAt ψ v ≠ 1 →
    ∀ Γ : AddSubgroup W, (∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ Γ, GlobalTheory.LatVac.liftV v a • γ ∈ Γ) →
    IsOpen ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    IsCompact ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ c : W → ℂ, c 0 = 1 → (∀ γ ∈ Γ, ∀ γ' ∈ Γ, c (γ + γ') = c γ * c γ' * ψ (⅟(2 : AF F) * B γ γ')) →
    (∀ γ ∈ Γ, c (GlobalTheory.LatVac.liftV v 2 • γ) = 1) →
    ∃ φ : (κ → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧
      ∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ (c γ • φ) := by
  intro F _ _ W _ _ B κ _ co ψ v hψc hψ1 Γ hAt _hO hopen hcomp c hc0 hcoc hc2
  have hsupp : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      a = GlobalTheory.LatVac.liftV v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 := ha (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
    conv_lhs => rw [h1]
    exact GlobalTheory.EmbChart.atPlace_mul_right v 1 a |>.trans (by rw [one_mul]; rfl)
  have hψloc : ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a →
      ψ a = GlobalTheory.LatVac.psiAt ψ v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    conv_lhs => rw [hsupp a ha]
    rfl
  have hAtE : ∀ γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ → ∀ k,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).1 k) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e γ).2 k) := by
    intro γ hγ k
    have e : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • co.e γ = 0 := fun u hu => by
      rw [← LinearEquiv.map_smul, hγ u hu, map_zero]
    exact ⟨fun u hu => by simpa using congrArg (fun p => p.1 k) (e u hu),
      fun u hu => by simpa using congrArg (fun p => p.2 k) (e u hu)⟩
  have hinj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ = GlobalTheory.LatVac.locCo co v γ' → γ = γ' := by
    intro γ hγ γ' hγ' h
    have hδ := hAt _ (sub_mem hγ hγ')
    have h0 : GlobalTheory.LatVac.locCo co v (γ - γ') = 0 := by rw [map_sub, h, sub_self]
    have he : co.e (γ - γ') = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · rw [hsupp _ (hAtE _ hδ k).1]
        have := congrFun (congrArg Prod.fst h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).1 k) = 0 at this
        rw [this, map_zero]; rfl
      · rw [hsupp _ (hAtE _ hδ k).2]
        have := congrFun (congrArg Prod.snd h0) k
        change GlobalTheory.AdelicU.evFin F v ((co.e (γ - γ')).2 k) = 0 at this
        rw [this, map_zero]; rfl
    rw [LinearEquiv.map_eq_zero_iff, sub_eq_zero] at he
    exact he
  classical
  let χ : (κ → Fv F v) × (κ → Fv F v) → ℂ := fun u =>
    if h : ∃ γ ∈ Γ, GlobalTheory.LatVac.locCo co v γ = u then c h.choose else 0
  have hχ : ∀ γ ∈ Γ, χ (GlobalTheory.LatVac.locCo co v γ) = c γ := by
    intro γ hγ
    have h : ∃ γ' ∈ Γ, GlobalTheory.LatVac.locCo co v γ' = GlobalTheory.LatVac.locCo co v γ := ⟨γ, hγ, rfl⟩
    simp only [χ, dif_pos h]
    rw [hinj _ h.choose_spec.1 _ hγ h.choose_spec.2]
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψc v
  obtain ⟨φ, hSB, hne, heig⟩ := exists_local_vac v (GlobalTheory.LatVac.psiAt ψ v) hcont hψ1
    (Γ.map (GlobalTheory.LatVac.locCo co v)) hopen hcomp χ
    (by rw [← map_zero (GlobalTheory.LatVac.locCo co v), hχ 0 (zero_mem _), hc0])
    (by
      rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
      rw [← map_add, hχ _ (add_mem hγ hγ'), hχ _ hγ, hχ _ hγ', hcoc γ hγ γ' hγ']
      congr 1
      have hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (⅟(2 : AF F) * B γ γ') := by
        rw [co.form]
        refine GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sub ?_ ?_)
        · exact GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_left _ (hAtE _ (hAt _ hγ') i).2
        · exact GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_left _ (hAtE _ (hAt _ hγ) i).2
      rw [hψloc _ hA, co.form, map_mul, GlobalTheory.VacAny.evFin_invOf_two, map_sub]
      simp only [dotProduct, map_sum, map_mul]
      rfl)
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      rw [← map_add, hχ _ (add_mem hγ hγ)]
      have e : γ + γ = GlobalTheory.LatVac.liftV v 2 • γ := by
        have h := hAt γ hγ (GlobalTheory.LatVac.liftV v 2 - 2)
          (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_ofNat, sub_self])
        rw [sub_smul, sub_eq_zero, two_smul] at h
        exact h.symm
      rw [e]
      exact hc2 γ hγ)
  refine ⟨φ, hSB, hne, fun γ hγ => ?_⟩
  have hb := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger co ψ v γ (hAt γ hγ) φ
  rwa [heig _ (AddSubgroup.mem_map_of_mem _ hγ), hχ γ hγ] at hb

end GlobalTheory.HeisLatVac
