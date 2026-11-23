import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GESymmApply

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Section

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def lpS (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  Λ ⊓ (perpS (VS D) F0.X).restrictScalars (𝓞 D.host.E)

variable {D F0}

theorem sE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (ρ : lpS D F0 Λ →ₗ[𝓞 D.host.E] lpS D F0 Λ)
    (hρid : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ F0.X → ρ y = y)
    {s : Type} [Fintype s] (c : Basis s D.host.E (WbQ D F0)) (a : s → perpS (VS D) F0.X)
    (hac : ∀ i, (Submodule.Quotient.mk (a i) : WbQ D F0) = c i)
    (y : s → lpS D F0 Λ) (hya : ∀ i, (y i : (VS D).V) = a i)
    (sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X)
    (hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V))
    (b : perpS (VS D) F0.X) (yb : lpS D F0 Λ) (hyb : (yb : (VS D).V) = b)
    (d : 𝓞 D.host.E) (hd0 : d ≠ 0) (o : s → 𝓞 D.host.E)
    (ho : ∑ i, o i • c i = d • (Submodule.Quotient.mk b : WbQ D F0)) :
    (sE (Submodule.Quotient.mk b) : (VS D).V) = (b : (VS D).V) - (ρ yb : (VS D).V) := by
  have hsm : ∀ (r : 𝓞 D.host.E) (v : (VS D).V),
      r • v = (algebraMap (𝓞 D.host.E) D.host.E r) • v := fun r v => (algebraMap_smul D.host.E r v).symm
  have hq : (Submodule.Quotient.mk (∑ i, o i • a i - d • b) : WbQ D F0) = 0 := by
    rw [← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, Submodule.mkQ_apply, hac, ho, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hq
  rw [Submodule.mem_comap] at hmem
  have hzX : ((∑ i, o i • y i - d • yb : lpS D F0 Λ) : (VS D).V) ∈ F0.X := by
    convert hmem using 1
    simp [hya, hyb]
  have hρz := hρid _ hzX
  have e := congrArg (fun u : lpS D F0 Λ => (u : (VS D).V)) hρz
  simp only [map_sub, map_sum, map_smul, Submodule.coe_sub, Submodule.coe_sum,
    Submodule.coe_smul] at e
  have h1 : ∑ i, o i • (y i : (VS D).V) - ∑ i, o i • (ρ (y i) : (VS D).V) =
      d • (yb : (VS D).V) - d • (ρ yb : (VS D).V) := by
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact e.symm
  have h2 := congrArg (fun q => ((sE q : perpS (VS D) F0.X) : (VS D).V)) ho
  simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    hsEc] at h2
  have hd : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 := by
    intro h0
    apply hd0
    exact (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)
  apply smul_right_injective (VS D).V hd
  simp only
  rw [← hsm, ← hsm, ← h2]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [h1, hyb]

theorem exists_sE (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ) :
    ∃ sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X,
      (∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a) ∧
      ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ := by
  classical
  have hlpfg : (lpS D F0 Λ).FG := Submodule.FG.of_le hL.fg inf_le_left
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract (lpS D F0 Λ) hlpfg F0.X
  have hlpP : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ perpS (VS D) F0.X := fun y => (Submodule.mem_inf.1 y.2).2
  have hlpΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) ∈ Λ := fun y => (Submodule.mem_inf.1 y.2).1
  have hPmem : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ perpS (VS D) F0.X :=
    fun y => Submodule.sub_mem _ (hlpP y) (hlpP (ρ y))
  have hPΛ : ∀ y : lpS D F0 Λ, (y : (VS D).V) - (ρ y : (VS D).V) ∈ Λ :=
    fun y => Submodule.sub_mem _ (hlpΛ y) (hlpΛ (ρ y))
  have hMlat := Mof_isLattice D F0 Λ hL
  obtain ⟨s, _, c, hcv, hsM⟩ :=
    Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 D.host.E) (Mof D F0 Λ) hMlat.span_eq_top
  have hci : ∀ i, c i ∈ Mof D F0 Λ := fun i => by rw [hcv]; exact hsM i.2
  choose a haΛ hac using fun i => (mem_Mof D F0 Λ (c i)).1 (hci i)
  let y : s → lpS D F0 Λ := fun i => ⟨(a i : (VS D).V), Submodule.mem_inf.2 ⟨haΛ i, (a i).2⟩⟩
  let sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X :=
    c.constr D.host.E (fun i => ⟨(y i : (VS D).V) - (ρ (y i) : (VS D).V), hPmem (y i)⟩)
  have hsEc : ∀ i, (sE (c i) : (VS D).V) = (y i : (VS D).V) - (ρ (y i) : (VS D).V) := by
    intro i
    simp only [sE, Basis.constr_basis]
  have hsE : ∀ b, (Submodule.Quotient.mk (sE b) : WbQ D F0) = b := by
    have hlin : (F0.X.comap (perpS (VS D) F0.X).subtype).mkQ ∘ₗ sE = LinearMap.id := by
      refine c.ext fun i => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.id_coe, id_eq]
      conv_rhs => rw [← hac i]
      rw [mk_eq_mk, hsEc]
      have : (y i : (VS D).V) = (a i : (VS D).V) := rfl
      rw [this, sub_sub_cancel_left]
      exact F0.X.neg_mem (hρX (y i))
    intro b
    exact LinearMap.congr_fun hlin b
  refine ⟨sE, hsE, ?_⟩
  intro m hm
  obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
  let yb : lpS D F0 Λ := ⟨(b : (VS D).V), Submodule.mem_inf.2 ⟨hbΛ, b.2⟩⟩
  obtain ⟨d, hd0, hdM⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom c (Mof D F0 Λ) hMlat.fg
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).1 (hdM _ hm)
  rw [sE_eq Λ ρ hρid c a hac y (fun i => rfl) sE hsEc b yb rfl d hd0 o ho]
  exact hPΛ yb

end Section

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf
