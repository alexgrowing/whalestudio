import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlotsGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulVecEqPow
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixFormStatement

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

private theorem lau_eq_vecL {F : Type} [Field F] {n : ℕ} (y : Fin n → F⟦X⟧) :
    GlobalTheory.WachBlock.lau y = GlobalTheory.WachPlace.vecL y := by
  funext a
  rfl

private theorem unConst : UnConst := by
  exact unit_series_constant_holds

private theorem lau_mem_iff_vecL_mem {F : Type} [Field F] {n : ℕ}
    {S : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)} {y : Fin n → F⟦X⟧} :
    GlobalTheory.WachBlock.lau y ∈ S ↔ GlobalTheory.WachPlace.vecL y ∈ S := by
  rw [lau_eq_vecL]

private theorem map_comp_rk1_eq_rk1_map {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (χ : Γ →* (↥(OL LL))ˣ) :
    (Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 χ) =
      GlobalTheory.TripleGal.rk1 ((Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp χ) := by
  ext g i j
  simp [GlobalTheory.TripleGal.rk1, toOm, GlobalTheory.WachBlock.ofOL]
  obtain rfl := Subsingleton.elim i j
  simp

open NumberField GlobalTheory.ExpFrame in

theorem GlobalTheory.WachPlace.wach_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl hd σ hσ n t h J bot hJ hbot hIB
  obtain ⟨LL, r, ψ, ϖ, R, M, rs, hz, hE, hcr, hψcr, hirr, hM0, hMtop, hmono, hstab, hrs, hlines⟩ := hIB
  obtain ⟨_, _, _⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : CharP (ResidueField ↥(OL LL)) l := GlobalTheory.WachMap.charP_residueField_of_irreducible LL
  obtain ⟨x, dim, hx, hd0, hdR, hds⟩ :=
    GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form _ ↥(OL LL) n t R r ψ ϖ M rs hirr hM0 hMtop hmono hstab hlines
  obtain ⟨u, c, ζ, jj, hu, hc, hζ, hζm, hjj⟩ := GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions l LL hl hz
  obtain ⟨un, hun⟩ := (unConst l ↥(OL LL) hl (u : ℤ_[l]) c hu).1
  have hψ' : ∀ s, GlobalTheory.ExpFrame.CrysWith
      ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)} := by
    intro s
    rw [map_comp_rk1_eq_rk1_map]
    exact hψcr s
  obtain ⟨N, Nψ, y, hN, hNψ, hy⟩ := GlobalTheory.WachPlace.exists_positions_global hBS hl hd hσ
    (J := J) (wt := fun s i => bot i + ((s : ℕ) : ℤ)) hJ (fun s i => hbot i s) hz hE
    (r := r) (ψ := fun s => GlobalTheory.TripleGal.rk1 (ψ s)) hcr hψ' hx hu hun hζ (fun a ha => (hjj a ha).2)
  obtain ⟨V, e, m, hV0, hVrk, hVphi, hVgam, hVe, hVphie, hVgame⟩ :=
    GlobalTheory.WachPlace.filtration_of_chain σ (Fact.out : l.Prime).pos
      (PowerSeries.map (residue ↥(OL LL)) un)
      (fun i => (N.P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun i => (N.D i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim y hd0 hdR hds hy
  refine ⟨↥(OL LL), ResidueField ↥(OL LL), ↥LL.1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, maximalIdeal ↥(OL LL), inferInstance,
    residue ↥(OL LL), un, N, Nψ, u, c, ζ, (OL LL).val.toRingHom, jj, ⟨hu, hc, hun⟩,
    ⟨hζ, hζm, Subtype.val_injective, fun b hb => (hjj b hb).1⟩, hN, hNψ, ?_⟩
  unfold GlobalTheory.WachBlock.RedFilt
  refine ⟨R, V, rs, e, m, hrs, hV0, hVrk, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVphi i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVgam i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i s
    simp only [lau_eq_vecL]
    exact hVe i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVphie i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVgame i s

end
