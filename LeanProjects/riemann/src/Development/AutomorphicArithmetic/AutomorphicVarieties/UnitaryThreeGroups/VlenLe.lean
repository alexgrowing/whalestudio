import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelLower
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem first_cohomology_torsion {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : Γ →* Oˣ) (x : H1U (twist₂ l α) (⊤ : Subgroup Γ)) : ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
  classical
  choose k hk0 hk using (UpperTheory.V.ML.qoCyc l O).1
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc : IsLocallyConstant fun g : Γ => z.1 ⟨g, trivial⟩ :=
    (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_id.subtype_mk _))
  have hfin := hc.range_finite
  refine ⟨∏ w ∈ hfin.toFinset, k w, Finset.prod_ne_zero_iff.2 fun w _ => hk0 w, ?_⟩
  have hz : (∏ w ∈ hfin.toFinset, k w) • z = 0 := Subtype.ext (funext fun g =>
    (hk _ _).2 (Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 ⟨g.1, rfl⟩)))
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]

private theorem len_of_torsion (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : ∀ x : M, ∃ a : O, a ≠ 0 ∧ a • x = 0) (n : ℕ∞)
    (hn : ∀ b : O, b ≠ 0 → Module.length O (Submodule.torsionBy O M b) ≤ n) : Module.length O M ≤ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [← Module.length_top]
  refine Kum.lenDirected O _ _ (fun k => Submodule.torsionBy O M (ϖ ^ k)) n ?_ ?_
    fun k => ⟨k, le_rfl, hn _ (pow_ne_zero _ hϖ.ne_zero)⟩
  · intro i j hij
    exact Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ hij)
  · intro x _
    obtain ⟨a, ha, hx⟩ := h x
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
    exact Submodule.mem_iSup_of_mem k (Submodule.torsionBy_le_torsionBy_of_dvd _ _ hk.dvd
      ((Submodule.mem_torsionBy_iff _ _).2 hx))

private theorem vs_le {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (m e : ℕ) (θ : G ℚ Ω →* Oˣ) (n : ℕ∞)
    (hn : ∀ b : O, b ≠ 0 → Module.length O (Submodule.torsionBy O (ShaU (Chr.rho l e θ) m ⊤) b) ≤ n) :
    Chr.VS l m e θ ≤ n := by
  refine len_of_torsion O _ (fun x => ?_) _ hn
  obtain ⟨a, ha, hx⟩ := first_cohomology_torsion l O _ x.1
  exact ⟨a, ha, Subtype.ext hx⟩

theorem UpperTheory.V.U3.vlen_le :
    CohInp → LemmaM' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ M : Model S (PadicAlgCl l), Vlen Ω c e ψ ≤ M.len := by
  intro hC hM' Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg S M
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  obtain ⟨-, -, -, -, -, hK, h2, -⟩ := dat_facts D
  have hG : LocGood U (D.loc.It U) := Loc.locGood hC.loc D.loc U
  refine vs_le l c.O (l * N) e (Chr.dirG ℚ Ω ψ) _ fun b hb => ?_
  have h := sha_inj D g₁ hg b hb
  refine h.elim fun a h => h.2.elim fun γ hγ => ?_
  exact model_lower S M h2 hg hM' hG D.Ψ_cont hK a h.1 _ γ hγ.1 hγ.2
