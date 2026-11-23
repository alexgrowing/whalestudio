import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2LevOut :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), u ∈ (hset Q τ₀).lev K → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧ ∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K u hu
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  let P : Subgroup (Ub n s) :=
    (⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'),
      (KO (w.adicCompletion L) (Fin n)).comap ((CaseU.cmp n w).comp (Ub n s).subtype)) ⊓
    ⨅ q : Q.Q, Subgroup.comap ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype) (K.1 q)
  have hP : ∀ x : Ub n s, x ∈ P ↔
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
        ∀ q : Q.Q, CaseU.cmp n (Q.wq q) (x : Ga l L n) ∈ K.1 q := fun x =>
    ⟨fun h => ⟨fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).1 w) hw,
      fun q => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).2 q⟩,
     fun h => Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.1 w hw,
      Subgroup.mem_iInf.2 fun q => h.2 q⟩⟩
  have hle : (hset Q τ₀).lev K ≤ P := by
    refine sup_le (fun x hx => ?_) (iSup_le fun q => ?_)
    · have hx' : x ∈ UQ n Q := hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx').1, Subgroup.mem_iInf.2 fun q => ?_⟩
      have e := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx').2 q)
      exact Subgroup.mem_comap.2 (e ▸ one_mem _)
    · rintro _ ⟨g, hg, rfl⟩
      refine (hP (sec n s (Q.wq q) g)).2 ⟨fun w hw => ?_, fun q' => ?_⟩
      · rw [h1 q g w fun h => hw (h ▸ hS q)]
        exact one_mem _
      · by_cases h : q' = q
        · subst h
          exact Set.mem_of_eq_of_mem ((hsec q').2.1 g) hg
        · rw [h1 q g _ fun h' => h (Q.inj h')]
          exact one_mem _
  exact (hP u).1 (hle hu)
