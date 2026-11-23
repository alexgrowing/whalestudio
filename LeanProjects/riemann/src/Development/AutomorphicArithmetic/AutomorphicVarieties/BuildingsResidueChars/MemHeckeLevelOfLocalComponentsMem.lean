import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.mem_heckeLevel_of_local_components_mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) → u ∈ (hset Q τ₀).lev K := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ (T : Finset Q.Q) (u : Ub n s),
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) →
      (∀ q : Q.Q, CaseU.cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) →
      (∀ q ∉ T, CaseU.cmp n (Q.wq q) (u : Ga l L n) = 1) → u ∈ (hset Q τ₀).lev K := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro u hu _ h0
      refine Subgroup.mem_sup_left (S := UQ n Q) ?_
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => hu w hw,
        Subgroup.mem_iInf.2 fun q => MonoidHom.mem_ker.2 (h0 q (Finset.notMem_empty q))⟩
    | insert q T _ ih =>
      intro u hu hK h0
      let x : Ub n s := sec n s (Q.wq q) (CaseU.cmp n (Q.wq q) (u : Ga l L n))
      have hx : x ∈ (hset Q τ₀).lev K :=
        Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨_, hK q, rfl⟩)
      have e1 : ∀ w : Plc L, w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
          CaseU.cmp n w ((x⁻¹ * u : Ub n s) : Ga l L n) = CaseU.cmp n w (u : Ga l L n) := fun w hw => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1 q _ w hw, inv_one, one_mul]
      have e2 : CaseU.cmp n (Q.wq q) ((x⁻¹ * u : Ub n s) : Ga l L n) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, (hsec q).2.1, inv_mul_cancel]
      have hy : x⁻¹ * u ∈ (hset Q τ₀).lev K := by
        refine ih _ (fun w hw => ?_) (fun q' => ?_) fun q' hq' => ?_
        · rw [e1 w fun h => hw (h ▸ hS q)]
          exact hu w hw
        · by_cases h : q' = q
          · subst h
            rw [e2]
            exact one_mem _
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact hK q'
        · by_cases h : q' = q
          · subst h
            exact e2
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact h0 q' fun h' => (Finset.mem_insert.1 h').elim h hq'
      have e : u = x * (x⁻¹ * u) := (mul_inv_cancel_left x u).symm
      rw [e]
      exact Subgroup.mul_mem _ hx hy
  exact fun u hu hK => key Finset.univ u hu hK fun q hq => (hq (Finset.mem_univ q)).elim
