import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevOut
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2Faith :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) [DecidableEq Q.Q] (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (k : GV n Q.wq) (j : GV n Q.wq →* Ub n s), (∀ q g, j (Pi.mulSingle q g) = sec n s (Q.wq q) g) → j k ∈ (hset Q τ₀).lev K → k ∈ Subgroup.pi Set.univ K.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q _ c m τ₀ K k j hj hk
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ q : Q.Q, ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype).comp j =
      Pi.evalMonoidHom (fun q : Q.Q => GLw n (Q.wq q)) q := fun q => by
    refine MonoidHom.pi_ext fun q' g => ?_
    change CaseU.cmp n (Q.wq q) ((j (Pi.mulSingle q' g) : Ub n s) : Ga l L n) =
      (Pi.mulSingle q' g : ∀ q : Q.Q, GLw n (Q.wq q)) q
    rw [hj]
    by_cases h : q = q'
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact (hsec q).2.1 g
    · rw [Pi.mulSingle_eq_of_ne h]
      exact h1 q' g _ fun h' => h (Q.inj h')
  intro q _
  have h2 := (levelUR2LevOut l L Ω s n hn V Q c m τ₀ K (j k) hk).2 q
  have h3 : CaseU.cmp n (Q.wq q) ((j k : Ub n s) : Ga l L n) = k q := DFunLike.congr_fun (key q) k
  rw [h3] at h2
  exact h2
