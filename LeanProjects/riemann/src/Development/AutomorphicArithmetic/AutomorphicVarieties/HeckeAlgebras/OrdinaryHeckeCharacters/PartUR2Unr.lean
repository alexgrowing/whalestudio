import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SatTUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Fix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem unr_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem unr_sum {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (t : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, t 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2Unr :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY w hw
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  have hA : F i ∈ (hset Q τ₀).X.AF ξ := hB.1 i (Set.mem_univ _)
  have h1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1 (F i) hA
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 (mt h1 hi)
  refine ⟨_, hσ i ℓ, hℓ, fun x hx hk => ?_⟩
  have hne : ∀ u : Plc L, u.under (𝓞 (Lp L)) ∈ V.S' → cLoc u x = 1 := fun u hu =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ hu)
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv => hne _ ((unr_under s v).symm ▸ V.sub hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have h2 := partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB x (Subgroup.mem_inf.1 hx).1
    (fun v => hS v.1 (Or.inl v.2)) 1 (fun u => (hS u.1 (Or.inr (Or.inl u.2))).symm)
    (by
      rw [hS s.v0 (Or.inr (Or.inr rfl))]
      exact one_mem _)
    (fun u _ => by
      by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
      · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
        exact one_mem _)
    (fun q => hne _ (Q.range.ge (Or.inr ⟨q, rfl⟩))) i ℓ
  exact (unr_sum _ (fun j => RU L n x (toForm ι e (F j) ℓ)) i).symm.trans h2
