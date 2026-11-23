import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.MemCongruenceSubgroupIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem form_inj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (hs : Function.Surjective fun k : finU L n =>
      (((away l L n).rangeRestrict k, fun v : V.frame.Vl => cLoc (s.w v.1) k) : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1)))
    (F F' : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (h : ∀ ℓ, toForm ι e F ℓ = toForm ι e F' ℓ) :
    F = F' := by
  funext y
  obtain ⟨k, rfl⟩ := hs y
  refine e.injective ?_
  have hR : ∀ u, infRep (V := V) ι lam k (infRep (V := V) ι lam (k : UA L n)⁻¹ u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine (hR _).symm.trans (Eq.trans (congrArg _ ?_) (hR _))
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_)
  rw [map_sub]
  exact sub_eq_zero.2 (congrFun (h ℓ) k)

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (m : ℕ) (i : Fin m)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) where
  toFun F := toForm ι e (F i) ℓ
  map_add' F F' := funext fun g => by
    simp only [toForm, Pi.add_apply, map_add]
  map_smul' a F := funext fun g => by
    simp only [toForm, Pi.smul_apply, map_smul, RingHom.id_apply]

private theorem push (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GLw n w) M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M')
    (σ : Submodule ℂ M') (τ : SmIrr (GLw n w)) (hiso : IsoSum ρ' σ τ) (j : ℕ) (a : ℂ)
    (ha : ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) (f : M →ₗ[ℂ] M')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (F : M) (hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), ρ k F = F) (hm : f F ∈ σ) :
    f (sphOp ρ j F) = f (a • F) := by
  have h3 := (UpperTheory.V.Hi.partUR2Abs L n w M ρ ⊥ τ bot_le).2.2.1 M' ρ' f.toAddMonoidHom hf j F
  have h2 := (UpperTheory.V.Hi.partUR2Abs L n w M' ρ' σ τ hiso).2.1 j a ha (f F)
    (Submodule.mem_inf.2 ⟨hm, fun k hk => (hf k F).symm.trans (congrArg f (hfix k hk))⟩)
  exact h3.trans (h2.trans (f.map_smul a F).symm)

theorem UpperTheory.V.Hi.partUR2Sph :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
    ∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ F ∈ YOf Q ι τ₀ e ξ σ, sphOp ((hset Q τ₀).atW ι d w) j F = a • F := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w hw hsp τ hτ j a ha F hF
  obtain ⟨j0, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn w hsp).1
  have hS : w.under (𝓞 (Lp L)) ∉ s.S := fun h => hw (Q.range ▸ Or.inl h)
  have hat := UpperTheory.V.Hi.partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ w hsp hS j0 hj1 hj2
  obtain ⟨hB, hm⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ w j0 hj1 hj2 hj3 τ hτ
  have hs := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ (fun _ => rfl)).2.2.2.1
  have hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), (hset Q τ₀).atW ι d w k F = F := fun k hk =>
    hB.2 _ (hAx.W_le w ⟨hw, hsp⟩ (Subgroup.mem_map_of_mem _ hk))
  funext i
  refine form_inj V ι lam d e hs _ _ fun ℓ => ?_
  exact push L n w (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ((hset Q τ₀).atW ι d w) _
    ((RU L n).comp j0) σ τ hiso j a ha (formLin V ι lam d e m i ℓ) (fun g v => hat v g i ℓ) F hfix (hm i ℓ)
