import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.InfRepFin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem frame_stab {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U : Subgroup X.Ub) (b : Gp) (F : Fin m → X.Fn ℂ d)
    (hF : F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.rpF ℂ d m b F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i hi γ g => ?_, fun u hu => ?_⟩
  · have h := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at h
    exact h
  · funext i g k
    have h := congrFun (congrFun (congrFun (hF.2 u hu) i) (g * (1, b))) k
    have e : g * (1, b) * ((u : Ga), 1) = g * ((u : Ga), 1) * (1, b) := by
      rw [mul_assoc, mul_assoc]
      simp
    change (Matrix.mulVec (τ u : Matrix (Fin m) (Fin m) ℂ) fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i = F i (g * (1, b)) k at h
    rw [e] at h
    exact h

private theorem big_stab {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (v : H.V)
    (g : GLw n (H.Sl v)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atV d v g F ∈ H.Big ι ξ :=
  frame_stab H.X ξ (H.τC ι) H.UQ _ F hF

private theorem iso_of {H P N W : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup W] [Module ℂ W] {m d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] W)
    (T : (P → Fin d → ℂ) →ₗ[ℂ] Module.Dual ℂ W →ₗ[ℂ] N) (ρ : Representation ℂ H (Fin m → P → Fin d → ℂ))
    (ρ' : Representation ℂ H N) (Y : Submodule ℂ (Fin m → P → Fin d → ℂ)) (Z : Submodule ℂ N) (τ : SmIrr H)
    (hZ : IsoSum ρ' Z τ) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hm : ∀ y ∈ Y, ∀ i ℓ, T (y i) ℓ ∈ Z)
    (he : ∀ y g i ℓ, T (ρ g y i) ℓ = ρ' g (T (y i) ℓ)) (hi : ∀ y ∈ Y, ∀ i, (∀ ℓ, T (y i) ℓ = 0) → y i = 0) :
    IsoSum ρ Y τ := by
  let b := (Pi.basisFun ℂ (Fin d)).map e
  refine UpperTheory.isoSum_of_injective_equivariant_family H _ N ρ ρ' Y Z τ (Fin m × Fin d)
    (fun x => T.flip (b.coord x.2) ∘ₗ LinearMap.proj x.1) hZ hY (fun x y hy => hm y hy x.1 _)
    (fun x g y _ => he y g x.1 _) fun y hy h => funext fun i => hi y hy i fun ℓ => ?_
  have h0 : T (y i) = 0 := b.dualBasis.ext fun k => by
    rw [Module.Basis.coe_dualBasis]
    exact h (i, k)
  rw [h0]
  rfl

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by
      simp only [toForm, Pi.add_apply, map_add])
    (fun a F ℓ => funext fun g => by
      simp only [toForm, Pi.smul_apply, map_smul])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoL :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∀ (v : V.frame.Vl) (τ : SmIrr (GLw n (s.w v.1))), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ → IsoSum (H := GLw n (s.w v.1)) ((hset Q τ₀).atV d v) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ v τ hτ
  have hsp : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA v.1) (s.split v.1 (Or.inl v.2)) _ (w_under s v.1)
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn (s.w v.1) hsp).1
  have hZ := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ (s.w v.1) j hj1 hj2 hj3 τ hτ
  have hM := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hA := partUR2AtV l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ v j hj1 hj2
  have hI := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  have hY : ∀ g, ∀ y ∈ YOf Q ι τ₀ e ξ σ, (hset Q τ₀).atV d v g y ∈ YOf Q ι τ₀ e ξ σ := fun g y hy =>
    (hM _).2 ⟨big_stab (hset Q τ₀) ι ξ v g y ((hM y).1 hy).1, fun i ℓ =>
      (hA y g i ℓ).symm ▸ hσ.stable (j g) _ (((hM y).1 hy).2 i ℓ)⟩
  exact iso_of (H := GLw n (s.w v.1)) (m := m) e (formLin ι e) ((hset Q τ₀).atV d v) ((RU L n).comp j) (YOf Q ι τ₀ e ξ σ) σ τ hZ hY
    (fun y hy => ((hM y).1 hy).2) hA fun y hy i h => hI (y i) (((hM y).1 hy).1.1 i trivial) h
