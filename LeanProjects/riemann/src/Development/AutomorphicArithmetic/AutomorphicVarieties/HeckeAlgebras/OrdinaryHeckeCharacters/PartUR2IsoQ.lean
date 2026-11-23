import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem raF_big {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (ξ : Gp →* GL (Fin d) ℂ) (U : Subgroup X.Ub) (x : X.Ub) (hx : ∀ u ∈ U, Commute u x)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.raF d τ x F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i _ => ?_, fun u hu => ?_⟩
  · have h : X.raF d τ x F i = ∑ j, (τ x : Matrix (Fin m) (Fin m) ℂ) i j • fun g => F j (g * ((x : Ga), 1)) := by
      funext g k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    change X.raF d τ x F i ∈ X.AF ξ
    rw [h]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ fun γ g => ?_
    have := hF.1 j trivial γ (g * ((x : Ga), 1))
    simpa only [mul_assoc] using this
  · rw [← Module.End.mul_apply, ← map_mul, (hx u hu).eq, map_mul, Module.End.mul_apply, hF.2 u hu]

private theorem big_atW {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)
    (q : H.Q) (g : GLw n (H.wq q)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atW ι d (H.wq q) g F ∈ H.Big ι ξ :=
  raF_big H.X (H.τC ι) ξ H.UQ (H.sec (H.wq q) g) (fun u hu => hA.Q_UQ q u hu g) F hF

private noncomputable def formL {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => rfl) (fun a F ℓ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoQ :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ (q : Q.Q) (τ : SmIrr (GLw n (Q.wq q))), IsCompAlong σ (locU n (Q.wq q)) ((cLoc (Q.wq q)).comp (locU n (Q.wq q)).subtype) τ.ρ → IsoSum ((hset Q τ₀).atW ι d (Q.wq q)) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hA q τ hτ
  have hS' : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsp : IsSplitAt (Q.wq q) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hS') _ rfl
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  have hmem := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hat := partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ _ hsp (Q.notS q) j hj1 hj2
  have hinj := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  let b := ((Pi.basisFun ℂ (Fin d)).map e).dualBasis
  let φ : Fin m × Fin d → (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun x => ((formL ι e).flip (b x.2)).comp (LinearMap.proj x.1)
  refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ ((RU L n).comp j) _ σ τ (Fin m × Fin d) φ hiso (fun g F hF => ?_) (fun x F hF => ?_)
    (fun x g F _ => ?_) (fun F hF h0 => ?_)
  · obtain ⟨h1, h2⟩ := (hmem F).1 hF
    refine (hmem _).2 ⟨big_atW (hset Q τ₀) hA ι ξ q g F h1, fun i ℓ => ?_⟩
    refine (hat F g i ℓ).symm ▸ ?_
    exact hσ.stable _ _ (h2 i ℓ)
  · exact ((hmem F).1 hF).2 x.1 (b x.2)
  · exact hat F g x.1 (b x.2)
  · refine funext fun i => hinj (F i) (((hmem F).1 hF).1.1 i trivial) fun ℓ => ?_
    have h : formL ι e (F i) = 0 := b.ext fun k => h0 (i, k)
    exact LinearMap.congr_fun h ℓ
