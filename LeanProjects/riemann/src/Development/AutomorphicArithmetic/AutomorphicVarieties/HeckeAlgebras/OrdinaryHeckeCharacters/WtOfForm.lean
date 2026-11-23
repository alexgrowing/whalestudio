import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveInfinitePlaceOfEmbAtSplitPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cLoc_inf {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {x : UA L n} (h : x ∈ infU L n)
    (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

private theorem exists_gen {M : Type} [AddCommGroup M] [Module ℂ M] (B : Submodule ℂ M) (T : Set M)
    (h : B ⊓ Submodule.span ℂ T ≠ ⊥) : ∃ x ∈ T, x ≠ 0 := by
  by_contra hc
  refine h ?_
  rw [Submodule.span_eq_bot.2 fun x hx => by_contra fun h0 => hc ⟨x, hx, h0⟩, inf_bot_eq]

private theorem wt_of_form {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) (V : s.Lev) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (J : UA L n → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1))
    (hJ : ∀ x, J x = ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))
    (h3 : ∀ (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ℓ (x : UA L n),
      RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * J x)) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (h4 : Function.Surjective (fun k : finU L n => J k))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (hF : F ≠ 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ) (y : Emb l (fun v : V.frame.Vl => s.w v.1)) :
    HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  let Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    { toFun := fun ℓ => toForm ι e F ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF (funext fun p => ?_)) hσ (fun ℓ x hx => ?_) y
  · obtain ⟨k, hk⟩ := h4 p
    have h1 : infRep (V := V) ι lam (k : UA L n)⁻¹ (e (F p)) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by
        have h2 := congrFun (LinearMap.congr_fun h0 ℓ) (k : UA L n)
        rw [← hk]
        simp only [hJ]
        exact h2
    have h2 := congrArg (infRep (V := V) ι lam (k : UA L n)) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at h2
    exact e.map_eq_zero_iff.1 h2
  · have h1 : J x = 1 := (hJ x).trans
      (Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _))
    have h2 := h3 F ℓ x
    simp only [h1, mul_one] at h2
    exact h2

theorem UpperTheory.V.Hi.partUR2Wt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY y
  obtain ⟨F, hF, hF0⟩ := exists_gen _ _ hY
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  obtain ⟨-, -, h3, h4, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl
  exact wt_of_form hn V ι e _ (fun _ => rfl) h3 h4 σ (F i) hi (hF i) y
