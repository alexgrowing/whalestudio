import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Pu

section Fr

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}

theorem raF_eq (τ : X.Ub →* GL (Fin m) ℂ) (u : X.Ub) (F : Fin m → X.Fn ℂ d) (i : Fin m) :
    X.raF d τ u F i = ∑ j, τ u i j • fun g => F j (g * ((u : Ga), 1)) := by
  funext g k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem AF_tr {ξ : Gp →* GL (Fin d) ℂ} {F : X.Fn ℂ d} (hF : F ∈ X.AF ξ) (y : Ga × Gp) :
    (fun g => F (g * y)) ∈ X.AF ξ := fun γ g => by
  simp only [mul_assoc]
  exact hF γ _

end Fr

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

theorem w_under (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

omit [Fact l.Prime] in
theorem l_iff (w : Plc L) : ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ w.asIdeal ↔ _
  rw [map_natCast]

theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

variable (V : s.Lev)

noncomputable def JU (x : UA L n) : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
  ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)

variable {V} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ι : Qbar l ≃+* ℂ)
  {lam : Wt L l n} {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

noncomputable def tf (i : Fin m) (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    (Fin m → (hset Q τ₀).X.Fn ℂ d) →ₗ[ℂ] (UA L n → ℂ) where
  toFun F := toForm ι e (F i) ℓ
  map_add' F F' := funext fun g => by
    change ℓ (infRep ι lam g⁻¹ (e (F i _ + F' i _))) = _
    rw [map_add, map_add, map_add]
    rfl
  map_smul' a F := funext fun g => by
    change ℓ (infRep ι lam g⁻¹ (e (a • F i _))) = _
    rw [map_smul, map_smul, map_smul]
    rfl

theorem mem_Y {ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ} {σ : Submodule ℂ (UA L n → ℂ)}
    {F : Fin m → (hset Q τ₀).X.Fn ℂ d} :
    F ∈ YOf Q ι τ₀ e ξ σ ↔ F ∈ (hset Q τ₀).Big ι ξ ∧ ∀ i ℓ, tf Q τ₀ ι e i ℓ F ∈ σ := by
  refine and_congr Iff.rfl ⟨fun h i ℓ => ?_, fun h => Submodule.subset_span h⟩
  exact (Submodule.span_le (p := σ.comap (tf Q τ₀ ι e i ℓ))).2 (fun F hF => by exact hF i ℓ) h

theorem RU_form (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (ℓ) (x : UA L n) :
    RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * JU V x)) (ℓ ∘ₗ infRep ι lam x⁻¹) := by
  funext g
  change ℓ (infRep ι lam (g * x)⁻¹ (e (F (JU V (g * x))))) = ℓ (infRep ι lam x⁻¹ (infRep ι lam g⁻¹ (e (F (JU V g * JU V x)))))
  have : JU V (g * x) = JU V g * JU V x := Prod.ext (map_mul _ _ _) (funext fun v => map_mul _ _ _)
  rw [this, mul_inv_rev, map_mul, Module.End.mul_apply]

theorem RU_fin (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (ℓ) {x : UA L n} (hx : x ∈ finU L n) :
    RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * JU V x)) ℓ := by
  have h : infRep (V := V) ι lam x⁻¹ = 1 := by
    have h1 : cInf x⁻¹ = 1 := inv_mem hx
    refine (congrArg PiTensorProduct.mapMonoidHom (funext fun y => ?_)).trans (map_one _)
    change GlobalTheory.Branching.sqRep ℂ n _ (Matrix.GeneralLinearGroup.map _ (cInf x⁻¹)) = 1
    rw [h1, map_one, map_one]
  rw [RU_form, h]
  rfl

end U

end UpperTheory.V.Hi.Pu
