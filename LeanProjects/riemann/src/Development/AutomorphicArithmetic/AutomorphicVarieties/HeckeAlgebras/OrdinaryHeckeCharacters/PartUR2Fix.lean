import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem cmp_mem {w : Plc L} (x : UA L n) (P : Subgroup (GLw n w)) (hx : cLoc w x ∈ P) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [cmp_eq h]
    exact hx
  · unfold CaseU.cmp
    rw [dif_neg h]
    exact P.one_mem

private theorem st_away (s : HidaSetting l L Ω) (u : s.St) : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => by
  refine s.St_l u.1 u.2 ((s.hA u.1 _).1 ?_)
  have h1 := (s.hw u.1 _).2 h
  simpa using h1

private theorem inf_one {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU L n) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem key {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d m : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) {x : UA L n} (hx : x ∈ finU L n)
    (hl : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) (a : Fin m → ℂ) (i : Fin m)
    (h : ∀ g k, ∑ j, a j * F j (g * ((away l L n).rangeRestrict x, 1)) k = F i g k) (ℓ) :
    ∑ j : Fin m, a j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  funext g
  rw [Finset.sum_apply]
  have e1 : ∀ j, RU L n x (toForm ι e (F j) ℓ) g = ℓ (infRep ι lam g⁻¹ (e (F j
      (((away l L n).rangeRestrict g, fun v : V.frame.Vl => cLoc (s.w v.1) g) * ((away l L n).rangeRestrict x, 1))))) := fun j => by
    change toForm ι e (F j) ℓ (g * x) = _
    unfold toForm
    rw [mul_inv_rev, map_mul, inf_one V ι lam (inv_mem hx), one_mul]
    simp only [map_mul, hl, mul_one, Prod.mk_mul_mk]
  have e2 : ∀ g, F i g = ∑ j, a j • F j (g * ((away l L n).rangeRestrict x, 1)) := fun g => funext fun k => by
    rw [← h g k, Finset.sum_apply]
    rfl
  simp only [Pi.smul_apply, e1]
  unfold toForm
  rw [e2]
  simp only [map_sum, map_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.partUR2Fix :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d), F ∈ (hset Q τ₀).Big ι ξ → ∀ x ∈ finU L n, (∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) → ∀ k : KT n (wt s), (∀ u : s.St, k.1 u = cLoc (s.w u) x) → cLoc (s.w s.v0) x ∈ Kc _ n 1 →
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q, cLoc (Q.wq q) x = 1) →
    ∀ (i : Fin m) ℓ, ∑ j : Fin m, ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) k i j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ F hF x hx hl k hk h0 hS hQ i ℓ
  let u : Ub n s := ⟨(away l L n).rangeRestrict x, Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u =>
    cmp_mem x _ (hk u ▸ k.2 u trivial), cmp_mem x _ h0⟩⟩
  have hu : u ∈ UQ n Q := Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw =>
    cmp_mem x _ (hS w hw), Subgroup.mem_iInf.2 fun q =>
      Subgroup.mem_bot.1 (cmp_mem (l := l) x ⊥ (Subgroup.mem_bot.2 (hQ q)))⟩
  have hk' : toKT n s u = k := Subtype.ext (funext fun a => (cmp_eq (st_away s a) x).trans (hk a).symm)
  have h1 := hF.2 u hu
  rw [← hk']
  exact key V ι lam e F hx hl _ i (fun g b => congrFun (congrFun (congrFun h1 i) g) b) ℓ
