import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlaceBis

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

private theorem Kc_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g⁻¹ * x * g ∈ Kc k n 1 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a⁻¹ * b * a, ?_, by simp only [map_mul, map_inv]⟩
  have hb' := MonoidHom.mem_ker.1 hb
  exact MonoidHom.mem_ker.2 (by simp only [map_mul, map_inv, hb', mul_one, inv_mul_cancel])

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

variable (s : HidaSetting l L Ω)

private theorem sec_one (w w' : Plc L) (h : GLw n w) (hw : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n w' (sec n s w h : Ga l L n) = 1 := by
  unfold CaseU.sec
  split_ifs with hb
  · have hm := ((MulEquiv.ofBijective _ hb).symm h).2
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm w') hw)
  · exact map_one _

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dif_pos h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_GaS {x : Ga l L n} (hx : x ∈ GaS n s) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0) : cmp n w x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

end UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

open UpperTheory.V.Z.Desc.V0.InertiaSectionNorm in
theorem UpperTheory.V.Z.Desc.V0.normS :
    NormS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV Q c m τ₀
  obtain ⟨hb, hcomm, hdesc⟩ := secSp l L Ω s n hn V hV
  have spec := secS_spec (n := n) s hb
  have hq : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)⟩
  have hlev : ∀ K, (hset Q τ₀).lev K = (hset Q τ₀).UQ := fun K => by
    haveI : IsEmpty (hset Q τ₀).Q := hq
    unfold HSet.lev
    rw [iSup_of_empty]
    exact sup_bot_eq _
  have h0 : ∀ (g : GLw n (s.w s.v0)) (t : s.St), cmp n (s.w t) (sec0 n s g) = 1 := fun g t =>
    congrFun (congrArg Prod.fst (spec (1, g)).1) t
  have hτ : ∀ (u u' : Ub n s), (∀ t : s.St, cmp n (s.w t) (u : Ga l L n) = cmp n (s.w t) (u' : Ga l L n)) →
      (hset Q τ₀).τ u = (hset Q τ₀).τ u' := fun u u' h =>
    congrArg τ₀ (Subtype.ext (funext h))
  have huq : ∀ g : GLw n (s.w s.v0), g ∈ KO _ (Fin n) → ∀ u ∈ UQ n Q, ∃ u' ∈ UQ n Q,
      (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g ∧ (hset Q τ₀).τ u' = (hset Q τ₀).τ u := by
    intro g hg u hu
    obtain ⟨k, hk, p, hp, e⟩ := (hdesc Q (u : Ga l L n)).1 ⟨u, hu, rfl⟩
    have hp' : ((p.1, g⁻¹ * p.2 * g) : GS n s) ∈ (KT n (wt s)).prod (Kc _ n 1) :=
      Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hp).1, Kc_conj hg (Subgroup.mem_prod.1 hp).2⟩
    have hconj : ((p.1, g⁻¹ * p.2 * g) : GS n s) = ((1, g) : GS n s)⁻¹ * p * (1, g) :=
      Prod.ext (by simp) (by simp)
    have e' : (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g = secS n s (p.1, g⁻¹ * p.2 * g) * k := by
      have hc : k * sec0 n s g = sec0 n s g * k := (hcomm (1, g) k hk).eq.symm
      rw [hconj, map_mul, map_mul, map_inv, e]
      change (sec0 n s g)⁻¹ * (secS n s p * k) * sec0 n s g = (sec0 n s g)⁻¹ * secS n s p * sec0 n s g * k
      simp only [mul_assoc, hc]
    obtain ⟨u', hu', e''⟩ := (hdesc Q _).2 ⟨k, hk, _, hp', e'⟩
    have e3 : (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g := e''
    refine ⟨u', hu', e3, hτ _ _ fun t => ?_⟩
    rw [e3, map_mul, map_mul, map_inv, h0, inv_one, one_mul, mul_one]
  refine ⟨fun g hg => ⟨fun K u hu => ?_, fun u hu => huq g hg u hu, fun w hw h => ?_⟩, fun g hg => ?_⟩
  · rw [hlev] at hu
    obtain ⟨u', hu', h⟩ := huq g hg u hu
    exact ⟨u', by rw [hlev]; exact hu', h⟩
  · refine comm_of fun w' => ?_
    by_cases hu : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · refine Or.inl (mem_GaS s (spec (1, g)).2 (notS s ?_))
      rw [hu, ← hV]
      exact hw.1
    · exact Or.inr (sec_one s w w' h hu)
  · obtain ⟨u, hu, e⟩ := (hdesc Q (sec0 n s g)).2 ⟨1, one_mem _, (1, g),
      Subgroup.mem_prod.2 ⟨one_mem _, hg⟩, (mul_one _).symm⟩
    have e3 : (u : Ga l L n) = sec0 n s g := e
    refine ⟨u, hu, e3, ?_⟩
    exact (hτ u 1 fun t => by rw [e3, h0]; exact (map_one _).symm).trans (map_one (hset Q τ₀).τ)
