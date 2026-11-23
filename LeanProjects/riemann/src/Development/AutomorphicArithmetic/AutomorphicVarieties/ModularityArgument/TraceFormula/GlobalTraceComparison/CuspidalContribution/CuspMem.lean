import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open UpperTheory.V.Cj.S (CI mem_CI fL ciBasic ciCompl capAct locOf Pl)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke

section Lin

variable {M O : Type*} [AddCommGroup M] [Module ℂ M]

private theorem exists_irr_compl (act : O → Module.End ℂ M) (C : Submodule ℂ M) (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C) {φ : M} (hφ : φ ∈ C) (h0 : φ ≠ 0) :
    ∃ V D : Submodule ℂ M, V ≤ C ∧ D ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      (∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V) ∧ (∀ o, ∀ x ∈ D, act o x ∈ D) ∧
      V ⊓ D = ⊥ ∧ V ⊔ D = C ∧ φ ∉ D := by
  let U : Submodule ℂ M := sInf {W | φ ∈ W ∧ ∀ o, ∀ x ∈ W, act o x ∈ W}
  have hUC : U ≤ C := sInf_le ⟨hφ, hC⟩
  have hφU : φ ∈ U := Submodule.mem_sInf.2 fun W hW => hW.1
  have hUs : ∀ o, ∀ x ∈ U, act o x ∈ U := fun o x hx =>
    Submodule.mem_sInf.2 fun W hW => hW.2 o x (Submodule.mem_sInf.1 hx W hW)
  have hle := UpperTheory.V.TR.SS.le_sSup_minimal act U hUs fun W hW hs => by
    obtain ⟨D, -, d2, d3, d4⟩ := hc W (hW.trans hUC) hs
    refine ⟨D ⊓ U, inf_le_right, fun o x hx => ⟨d2 o x hx.1, hUs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, d3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hW, d4, inf_eq_right.2 hUC]
  by_contra hn
  refine h0 ((Submodule.mem_bot ℂ).1 ((hle.trans (sSup_le ?_)) hφU))
  rintro V ⟨v1, v2, v3, v4⟩
  obtain ⟨D, d1, d2, d3, d4⟩ := hc V (v1.trans hUC) v2
  by_cases hD : φ ∈ D
  · rw [← d3]
    exact le_inf le_rfl (v1.trans (sInf_le ⟨hD, d2⟩))
  · exact absurd ⟨V, D, v1.trans hUC, d1, v2, v3, v4, d2, d3, d4, hD⟩ hn

private theorem compl_sub (act : O → Module.End ℂ M) {C D : Submodule ℂ M}
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C)
    (hD : D ≤ C) (hs : ∀ o, ∀ x ∈ D, act o x ∈ D) :
    ∀ U ≤ D, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D' ≤ D, (∀ o, ∀ x ∈ D', act o x ∈ D') ∧ U ⊓ D' = ⊥ ∧ U ⊔ D' = D := by
  intro U hU hUs
  obtain ⟨D₀, -, a2, a3, a4⟩ := hc U (hU.trans hD) hUs
  refine ⟨D₀ ⊓ D, inf_le_right, fun o x hx => ⟨a2 o x hx.1, hs o x hx.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, a3, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, a4, inf_eq_right.2 hD]

end Lin

private theorem exists_proj {M : Type*} [AddCommGroup M] [Module ℂ M] {C V D : Submodule ℂ M} (hV : V ≤ C) (hD : D ≤ C)
    (h1 : V ⊓ D = ⊥) (h2 : V ⊔ D = C) :
    ∃ p : C →ₗ[ℂ] V, (∀ x : C, x.1 - (p x).1 ∈ D) ∧ ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v := by
  have hc : IsCompl (V.comap C.subtype) (D.comap C.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, h1, Submodule.comap_bot, Submodule.ker_subtype]
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (h2.ge hx)
      exact Submodule.mem_sup.2 ⟨⟨v, hV hv⟩, hv, ⟨d, hD hd⟩, hd, rfl⟩
  let p : C →ₗ[ℂ] V := (Submodule.comapSubtypeEquivOfLe hV).toLinearMap ∘ₗ Submodule.projectionOnto _ _ hc
  have hp : ∀ x : C, x.1 - (p x).1 ∈ D := fun x => by
    obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top.ge (Submodule.mem_top (x := x)))
    have e1 : Submodule.projectionOnto _ _ hc v = ⟨v, hv⟩ := Submodule.projectionOnto_apply_left hc ⟨v, hv⟩
    have e2 : Submodule.projectionOnto _ _ hc d = 0 := Submodule.projectionOnto_apply_right hc ⟨d, hd⟩
    have : (p (v + d)).1 = v.1 := by
      simp only [p, LinearMap.comp_apply, map_add, e1, e2, map_zero, add_zero]
      rfl
    rw [this]
    simpa using hd
  refine ⟨p, hp, fun x v h => Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 (h1.le ⟨V.sub_mem (p x).2 v.2, ?_⟩)))⟩
  have := D.sub_mem h (hp x)
  rwa [sub_sub_sub_cancel_left] at this

section Forms

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private noncomputable def stRep (C : Submodule ℂ (Sm E a)) (hC : IsStable C) : Representation ℂ (GL (Fin a) (Af E)) C :=
  GlobalTheory.PRep.sub (finRep E a) C fun k => hC (.fin k)

private theorem proj_rep {C V D : Submodule ℂ (Sm E a)} (hC : IsStable C) (hV : IsStable V) (hD : IsStable D)
    (p : C →ₗ[ℂ] V) (p1 : ∀ x : C, x.1 - (p x).1 ∈ D) (p2 : ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v)
    (g : GL (Fin a) (Af E)) (y : C) : p (stRep C hC g y) = stRep V hV g (p y) := by
  refine p2 _ _ ?_
  have := hD (.fin g) _ (p1 y)
  rw [map_sub] at this
  exact this

private theorem hasSat_of_map {C : Submodule ℂ (Sm E a)} (hC : IsStable C) (π : CuspSub E a) (f : C →ₗ[ℂ] π.V)
    (hf : ∀ g (y : C), f (stRep C hC g y) = π.finPart g (f y)) (w : Pl E) (B : Multiset ℂˣ) {x : C}
    (hx : IsSatVecGL w (fL a w) x.1 B) (h0 : f x ≠ 0) : HasSatGL w (π.locRep w) B := by
  have h1 : IsSatVecGL w (locOf (stRep C hC) w) x B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hx
  have h2 : IsSatVecGL w (π.locRep w) (f x) B := h1.map f (fun g y => hf _ y) h0
  obtain ⟨B', hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨f x, h2.2.1, h0⟩)
  rwa [(hB.2 _ h2.2.1 h0).unique h2] at hB

end Forms

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.cuspMem :
    CuspMem := by
  intro E _ _ _ N hN bad hbad K W φ m B h hc
  have hb := ciBasic capAct E N m
  have hc0 := ciCompl (ciBasic capAct) E N hN m
  have hφ : φ ∈ CI N m := mem_CI.2 ⟨hc, fun t => (h.cap t).2⟩
  obtain ⟨V, D, v1, d1, v2, v3, v4, d2, h1, h2, hφD⟩ := exists_irr_compl act (CI N m) hb.1 hc0 hφ h.ne
  let π : CuspSub E N := ⟨V, fun ψ hψ => (mem_CI.1 (v1 hψ)).1, v2, v3, v4⟩
  let x : CI N m := ⟨φ, hφ⟩
  obtain ⟨p, p1, p2⟩ := exists_proj v1 d1 h1 h2
  obtain ⟨q, q1, q2⟩ := exists_proj d1 v1 (by rwa [inf_comm]) (by rwa [sup_comm])
  have hp0 : p x ≠ 0 := fun e => hφD (by simpa [e, x] using p1 x)
  have hS : ∀ w ∉ bad, HasSatGL w (π.locRep w) (B w) := fun w hw =>
    hasSat_of_map hb.1 π p (proj_rep hb.1 v2 d2 p p1 p2) w (B w) (x := x) (h.sat w hw) hp0
  have hq : q x = 0 := by
    by_contra hq0
    have hq0' : (q x).1 ≠ 0 := fun e => hq0 (Subtype.ext e)
    obtain ⟨V', D', u1, e1, u2, u3, u4, e2, g1, g2, hD'⟩ :=
      exists_irr_compl act D d2 (compl_sub act hc0 d1 d2) (q x).2 hq0'
    let π' : CuspSub E N := ⟨V', fun ψ hψ => (mem_CI.1 (d1 (u1 hψ))).1, u2, u3, u4⟩
    obtain ⟨p', p1', p2'⟩ := exists_proj u1 e1 g1 g2
    have hp0' : p' (q x) ≠ 0 := fun e => hD' (by simpa [e] using p1' (q x))
    have hS' : ∀ w ∉ bad, HasSatGL w (π'.locRep w) (B w) := fun w hw =>
      hasSat_of_map hb.1 π' (p' ∘ₗ q) (fun g y => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, proj_rep hb.1 d2 v2 q q1 q2, proj_rep d2 u2 e2 p' p1' p2']
        rfl) w (B w) (x := x) (h.sat w hw) hp0'
    have e : V = V' := UpperTheory.V.Af.strongMultOneC E N π π'
      (Filter.eventually_cofinite.2 (hbad.subset fun w hw => by_contra fun hn => hw ⟨B w, hS w hn, hS' w hn⟩))
    exact v3 (eq_bot_iff.2 (h1 ▸ le_inf le_rfl (e.le.trans u1)))
  have hφV : φ ∈ V := by simpa [hq, x] using q1 x
  exact ⟨π, hφV, fun t => ⟨(h.cap t).1, fun u ψ hψ => (mem_CI.1 (v1 hψ)).2 t u⟩,
    fun w hw => (CG.hasSat_mk π w _).2 (hS w hw)⟩
