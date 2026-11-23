import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ShiftSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalVectorMemFixedRight

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.LFun
open Formalism.UG (Hecke IsCommensurated Tj Ov qV IsUnifV dosetInd)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G : Type} [Group G]

private theorem hint_mul_eq_conv (K : Subgroup G) {f g : G → ℂ} (hf : f ∈ Hecke ℂ K) (hg : g ∈ Hecke ℂ K) :
    (fun y => hint K fun z => f z * g (z⁻¹ * y)) = Formalism.UG.conv K f g := by
  funext y
  refine (hintSph G K _ fun k hk x => ?_).trans rfl
  have h1 : f (x * k) = f x := by simpa using hf.1 1 ⟨k, hk⟩ x
  have h2 : g (k⁻¹ * (x⁻¹ * y)) = g (x⁻¹ * y) := by
    simpa using hg.1 ⟨k⁻¹, K.inv_mem hk⟩ 1 (x⁻¹ * y)
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  show f (x * k) * g ((x * k)⁻¹ * y) = f x * g (x⁻¹ * y)
  rw [h1, e, h2]

private theorem ind_eq_dosetInd (K : Subgroup G) : (K : Set G).indicator (1 : G → ℂ) = dosetInd ℂ K 1 := by
  funext x
  by_cases hx : x ∈ K
  · rw [Formalism.UG.P.dosetInd_of_mem ℂ K 1 x ((Formalism.UG.P.mem_dc_one K x).2 hx)]
    simp [Set.indicator_apply, hx]
  · rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K 1 x fun h => hx ((Formalism.UG.P.mem_dc_one K x).1 h)]
    simp [Set.indicator_apply, hx]

private theorem fn_mem {ι : Type} (K : Subgroup G) (hK : IsCommensurated K) (g : ι → G → ℂ)
    (hg : ∀ i, g i ∈ Hecke ℂ K) (e : Ex ι) : e.fn K g ∈ Hecke ℂ K := by
  induction e with
  | one =>
    show (K : Set G).indicator 1 ∈ Hecke ℂ K
    rw [ind_eq_dosetInd]
    exact Formalism.UG.Final.DosetIndMem G K ℂ 1
  | gen i => exact hg i
  | smul c a ih => exact (Hecke ℂ K).smul_mem c ih
  | add a b iha ihb => exact (Hecke ℂ K).add_mem iha ihb
  | mul a b iha ihb =>
    show (fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)) ∈ Hecke ℂ K
    rw [hint_mul_eq_conv K iha ihb]
    exact Formalism.UG.Final.HeckeConvMem G K ℂ hK _ iha _ ihb

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem heckeVec_ind (K : Subgroup G) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K ((K : Set G).indicator 1) x = x := by
  rw [ind_eq_dosetInd, heckeVec_dosetInd hx (a := 1) (R := {1})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact (Formalism.UG.P.mem_dc_one K 1).2 K.one_mem
  · intro g hg
    refine ⟨1, ⟨Finset.mem_singleton_self _, by simpa using (Formalism.UG.P.mem_dc_one K g).1 hg⟩, ?_⟩
    exact fun γ hγ => Finset.mem_singleton.1 hγ.1

private theorem heckeVec_fn {ι : Type} (K : Subgroup G) (hK : IsCommensurated K) (g : ι → G → ℂ)
    (hg : ∀ i, g i ∈ Hecke ℂ K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) (c : ι → ℂ)
    (hc : ∀ i, heckeVec ρ K (g i) x = c i • x) (e : Ex ι) :
    heckeVec ρ K (e.fn K g) x = e.ev c • x := by
  induction e with
  | one =>
    show heckeVec ρ K ((K : Set G).indicator 1) x = (1 : ℂ) • x
    rw [heckeVec_ind K ρ hx, one_smul]
  | gen i => exact hc i
  | smul z a ih =>
    show heckeVec ρ K (z • a.fn K g) x = (z * a.ev c) • x
    rw [GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_smul, ih, mul_smul]
  | add a b iha ihb =>
    show heckeVec ρ K (a.fn K g + b.fn K g) x = (a.ev c + b.ev c) • x
    rw [GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_add hK (fn_mem K hK g hg a) (fn_mem K hK g hg b), iha, ihb, add_smul]
  | mul a b iha ihb =>
    show heckeVec ρ K (fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)) x = (a.ev c * b.ev c) • x
    rw [hint_mul_eq_conv K (fn_mem K hK g hg a) (fn_mem K hK g hg b),
      GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_conv hK (fn_mem K hK g hg a) (fn_mem K hK g hg b) ρ hx, ihb,
      GlobalTheory.CompanionTheory.Ipf.Val.SphM.heckeVec_smul_vec, iha, smul_smul, mul_comm]

private theorem isHecke_of_mem [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hc : IsCompact (K : Set G)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : IsHecke K f := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have hcomp : IsCompact (⋃ s ∈ (S : Set G), (fun p : G × G => p.1 * s * p.2) '' ((K : Set G) ×ˢ (K : Set G))) :=
      S.finite_toSet.isCompact_biUnion fun s _ => (hc.prod hc).image (by fun_prop)
    refine HasCompactSupport.intro hcomp fun x hx => ?_
    by_contra h0
    obtain ⟨s, hs, a, b, e⟩ := hS x h0
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨(a, b), ⟨a.2, b.2⟩, e.symm⟩)
  · simpa using hb ⟨k, hk⟩ 1 x
  · simpa using hb 1 ⟨k, hk⟩ x

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exAct :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExAct := by
  intro E _ _ _ n w e
  have hu : IsUnifV E w (unif w) := Classical.epsilon_spec (exists_isUnifV w)
  have hK : IsCommensurated (KGL w n) := Formalism.UG.Final.GLintComm E w n
  have hT : ∀ j : Fin (n + 1), Tj ℂ n (Ov E w) (unif w) j ∈ Formalism.UG.Hecke ℂ (KGL w n) :=
    fun j => Tj_mem_hecke hu j
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hmem : fn1 n w e ∈ Formalism.UG.Hecke ℂ (KGL w n) := fn_mem _ hK _ hT e
  have hH : IsHecke (KGL w n) (fn1 n w e) := isHecke_of_mem hc hmem
  refine ⟨hH, fun V _ _ ρ x B hx => ?_⟩
  have hfix : x ∈ fixed ρ (KGL w n) := hx.2.1
  rw [(cvOp _ _ ho hc V ρ _ _ hH hH x hfix).2.2]
  exact heckeVec_fn _ hK _ hT ρ hfix _ (fun j => hx.2.2.2 (unif w) hu j (Nat.lt_succ_iff.1 j.2)) e
