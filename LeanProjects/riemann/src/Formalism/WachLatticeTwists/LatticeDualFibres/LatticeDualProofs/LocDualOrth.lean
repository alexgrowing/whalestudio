import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange

universe u

open Formalism.NG (KO annih)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem mem_annih' {O A H : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (x : A) :
    x ∈ annih pr M ↔ ∀ m ∈ M, pr x m = 0 := by
  simp only [annih, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

theorem locDirect : StatLocDirect.{u} := by
  intro O A HV _ _ _ _ _ q HfV P ℓ e' hF hL y hy
  obtain ⟨x, hx, hxy⟩ := hL y hy
  refine ⟨P.p2 (P.jL x), hF hx, ?_⟩
  rw [← P.comm x, hxy, map_smul]

theorem locDualOrth : StatLocDualOrth.{u} := by
  intro O A HT' _ _ _ _ _ _ _ pr HfT' Q ℓ e' hF hO hL y hy
  rw [mem_annih']
  intro κ hκ
  obtain ⟨x, hx, hxκ⟩ := hL κ hκ
  rw [map_smul, LinearMap.smul_apply, ← LinearMap.map_smul, ← hxκ, Q.cup, hO _ hy _ (hF hx), map_zero]

theorem locTorsDual : StatLocTorsDual.{u} := by
  intro O A H _ _ _ _ _ _ _ pr M S a hS
  have hIm : (mulSub a M).map M.subtype ≤ M := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have h0 := Formalism.NG.annColength O A H pr M ((mulSub a M).map M.subtype) hIm
  rw [Submodule.comap_map_eq_of_injective M.injective_subtype] at h0
  refine le_trans ?_ h0
  have hSle : S ≤ annih pr ((mulSub a M).map M.subtype) := by
    intro s hs
    rw [mem_annih']
    rintro _ ⟨x, ⟨m, rfl⟩, rfl⟩
    have := (mem_annih' pr M _).1 (hS s hs) m m.2
    simpa only [LinearMap.lsmul_apply, Submodule.subtype_apply, Submodule.coe_smul, map_smul,
      LinearMap.smul_apply] using this
  let f : (S ⧸ (annih pr M).comap S.subtype) →ₗ[O]
      (annih pr ((mulSub a M).map M.subtype) ⧸
        (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hSle) (by
      intro x hx
      exact hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    have hx' : (Submodule.Quotient.mk (Submodule.inclusion hSle x) :
        (annih pr ((mulSub a M).map M.subtype) ⧸
          (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype)) = 0 := hx
    have hx'' := (Submodule.Quotient.mk_eq_zero _).1 hx'
    exact (Submodule.Quotient.mk_eq_zero _).2 hx''

theorem propLoc_of (hQ : StatLocQuotLen.{u}) : StatPropLoc.{u} := by
  intro O A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr HfV HfV' ℓ e' d N δ ι₁ ι₂ P Q hann hδ hP hQ'
  have h1 : ∀ i, ∀ y ∈ (P i).HfY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map q :=
    fun i => locDirect O A HV q HfV (P i) ℓ e' (hP i).1 (hP i).2
  have h2 : ∀ i, ∀ y ∈ (Q i).HfY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map q := by
    intro i y hy
    rw [hann]
    exact locDualOrth O A HT' pr (HfV'.comap j') (Q i) ℓ e' (hQ' i).1 (hQ' i).2.1 (hQ' i).2.2 y hy
  refine ⟨h1, h2, ?_⟩
  have hle : pushSpan P Q ≤ (HfV.map q).comap (LinearMap.lsmul O A ((ℓ : O) ^ e')) := by
    refine sup_le (iSup_le fun i => ?_) (iSup_le fun i => ?_)
    · rintro _ ⟨y, hy, rfl⟩
      exact h1 i y hy
    · rintro _ ⟨y, hy, rfl⟩
      exact h2 i y hy
  have hS : ∀ s ∈ pushSpan P Q, ((ℓ : O) ^ e') • s ∈ annih pr (HfV'.comap j') := fun s hs => by
    rw [← hann]
    exact hle hs
  have hT := locTorsDual O A HT' pr (HfV'.comap j') (pushSpan P Q) ((ℓ : O) ^ e') hS
  rw [← hann] at hT
  refine hT.trans ?_
  haveI : IsNoetherian O HT' := isNoetherian_of_isNoetherianRing_of_finite O HT'
  haveI : Module.Finite O (HfV'.comap j') := Module.IsNoetherian.finite O (HfV'.comap j')
  have htors : Submodule.torsion O HT' ≤ HfV'.comap j' := by
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have h0 : (a : O) • j' x = 0 := by
      rw [← map_smul]
      have : (a : O) • x = 0 := hax
      rw [this, map_zero]
    have hj : j' x = 0 :=
      ((Module.isTorsionFree_iff_smul_eq_zero.1 inferInstance (a : O) (j' x) h0).resolve_left
        (nonZeroDivisors.coe_ne_zero a))
    show j' x ∈ HfV'
    rw [hj]
    exact HfV'.zero_mem
  let δ' : N →ₗ[O] HfV'.comap j' :=
    δ.codRestrict (HfV'.comap j') (fun n => htors (hδ ▸ LinearMap.mem_range_self δ n))
  have htors' : Submodule.torsion O (HfV'.comap j') ≤ LinearMap.range δ' := by
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have hx' : (x : HT') ∈ Submodule.torsion O HT' := by
      refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
      have := congrArg Subtype.val hax
      simpa using this
    rw [← hδ] at hx'
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, Subtype.ext hn⟩
  exact hQ O (HfV'.comap j') d N δ' htors' ℓ e'

end Formalism.RepresentationBoundsCohomology.LOC
