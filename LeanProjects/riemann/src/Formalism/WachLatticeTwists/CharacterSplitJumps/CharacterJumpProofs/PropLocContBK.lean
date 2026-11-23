import Formalism.WachLatticeTwists.CharacterSplitJumps.StatPropLocContBK
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.LatticeDualFibres.PropLocContOfLattices

universe u

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.RepresentationBoundsCohomology.LOC

theorem baerFrac (O : Type u) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] :
    Module.Baer O (FractionRing O) := fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  have hm : algebraMap O (FractionRing O) m ≠ 0 := by
    simpa using h0
  let gm := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton O (FractionRing O) (gm / algebraMap O (FractionRing O) m),
    fun n hn => ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  have h1 : g ⟨n • m, hn⟩ = n • gm := by
    rw [← map_smul g, SetLike.mk_smul_mk]
  rw [h1, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_smul, Algebra.smul_def m,
    mul_div_cancel₀ _ hm]

theorem bkbConvO : StatBKbConvO.{u} := by
  intro O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' hA hS hP hC hN
  set L : Submodule O HT' := HfV'.comap j' with hL
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_annih]
    intro t ht
    rw [hC, (hA a).1 ha _ ht]
    simp
  · intro x hx
    rw [mem_annih] at hx
    let jb : (HT' ⧸ L) →ₗ[O] (HV' ⧸ HfV') :=
      L.liftQ (HfV'.mkQ ∘ₗ j') (by
        intro t ht
        have ht' : j' t ∈ HfV' := ht
        simpa [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero] using ht')
    have hjb : Function.Injective jb := by
      rw [← LinearMap.ker_eq_bot]
      apply Submodule.ker_liftQ_eq_bot
      intro t ht
      have ht' : j' t ∈ HfV' := by
        simpa [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero] using ht
      exact ht'
    have htf : Module.IsTorsionFree O (HT' ⧸ L) := by
      refine ⟨fun r hr => ?_⟩
      have hr0 : r ≠ 0 := hr.ne_zero
      have key : ∀ y : HT' ⧸ L, r • y = 0 → y = 0 := by
        intro y
        induction y using Submodule.Quotient.induction_on with
        | H t =>
          intro h
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
          have h' : r • j' t ∈ HfV' := by
            rw [← map_smul]
            exact h
          rw [Submodule.Quotient.mk_eq_zero]
          exact hS r _ hr0 h'
      intro y z hyz
      have hyz' : r • y = r • z := hyz
      have : r • (y - z) = 0 := by rw [smul_sub, hyz', sub_self]
      exact sub_eq_zero.1 (key _ this)
    let lam0 : (HT' ⧸ L) →ₗ[O] KO O := L.liftQ (pr x) (by
      intro t ht
      exact hx t ht)
    obtain ⟨lam1, hlam1⟩ := Module.projective_lifting_property
      (Submodule.mkQ (1 : Submodule O (FractionRing O))) lam0 (Submodule.mkQ_surjective _)
    obtain ⟨μ, hμ⟩ := (baerFrac O).extension_property jb hjb lam1
    obtain ⟨a, ha⟩ := hP (μ ∘ₗ HfV'.mkQ)
    have haf : a ∈ HfV := by
      rw [hA]
      intro v hv
      rw [ha]
      simp [(Submodule.Quotient.mk_eq_zero HfV').2 hv]
    refine ⟨a, haf, ?_⟩
    symm
    rw [← sub_eq_zero]
    apply hN
    intro t
    rw [map_sub, LinearMap.sub_apply, hC, ha, sub_eq_zero]
    have h3 : lam0 (Submodule.Quotient.mk t) = pr x t := rfl
    have h4 : μ (jb (Submodule.Quotient.mk t)) = lam1 (Submodule.Quotient.mk t) :=
      LinearMap.congr_fun hμ _
    have h5 : Submodule.mkQ (1 : Submodule O (FractionRing O)) (lam1 (Submodule.Quotient.mk t)) =
        lam0 (Submodule.Quotient.mk t) := LinearMap.congr_fun hlam1 _
    rw [← h3, ← h5, ← h4]
    rfl

theorem propLocContBK : StatPropLocContBK.{u} := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' pair ℓ e' ι₁ ι₂ P Q
    hT hperf hfin hc hA hS hP hC hN h1 h2
  exact propLocCont O G VT VT' D HfV HfV' ℓ e' ι₁ ι₂ P Q hT hperf hfin hc
    (bkbConvO O _ _ _ _ D.q D.j' D.pr pair HfV HfV' hA hS hP hC hN) h1 h2

end Formalism.RepresentationBoundsCohomology.JT
