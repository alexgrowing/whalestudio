import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisFiniteOfIsDR

noncomputable section

namespace GlobalTheory.HyodoFE

open Formalism Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HyodoDef TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [mem_Dcris_iff] at hx ⊢
  intro g
  rw [← GlobalTheory.CobCrisLift.φVB_act, hx g]

def oneSubφ : Dcris PD ρ →ₗ[LL] Dcris PD ρ :=
  (LinearMap.id - φVB PD (LL := LL) (V := V)).restrict (p := Dcris PD ρ) (q := Dcris PD ρ)
    (fun x hx => (Dcris PD ρ).sub_mem hx (φVB_mem_Dcris PD ρ hx))

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def pairs : Submodule LL ((G → V) × (V ⊗[Qp] B)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def projZ : pairs PD ρ →ₗ[LL] finiteCocycles PD ρ :=
  LinearMap.codRestrict (finiteCocycles PD ρ) ((LinearMap.fst LL (G → V) (V ⊗[Qp] B)).comp (pairs PD ρ).subtype)
    (fun p => ⟨p.2.1, p.1.2, p.2.2⟩)

theorem projZ_surjective : Function.Surjective (projZ PD ρ) := by
  rintro ⟨c, hc, x, hx⟩
  exact ⟨⟨(c, x), hc, hx⟩, rfl⟩

def toDcris : pairs PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    (((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (LinearMap.snd LL (G → V) (V ⊗[Qp] B))).comp
      (pairs PD ρ).subtype)
    (fun p => GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ p.1.1 p.1.2 p.2.2)

theorem fst_mem_exponential_cocycles (p : pairs PD ρ) (hp : toDcris PD ρ p ∈ LinearMap.range (oneSubφ PD ρ)) :
    (p : (G → V) × (V ⊗[Qp] B)).1 ∈ crystallineCocycles PD ρ := by
  obtain ⟨e, he⟩ := hp
  have he' : (e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e
      = p.1.2 - φVB PD (LL := LL) (V := V) p.1.2 := congrArg Subtype.val he
  refine ⟨p.2.1, p.1.2 - e, ?_, fun g => ?_⟩
  · rw [map_sub]
    calc φVB PD (LL := LL) (V := V) p.1.2 - φVB PD (LL := LL) (V := V) e
        = (p.1.2 - (e : V ⊗[Qp] B)) + (((e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e)
          - (p.1.2 - φVB PD (LL := LL) (V := V) p.1.2)) := by abel
      _ = p.1.2 - e := by rw [he', sub_self, add_zero]
  · have hg := (mem_Dcris_iff PD ρ e).1 e.2 g
    rw [p.2.2 g, map_sub, hg]
    abel

theorem finrank_finite_cocycles_le [Module.Finite LL (Dcris PD ρ)] :
    finrank LL (finiteCocycles PD ρ) ≤ finrank LL (crystallineCocycles PD ρ) +
      finrank LL ↥(Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id)) := by
  by_cases hf : Module.Finite LL (finiteCocycles PD ρ)
  swap
  · rw [Module.finrank_of_not_finite hf]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := (projZ PD ρ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (projZ_surjective PD ρ))
  set N := LinearMap.range (oneSubφ PD ρ) with hN
  let T : finiteCocycles PD ρ →ₗ[LL] (Dcris PD ρ ⧸ N) := N.mkQ ∘ₗ toDcris PD ρ ∘ₗ s
  have hle : crystallineCocycles PD ρ ≤ finiteCocycles PD ρ := fun c ⟨hc, x, _, hx⟩ => ⟨hc, x, hx⟩
  haveI : Module.Finite LL (crystallineCocycles PD ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hmem : ∀ k : LinearMap.ker T, ((k : finiteCocycles PD ρ) : G → V) ∈ crystallineCocycles PD ρ := by
    intro k
    have hk : T k = 0 := LinearMap.mem_ker.1 k.2
    have h := fst_mem_exponential_cocycles PD ρ (s k) ((Submodule.Quotient.mk_eq_zero N).1 hk)
    have hsk : projZ PD ρ (s k) = k := LinearMap.congr_fun hs k
    have hv : ((s k : pairs PD ρ) : (G → V) × (V ⊗[Qp] B)).1 = ((k : finiteCocycles PD ρ) : G → V) :=
      congrArg Subtype.val hsk
    rwa [hv] at h
  have h1 : finrank LL (LinearMap.ker T) ≤ finrank LL (crystallineCocycles PD ρ) := by
    let j : LinearMap.ker T →ₗ[LL] crystallineCocycles PD ρ :=
      LinearMap.codRestrict (crystallineCocycles PD ρ) ((finiteCocycles PD ρ).subtype ∘ₗ (LinearMap.ker T).subtype) hmem
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h2 : finrank LL (LinearMap.range T) ≤ finrank LL (Dcris PD ρ ⧸ N) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank N
  have h4 := LinearMap.finrank_range_add_finrank_ker (oneSubφ PD ρ)
  have h5 := LinearMap.finrank_range_add_finrank_ker T
  set W := Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id) with hW
  haveI : Module.Finite LL W :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : W ≤ Dcris PD ρ))
      (Submodule.inclusion_injective _)
  have hmemW : ∀ k : LinearMap.ker (oneSubφ PD ρ), ((k : Dcris PD ρ) : V ⊗[Qp] B) ∈ W := by
    intro k
    have hk : oneSubφ PD ρ k = 0 := LinearMap.mem_ker.1 k.2
    have hk' : ((k : Dcris PD ρ) : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) (k : Dcris PD ρ) = 0 :=
      congrArg Subtype.val hk
    refine Submodule.mem_inf.2 ⟨(k : Dcris PD ρ).2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [sub_eq_zero] at hk' ⊢
    exact hk'.symm
  have h6 : finrank LL (LinearMap.ker (oneSubφ PD ρ)) ≤ finrank LL W := by
    let j : LinearMap.ker (oneSubφ PD ρ) →ₗ[LL] W :=
      LinearMap.codRestrict W ((Dcris PD ρ).subtype ∘ₗ (LinearMap.ker (oneSubφ PD ρ)).subtype) hmemW
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h7 : finrank LL N = finrank LL (LinearMap.range (oneSubφ PD ρ)) := rfl
  omega

end Generic

end GlobalTheory.HyodoFE

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.HyodoFE.finrank_finite_le_exponential_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  intro l _ P AI _ K V _ _ _ _ _ _ _ ρ _ hdR
  haveI := GlobalTheory.DcrisFin.dcris_finite_of_isDR l P K V ρ hdR
  exact GlobalTheory.HyodoFE.finrank_finite_cocycles_le (P.PD K) ρ
