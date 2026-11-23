import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.ZonalBorel

open GlobalTheory.PRep Formalism.UG

section Abstract

variable {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_sum_eq {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) {v : V} (hv : v ∈ fixed π K)
    (l : Module.Dual ℂ V) (hlv : l v = 1) :
    ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ∑ c ∈ S, l (π c.out v) = ∑ c ∈ S, E (ρ c.out z) := by
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw' : f w = f u := hfw
  have hEw : E w ≠ 0 := fun h => by
    have h0 := hE w hw' h
    rw [h0, map_zero] at hfw'
    rw [← hfw', map_zero] at hlv
    exact zero_ne_one hlv
  refine ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], fun S hS => ?_⟩
  set z := (E w)⁻¹ • w with hz
  have hzK : ∀ x ∈ K, ρ x z = z := fun x hx => by rw [hz, map_smul, hw' x hx]
  have hEz : E z = 1 := by simp [hz, hEw]
  have hfz : f z = (E w)⁻¹ • f u := by rw [hz, map_smul, hfw']
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, Rep.sum_fixed ρ K hzK S hS x hx, map_smul, hzK x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg (fun y => l (f y)) (sub_eq_zero.1 h1)
  have hI : ∀ c : G ⧸ K, f (ρ c.out z) = π c.out (f z) := fun c => f.isIntertwining _ _ _ _
  simp only [map_sum, map_smul, hI, hfz, smul_eq_mul, hlv, mul_one] at h2
  rw [← Finset.mul_sum] at h2
  exact (mul_right_injective₀ (inv_ne_zero hEw)).eq_iff.1 (h2.trans (mul_comm _ _))

end Abstract

theorem exists_isBorelSph_hAct_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  intro k _ _ _ _ n V _ _ π α ⟨_, _hs, S, f, hf⟩ ω ⟨v, hv, l, _hl, hlv, hω⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨z, hzK, hEz, key⟩ := exists_fixed_sum_eq hsm SplitFlip.isCompact_KO f hf E (fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1) hv l hlv
  refine ⟨fun g => z.1.1.1 g, ⟨hr z hzK, fun b hb t ht => ?_⟩, fun g => ?_⟩
  · have h1 := Rep.law α z.1 b hb t ht 1
    have h2 : z.1.1.1 1 = 1 := hEz
    rwa [h2, mul_one, mul_one] at h1
  · have hK : IsCommensurated (KO k (Fin n)) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ SplitFlip.isOpen_KO SplitFlip.isCompact_KO
    have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem _ (KO k (Fin n)) ℂ g).2
    have hmem : ∀ c : GL (Fin n) k ⧸ KO k (Fin n), c ∈ hfin.toFinset ↔
        c.out ∈ DoubleCoset.doubleCoset g (KO k (Fin n) : Set (GL (Fin n) k)) (KO k (Fin n)) := fun c => by
      simp [dosetInd]
    have hT : ∀ x ∈ KO k (Fin n), ∀ c ∈ hfin.toFinset, x • c ∈ hfin.toFinset := by
      intro x hx c hc
      obtain ⟨a, ha, rfl⟩ := (GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g c).1 ((hmem c).1 hc)
      refine (hmem _).2 ((GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g _).2 ⟨x * a, mul_mem hx ha, ?_⟩)
      rw [mul_assoc]
      rfl
    have e : ∀ F : GL (Fin n) k → ℂ, hAct (KO k (Fin n)) (dosetInd ℂ (KO k (Fin n)) g) F 1 =
        ∑ c ∈ hfin.toFinset, F c.out := by
      intro F
      rw [hAct, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [dosetInd, Set.indicator_of_mem ((hmem c).1 hc), one_mul, Pi.one_apply, one_smul]
      · intro c hc
        rw [Function.mem_support] at hc
        refine (hmem c).2 ?_
        by_contra h
        rw [dosetInd, Set.indicator_of_notMem h, zero_smul] at hc
        exact hc rfl
    rw [e, e]
    refine ((Finset.sum_congr rfl fun c _ => hω c.out).trans (key _ hT)).trans
      (Finset.sum_congr rfl fun c _ => ?_)
    show z.1.1.1 (1 * c.out) = _
    rw [one_mul]

end GlobalTheory.ZonalBorel
