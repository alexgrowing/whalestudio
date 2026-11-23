import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SmGL.DepthZero GlobalTheory.LocLanglands.SphFac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5

namespace LevelFixedParabolic

section Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem fixed_ne_bot_mono {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H K : Subgroup G} (hle : H ≤ K) (h : fixed ρ K ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, hle g.2⟩, hv0⟩

variable (k n) in

def coreH (K : Subgroup (GL n k)) : Subgroup (GL n k) :=
  ((K.subgroupOf (KO k n)).normalCore).map (KO k n).subtype

theorem coreH_le (K : Subgroup (GL n k)) : coreH k n K ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hy)

theorem conj_mem_coreH (K : Subgroup (GL n k)) {c : GL n k} (hc : c ∈ KO k n) {x : GL n k}
    (hx : x ∈ coreH k n K) : c⁻¹ * x * c ∈ coreH k n K := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(⟨c, hc⟩ : KO k n)⁻¹ * y * (⟨c, hc⟩ : KO k n)⁻¹⁻¹,
    (Subgroup.normalCore_normal _).conj_mem y hy _, ?_⟩
  simp

theorem KO_le_coreH {K : Subgroup (GL n k)} (hK : KO k n ≤ K) : KO k n ≤ coreH k n K := by
  intro x hx
  have htop : K.subgroupOf (KO k n) = ⊤ := Subgroup.subgroupOf_eq_top.2 hK
  have hc : (⊤ : Subgroup (KO k n)) ≤ (K.subgroupOf (KO k n)).normalCore :=
    Subgroup.normal_le_normalCore.2 (by rw [htop])
  exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, hc (Subgroup.mem_top _), rfl⟩

theorem isOpen_coreH {K : Subgroup (GL n k)} (hK : IsOpen (K : Set (GL n k))) :
    IsOpen (coreH k n K : Set (GL n k)) := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  have hU : IsOpen ((K.subgroupOf (KO k n) : Subgroup (KO k n)) : Set (KO k n)) :=
    hK.preimage continuous_subtype_val
  haveI : Finite (KO k n ⧸ K.subgroupOf (KO k n)) := Subgroup.quotient_finite_of_isOpen _ hU
  haveI : (K.subgroupOf (KO k n)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hC : IsClosed (((K.subgroupOf (KO k n)).normalCore : Subgroup (KO k n)) : Set (KO k n)) :=
    Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hU)
  have hO := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hC
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 hO
  convert ht.inter GlobalTheory.SplitFlip.isOpen_KO using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyt : y ∈ Subtype.val ⁻¹' t := by rw [hts]; exact hy
    exact ⟨hyt, y.2⟩
  · rintro ⟨hxt, hxK⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have : (⟨x, hxK⟩ : KO k n) ∈ Subtype.val ⁻¹' t := hxt
    rw [hts] at this
    exact this

variable (k) in

def Ki (e : (Σ a, m a) ≃ n) (H : Subgroup (GL n k)) (a : α) : Subgroup (GL (m a) k) :=
  H.comap ((leviEmb k e).comp (MonoidHom.mulSingle (fun b => GL (m b) k) a)) ⊓ KO k (m a)

theorem isOpen_Ki (e : (Σ a, m a) ≃ n) {H : Subgroup (GL n k)} (hH : IsOpen (H : Set (GL n k))) (a : α) :
    IsOpen (Ki k e H a : Set (GL (m a) k)) := by
  have hc : Continuous ((leviEmb k e).comp (MonoidHom.mulSingle (fun b => GL (m b) k) a)) :=
    (continuous_leviEmb k e).comp (continuous_mulSingle (A := fun b => GL (m b) k) a)
  exact (hH.preimage hc).inter GlobalTheory.SplitFlip.isOpen_KO

theorem KO_le_Ki (e : (Σ a, m a) ≃ n) {H : Subgroup (GL n k)} (hH : KO k n ≤ H) (a : α) :
    KO k (m a) ≤ Ki k e H a := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (hH (leviEmb_mem_KO' (g := Pi.mulSingle a x) e fun b => ?_)), hx⟩
  by_cases hb : b = a
  · subst hb; simpa using hx
  · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

theorem exists_fixed_of_parInd_H (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) (H : Subgroup (GL n k))
    (hH : ∀ c ∈ KO k n, ∀ x ∈ H, c⁻¹ * x * c ∈ H)
    {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) H) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KO k (m a)) → leviEmb k e g ∈ H → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg hgH => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one_of_KO hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨c⁻¹ * leviEmb k e g * c, hH c hc _ hgH⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem exists_fixed_factor (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (H : Subgroup (GL n k))
    (hH : ∀ c ∈ KO k n, ∀ x ∈ H, c⁻¹ * x * c ∈ H)
    (hv : fixed (multiProd e σ) H ≠ ⊥) (a : α) : fixed (σ a) (Ki k e H a) ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hv
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd_H e (piTensor σ) H hH hf hf0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine (Submodule.ne_bot_iff _).2 ⟨_, fun g => ?_, hφ⟩
  have hg := Subgroup.mem_inf.1 g.2
  rw [← contract_piTensor, hw (Pi.mulSingle a g) (fun b => ?_) (Subgroup.mem_comap.1 hg.1)]
  · simp
  · by_cases hb : b = a
    · subst hb; simpa using hg.2
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end Gen

end LevelFixedParabolic

open LevelFixedParabolic in
theorem levelFactor : LevelFactor := by
  intro E _ _ _ w c n N h K hK
  have hKO : ∀ m, GlobalTheory.LFun.KGL w m = KO (w.adicCompletion E) (Fin m) := fun m =>
    (GlobalTheory.SmGL.SphCompletion.KO_completion w m).symm
  refine ⟨Ki (m := fun i => Fin (N i)) (w.adicCompletion E) (stdBlocks N h) (coreH (w.adicCompletion E) (Fin n) K),
    fun i => isOpen_Ki (stdBlocks N h) (isOpen_coreH hK) i, fun hle i => ?_, fun σ hσ i => ?_⟩
  · rw [hKO n] at hle
    rw [hKO (N i)]
    exact KO_le_Ki (stdBlocks N h) (KO_le_coreH hle) i
  · exact exists_fixed_factor (stdBlocks N h) (fun i => (σ i).ρ) _ (fun c hc x hx => conj_mem_coreH K hc hx)
      (fixed_ne_bot_mono (coreH_le K) hσ) i

end PositivityTheory.Rg.BcB.F.F5

end
