import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeEqTopOfLiftSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickeninStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnPer.TaylorClause

theorem isSep {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have : IsProper A.hom := h.proper
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
  infer_instance

theorem of_core (core : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn) :
    GlobalTheory.Published.AbelianDeRham.BaseChange → GlobalTheory.Published.AbelianDeRham.Rigid → PTaylor := by
  intro hB hR I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ h₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP D _ _ π κ hκ hπ N t ht hN j hj
    A' _ φ' h' m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g h₀ hA hg
  have hsp := (GlobalTheory.PeriodFamily.isBC_augmented hB hR A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hm : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by rw [hsp]; trivial
  obtain ⟨m, dd, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose cs hcs using fun a ↦ (v a).2
  have n : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    have := m'.isMor.comp (liftMor κ h).isMor
    rwa [RingHom.id_comp, hi] at this
  have hn : n.pull1 c.1 = ∑ a, dd a • k.isMor.pull1 (cs a).1 := by
    rw [← IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor n (fun _ ↦ rfl) hi c.1]
    have := congrArg Subtype.val hv
    rw [Submodule.coe_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hcs a]
    rfl
  have key := core (F₀ := fibFam u₀) e (fibUnif u₀) (isSep 𝒜 hA) (isSep A₀ hA₀) h0 ⟨fun a ↦ a.elim, trivial⟩
    (fun l _ ↦ (hτ l).symm) φ₀ (fun p _ ↦ (hE p.2).symm) D π κ hκ hπ N t ht hN (j : B →+* D) hj
    (A₀.hom ≫ spMap π) (by rw [Category.comp_id]) n (Over.Hom.left (𝟙 A₀)) rfl k.isMor c.1 per hper m dd
    (fun a ↦ (cs a).1) (fun a l ↦ P₀ l (cs a)) _ (fun _ _ ↦ rfl) (fun a ↦ hP (cs a)) hn x
  rw [← key, crysToDR_apply, ← hv, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, ← hcs a, hd, smul_eq_mul]

theorem of_core0 (core : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn) :
    PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ h₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP D _ _ π κ hκ hπ N t ht hN j hj
    A' _ φ' h' m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g h₀ hA hg
  have hsp := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hm : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by rw [hsp]; trivial
  obtain ⟨m, dd, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose cs hcs using fun a ↦ (v a).2
  have n : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    have := m'.isMor.comp (liftMor κ h).isMor
    rwa [RingHom.id_comp, hi] at this
  have hn : n.pull1 c.1 = ∑ a, dd a • k.isMor.pull1 (cs a).1 := by
    rw [← IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor n (fun _ ↦ rfl) hi c.1]
    have := congrArg Subtype.val hv
    rw [Submodule.coe_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hcs a]
    rfl
  have key := core (F₀ := fibFam u₀) e (fibUnif u₀) (isSep 𝒜 hA) (isSep A₀ hA₀) h0 ⟨fun a ↦ a.elim, trivial⟩
    (fun l _ ↦ (hτ l).symm) φ₀ (fun p _ ↦ (hE p.2).symm) D π κ hκ hπ N t ht hN (j : B →+* D) hj
    (A₀.hom ≫ spMap π) (by rw [Category.comp_id]) n (Over.Hom.left (𝟙 A₀)) rfl k.isMor c.1 per hper m dd
    (fun a ↦ (cs a).1) (fun a l ↦ P₀ l (cs a)) _ (fun _ _ ↦ rfl) (fun a ↦ hP (cs a)) hn x
  rw [← key, crysToDR_apply, ← hv, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, ← hcs a, hd, smul_eq_mul]

theorem pTaylor : GlobalTheory.Published.AbelianDeRham.BaseChange → GlobalTheory.Published.AbelianDeRham.Rigid → PTaylor := of_core GlobalTheory.AnPer.TaylorCore.main

theorem pTaylor0 : PTaylor := of_core0 GlobalTheory.AnPer.TaylorCore.main

end GlobalTheory.AnPer.TaylorClause
