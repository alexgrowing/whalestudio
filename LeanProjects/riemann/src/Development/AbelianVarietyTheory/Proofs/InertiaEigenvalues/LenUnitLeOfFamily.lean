import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.EtaFromCut

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths IsDiscreteValuationRing

section General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem congMod_le_of_family (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = 0) :
    Module.length O (CongMod T (actK T act).toRingHom (latIn O M) (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) * addVal O (a x) := by
  have hspan := eigSpan T act hsep
  have hcK : ∀ α ∈ E, ∀ f : T, α.baseChange (FractionRing O) * (actK T act).toRingHom f =
      (actK T act).toRingHom f * α.baseChange (FractionRing O) := by
    intro α hα f
    show α.baseChange (FractionRing O) * (act f).baseChange (FractionRing O) =
      (act f).baseChange (FractionRing O) * α.baseChange (FractionRing O)
    rw [← LinearMap.baseChange_mul, hc α hα f, LinearMap.baseChange_mul]
  refine congMod_le hspan (latIn O M) fg_latIn S ((fun α => α.baseChange (FractionRing O)) '' E)
    (fun x => addVal O (a x)) ?_ ?_ ?_ ?_
  · rintro _ ⟨α, hα, rfl⟩ f
    exact hcK α hα f
  · rintro _ ⟨α, hα, rfl⟩ v hv
    exact baseChange_latIn α v hv
  · rintro _ ⟨α, hα, rfl⟩ v _
    have hle : (⨆ x, Vx T (actK T act).toRingHom x) ≤
        (Formalism.NG.VS T (actK T act).toRingHom (S : Set X)).comap (α.baseChange (FractionRing O)) := by
      refine iSup_le fun x u hu => ?_
      rw [Submodule.mem_comap]
      by_cases hx : x ∈ S
      · refine le_iSup₂ (f := fun y (_ : y ∈ (S : Set X)) => Vx T (actK T act).toRingHom y) x hx ?_
        refine mem_Vx.mpr fun f => ?_
        rw [← Module.End.mul_apply, ← hcK α hα f, Module.End.mul_apply, mem_Vx.mp hu f,
          LinearMap.map_smul_of_tower]
      · rw [h0 α hα x hx u hu]
        exact zero_mem _
    rw [hspan] at hle
    exact hle (Submodule.mem_top (x := v))
  · intro x hx
    obtain ⟨α, hα, h⟩ := h1 x hx
    exact ⟨_, ⟨α, hα, rfl⟩, a x, h, le_rfl⟩

theorem lenUnit_le_of_family (l : ℕ) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O) (ha : ∀ x ∈ S, a x ≠ 0)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    lenUnit (O := O) l
        (↥((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
            (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O) ⧸
          (latIn O M ⊓ (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).comap
            ((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
              (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).subtype) ≤
      ∑ π ∈ S, (heckeMult T act π : ℚ) * lenUnit (O := O) l (O ⧸ Ideal.span {a π}) := by
  have hE : heckeEig T act = Vx T (actK T act).toRingHom := funext (heckeEig_eq T act)
  rw [hE] at h1 h0
  have hlen := (len_le T act hsep (latIn O M) S).trans
    (congMod_le_of_family T act hsep S E a hc h1 h0)
  simp only [heckeMult, lenUnit, IdempotentNormalFormsLenFacts.length_quot_span]
  rw [hE]
  have hsum : ∑ x ∈ S, (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) *
        addVal O (a x) =
      ((∑ x ∈ S, Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) *
        (addVal O (a x)).toNat : ℕ) : ℕ∞) := by
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ENat.natCast_toNat (fun h => ha x hx (addVal_eq_top_iff.mp h))]
  rw [hsum] at hlen
  have hnat := ENat.toNat_le_of_le_natCast hlen
  simp only [← mul_div_assoc, ← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast hnat

end General

theorem etaBound_of_fam : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceFamilyEndomorphisms CT i k ρ eta → EtaBound CT i k ρ eta := by
  rintro D CT i k ρ eta ⟨E, a, c, hE, hg⟩
  refine ⟨c, ?_, fun π hπ => (hg π hπ).2.2.2⟩
  rw [etaLoc_eq]
  refine (lenUnit_le_of_family (D.nd.T i) (D.nd.act i) (D.nd.l i) (D.nd.T_sep i) (D.nd.Zgood i) E a
    (fun π hπ => (hg π hπ).1) (fun α hα => (hE α hα).1) (fun π hπ => (hg π hπ).2.1)
    (fun α hα => (hE α hα).2)).trans ?_
  exact Finset.sum_le_sum fun π hπ =>
    mul_le_mul_of_nonneg_left (hg π hπ).2.2.1 (Nat.cast_nonneg _)

theorem etaBound_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceLocalDecomposition CT i k ρ eta → EtaBound CT i k ρ eta :=
  fun D CT i k ρ eta h => etaBound_of_fam D CT i k ρ eta (GlobalTheory.CutFam.fam_of_cut D CT i k ρ eta h)

end GlobalTheory.EtaFromCut
