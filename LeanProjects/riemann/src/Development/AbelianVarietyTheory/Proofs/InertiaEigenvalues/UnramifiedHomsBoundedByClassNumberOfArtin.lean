import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.UnramifiedHomBound

noncomputable def homToH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    U →ₗ[O] NG.H1z (Representation.trivial O G M) :=
  (Submodule.mkQ _).comp (Submodule.inclusion
    (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h))

theorem homToH1_injective {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    Function.Injective (homToH1 U hU) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  apply Subtype.ext
  funext g
  have h := congrFun hv g
  have h2 : NG.coD0 (Representation.trivial O G M) v g = 0 := by simp [NG.coD0]
  exact h.symm.trans h2

theorem homToH1_mem_unrH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) (I : Subgroup G)
    (c : U) (hc : ∀ g ∈ I, (c : G → M) g = 0) :
    homToH1 U hU c ∈ RepresentationBoundsCohomology.BR.unrH1 (Representation.trivial O G M) I := by
  change NG.resH1 (Representation.trivial O G M) I (Submodule.Quotient.mk _) = 0
  rw [NG.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  have h : NG.restrictCocycles1 (Representation.trivial O G M) I (Submodule.inclusion
      (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h) c)
      = 0 := Subtype.ext (funext fun g => hc g g.2)
  rw [h]
  exact Submodule.zero_mem _

theorem l_ne_zero (D : D7) (i : D.nd.Loc) : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := by
  have : CharZero (FractionRing (D.nd.O i)) :=
    charZero_of_injective_ringHom (D.nd.embK i).injective
  intro h
  have h2 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
  rw [map_natCast, map_zero] at h2
  exact (Fact.out : (D.nd.l i).Prime).ne_zero (Nat.cast_eq_zero.1 h2)

theorem length_unrHom_le (h : ReciprocityTheory.ChartRestriction.T2.VhE) (D : D7) (i : D.nd.Loc) :
    Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) ≤
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) *
        (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hU : ∀ c ∈ TruncatedSeriesCountingIdentities.unrHom i, ∀ g h, c (g * h) = c g + c h := fun c hc => hc.2.1
  rw [(LinearEquiv.ofInjective _ (homToH1_injective _ hU)).length_eq]
  refine h D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2 (D.nd.l i) (D.nd.O i)
    (Or.inr (IsTotallyComplex.nrRealPlaces_eq_zero _)) (KmodO (D.nd.O i))
    ⟨Submodule.quotEquivOfEq _ _ (Submodule.one_eq_range).symm⟩ _ (fun _ _ => rfl) _ ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl, c.2.1⟩
  · rintro v _ ⟨c, rfl⟩
    exact homToH1_mem_unrH1 _ hU _ c (c.2.2.2 v)

theorem unramified_homs_bounded_by_class_number_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  intro hA D i
  have h := length_unrHom_le (GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA) D i
  have hfin : Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) ≠ ⊤ :=
    Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (l_ne_zero D i)))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hfin
  have hlt : Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    rw [← he, ← Nat.cast_mul]
    exact ENat.natCast_lt_top _
  refine ⟨hlt, ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
  rw [← he, ← hn, ← Nat.cast_mul, Nat.cast_le] at h
  unfold lenUnit
  rw [← he, ← hn, ENat.toNat_natCast, ENat.toNat_natCast]
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  rw [mul_comm]
  exact_mod_cast h

end GlobalTheory.UnramifiedHomBound
