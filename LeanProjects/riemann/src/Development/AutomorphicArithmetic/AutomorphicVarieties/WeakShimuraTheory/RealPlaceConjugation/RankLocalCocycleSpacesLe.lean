import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.TowerPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardLocalCocyclesLeOfPlaceAbovePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.SumDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOpenPreimage

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem lc_of_open {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOpenPreimage.lc_of_open ψ h

private def scalRep {k Γ : Type} [Field k] [Group Γ] (γ : Γ →* kˣ) : Representation k Γ k where
  toFun g := (γ g : k) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

theorem UpperTheory.V.Ws.rank_localCocycleSpaces_le :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (g : ℕ), (plDvd T.F (prodS D)).ncard ≤ g → Nat.card T.ι ≤ g ∧ ∀ w, Module.rank (ResidueField c.O) (∀ v, (T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w) ≤ T.d + (2 * g : ℕ) := by
  intro P Ω _ _ _ l hl c D hD T g hg
  haveI : IsAlgClosure T.F Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  obtain ⟨pl, hinj, hpl⟩ := exists_injective_places_above_l_of_tower D T
  obtain ⟨-, hKo, -, -, hK1, hK2, ⟨h0, hlS⟩, -, -⟩ := residualKernel_properties D hD T
  have hfin : (plDvd T.F (prodS D)).Finite := by
    have hne : Ideal.span {((prodS D : ℕ) : 𝓞 T.F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 h0
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hmem : ∀ v, pl v ∈ plDvd T.F (prodS D) := fun v => by
    obtain ⟨m, hm⟩ := hlS
    show ((prodS D : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hpl v).2
  have hcard : Nat.card T.ι ≤ g := by
    haveI := hfin.to_subtype
    refine le_trans ?_ hg
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun v => (⟨pl v, hmem v⟩ : plDvd T.F (prodS D)))
      fun a b h => hinj (congrArg Subtype.val h)
  refine ⟨hcard, fun w => ?_⟩
  have hl0 : ((l : ℕ) : ResidueField c.O) = 0 := by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  have hlc : IsLocallyConstant (T.rbU w) :=
    lc_of_open _ (Subgroup.isOpen_mono (fun x hx => hK2 w x (hK1 x hx)) hKo)
  have hv : ∀ v : T.ι, CardLe ((T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w)
      (Nat.card (ResidueField c.O) ^ (2 + locDeg (pl v))) := fun v => by
    have h := card_localCocycles_le_of_place_above_prime P.loc.lf P.loc.lt P.loc.le T.F Ω l (ResidueField c.O) (ResidueField c.O)
      (fun m => by rw [nsmul_eq_mul, hl0, zero_mul]) (T.pl v) (pl v)
      (scalRep ((T.rbU w).comp (Dec (F := T.F) (T.pl v)).subtype)) (hpl v).1 (hpl v).2
      (fun m => (hlc.comp_continuous continuous_subtype_val).comp fun u => (u : ResidueField c.O) • m)
    exact h.of_injective (fun z => ⟨z.1, z.2.1, z.2.2, fun _ h => h.elim⟩)
      fun a b h => Subtype.ext (Subtype.mk.inj h)
  haveI : Fintype T.ι := Fintype.ofFinite _
  haveI : Finite (T.fr ∅).ι := T.fin
  have hsum : ∑ v : T.ι, (2 + locDeg (pl v)) ≤ T.d + 2 * g := by
    have h1 := sum_local_degree_above_l_le_finrank T.F l (Finset.univ.map ⟨pl, hinj⟩)
    rw [Finset.sum_map] at h1
    simp only [Function.Embedding.coeFn_mk, (hpl _).2, if_true] at h1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
    have : T.d = Module.finrank ℚ T.F := rfl
    omega
  have hC : CardLe (∀ v : T.ι, (T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w)
      (Nat.card (ResidueField c.O) ^ (T.d + 2 * g)) := by
    haveI := fun v => (hv v).1
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_pi]
    refine (Finset.prod_le_prod' fun v _ => (hv v).2).trans ?_
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right Nat.card_pos hsum
  have := rank_le_of_card_le_pow_card_field (ResidueField c.O) _ _ hC
  rw [Nat.cast_add] at this
  exact this
