import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuasiFiniteLocal

theorem finite_quotient_of_pow_le_of_span {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (T : Set S) (hT : T.Finite)
    (h : ∀ s : S, ∃ t ∈ Submodule.span A T, s - t ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (Set.image2 (· * ·) T (G : Set S)),
        hF.sup (Submodule.fg_span (hT.image2 _ G.finite_toSet)), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨t, ht, ha⟩ := h (c y)
      have e : c y • y = t * y + y * (c y - t) := by rw [smul_eq_mul]; ring
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · have hmul : ∀ u ∈ Submodule.span A T,
            u * y ∈ Submodule.span A (Set.image2 (· * ·) T (G : Set S)) := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu => exact Submodule.subset_span (Set.mem_image2_of_mem hu hy)
          | zero => simp
          | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
          | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
        exact hmul t ht
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem finite_of_quasiFinite : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  intro A R _ _ _ _ _ _ b _ hc hq hres
  letI : Algebra A R := b.toAlgebra
  have hb : algebraMap A R = b := rfl
  have hle : (maximalIdeal A).map (algebraMap A R) ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, hb, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit b a h)
  have hrad : maximalIdeal R ≤ ((maximalIdeal A).map (algebraMap A R)).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun p ⟨hJp, hp⟩ => (hq p hp hJp).ge
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

  obtain ⟨T0, hT0⟩ : (⊤ : Submodule A (ResidueField R)).FG := by
    letI : Algebra A (ResidueField R) := ((residue R).comp b).toAlgebra
    exact hres.fg_top
  classical
  let lift : ResidueField R → R := Function.surjInv (residue_surjective (R := R))
  have hlift : ∀ t, residue R (lift t) = t := Function.surjInv_eq _
  let L : R →ₗ[A] ResidueField R :=
    { toFun := residue R
      map_add' := map_add _
      map_smul' := fun a x => by
        show residue R (b a * x) = residue R (b a) * residue R x
        exact map_mul _ _ _ }
  have hfin : Module.Finite A (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
    refine finite_quotient_of_pow_le_of_span (I := maximalIdeal R) (lift '' (T0 : Set _))
      ((T0.finite_toSet).image _) (fun s => ?_) hN
    have hs : residue R s ∈ Submodule.map L (Submodule.span A (lift '' (T0 : Set _))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      have e : (⇑L ∘ lift) = id := funext fun t => hlift t
      rw [e, Set.image_id, hT0]
      trivial
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 hts.symm
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A R)) R :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  haveI := hc
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

end GlobalTheory.QuasiFiniteLocal
