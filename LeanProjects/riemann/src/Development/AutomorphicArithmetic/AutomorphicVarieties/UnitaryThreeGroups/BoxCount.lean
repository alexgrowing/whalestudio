import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDecompositionFieldFrobeniusData
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CohomologyOfFiniteRepresentation
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LocalEulerCharacteristicOfPrimeNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GlobalEulerCharacteristicOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GlobalEulerCharRatOfNeTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FrameCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Matrix IsLocalRing Module
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem res_surj {k G H M : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    [AddCommGroup M] [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
    (ρ : Representation k G M) (e : H ≃* G) (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (resH2 ρ e.toMonoidHom he) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    refine ⟨Submodule.Quotient.mk ⟨fun p => c.1 (e.symm p.1, e.symm p.2), c.2.1.comp (he'.prodMap he'),
      fun g g' g'' => ?_⟩, congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))⟩
    · have := c.2.2 (e.symm g) (e.symm g') (e.symm g'')
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] at this
      simp only [map_mul]
      exact this
    · show c.1 (e.symm (e p.1), e.symm (e p.2)) = c.1 p
      rw [e.symm_apply_apply, e.symm_apply_apply]

private theorem contAction_of_open {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M)
    (h : IsOpen (ρ.ker : Set G)) : ContAction ρ := by
  refine continuous_prod_of_discrete_right.2 fun m => IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, h.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h1 : ρ (g⁻¹ * x) = 1 := hx
  show ρ x m = ρ g m
  rw [← mul_inv_cancel_left g x, map_mul, h1, mul_one]

private theorem contAction_comp {k G H M : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [AddCommGroup M] [Module k M] [TopologicalSpace M] (ρ : Representation k G M)
    (h : ContAction ρ) (φ : H →* G) (hφ : Continuous φ) : ContAction (ρ.comp φ : Representation k H M) :=
  Continuous.comp h (hφ.prodMap continuous_id)

private theorem arith {h0 h1c L1 Q1 h2 L0 h1 Q0 ob L2 Q2 d f : ℕ}
    (c3 : h0 + h1c + L1 + Q1 + h2 + 0 = L0 + h1 + Q0 + ob + L2 + Q2) (e1 : Q1 = Q0 + Q2) (e2 : L1 = L0 + L2 + d)
    (g3 : h0 + h2 + d = h1 + f) : ob = h1c + f := by omega

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.U3.box_count (hI : CohInp) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] (hl : l ≠ 2)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (hS : ContainsAbove S l)
    (hA : ∀ v, IsPlaceOver (A v) v.1) (hv : ∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀)
    (ι : GQ l →* G ℚ Ω) (hι : Continuous ι) (hinj : Function.Injective ι) (hr : ι.range = Dec (F := ℚ) (A v₀))
    (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M)
    (hρ : IsOpen (ρ.ker : Set (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))))))
    [Fintype {v : S // v ≠ v₀}] (N : {v : S // v ≠ v₀} → Subgroup (G ℚ Ω)) (hN1 : ∀ q, N q ≤ Ine (F := ℚ) (A q))
    (hN2 : ∀ q, ((N q).subgroupOf (Dec (F := ℚ) (A q))).Normal) (hN3 : ∀ q, IsClosed (N q : Set (G ℚ Ω)))
    (hN4 : ∀ q, ∀ n ∈ N q, ρ (toGS Ω _ n) = 1) (hN5 : ∀ q, ¬ l ∣ (N q).relIndex (Ine (F := ℚ) (A q)))
    (hg : ∃ g : G ℚ Ω, cycMod ℚ Ω l 1 g = -1 ∧ ρ (toGS Ω _ g) = 1)
    (σ : G ℚ Ω) (hσ : ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x)) :
    Module.Finite k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).Ob ρ) ∧
      finrank k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).Ob ρ) =
        finrank k ((unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N).H1c ρ) +
          finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : IsTopologicalAddGroup M :=
    { continuous_add := continuous_of_discreteTopology, continuous_neg := continuous_of_discreteTopology }
  haveI : ContinuousConstSMul k M := ⟨fun _ => continuous_of_discreteTopology⟩
  letI : Algebra ℤ_[l] k := ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod).toAlgebra
  have hπ := continuous_toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))
  have hc := contAction_of_open ρ hρ
  set F := unitFrame (toGS Ω _) (continuous_toGS Ω _) ι hι (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) N with hF
  obtain ⟨g1, g2, g3⟩ := UpperTheory.global_euler_char_rat_of_ne_two hI.gf hI.ge Ω l k M hl S hS ρ hc σ hσ
  obtain ⟨l1, l2, l3, -⟩ := Loc.tateFin hI.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id k M
    (ρ.comp ((toGS Ω _).comp ι)) (contAction_comp ρ hc _ (hπ.comp hι))
  rw [if_pos rfl, MonoidHom.range_eq_top.2 Function.surjective_id, Subgroup.index_top, one_mul] at l3
  have hq : ∀ q : {v : S // v ≠ v₀}, _ := fun q => UpperTheory.local_euler_characteristic_of_prime_not_mem hI.loc.lf hI.loc.le Ω l k M (A q) q.1.1 (hA q)
    (fun h => q.2 ((hv q).1 h)) (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A q)).subtype))
    (contAction_comp ρ hc _ (hπ.comp continuous_subtype_val))
  have hur : ∀ q : {v : S // v ≠ v₀}, finrank k (H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) =
      finrank k (H0 (ρ.comp (F.ψ q) : Representation k _ M)) := fun q => by
    obtain ⟨d1, d2, d3, d4, d5⟩ := UpperTheory.exists_decompositionField_frobenius_data Ω (A q) q.1.1 (hA q)
    haveI := hN2 q
    refine UpperTheory.cohomology_of_finite_representation l k M (Dec (F := ℚ) (A q)) (ρ.comp (F.ψ q)) (hρ.preimage (F.hψ q)) _ _ (d3.preimage continuous_subtype_val)
      ((hN3 q).preimage continuous_subtype_val) (fun x hx => hN1 q hx) (fun x hx => hN4 q x hx) ?_ d4
      fun n => d5 _ (pow_pos (Fact.out : l.Prime).pos n)
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _)]
    exact hN5 q
  have hsurj : LinearMap.range ((LinearMap.pi fun v => resH2 ρ (F.φ v) (F.hφ v)).prod
      (LinearMap.pi fun q => resH2 ρ (F.ψ q) (F.hψ q))) = ⊤ := by
    classical
    rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    let e : GQ l ≃* Dec (F := ℚ) (A v₀) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
    have he : Continuous e := hι.subtype_mk _
    have he' : Continuous e.symm := (he.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous
    obtain ⟨x', hx'⟩ := res_surj (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v₀)).subtype)) e he he' (x ())
    obtain ⟨z, hz⟩ := UpperTheory.global_euler_characteristic_odd hI.pt Ω l k M hl S A hS hA ρ hc hg
      fun v => if h : v = v₀ then h ▸ x' else y ⟨v, h⟩
    refine ⟨z, Prod.ext (funext fun _ => ?_) (funext fun q => ?_)⟩
    · have h0 := hz v₀
      rw [dif_pos rfl] at h0
      have h1 : _ = x' := h0
      refine Eq.trans ?_ hx'
      rw [← h1]
      induction z using Submodule.Quotient.induction_on with
      | H c => rfl
    · have h0 := hz q.1
      rw [dif_neg q.2] at h0
      exact h0
  obtain ⟨-, c2, c3⟩ := frame_count k _ M ρ hρ F (fun q n hn => hN4 q n hn) g1 g2 (fun _ => ⟨l1, l2⟩)
    fun q => ⟨(hq q).1, (hq q).2.1⟩
  refine ⟨c2, ?_⟩
  rw [@finrank_zero_of_subsingleton k _ _ _ _ _ (Submodule.Quotient.subsingleton_iff.2 hsurj), Finset.sum_congr rfl fun q _ => hur q] at c3
  have e1 : ∑ q, finrank k (H1 (ρ.comp (F.ψ q) : Representation k _ M)) =
      ∑ q, finrank k (H0 (ρ.comp (F.ψ q) : Representation k _ M)) +
        ∑ q, finrank k (H2 (ρ.comp (F.ψ q) : Representation k _ M)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => (hq q).2.2
  have e2 : ∑ v, finrank k (H1 (ρ.comp (F.φ v) : Representation k _ M)) =
      ∑ v, finrank k (H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        ∑ v, finrank k (H2 (ρ.comp (F.φ v) : Representation k _ M)) + finrank k M := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact l3
  exact arith c3 e1 e2 g3
