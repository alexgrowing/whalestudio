import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

namespace RatioDim

abbrev graphIdxFintype (N m : ℕ) : ∀ c, Fintype (graphIdx N m c)
  | Sum.inl () => inferInstanceAs (Fintype (Fin (N + 1)))
  | Sum.inr () => inferInstanceAs (Fintype (Fin m))

attribute [local instance] graphIdxFintype

variable {k : Type} [Field k] {N m : ℕ}

abbrev baseRen (k : Type) [Field k] (N m : ℕ) :
    Kleiman.Poly k N →ₐ[k] NumbersDVR.MRing (graphIdx N m) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

variable (W : Ideal (NumbersDVR.MRing (graphIdx N m) k))

def phi : Kleiman.Poly k N →ₐ[k] FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) :=
  (IsScalarTower.toAlgHom k _ _).comp ((Ideal.Quotient.mkₐ k W).comp (baseRen k N m))

theorem phi_apply (f : Kleiman.Poly k N) :
    phi W f = algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W)
      (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) (Ideal.Quotient.mk W (baseRen k N m f)) := rfl

theorem baseRen_X (a : Fin (N + 1)) : baseRen k N m (X a) = X ⟨baseBlock, a⟩ := rename_X _ _

theorem baseRen_C (c : k) : baseRen k N m (C c) = C c := rename_C _ _

abbrev eta (b : Fin m) : FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) :=
  algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W) _ (Ideal.Quotient.mk W (X ⟨Sum.inr (), b⟩))

theorem map_eq_zero_iff (f : NumbersDVR.MRing (graphIdx N m) k) :
    algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W) (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W))
      (Ideal.Quotient.mk W f) = 0 ↔ f ∈ W := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem ker_phi : RingHom.ker (phi W) = W.comap (baseRen k N m) := by
  ext f
  rw [RingHom.mem_ker, phi_apply, map_eq_zero_iff, Ideal.mem_comap]

abbrev bideg (d c : ℕ) : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => d) (fun _ => c)

theorem isMultiHomog_term (F : Kleiman.Poly k N) (d c : ℕ) (b : Fin m) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (graphIdx N m))
      (baseRen k N m (homogeneousComponent d F) * X ⟨Sum.inr (), b⟩ ^ c) (bideg d c) := by
  have h1 : IsWeightedHomogeneous (NumbersDVR.blockWeight (graphIdx N m))
      (baseRen k N m (homogeneousComponent d F)) (Sum.elim (fun _ => d) (fun _ => 0)) := by
    rw [rename_base_homogeneousComponent]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have h2 := (isWeightedHomogeneous_X k (NumbersDVR.blockWeight (graphIdx N m))
    (⟨Sum.inr (), b⟩ : Σ c, graphIdx N m c)).pow c
  convert h1.mul h2 using 1
  funext x
  rcases x with ⟨⟩ | ⟨⟩ <;> simp [NumbersDVR.blockWeight]

theorem transcendental_eta [W.IsPrime] (hH : NumbersDVR.IsMultiHomogIdeal W) (j : Fin m)
    (hj : (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W) :
    Transcendental (phi W).range (eta W j) := by
  classical
  rw [transcendental_iff]
  intro p hp
  have hq : ∀ c, ∃ f, phi W f = ((p.coeff c : (phi W).range) :
      FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) := fun c => (p.coeff c).2
  choose f hf using hq
  set Y := (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) with hY
  set s := p.support
  set G := ∑ c ∈ s, ∑ d ∈ Finset.range ((f c).totalDegree + 1),
    baseRen k N m (homogeneousComponent d (f c)) * Y ^ c with hGdef
  have hGc : ∀ c, ∑ d ∈ Finset.range ((f c).totalDegree + 1),
      baseRen k N m (homogeneousComponent d (f c)) * Y ^ c = baseRen k N m (f c) * Y ^ c := by
    intro c
    rw [← Finset.sum_mul, ← map_sum, sum_homogeneousComponent]

  have hG : G ∈ W := by
    rw [← map_eq_zero_iff W, ← hp, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, hGdef]
    simp only [hGc, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← phi_apply, hf c]
    rfl

  have hcomp : ∀ c ∈ s, ∀ d ∈ Finset.range ((f c).totalDegree + 1),
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (bideg d c) G =
        baseRen k N m (homogeneousComponent d (f c)) * Y ^ c := by
    intro c hc d hd
    rw [hGdef, map_sum, Finset.sum_eq_single c, map_sum, Finset.sum_eq_single d]
    · exact (isMultiHomog_term (f c) d c j).weightedHomogeneousComponent_same
    · intro d' _ hne
      refine (isMultiHomog_term (f c) d' c j).weightedHomogeneousComponent_ne _ fun e => hne ?_
      have := congrFun e (Sum.inl ())
      simp only [bideg, Sum.elim_inl] at this
      omega
    · intro h
      exact absurd hd h
    · intro c' _ hne
      rw [map_sum]
      refine Finset.sum_eq_zero fun d' _ => ?_
      refine (isMultiHomog_term (f c') d' c' j).weightedHomogeneousComponent_ne _ fun e => hne ?_
      have := congrFun e (Sum.inr ())
      simp only [bideg, Sum.elim_inr] at this
      omega
    · intro h
      exact absurd hc h

  have hmemF : ∀ c ∈ s, baseRen k N m (f c) ∈ W := by
    intro c hc
    rw [← sum_homogeneousComponent (f c), map_sum]
    refine Ideal.sum_mem _ fun d hd => ?_
    have hmem : baseRen k N m (homogeneousComponent d (f c)) * Y ^ c ∈ W := by
      rw [← hcomp c hc d hd]
      exact hH G hG _
    exact (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right
      fun h => hj (Ideal.IsPrime.mem_of_pow_mem ‹_› c h)
  refine Polynomial.ext fun c => ?_
  rw [Polynomial.coeff_zero]
  by_cases hc : c ∈ s
  · have := hf c
    rw [phi_apply, (map_eq_zero_iff W _).2 (hmemF c hc)] at this
    exact Subtype.ext this.symm
  · exact Polynomial.notMem_support_iff.mp hc

theorem isAlgebraic_adjoin [W.IsPrime] (j : Fin m)
    (hrat : ∀ b : Fin m, ∃ f g : Kleiman.Poly k N, baseRen k N m g ∉ W ∧
      baseRen k N m g * X ⟨Sum.inr (), b⟩ - baseRen k N m f * X ⟨Sum.inr (), j⟩ ∈ W) :
    Algebra.IsAlgebraic (Algebra.adjoin (phi W).range (Set.range fun _ : Unit => eta W j))
      (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) := by
  set R := NumbersDVR.MRing (graphIdx N m) k ⧸ W
  set L := FractionRing R
  set T := Algebra.adjoin (phi W).range (Set.range fun _ : Unit => eta W j)
  have hT : ∀ x ∈ T, IsAlgebraic T x := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : T)
  have hA : ∀ f, phi W f ∈ T := fun f => T.algebraMap_mem (⟨phi W f, f, rfl⟩ : (phi W).range)
  have hη : eta W j ∈ T := Algebra.subset_adjoin ⟨(), rfl⟩
  have hbase : ∀ a : Fin (N + 1), IsAlgebraic T (algebraMap R L (Ideal.Quotient.mk W (X ⟨Sum.inl (), a⟩))) := by
    intro a
    refine hT _ ?_
    have := hA (X a)
    rwa [phi_apply, baseRen_X] at this
  have hvar : ∀ v, IsAlgebraic T (algebraMap R L (Ideal.Quotient.mk W (X v))) := by
    rintro ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, i⟩
    · exact hbase i
    · obtain ⟨f, g, hg, hfg⟩ := hrat i
      have hg0 : phi W g ≠ 0 := by
        rw [phi_apply, Ne, map_eq_zero_iff]
        exact hg
      have hrel := (map_eq_zero_iff W _).2 hfg
      simp only [map_sub, map_mul] at hrel
      have e : algebraMap R L (Ideal.Quotient.mk W (X ⟨Sum.inr (), i⟩)) = phi W f * eta W j / phi W g := by
        rw [eq_div_iff hg0, phi_apply, phi_apply]
        linear_combination hrel
      rw [e, div_eq_mul_inv]
      exact (hT _ (T.mul_mem (hA f) hη)).mul (IsAlgebraic.inv_iff.mpr (hT _ (hA g)))
  have hR : ∀ r : R, IsAlgebraic T (algebraMap R L r) := by
    intro r
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction F using MvPolynomial.induction_on with
    | C c =>
      refine hT _ ?_
      have := hA (C c)
      rwa [phi_apply, baseRen_C] at this
    | add f g hf hg => rw [map_add, map_add]; exact hf.add hg
    | mul_X f v hf => rw [map_mul, map_mul]; exact hf.mul (hvar v)
  refine ⟨fun x => ?_⟩
  obtain ⟨a, d, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [div_eq_mul_inv]
  exact (hR a).mul (IsAlgebraic.inv_iff.mpr (hR d))

end RatioDim

open RatioDim in

theorem RatioDim.full : RatioDim.Statement := by
  intro k _ N m W hW hH j hj hrat
  have := hW
  set R := NumbersDVR.MRing (graphIdx N m) k ⧸ W
  set L := FractionRing R
  set A := (phi W).range
  have hb : IsTranscendenceBasis A (fun _ : Unit => eta W j) :=
    (algebraicIndependent_unique_type_iff.mpr (transcendental_eta W hH j hj)).isTranscendenceBasis_iff_isAlgebraic.mpr
      (isAlgebraic_adjoin W j hrat)
  have h1 : Algebra.trdeg A L = 1 := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k A).injective
  have hkA : Algebra.trdeg k A = Algebra.trdeg k (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) := by
    rw [← ker_phi]
    exact (Ideal.quotientKerEquivRange (phi W)).trdeg_eq.symm
  have htot : Algebra.trdeg k R = Algebra.trdeg k (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) + 1 := by
    rw [← GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := k) (A := R) L,
      ← trdeg_add_eq k A (A := L), h1, hkA]
  change ringKrullDim R = ringKrullDim (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) + 1
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k (A := R),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k (A := Kleiman.Poly k N ⧸ W.comap (baseRen k N m)),
    htot, map_add, map_one]
  rfl

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
