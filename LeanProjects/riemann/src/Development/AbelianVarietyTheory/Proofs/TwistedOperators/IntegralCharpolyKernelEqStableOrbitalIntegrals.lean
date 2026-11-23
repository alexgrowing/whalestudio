import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePreimageOfNhdsZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsumRestrictedFamilyEqProdFinsum

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt (ratClass classKernel)

theorem classKernel_eq_sum {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (g : H) (f : G → ℂ)
    (x : G) (T : Finset H) (hT : ∀ δ, f (x⁻¹ * ι δ * x) ≠ 0 → δ ∈ T) :
    classKernel ι.range (ι g) f x = ∑ δ ∈ T, {δ | IsConj g δ}.indicator (fun δ => f (x⁻¹ * ι δ * x)) δ := by
  let e : {δ | IsConj g δ} → ratClass ι.range (ι g) := fun δ => ⟨ι δ, by
    obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
    exact ⟨ι c⁻¹, ⟨_, rfl⟩, by rw [← hc]; simp⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c⁻¹ * g * c, isConj_iff.2 ⟨c⁻¹, by simp⟩⟩, Subtype.ext (by simp [e])⟩
  rw [classKernel, ← (Equiv.ofBijective e he).tsum_eq fun δ => f (x⁻¹ * δ * x)]
  refine (tsum_subtype {δ | IsConj g δ} fun δ => f (x⁻¹ * ι δ * x)).trans (tsum_eq_sum fun δ hδ => ?_)
  by_contra h
  exact hδ (hT δ fun h0 => h (by simp [indicator, h0]))

theorem finsum_eq_sum_classKernel {G H I : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι)
    (p : H → Prop) (g : I → H) (hp : ∀ δ, p δ ↔ ∃ i, IsConj (g i) δ) (hg : ∀ i j, IsConj (g i) (g j) → i = j)
    (f : G → ℂ) (S : Finset I) (hS : ∀ i ∉ S, ∀ x, f (x⁻¹ * ι (g i) * x) = 0) (x : G)
    (hx : {δ | f (x⁻¹ * ι δ * x) ≠ 0}.Finite) :
    ∑ᶠ δ : {δ // p δ}, f (x⁻¹ * ι δ.1 * x) = ∑ i ∈ S, classKernel ι.range (ι (g i)) f x := by
  classical
  rw [Finset.sum_congr rfl fun i _ => classKernel_eq_sum ι hι (g i) f x hx.toFinset fun δ h => hx.mem_toFinset.2 h,
    Finset.sum_comm]
  refine (finsum_set_coe_eq_finsum_mem (f := fun δ => f (x⁻¹ * ι δ * x)) {δ | p δ}).trans ?_
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := hx.toFinset) _ fun δ h => by
    simpa using fun h0 => h (by simp [indicator, h0])]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  by_cases h : p δ
  · obtain ⟨i, hi⟩ := (hp δ).1 h
    have hiS : i ∈ S := by
      by_contra hn
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      refine hx.mem_toFinset.1 hδ ?_
      rw [← hS i hn ((ι c)⁻¹ * x), ← hc]
      simp [mul_assoc]
    rw [indicator_of_mem (show δ ∈ {δ | p δ} from h), Finset.sum_eq_single_of_mem i hiS fun j _ hj =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => hj (hg j i (hc.trans hi.symm))) _,
      indicator_of_mem (show δ ∈ {δ | IsConj (g i) δ} from hi)]
  · rw [indicator_of_notMem (show δ ∉ {δ | p δ} from h), Finset.sum_eq_zero fun j _ =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => h ((hp δ).2 ⟨j, hc⟩)) _]

theorem classKernel_eq_zero {G : Type} [Group G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    classKernel Γ γ f = 0 := by
  funext x
  refine (tsum_congr ?_).trans tsum_zero
  rintro ⟨_, c, -, rfl⟩
  rw [← h (c * x)]
  simp [mul_assoc]

theorem finite_of_eventually_eq_one {V Y : Type} [Finite Y] {C : V → Type} [∀ v, One (C v)] [∀ v, Finite (C v)]
    {X : ∀ v, Set (C v)} {p : (∀ v, X v) × Y → Prop} (A : Set {q // p q})
    (h : ∀ᶠ v in cofinite, ∀ i ∈ A, (i.1.1 v).1 = 1) : A.Finite := by
  have : Finite {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} := eventually_cofinite.1 h
  refine Set.Finite.of_finite_image
    (f := fun i : {q // p q} => ((fun v : {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} => i.1.1 v), i.1.2)) (Set.toFinite _)
    fun i hi j hj e => Subtype.ext (Prod.ext (funext fun v => ?_) (congrArg Prod.snd e :))
  by_cases hv : ∀ i ∈ A, (i.1.1 v).1 = 1
  · exact Subtype.ext ((hv i hi).trans (hv j hj).symm)
  · exact congrFun (congrArg Prod.fst e) ⟨v, hv⟩

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem exists_isCompact_tensor (ha : ∀ w, HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    ∃ C, IsCompact C ∧ ∀ y, tensor σ J fa ff y ≠ 0 → y ∈ C := by
  refine ⟨_, (infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod
    ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi ha))
      hf.tensorFin_mem.2), fun y hy => ?_⟩
  rw [tensor_eq_infFin] at hy
  exact ⟨fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hy) w (Finset.mem_univ w)),
    subset_tsupport _ (right_ne_zero_of_mul hy)⟩

theorem ne_zero_of_tensor (hf : IsFinFamily σ J L ff) {y : GAd σ J} (hy : tensor σ J fa ff y ≠ 0) (v) :
    ff v (proj σ J v y) ≠ 0 := by
  rw [tensor_eq_infFin] at hy
  simpa only [projFinLoc_projFin] using (hf.tensorFin_ne_zero_iff _).1 (right_ne_zero_of_mul hy) v

omit [NumberField F] [NumberField E] in

theorem charpoly_eq_of_isConj {γ δ : GRat σ J} (h : IsConj γ δ) : δ.1.1.charpoly = γ.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have : (c * γ * c⁻¹).1.1 = c.1.1 * γ.1.1 * (c.1⁻¹).1 := rfl
  rw [this, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Adelic

theorem integral_polKernel : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  classical
  intro E _ _ F _ σ hCM hun r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  obtain ⟨H1, H2, H3⟩ := GlobalTheory.T.rational_unitary_classes_iff_local_class_families E F σ hCM hun r P J hJ
  obtain ⟨Ff, Fa⟩ := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hCM r P
  have hae := GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hCM r P J hJ L
  have hcl := GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals F E σ hCM r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  let I := {p : (∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) × (∀ w : InfinitePlace F, XSet P w.Completion J) //
    ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  obtain ⟨hsupp, hsum⟩ := finsum_restrictedFamily_eq_prod_finsum (HeightOneSpectrum (𝓞 F)) (InfinitePlace F)
    (fun v => Cls P (Fv F v)) (fun v => XSet P (Fv F v) J) (fun w => XSet P w.Completion J) (fun v => Set.toFinite _)
    (fun v => orbCls (μf v) (dtf v) (ff v)) (fun w => orbCls (μa w) (dta w) (fa w)) (by
      filter_upwards [hae, hff.2, hμ.eventually_eq_one, IsRestrictedProd.eventually_eq_one hdt] with v h1 h2 h3 h4
      rw [h2]
      exact ⟨h1.1, h1.2.2.2 _ _ (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) h3 h4⟩)
  choose g g1 g2 g3 using fun i : I => H3 (fun v => (i.1.1 v).1) (fun w => (i.1.2 w).1) (fun v => (i.1.1 v).2)
    (fun w => (i.1.2 w).2) i.2
  have hp : ∀ δ : GRat σ J, δ.1.1.charpoly = P.1 ↔ ∃ i, IsConj (g i) δ := fun δ => by
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (charpoly_eq_of_isConj hi).trans (g1 i)⟩
    obtain ⟨a1, a2, a3⟩ := H1 δ h
    choose qf qf1 qf2 using a1
    choose qa qa1 qa2 using a2
    let i : I := ⟨(fun v => ⟨qf v, (qf1 v).mem⟩, fun w => ⟨qa w, (qa1 w).mem⟩), a3.mono fun v hv => (qf2 v 1 hv).symm⟩
    refine ⟨i, IsConj.symm ((H2 δ (g i) h (g1 i)).2 ⟨fun v q hq => ?_, fun w q hq => ?_⟩)⟩
    · rw [qf2 v q hq]; exact g2 i v
    · rw [qa2 w q hq]; exact g3 i w
  have hg : ∀ i j, IsConj (g i) (g j) → i = j := fun i j h => by
    obtain ⟨b1, b2⟩ := (H2 _ _ (g1 i) (g1 j)).1 h
    obtain ⟨a1, a2, -⟩ := H1 _ (g1 j)
    have e1 : ∀ v, i.1.1 v = j.1.1 v := fun v => Subtype.ext ((a1 v).unique (b1 v _ (g2 i v)) (g2 j v))
    have e2 : ∀ w, i.1.2 w = j.1.2 w := fun w => Subtype.ext ((a2 w).unique (b2 w _ (g3 i w)) (g3 j w))
    exact Subtype.ext (Prod.ext (funext e1) (funext e2))
  have hfin : {i : I | ∃ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) ≠ 0}.Finite := by
    refine finite_of_eventually_eq_one _ ?_
    filter_upwards [hae, hff.2] with v h1 h2
    rintro i ⟨x, hx⟩
    have h3 := ne_zero_of_tensor hff hx v
    rw [h2, map_mul, map_mul, map_inv] at h3
    exact h1.2.1 _ _ (g2 i v) ⟨_, by_contra fun hn => h3 (indicator_of_notMem hn _)⟩
  have hS : ∀ i ∉ hfin.toFinset, ∀ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) = 0 := fun i hi x =>
    by_contra fun h => hi (hfin.mem_toFinset.2 ⟨x, h⟩)
  obtain ⟨C, hC, hC'⟩ := exists_isCompact_tensor (fun w => (hfa w).2) hff
  have hker0 : ∀ x, polKernel P J (tensor σ J fa ff) x = ∑ i ∈ hfin.toFinset,
      classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff) x := fun x => by
    rw [polKernel, ← range_ratEmb]
    exact finsum_eq_sum_classKernel (ratEmb σ J) (ratEmb_injective σ J) _ g hp hg _ _ hS x
      (((GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hCM r J C hC).2 x).subset fun δ h => hC' _ h)
  have hker : descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) = fun q => ∑ i ∈ hfin.toFinset,
      descend (ratPts σ J) (classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff)) q := by
    funext q
    simp only [descend, hker0]
  have hi := fun i : I => hcl (g i) (g1 i) i.1.1 i.1.2 (g2 i) (g3 i)
  rw [hker]
  refine ⟨integrable_finset_sum _ fun i _ => (hi i).1, ?_⟩
  rw [integral_finset_sum _ fun i _ => (hi i).1, Finset.sum_congr rfl fun i _ => (hi i).2, mul_assoc]
  simp only [Phi]
  rw [← hsum, mul_finsum' _ _ hsupp]
  refine (finsum_eq_sum_of_support_subset _ fun i hn => ?_).symm
  by_contra h
  refine hn ((hi i).2.symm.trans ?_)
  rw [classKernel_eq_zero _ _ _ (hS i h)]
  simp only [descend, Pi.zero_apply, integral_zero]

end GlobalTheory.TrEll
