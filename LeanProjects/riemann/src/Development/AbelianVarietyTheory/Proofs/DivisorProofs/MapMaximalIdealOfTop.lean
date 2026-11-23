import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FlatLength
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmCut

open TopologicalSpace GlobalTheory.VdmWd

section Geometry

variable {X V W : Scheme.{0}}

theorem map_maximalIdeal_of_top (π : V ⟶ W) [Smooth π] {v : V} (hv : ∀ v', π v' = π v → v ⤳ v') :
    (IsLocalRing.maximalIdeal (W.presheaf.stalk (π v))).map (π.stalkMap v).hom =
      IsLocalRing.maximalIdeal (V.presheaf.stalk v) := by
  obtain ⟨b, x, rfl⟩ : ∃ (b : W) (x : π.fiber b), π.fiberι b x = v := ⟨π v, π.asFiber v, π.fiberι_asFiber v⟩
  have : Smooth (π.fiberToSpecResidueField b) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (W.fromSpecResidueField b)) ‹_›
  have : IsReduced (π.fiber b) := GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)
  have hmax : IsMax x := fun x' _ => (π.fiberι b).isEmbedding.isInducing.specializes_iff.1
    (hv _ ((GlobalTheory.FibreStalk.image_eq W V π b x').trans (GlobalTheory.FibreStalk.image_eq W V π b x).symm))
  have : Ring.KrullDimLE 0 ((π.fiber b).presheaf.stalk x) :=
    krullDimLE_of_coheight_le (Order.coheight_eq_zero.2 hmax).le
  have hF : IsField ((π.fiber b).presheaf.stalk x) := Ring.KrullDimLE.isField_of_isReduced
  rw [← GlobalTheory.FibreStalk.ker_stalkMap_fiberι]
  letI := hF.toField
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ ((π.fiberι b).stalkMap_surjective x))

theorem coheight_of_top [IsLocallyNoetherian V] [IsLocallyNoetherian W] (π : V ⟶ W) [Smooth π] {v : V}
    (hv : ∀ v', π v' = π v → v ⤳ v') : Order.coheight v = Order.coheight (π v) := by
  have h := GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add W V π v
  rw [map_maximalIdeal_of_top π hv, ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance), add_zero, ringKrullDim_stalk_eq_coheight,
    ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

theorem germ_secPull {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((Cartier.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem mult_of_top [IsIntegral V] [IsIntegral W] [IsLocallyNoetherian V] [IsLocallyNoetherian W] (π : V ⟶ W) [Smooth π]
    (a : W ⟶ X) {L : LB X} (hL : L.IsLB) (s : L.Sec) (hV : genericPoint V ∈ Out.nonzeroLocus (Cartier.secPull s (π ≫ a)))
    (hW : genericPoint W ∈ Out.nonzeroLocus (Cartier.secPull s a)) {v : V} (hv : ∀ v', π v' = π v → v ⤳ v') :
    (divOfSec (LB.isLB_pull hL _) _ hV).mult v = (divOfSec (LB.isLB_pull hL _) _ hW).mult (π v) := by
  have hc := coheight_of_top π hv
  by_cases h1 : Order.coheight v = 1
  swap
  · rw [not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero h1),
      not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero (hc ▸ h1))]
  obtain ⟨i, hi⟩ := exists_chart hL ((π ≫ a) v)
  have hi' : a (π v) ∈ L.U i := hi
  have h₁ : v ∈ (L.pull (π ≫ a)).U fun _ => i := Set.mem_iInter.2 fun _ => hi
  have h₂ : π v ∈ (L.pull a).U fun _ => i := Set.mem_iInter.2 fun _ => hi'
  rw [mult_divOfSec h1 h₁, mult_divOfSec (hc ▸ h1) h₂, germ_secPull s _ v i hi, germ_secPull s _ _ i hi']
  letI : Algebra (W.presheaf.stalk (π v)) (V.presheaf.stalk v) := (π.stalkMap v).hom.toAlgebra
  haveI : Module.Flat (W.presheaf.stalk (π v)) (V.presheaf.stalk v) := Flat.stalkMap π v
  haveI : IsLocalHom (algebraMap (W.presheaf.stalk (π v)) (V.presheaf.stalk v)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap v).hom)
  rw [← ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq (S := V.presheaf.stalk v) (map_maximalIdeal_of_top π hv),
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := W.presheaf.stalk (π v)) (V.presheaf.stalk v) _).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton, Scheme.Hom.stalkMap_comp]
  rfl

theorem eq_of_mult_ne_zero [IsIntegral V] [IsLocallyNoetherian V] (b : V ⟶ X) {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hV : genericPoint V ∈ Out.nonzeroLocus (Cartier.secPull s b)) {v v' : V} (h : v' ⤳ v) (hb : b v' = b v)
    (hv : (divOfSec (LB.isLB_pull hL _) _ hV).mult v ≠ 0) : v' = v := by
  have hn : v ∉ Out.nonzeroLocus (Cartier.secPull s b) := fun hs =>
    notMem_supp_divOfSec.2 hs (CartierDiv.mem_supp_of_mult_ne_zero hv)
  have hn' : v' ∉ Out.nonzeroLocus (Cartier.secPull s b) := by
    rw [Cartier.nonzeroLocus_secPull] at hn ⊢
    change b v' ∉ Out.nonzeroLocus s
    rw [hb]
    exact hn
  by_contra hne
  have l₁ : v < v' := ⟨h, fun h' => hne (h.antisymm h').eq⟩
  have l₂ : v' < genericPoint V := ⟨genericPoint_specializes v', fun h' =>
    hn' ((show v' ⤳ genericPoint V from h').mem_open (Out.nonzeroLocus _).isOpen hV)⟩
  have h₄ := Order.coheight_add_one_le l₁
  have h₅ := Order.coheight_add_one_le l₂
  rw [CartierDiv.coheight_eq_one_of_mult_ne_zero hv] at h₄
  have h₆ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₅) 1).trans h₄
  exact absurd h₆ (by decide)

theorem exists_smooth_clo (π : V ⟶ X) [Smooth π] {y : V} {z : X} (h : closure {y} = π ⁻¹' closure {z}) :
    ∃ ρ : _ ⟶ _, Smooth ρ ∧ ρ ≫ redι (clo z) = redι (clo y) ≫ π := by
  let j := Limits.pullback.fst π (redι (clo z))
  have : IsReduced (Limits.pullback π (redι (clo z))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (Limits.pullback.snd π (redι (clo z)))
  have hj : Set.range j = closure {y} := by
    rw [h, ← show Set.range (redι (clo z)) = closure {z} from range_redι (clo z)]
    exact Scheme.Pullback.range_fst π _
  have hk : j.ker = (redι (clo y)).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← InterModel.radical_ker j, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, hj, closure_closure]
    rfl
  let f := IsClosedImmersion.lift j (redι (clo y)) hk.le
  have hf : f ≫ j = redι (clo y) := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_of_ker_eq _ _ f hf hk.symm
  refine ⟨f ≫ Limits.pullback.snd π (redι (clo z)), inferInstance, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, hf]

end Geometry

section Poly

variable {ι : Type} [Fintype ι]

theorem exists_functional_prod (e : ℕ) (I : (Fin e → ι) → ℝ) (hI : ∀ a (σ : Equiv.Perm (Fin e)), I (a ∘ σ) = I a) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ a : Fin e → ι, T (∏ j, MvPolynomial.X (a j)) = I a := by
  refine ⟨(basisMonomials ι ℝ).constr ℝ fun u =>
    if h : ∃ a : Fin e → ι, ∑ j, Finsupp.single (a j) 1 = u then I h.choose else 0, fun a => ?_⟩
  have e₁ : (∏ j, MvPolynomial.X (a j) : MvPolynomial ι ℝ) = basisMonomials ι ℝ (∑ j, Finsupp.single (a j) 1) := by
    rw [coe_basisMonomials]
    exact (monomial_sum_one _ _).symm
  have h : ∃ a' : Fin e → ι, ∑ j, Finsupp.single (a' j) 1 = ∑ j, Finsupp.single (a j) 1 := ⟨a, rfl⟩
  rw [e₁, Module.Basis.constr_basis, dif_pos h]
  have hc (c : ι) : Fintype.card {j // h.choose j = c} = Fintype.card {j // a j = c} := by
    have := DFunLike.congr_fun h.choose_spec c
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply] at this
    simp only [Fintype.card_subtype, Finset.card_filter]
    exact this
  rw [← hI a (Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c))]
  exact congrArg I (funext fun j => (Equiv.ofFiberEquiv_map _ j).symm)

theorem prod_lin {e : ℕ} (c : Fin e → ι → ℝ) :
    ∏ j, lin (c j) = ∑ a : Fin e → ι, (∏ j, c j (a j)) • ∏ j, MvPolynomial.X (a j) := by
  simp only [lin, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib, smul_eq_C_mul, map_prod]

theorem apply_prod_lin {e : ℕ} {I : (Fin e → ι) → ℝ} (hI : ∀ a (σ : Equiv.Perm (Fin e)), I (a ∘ σ) = I a)
    {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ n : ι → ℤ, Φ (lin (fun j => (n j : ℝ)) ^ e) = ∑ a : Fin e → ι, (∏ j, (n (a j) : ℝ)) * I a)
    (h₂ : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ e → P.IsHomogeneous d → Φ P = 0) (c : Fin e → ι → ℝ) :
    Φ (∏ j, lin (c j)) = ∑ a : Fin e → ι, (∏ j, c j (a j)) * I a := by
  obtain ⟨T, hT⟩ := exists_functional_prod e I hI
  have hT' (c : Fin e → ι → ℝ) : (T ∘ₗ homogeneousComponent e) (∏ j, lin (c j)) =
      ∑ a : Fin e → ι, (∏ j, c j (a j)) * I a := by
    have hh : (∏ j, lin (c j)).IsHomogeneous e := by
      simpa using IsHomogeneous.prod Finset.univ (fun j => lin (c j)) (fun _ => 1) fun j _ => by
        simpa using isHomogeneous_lin_pow (c j) 1
    rw [LinearMap.comp_apply, homogeneousComponent_of_mem hh, if_pos rfl, prod_lin, map_sum]
    simp only [map_smul, hT, smul_eq_mul]
  rw [← hT', sub_eq_zero.1 (Model.eq_zero_of_pow e (Φ - T ∘ₗ homogeneousComponent e) (fun n => ?_) fun P d hd hP => ?_)]
  · rw [LinearMap.sub_apply, h₁, ← hT' fun _ j => n j, Fin.prod_const, sub_self]
  · rw [LinearMap.sub_apply, h₂ P d hd hP, LinearMap.comp_apply, homogeneousComponent_of_mem hP, if_neg hd.symm, map_zero,
      sub_self]

theorem lin_single (o : ι) (m : ℤ) : lin (fun j => ((Pi.single o m : ι → ℤ) j : ℝ)) = (m : ℝ) • MvPolynomial.X o := by
  rw [lin, Finset.sum_eq_single o (fun b _ hb => by simp [hb]) (by simp), smul_eq_C_mul]
  simp

end Poly

section Mixed

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {ι : Type} [Fintype ι]

theorem archInt_eq_chInt [IsIntegral Y] {D : ℕ} (hY : IsArithVar p D) (P M : HermLB p) (s : M.B.Sec)
    (hs : genericPoint Y ∈ Out.nonzeroLocus s) : P.archInt M D (isRatSec_ratOfSec s hs) =
      chInt P D fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2 := by
  refine finsum_congr fun σ => ?_
  have hnull (ε : ℤˣ) : (P.φ σ).chernPart D ε (offSupp p σ (divOfSec M.isLB s hs))ᶜ = 0 := by
    have e : (offSupp p σ (divOfSec M.isLB s hs))ᶜ =
        {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((divOfSec M.isLB s hs).supp : Set Y)} := by
      ext y
      simp only [Set.mem_compl_iff, mem_offSupp, not_not]
      rfl
    rw [e]
    exact GlobalTheory.ChernNull.chernPart_over_closed hY _ (divOfSec M.isLB s hs).supp.isClosed
      (CartierDiv.genericPoint_notMem_supp _) σ _ ε
  rw [Weight.chernInt_congr (g := fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2)
    (isOpen_offSupp _).measurableSet fun y hy =>
      logNorm_ratOfSec _ ((offSupp_divOfSec (q := p) (σ := σ) (hL := M.isLB) (hs := hs)).le hy)]
  simp only [Weight.chernInt, MeasureTheory.Measure.restrict_univ]
  rw [MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull 1),
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull (-1))]

variable {D₀ : ℕ} (hY : IsArithVar p D₀) {L : ι → HermLB p} (o : ι) (m : ℕ) {Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i]
  [IsIntegral Z] [IsLocallyNoetherian Z] {D : ℕ} (hd : topologicalKrullDim Z = (D + 1 : ℕ)) (M : HermLB (i ≫ p))
  (hM : (((L o).restr i).pow m).Isometric M) (t : M.B.Sec) (ht : genericPoint Z ∈ Out.nonzeroLocus t)
  {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsHtFun L (i (genericPoint Z)) (D + 1) Φ) (n : ι → ℤ) {g : Y → ℝ}
  (hg : (comb L n).IsArithHeight g)
include hY hd hM hΦ hg

theorem mixed_horizontal (hC : ArCalc) (hc : CharZero Γ(Z, ⊤)) :
    (m : ℝ) * Φ (MvPolynomial.X o * lin (fun j => (n j : ℝ)) ^ D) = ∑ᶠ v, ((divOfSec M.isLB t ht).mult v : ℝ) * g (i v) -
      chInt (comb (fun j => (L j).restr i) n) D fun σ v => Real.log ((M.φ σ).nsq (secVal _ σ t) v) / 2 := by
  have hZ : IsArithVar (i ≫ p) D := hY.of_isClosedImmersion i hc hd
  have hΦ' : IsArFun (fun j => (L j).restr i) D Φ := ⟨fun n' => by
    obtain ⟨g', hg', e⟩ := hΦ.1 n'
    rw [← e]
    exact (isometric_comb_pull L n' i rfl).symm.isSelfInter hZ (hg'.isSelfInter_restrict hY i rfl), hΦ.2⟩
  have h₁ := ((hC.arIso k Z (i ≫ p) D hZ).2 ι _ Φ hΦ').2.2 (Option ι) (fun x => x.elim M fun j => (L j).restr i)
    (fun x => x.elim (Pi.single o m) fun j => Pi.single j 1) (by
      rintro (_ | j)
      · refine HermLB.Isometric.trans (HermLB.icls_eq_iff.1 ?_) hM
        simp [icls_comb, HermLB.icls_pow, Pi.single_apply]
      · exact isometric_comb_single _ j)
  have h₂ := (hC.arMix k Z (i ≫ p) D hZ ι M _ _ h₁ n (fun v => g (i v))
    ((isometric_comb_pull L n i rfl).symm.isArithHeight hZ (hg.restrict hY i rfl)) _ (isRatSec_ratOfSec t ht)).2
  rw [archInt_eq_chInt hZ] at h₂
  rw [← h₂, LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
  refine congrArg Φ ?_
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  congr 2
  · exact (lin_single o m).symm
  · rw [lin, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, aeval_C, aeval_X]
    exact congrArg _ ((one_smul ℝ _).symm.trans ((Int.cast_one (R := ℝ)) ▸ (lin_single j 1).symm))

theorem mixed_vertical (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(Z, ⊤)] :
    (m : ℝ) * Φ (MvPolynomial.X o * lin (fun j => (n j : ℝ)) ^ D) = ∑ᶠ v, ((divOfSec M.isLB t ht).mult v : ℝ) * g (i v) := by
  have hp := GlobalTheory.VertProj.isProjOver_strHom_zmod k Y p D₀ hY Z i ℓ
  have hL : ∀ j, ((L j).B.pull i).IsLB := fun j => LB.isLB_pull (L j).isLB i
  have hP := LB.isLB_pull (comb L n).isLB i
  have h₁ := apply_prod_lin (Φ := Φ)
    (I := fun a : Fin (D + 1) → ι => (interNum (ZMod ℓ) (structureModule Z) (fun j => (L (a j)).B.pull i) : ℝ) * Real.log ℓ)
    (fun a σ => congrArg (fun x : ℤ => (x : ℝ) * Real.log ℓ)
      (interNum_comp_perm (ZMod ℓ) (structureModule Z) (L := fun j => (L (a j)).B.pull i) (fun j => hL _) σ))
    (fun n' => by
      obtain ⟨g', hg', e⟩ := hΦ.1 n'
      rw [← e, hg'.vertical Z i (ZMod ℓ) _ hd, Nat.card_zmod, GlobalTheory.VertFun.topSelf_comb_pull hp hd i L n', Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _) hΦ.2
    fun x j => ((Fin.cons (Pi.single o m) (fun _ => n) : Fin (D + 1) → ι → ℤ) x j : ℝ)
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom (ZMod ℓ) Z) (structureModule Z) hp (d := D + 1)
    (by rw [QCoh.suppDim_structureModule, hd])
  have h₂ := HD.interNum_of_cls_eq_sum (L := fun j => (L j).B.pull i) hL
    (Q := Fin.cons M.B fun _ => (comb L n).B.pull i) (Fin.cases M.isLB fun _ => hP)
    (Fin.cons (Pi.single o m) (fun _ => n)) (Fin.cases (by
      refine ((CechPic.cls_eq_iff (((L o).restr i).pow m).isLB M.isLB).2 ⟨_, hM.choose_spec.1⟩).symm.trans
        ((CechPic.cls_lbPow (hL o) m _).trans ?_)
      simp [Pi.single_apply]) fun _ => by
      refine (CechPic.cls_pull (comb L n).isLB i hP).trans ?_
      rw [GenFibreSecs.cls_comb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, CechPic.cls_pull (L j).isLB]
      rfl)
  rw [GlobalTheory.T.rational_section_cycle_formula_projective (ZMod ℓ) Z hp D hd.le _ M.isLB _ (fun _ => hP) _ (isRatSec_ratOfSec t ht)] at h₂
  simp only [Fin.prod_univ_succ (fun x => lin _), Fin.cons_zero, Fin.cons_succ, Fin.prod_const, lin_single, smul_mul_assoc,
    map_smul, smul_eq_mul, Int.cast_natCast] at h₁
  have := hY.isNoetherian_sub i
  have hfin := (divOfSec M.isLB t ht).finite_support_mult
  have h₃ := congrArg (fun x : ℤ => (x : ℝ) * Real.log ℓ) h₂
  push_cast at h₃
  rw [h₁]
  refine Eq.trans (Eq.trans ?_ h₃.symm) ?_
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => (mul_assoc _ _ _).symm
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun v hv => by
      simpa using fun h0 : (divOfSec M.isLB t ht).mult v = 0 => hv (by simp [h0]),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun v hv => by
      simpa using fun h0 : (divOfSec M.isLB t ht).mult v = 0 => hv (by simp [h0]), Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv' : (divOfSec M.isLB t ht).mult v ≠ 0 := by simpa using hv
  letI : Algebra (ZMod ℓ) Γ((Scheme.IdealSheafData.vanishingIdeal (clo v)).subscheme, ⊤) :=
    ((redι (clo v)).appTop.hom.comp (algebraMap (ZMod ℓ) Γ(Z, ⊤))).toAlgebra
  have e := hg.vertical _ (redι (clo v) ≫ i) (ZMod ℓ) D ((dim_clo v).trans
    (CutSec.dim_closure_of_coheight hY i hd (CartierDiv.coheight_eq_one_of_mult_ne_zero hv')))
  rw [Scheme.Hom.comp_apply, redι_clo, Nat.card_zmod] at e
  rw [e, Int.cast_mul, mul_assoc]
  congr 3
  refine (interNumOn_eq_interNum_pull (k := ZMod ℓ) (f := redι (clo v)) (L := fun _ : Fin D => (comb L n).B.pull i)
    (fun _ => rfl) fun _ => hP).trans ?_
  refine interNum_congr_cls _ _ (fun _ => LB.isLB_pull hP _) (fun _ => LB.isLB_pull (comb L n).isLB _) fun _ => ?_
  rw [CechPic.cls_pull hP, CechPic.cls_pull (comb L n).isLB, CechPic.cls_pull (comb L n).isLB, CechPic.pull_comp]

theorem mixed (hC : ArCalc) :
    (m : ℝ) * Φ (MvPolynomial.X o * lin (fun j => (n j : ℝ)) ^ D) = ∑ᶠ v, ((divOfSec M.isLB t ht).mult v : ℝ) * g (i v) -
      chInt (comb (fun j => (L j).restr i) n) D fun σ v => Real.log ((M.φ σ).nsq (secVal _ σ t) v) / 2 := by
  rcases hY.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  · rw [mixed_vertical hY o m i hd M hM t ht hΦ n hg ℓ, chInt, finsum_eq_zero_of_forall_eq_zero (f := fun σ : k →+* ℂ => _)
      fun σ => ?_, sub_zero]
    have := isEmpty_cxPts (p := i ≫ p) ℓ σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  · exact mixed_horizontal hY o m i hd M hM t ht hΦ n hg hC hc

end Mixed

theorem vdmPol_succ (r e : ℕ) : vdmPol r (e + 1) = MvPolynomial.X none * vdmPol r e := by
  rw [vdmPol, vdmPol]
  ring

theorem val_recursion : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p), ∀ (m : ℕ) (s : (N.pow m).B.Sec) (z : X) (e : ℕ), topologicalKrullDim (closure ({z} : Set X)) = (e + 3 : ℕ) → z ∈ Out.nonzeroLocus s → (Function.support (cutMult (N.pow m).isLB s z)).Finite ∧ (m : ℝ) * F.val H N z (e + 1) = ∑ᶠ w, (cutMult (N.pow m).isLB s z w : ℝ) * F.val H N w e - F.arch H N (N.pow m) s z e := by
  intro hC k _ X _ _ p d hX E r h H F N m s z e hdim hz
  obtain ⟨hY, hsm, htop⟩ := (GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r h.isVB).2 F
  choose top htop hcl hd using htop
  have := hY.isIntegral
  have := hY.isLocallyNoetherian
  set i := redι (clo z) with hi
  set j := redι (clo (top z)) with hj
  have : IsNoetherian _ := hX.isNoetherian_sub i
  have : IsNoetherian _ := hY.isNoetherian_sub j
  obtain ⟨ρ, _, hρ⟩ := exists_smooth_clo F.π (hcl z)
  have hρ' (v) : i (ρ v) = F.π (j v) := by rw [← Scheme.Hom.comp_apply, hρ, Scheme.Hom.comp_apply]
  have hW : genericPoint _ ∈ Out.nonzeroLocus (Cartier.secPull s i) := by
    rw [Cartier.nonzeroLocus_secPull]
    change i (genericPoint _) ∈ Out.nonzeroLocus s
    rwa [redι_clo]
  have hV : genericPoint _ ∈ Out.nonzeroLocus (Cartier.secPull s (j ≫ F.π)) := by
    rw [Cartier.nonzeroLocus_secPull]
    change F.π (j (genericPoint _)) ∈ Out.nonzeroLocus s
    rwa [redι_clo, (htop z).1]
  have hii := i.isClosedEmbedding.injective
  have hmul (a) : cutMult (N.pow m).isLB s z (i a) = (divOfSec (LB.isLB_pull (N.pow m).isLB i) _ hW).mult a := by
    rw [cutMult, dif_pos (show _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull (N.pow m).B i s) from hW)]
    exact hii.extend_apply _ _ a
  have hfinW := (divOfSec (LB.isLB_pull (N.pow m).isLB i) _ hW).finite_support_mult
  have hfin : (Function.support (cutMult (N.pow m).isLB s z)).Finite := (hfinW.image i).subset fun w hw => by
    obtain ⟨a, rfl, -⟩ := CutSec.exists_of_cutMult_ne_zero _ s hw
    exact ⟨a, by rw [Function.mem_support, ← hmul]; exact hw, rfl⟩
  refine ⟨hfin, ?_⟩

  have hlift (a) : ∃ v, j v = top (i a) := by
    change _ ∈ Set.range j
    rw [range_redι]
    change _ ∈ closure {top z}
    rw [hcl, Set.mem_preimage, (htop _).1]
    exact (range_redι (clo z)).le ⟨a, rfl⟩
  choose u hu using hlift
  have hρu (a) : ρ (u a) = a := hii (by rw [hρ', hu, (htop _).1])
  have hut (a) (v) (hv : ρ v = a) : u a ⤳ v := j.isClosedEmbedding.isInducing.specializes_iff.1 (by
    rw [hu]
    exact (htop _).2 _ (by rw [← hρ', hv]))
  have hmu (a) : (divOfSec (LB.isLB_pull (N.pow m).isLB _) _ hV).mult (u a) = cutMult (N.pow m).isLB s z (i a) := by
    have key (b) (hb : ρ ≫ i = b) (hV : genericPoint _ ∈ Out.nonzeroLocus (Cartier.secPull s b)) :
        (divOfSec (LB.isLB_pull (N.pow m).isLB b) _ hV).mult (u a) = (divOfSec (LB.isLB_pull (N.pow m).isLB i) _ hW).mult (ρ (u a)) := by
      subst hb
      exact mult_of_top ρ i (N.pow m).isLB s hV hW fun v hv => hut a v (hv.trans (hρu a))
    exact (key _ hρ hV).trans ((congrArg _ (hρu a)).trans (hmul a).symm)
  have hsum (g : F.Y → ℝ) : ∑ᶠ v, ((divOfSec (LB.isLB_pull (N.pow m).isLB _) _ hV).mult v : ℝ) * g (j v) =
      ∑ w ∈ hfin.toFinset, (cutMult (N.pow m).isLB s z w : ℝ) * g (top w) := by
    have e₁ : ∀ {A B : Type} (f : B → ℝ) (c : A → B), Function.Injective c → Function.support f ⊆ Set.range c →
        ∑ᶠ b, f b = ∑ᶠ a, f (c a) := fun f c hc hs => by
      rw [← finsum_mem_range hc, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]
    refine (e₁ _ u (Function.LeftInverse.injective hρu) fun v hv => ⟨ρ v, eq_of_mult_ne_zero _ (N.pow m).isLB s hV
      (hut _ v rfl) (by rw [← hρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hρu]) fun h0 => hv (by simp [h0])⟩).trans
      (Eq.trans ?_ (finsum_eq_sum_of_support_subset (fun w => (cutMult (N.pow m).isLB s z w : ℝ) * g (top w)) fun w hw => by
        simpa using fun h0 : cutMult (N.pow m).isLB s z w = 0 => hw (by simp [h0])))
    refine Eq.trans (finsum_congr fun a => ?_) (e₁ _ i hii fun w hw =>
      (CutSec.exists_of_cutMult_ne_zero (N.pow m).isLB s (z := z) fun h0 => hw (by simp [h0])).imp fun _ h => h.1).symm
    rw [hmu, hu]

  have hwd := existsUnique_val_arch hC k X p d hX E r h H F N
  have hval (w : X) (e' : ℕ) (hw : topologicalKrullDim (closure ({w} : Set X)) = (e' + 2 : ℕ)) :
      ∃ Φ, IsHtFun (F.fam H N) (top w) (e' + 2 + r.choose 2) Φ ∧ Φ (vdmPol r e') = F.val H N w e' := by
    obtain ⟨y, Φ, hy, hΦ, e⟩ := Classical.epsilon_spec ((hwd w e').1 hw).exists
    obtain rfl := isTop_unique (htop w) hy
    exact ⟨Φ, hΦ, e⟩
  have hval' (w : X) : ∃ Φ, cutMult (N.pow m).isLB s z w ≠ 0 →
      IsHtFun (F.fam H N) (top w) (e + 2 + r.choose 2) Φ ∧ Φ (vdmPol r e) = F.val H N w e := by
    by_cases hw : cutMult (N.pow m).isLB s z w = 0
    · exact ⟨0, fun h => absurd hw h⟩
    obtain ⟨a, rfl, ha, -⟩ := CutSec.exists_of_cutMult_ne_zero _ s hw
    refine (hval _ e ?_).imp fun _ h _ => h
    rw [← CutSec.dim_closure_of_coheight hX i (n := e + 2) ((dim_clo z).trans hdim) ha]
    refine topologicalKrullDim_eq_of_isEmbedding (i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton]
  choose Ψ hΨ using hval'
  obtain ⟨Φ, hΦ, hΦv⟩ := hval z (e + 1) hdim
  obtain ⟨y, Λ, hy, hΛ, hΛv⟩ := Classical.epsilon_spec ((hwd z e).2 hdim (N.pow m) s hz).exists
  obtain rfl := isTop_unique (htop z) hy
  have eD : e + 1 + 2 + r.choose 2 = e + 2 + r.choose 2 + 1 := by omega
  rw [eD] at hΦ
  have hdV : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (clo (top z))).subscheme =
      (e + 2 + r.choose 2 + 1 : ℕ) := by
    rw [dim_clo, hd z _ hdim, ← eD]
  have hiso : (((F.fam H N none).restr j).pow m).Isometric ((N.pow m).pull (j ≫ F.π) (Category.assoc _ _ _)) := by
    have R := N.refines_pull_comp F.π rfl j rfl (Category.assoc _ _ _)
    have I : (N.pull (j ≫ F.π) (Category.assoc _ _ _)).Isometric ((N.pull F.π rfl).pull j rfl) :=
      HermLB.isometric_of_chart _ R.le (fun x => R.g _ (𝟙 _) x) fun σ c y hy => ((R.φ σ c y hy).trans (add_zero _)).symm
    refine (I.symm.pow m).trans (HermLB.icls_eq_iff.1 ?_)
    rw [HermLB.icls_pow, HermLB.icls_pull, HermLB.icls_pull, HermLB.icls_pow, map_nsmul]
  have hzero := Model.eq_zero_of_pow (e + 2 + r.choose 2)
    ((m : ℝ) • Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) -
      (∑ w ∈ hfin.toFinset, (cutMult (N.pow m).isLB s z w : ℝ) • Ψ w - Λ)) (fun n => ?_) fun P D hD hP => ?_
  · have := sub_eq_zero.1 (DFunLike.congr_fun hzero (vdmPol r e))
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
      LinearMap.sum_apply, smul_eq_mul] at this
    rw [← hΦv, vdmPol_succ, this, hΛv, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun w hw => by
      simpa using fun h0 : cutMult (N.pow m).isLB s z w = 0 => hw (by simp [h0])]
    exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun w hw => by rw [(hΨ w (by simpa using hw)).2]) rfl
  · obtain ⟨g, hg⟩ := (hC.arExists k F.Y _ _ hY).1 (comb (F.fam H N) n)
    have e₁ := mixed hY none m j hdV _ hiso (Cartier.secPull s _) hV (by rw [redι_clo]; exact hΦ) n hg hC
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
      LinearMap.sum_apply, smul_eq_mul]
    rw [e₁, hΛ.1 n, sub_eq_zero]
    refine congrArg₂ (· - ·) ((hsum g).trans (Finset.sum_congr rfl fun w hw => ?_)) (congrArg _ ?_)
    · obtain ⟨g', hg', e₂⟩ := (hΨ w (by simpa using hw)).1.1 n
      rw [← e₂, hg.unique hY hg']
    · funext σ v
      exact congrArg (Real.log · / 2) (((N.pow m).φ σ).nsq_pull_secPull (j ≫ F.π) (Category.assoc _ _ _) s v)
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
      LinearMap.sum_apply, smul_eq_mul]
    rw [hΦ.2 _ (1 + D) (by omega) ((isHomogeneous_X ℝ none).mul hP), hΛ.2 P D hD hP,
      Finset.sum_eq_zero fun w hw => by rw [(hΨ w (by simpa using hw)).1.2 P D hD hP, mul_zero]]
    simp

end GlobalTheory.VdmCut

end
