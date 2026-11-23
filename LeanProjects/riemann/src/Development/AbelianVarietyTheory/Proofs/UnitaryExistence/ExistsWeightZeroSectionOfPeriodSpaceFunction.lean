import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CompFun

open GlobalTheory.CompIdem

theorem isField_tensor {K κ F : Type} [Field K] [CharZero K] [Field κ] [Field F] [Algebra K κ] [Algebra K F]
    [FiniteDimensional K F] (h : ∀ x : κ, IsIntegral K x → x ∈ (algebraMap K κ).range) : IsField (κ ⊗[K] F) := by
  let Ω := AlgebraicClosure κ
  let ψ : F →ₐ[K] Ω := IsAlgClosed.lift
  let pb := Field.powerBasisOfFiniteOfSeparable K F
  let m : κ ⊗[K] F →ₐ[κ] Ω := Algebra.TensorProduct.lift (Algebra.ofId κ Ω) ψ fun _ _ => Commute.all _ _
  let b := Algebra.TensorProduct.basis κ pb.basis
  have hd : (minpoly κ (ψ pb.gen)).natDegree = pb.dim := by
    rw [GlobalTheory.GeomIrr.natDegree_minpoly_eq h (pb.isIntegral_gen.map ψ),
      minpoly.algHom_eq ψ ψ.toRingHom.injective, pb.natDegree_minpoly]
  have li : LinearIndependent κ (m.toLinearMap ∘ b) := by
    have h1 := (linearIndependent_pow (K := κ) (ψ pb.gen)).comp (Fin.cast hd.symm) (Fin.cast_injective _)
    convert h1 using 1
    funext i
    simp [m, b]
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : Finsupp.linearCombination κ (m.toLinearMap ∘ b) (b.repr x) = 0 := by
      rw [← Finsupp.apply_linearCombination, b.linearCombination_repr]
      exact hx
    exact b.repr.map_eq_zero_iff.1 (linearIndependent_iff.1 li _ h2)
  have : IsDomain (κ ⊗[K] F) := hinj.isDomain m.toRingHom
  exact Algebra.TensorProduct.isField_of_isAlgebraic K κ F (Or.inr inferInstance)

theorem eq_of_fst_eq {K F : Type} [Field K] [CharZero K] [Field F] [Algebra K F] [FiniteDimensional K F]
    {Y : Scheme.{0}} (s : Y ⟶ Sp K) (pt : Y)
    (h : ∀ x : Y.residueField pt, (Spec.preimage (Y.fromSpecResidueField pt ≫ s)).hom.IsIntegralElem x →
      x ∈ (Spec.preimage (Y.fromSpecResidueField pt ≫ s)).hom.range)
    (a b : ↥(pullback s (spMap (algebraMap K F)))) (ha : pullback.fst s _ a = pt) (hb : pullback.fst s _ b = pt) :
    a = b := by
  letI : Algebra K (Y.residueField pt) := (Spec.preimage (Y.fromSpecResidueField pt ≫ s)).hom.toAlgebra
  have hf := isField_tensor (F := F) (κ := Y.residueField pt) h
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct K (Y.residueField pt) F)
  have e : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField pt))) = Y.fromSpecResidueField pt ≫ s :=
    Spec.map_preimage _
  rw [e] at H
  have H' := IsPullback.of_right' H.flip (IsPullback.of_hasPullback s (spMap (algebraMap K F))).flip
  have hs : Subsingleton (PrimeSpectrum (Y.residueField pt ⊗[K] F)) := by
    letI := hf.toField
    infer_instance
  obtain ⟨x, hx, -⟩ := Scheme.exists_preimage_of_isPullback H' a (IsLocalRing.closedPoint _)
    (ha.trans (Scheme.fromSpecResidueField_apply pt _).symm)
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H' b (IsLocalRing.closedPoint _)
    (hb.trans (Scheme.fromSpecResidueField_apply pt _).symm)
  rw [← hx, ← hy, hs.elim x y]

theorem mem_connectedComponent_of_fst {K F : Type} [Field K] [CharZero K] [Field F] [Algebra K F]
    [FiniteDimensional K F] {Y : Scheme.{0}} (s : Y ⟶ Sp K) [Smooth s]
    (h : ∀ (Z : irreducibleComponents Y) (x : Y.residueField (Z.2.1 : IsIrreducible Z.1).genericPoint),
      (Spec.preimage (Y.fromSpecResidueField _ ≫ s)).hom.IsIntegralElem x →
      x ∈ (Spec.preimage (Y.fromSpecResidueField _ ≫ s)).hom.range)
    (a b : ↥(pullback s (spMap (algebraMap K F))))
    (hab : pullback.fst s (spMap (algebraMap K F)) a ∈
      connectedComponent (pullback.fst s (spMap (algebraMap K F)) b)) :
    a ∈ connectedComponent b := by
  let π := pullback.fst s (spMap (algebraMap K F))
  haveI : Flat (spMap (algebraMap K F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (GlobalTheory.GeomIrr.flat_of_field _)
  obtain ⟨Z, hZ, hle⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (connectedComponent (π b))
    ⟨⟨_, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth s _⟩
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨a', ha, ea⟩ := Flat.generalizingMap π (hg.specializes (hle hab))
  obtain ⟨b', hb, eb⟩ := Flat.generalizingMap π (hg.specializes (hle mem_connectedComponent))
  obtain rfl : a' = b' := eq_of_fst_eq s _ (h ⟨Z, hZ⟩) a' b' ea eb
  have h1 := ha.mem_closed isClosed_connectedComponent mem_connectedComponent
  have h2 := hb.mem_closed isClosed_connectedComponent mem_connectedComponent
  rwa [connectedComponent_eq h2] at h1

theorem exists_extension {K F : Type} [Field K] [Field F] [Algebra K F] [Algebra.IsAlgebraic K F] (σ : K →+* ℂ) :
    ∃ σ' : F →+* ℂ, σ'.comp (algebraMap K F) = σ := by
  letI := σ.toAlgebra
  exact ⟨(IsAlgClosed.lift : F →ₐ[K] ℂ).toRingHom, AlgHom.comp_algebraMap _⟩

theorem const_on_component_of_closed {K : IntermediateField ℚ ℂ} [FiniteDimensional ℚ K] (σ : K →+* ℂ)
    {Y : Scheme.{0}} (s : Y ⟶ Sp K) [Smooth s] [QuasiCompact s]
    (h : ∀ (Z : irreducibleComponents Y) (x : Y.residueField (Z.2.1 : IsIrreducible Z.1).genericPoint),
      (Spec.preimage (Y.fromSpecResidueField _ ≫ s)).hom.IsIntegralElem x →
      x ∈ (Spec.preimage (Y.fromSpecResidueField _ ≫ s)).hom.range)
    (t : (Sp ℂ ⟶ Y) → ℕ)
    (ht : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y)), IsOpen B →
      (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ContinuousOn (fun b => t (y b)) B)
    (p q : Sp ℂ ⟶ Y) (hp : p ≫ s = spMap σ) (hq : q ≫ s = spMap σ)
    (hpq : p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ))) : t p = t q := by
  have hKL : K ≤ algebraicClosure ℚ ℂ := fun z hz =>
    mem_algebraicClosure_iff'.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : K)).map K.val)
  obtain ⟨S, hS, hrat⟩ := exists_rational_components hKL s
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => mem_algebraicClosure_iff'.1 (hS z hz)
  let F : IntermediateField ℚ ℂ := K ⊔ IntermediateField.adjoin ℚ (S : Set ℂ)
  have hK : K ≤ F := le_sup_left
  have hr := hrat F hK (sup_le hKL (IntermediateField.adjoin_le_iff.2 hS)) fun z hz =>
    (le_sup_right : _ ≤ F) (IntermediateField.subset_adjoin ℚ _ hz)
  letI : Algebra K F := (IntermediateField.inclusion hK).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite ℚ K F
  obtain ⟨σ', hσ⟩ := exists_extension (F := F) σ
  have e : spMap σ' ≫ spMap (algebraMap K F) = spMap σ := by rw [CompIdem.spMap_comp, hσ]
  let Y' := pullback s (spMap (algebraMap K F))
  let π : Y' ⟶ Y := pullback.fst _ _
  let s' : Y' ⟶ Sp F := pullback.snd _ _
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian s'
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace s'
  have : IsNoetherian Y' := {}
  let p' : Sp ℂ ⟶ Y' := pullback.lift p (spMap σ') (hp.trans e.symm)
  let q' : Sp ℂ ⟶ Y' := pullback.lift q (spMap σ') (hq.trans e.symm)
  have ep : p' ≫ π = p := pullback.lift_fst _ _ _
  have eq : q' ≫ π = q := pullback.lift_fst _ _ _
  have hc : p' (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q' (IsLocalRing.closedPoint ℂ)) :=
    mem_connectedComponent_of_fst s h _ _ (by rw [← ep, ← eq] at hpq; exact hpq)
  obtain ⟨r, hr1, hr2⟩ := hr (q' (IsLocalRing.closedPoint ℂ))
  have := const_on_component σ' s' r hr1 (fun x => t (x ≫ π))
    (fun m B y hB hy hh => ht m B _ hB (fun b hb => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy b hb, e]) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    p' q' (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) ((connectedComponent_eq hr2) ▸ hc) hr2
  simpa only [ep, eq] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_idempotent (hA : AllTest Xo c) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed Xo c)
    (i : Fin F.n) : ∃ χ ∈ sec Xo c 0 0, χ * χ = χ ∧ ∀ (y : FrPt Xo c (CAt σ)) (i' : Fin F.n) P,
      IsPeriod (F.Di i') ty P → y.x = F.u i' P → evR Xo c χ y = if i' = i then 1 else 0 := by
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  let pr : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ →
      (p ≫ pr) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, CompIdem.spMap_comp]
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    refine const_on_component_of_closed σ s (fun Z x hx => ?_) (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    have hx' : IsIntegral c.F (A := kap Z) x := hx
    obtain ⟨k, hk⟩ := hcl Z (algebraMap (kap Z) (Om Z) x) hx'.algebraMap.isAlgebraic
    rw [IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)] at hk
    exact ⟨k, (algebraMap (kap Z) (Om Z)).injective hk⟩
  let U : Set (Xo.XF c) := {z | ∃ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨χ, h1, h2, h3⟩ := exists_indicator hA U hU
  refine ⟨χ, h1, h2, fun y i' P hP hy => ?_⟩
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨h4, h5⟩ := h3 (CAt σ) y
  let p : Sp ℂ ⟶ Xo.XF c := basePt (S := CAt σ) y
  have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := (pullback.lift_fst _ _ _).trans hy
    rw [this]
    exact ht i' P hP
  let v : ℂ := evR Xo c χ (S := CAt σ) y
  have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ p (IsLocalRing.closedPoint ℂ) ∈ U :=
    h5 (IsLocalRing.closedPoint ℂ)
  have h7 : v ≠ 0 ↔ i' = i := by
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [← h8, h6]
    constructor
    · rintro ⟨q, hq, hqp, hqi⟩
      exact Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi))
    · rintro rfl
      exact ⟨p, hp, mem_connectedComponent, hp'⟩
  have h9 : IsIdempotentElem v := h4
  split_ifs with h
  · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h7.2 h)
  · exact not_not.1 (mt h7.1 h)

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => (map_one φ).symm, fun p t y y' _ => ?_⟩
  have hw : wchar (ex D 0 0) t = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex D 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  rw [hw, _root_.one_mul]
  rfl

theorem one_add_smul_pow {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {e : R} (he : e * e = e) (v : K)
    (m : ℕ) : (1 + (v - 1) • e) ^ m = 1 + (v ^ m - 1) • e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Algebra.smul_def, map_sub, map_mul, map_one]
    linear_combination (algebraMap K R (v ^ m) - 1) * (algebraMap K R v - 1) * he

theorem exists_section_of_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), 1 ≤ D.p + D.q → (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → FnAlgClosed Xo c → ∀ v : Fin F.n → c.F, ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ i, v i ^ m = 1) → f ^ m = 1) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P → Formalism.L2.PjFree.toC (evR Xo c f y) = σ (v i) := by
  intro E _ _ _ H D l Xo c σ g ty F _ _ _ _ hcl v
  classical
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H D l Xo c
  choose χ h1 h2 h3 using exists_idempotent hA σ F hcl
  refine ⟨∏ i, (1 + (v i - 1) • χ i), ?_, fun m hm => ?_, fun y i P hP hy => ?_⟩
  · refine Finset.prod_induction _ (· ∈ sec Xo c 0 0) (fun a b ha hb => ?_) one_mem_sec fun i _ =>
      add_mem one_mem_sec (Submodule.smul_mem _ _ (h1 i))
    simpa using sec_mul Xo c 0 0 0 0 ha hb
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [one_add_smul_pow (h2 i), hm i, sub_self, zero_smul, add_zero]
  · have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    have hy' := hA (CAt σ) y
    let ev : Rul Xo c →* CAt σ :=
      { toFun := fun f => evR Xo c f y
        map_one' := evalAt_one _ _ y hy'
        map_mul' := fun f f' => evalAt_mul _ _ f f' y }
    have hv : ∀ j, ev (1 + (v j - 1) • χ j) = if i = j then algebraMap c.F (CAt σ) (v i) else 1 := by
      intro j
      have e := h3 j y i P hP hy
      have e' : ev (1 + (v j - 1) • χ j) = 1 + algebraMap c.F (CAt σ) (v j - 1) * evR Xo c (χ j) y := by
        refine (evalAt_add _ _ _ _ y).trans ?_
        rw [evalAt_one _ _ y hy', evalAt_smul]
        rfl
      rw [e', e]
      split_ifs with h
      · subst h
        simp
      · simp
    have : ev (∏ i, (1 + (v i - 1) • χ i)) = algebraMap c.F (CAt σ) (v i) := by
      rw [map_prod, Finset.prod_congr rfl fun j _ => hv j, Finset.prod_ite_eq]
      simp
    exact this

end GlobalTheory.CompFun
