import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_epsMul_one (R : Type) [CommRing R] : spMap (epsMul (1 : R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [epsMul]

theorem latDR_subset_latHT {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB H X) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X) : latDR t x ⊆ latHT t p x := by
  rintro v ⟨xO, hx, vO, hv, e⟩
  refine ⟨xO, hx, 0, vO, hv, by rw [pow_zero, sp_epsMul_one, Category.id_comp, e], fun n c g _ => ?_⟩
  simp

abbrev torus (X : Scheme.{0}) : SAB H X :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus X (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def charUnit {A : Type} [CommRing A] {g : Sp A ⟶ X} (w : Over.mk g ⟶ splitTorus X (𝓞 E)) (a : 𝓞 E) : Aˣ :=
  ⟨GlobalTheory.Diag.charVal w a, GlobalTheory.Diag.charVal w (-a), by rw [← GlobalTheory.Diag.charVal_add, add_neg_cancel, GlobalTheory.Diag.charVal_zero],
    by rw [← GlobalTheory.Diag.charVal_add, neg_add_cancel, GlobalTheory.Diag.charVal_zero]⟩

def torusChar {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) : TorsChar (torus H X) x q where
  χ _ _ _ _ g := charUnit g a
  mul _ _ _ _ g g' _ _ := Units.ext (GlobalTheory.Diag.charVal_mul g g' a)
  nat B B' _ _ _ _ _ _ φ g g' _ h :=
    (GlobalTheory.Diag.left_eq_iff φ.toRingHom (by rw [← Category.assoc, sp_comp]; congr 2; exact φ.comp_algebraMap.symm) g' g).1 h a

theorem torusChar_epsVec {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) (I : Ideal O) (c : 𝓞 E →+ O ⧸ I) :
    (((torusChar H x q a).χ (DualNumber (O ⧸ I)) (GlobalTheory.Diag.epsVec _ c) : (DualNumber (O ⧸ I))ˣ) :
      DualNumber (O ⧸ I)).snd = c a := by
  refine (congrArg TrivSqZeroExt.snd (GlobalTheory.Diag.charVal_epsVec c a)).trans ?_
  simp

theorem dual_base {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [sp_comp, sp_comp]
  congr 1
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem latHT_torus {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (hp : (p : C) ≠ 0)
    (x : Sp C ⟶ X) : latHT (torus H X) p x = latDR (torus H X) x := by
  refine Set.Subset.antisymm ?_ (latDR_subset_latHT _ p x)
  rintro v ⟨xO, hx, m, vO, hv, e, hd⟩
  let O : Type := intO C
  let w : Over.mk (spMap (algebraMap O (DualNumber O)) ≫ xO) ⟶ splitTorus X (𝓞 E) := Over.homMk vO hv.1
  have hb : xO = spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (algebraMap O (DualNumber O)) ≫ xO := by
    rw [← Category.assoc, GlobalTheory.Diag.fstHom_base, Category.id_comp]
  obtain ⟨c, hc⟩ := (GlobalTheory.Diag.exists_epsVec_iff w).2 ((GlobalTheory.Diag.reduces_iff hb w).1 hv.2)
  have hdiv : ∀ a, (p : O) ^ m ∣ c a := fun a => by
    let I : Ideal O := Ideal.span {(p : O) ^ m}
    have hg : spMap (algebraMap O (DualNumber (O ⧸ I))) ≫ xO =
        spMap (dualMap (Ideal.Quotient.mk I)) ≫ spMap (algebraMap O (DualNumber O)) ≫ xO := by
      rw [← Category.assoc, sp_comp]
      congr 2
      ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']
    have h := hd m (torusChar H xO _ a) (GlobalTheory.Diag.epsVec _ ((Ideal.Quotient.mk I).toAddMonoidHom.comp c)) (by
      change _ = spMap _ ≫ w.left
      rw [← hc]
      refine (GlobalTheory.Diag.left_eq_iff _ hg _ _).2 fun b => ?_
      rw [GlobalTheory.Diag.charVal_epsVec, GlobalTheory.Diag.charVal_epsVec]
      ext <;> simp [dualMap])
    rw [torusChar_epsVec] at h
    have h0 : (p : O ⧸ I) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.span_singleton_zero, Ideal.mem_bot] at h
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
  choose d hdd using hdiv
  have hp' : (p : O) ^ m ≠ 0 := pow_ne_zero _ fun h => hp (by simpa using congrArg (intO C).subtype h)
  let c' : 𝓞 E →+ O := AddMonoidHom.mk' d fun a b => mul_left_cancel₀ hp' (by rw [mul_add, ← hdd, ← hdd, ← hdd, map_add])
  let w' : Over.mk (spMap (algebraMap O (DualNumber O)) ≫ xO) ⟶ splitTorus X (𝓞 E) := GlobalTheory.Diag.epsVec _ c'
  refine ⟨xO, hx, w'.left, ⟨Over.w w', (GlobalTheory.Diag.reduces_iff hb w').2 ((GlobalTheory.Diag.exists_epsVec_iff w').1 ⟨_, rfl⟩)⟩, ?_⟩
  have h1 : vO = spMap (epsMul ((p : O) ^ m)) ≫ w'.left := by
    change w.left = _
    rw [← hc]
    refine (GlobalTheory.Diag.left_eq_iff _ ?_ _ _).2 fun b => ?_
    · rw [← Category.assoc, sp_comp]
      congr 2
      ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [GlobalTheory.Diag.charVal_epsVec, GlobalTheory.Diag.charVal_epsVec, hdd]
      ext <;> simp [epsMul, c', mul_comm]
  have h2 : spMap (epsMul ((p : C) ^ m)⁻¹) ≫ spMap (epsMul ((p : C) ^ m)) = 𝟙 _ := by
    rw [sp_comp, ← sp_epsMul_one]
    congr 1
    ext r <;> simp [epsMul, hp]
  have h3 : spMap (epsMul ((p : C) ^ m)⁻¹) ≫ spMap (dualMap (intO C).subtype) ≫ spMap (epsMul ((p : O) ^ m)) =
      spMap (dualMap (intO C).subtype) := by
    rw [sp_comp, sp_comp]
    congr 1
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul, dualMap, O]
    · simp [epsMul, dualMap, O]
      field_simp
  rw [← Category.id_comp v, ← h2, Category.assoc, ← e, h1]
  exact (congrArg (· ≫ w'.left) h3.symm).trans (by simp only [Category.assoc]; rfl)

end Lat

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_flagPt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]
    (y : Sp Ω ⟶ gen Z) : ∃ z : FlagPt Z Ω, z.y = y := by
  have h : y ≫ genStr Z = spMap (Spec.preimage (y ≫ genStr Z)).hom := (Spec.map_preimage _).symm
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z Ω _ y h
  exact ⟨⟨_, y, h, f.v, f.tan, f.eig, f.basis⟩, rfl⟩

instance intO_valRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing (intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  by_cases h : ‖(a : C)‖ ≤ ‖(b : C)‖
  · by_cases hb : (b : C) = 0
    · refine ⟨1, Or.inr (Subtype.ext ?_)⟩
      rw [hb, norm_zero, norm_le_zero_iff] at h
      simp [h, hb]
    · refine ⟨⟨a / b, show ‖(a / b : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩,
        Or.inr (Subtype.ext ?_)⟩
      simp [mul_div_cancel₀ _ hb]
  · have ha : (a : C) ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨⟨b / a, show ‖(b / a : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ (le_of_not_ge h) (norm_nonneg _)⟩,
      Or.inl (Subtype.ext ?_)⟩
    simp [mul_div_cancel₀ _ ha]

instance intO_frac (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

theorem latDR_nonempty (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : (latDR Z.t x).Nonempty := by
  have := isProper_toroidalModel_structureMap Z
  let φ : 𝓞 c.F →+* C := (Spec.preimage (x ≫ Z.s)).hom
  have hφ : ∀ a, φ a ∈ intO C := fun a => by
    have h1 : IsIntegral (intO C) (φ a) := (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) φ
      (RingHom.ext_int _ _)
    classical
    let _ : GCDMonoid (intO C) := IsBezout.toGCDDomain _
    have : IsIntegrallyClosed (intO C) := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := intO C) (K := C)).1 h1
    exact hb ▸ b.2
  have hv : ValuativeCriterion.Existence Z.s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s)
    exact h.1
  let S : ValuativeCommSq Z.s :=
    { R := intO C, K := C, i₁ := x, i₂ := spMap (φ.codRestrict _ hφ)
      commSq := ⟨by
        rw [← Spec.map_preimage (x ≫ Z.s)]
        exact Spec.map_comp (CommRingCat.ofHom (φ.codRestrict _ hφ)) (CommRingCat.ofHom (intO C).subtype)⟩ }
  obtain ⟨⟨xO, h1, -⟩⟩ := (hv S).exists_lift
  let p : tEpsG xO ⟶ Over.mk xO := Over.homMk (spMap (algebraMap _ (DualNumber _))) rfl
  refine ⟨_, xO, h1, (1 : tEpsG xO ⟶ Z.t.G).left, ⟨Over.w _, ?_⟩, rfl⟩
  rw [← MonObj.comp_one p, Over.comp_left, ← Category.assoc]
  change (_ ≫ spMap _) ≫ _ = _
  rw [GlobalTheory.Diag.fstHom_base, Category.id_comp]

end Pts

theorem polar_sq (a b : ℝ) : polar (fun x : ℝ => x ^ 2) {a, b} = a * b := by
  have h : ({a, b} : Multiset ℝ) = a ::ₘ b ::ₘ 0 := rfl
  simp only [h, polar, Multiset.powerset_cons, Multiset.powerset_zero]
  simp
  ring

theorem polar_cube (a b c : ℝ) : polar (fun x : ℝ => x ^ 3) {a, b, c} = a * b * c := by
  have h : ({a, b, c} : Multiset ℝ) = a ::ₘ b ::ₘ c ::ₘ 0 := rfl
  simp only [h, polar, Multiset.powerset_cons, Multiset.powerset_zero]
  simp [Nat.factorial]
  ring

def arReal (Tau : Type) (N g : ℕ) : ArIn Tau N g Unit where
  A _ := ℝ
  num _ M := M.prod
  root a R _ _ := if a 2 then R else 1
  whole _ _ _ _ := 1

theorem numL_pow {A : Type} (num : Multiset A → ℝ) (d : ℕ) (a : A) :
    numL num d (MvPolynomial.X a ^ d) = num (Multiset.replicate d a) := by
  have : (MvPolynomial.X a ^ d : MvPolynomial A ℝ) = MvPolynomial.basisMonomials A ℝ (Finsupp.single a d) := by
    simp [MvPolynomial.X_pow_eq_monomial]
  rw [this, numL, Module.Basis.constr_basis]
  simp [Multiset.nsmul_singleton]

theorem arReal_deg {Tau : Type} [Fintype Tau] {N g : ℕ} (x : Tau × Fin N) (S : Finset ℕ) (R : ℝ) :
    (arReal Tau N g).arDeg S R (MvPolynomial.X x ^ (Formalism.DegreeFormula.dimFl Tau N + 1)) =
      (if 2 ∈ S then R else 1) ^ (Formalism.DegreeFormula.dimFl Tau N + 1) := by
  rw [ArIn.arDeg, LinearMap.sum_apply, Fintype.sum_unique]
  change numL _ _ (MvPolynomial.rename _ _) = _
  rw [map_pow, MvPolynomial.rename_X, numL_pow]
  simp [arReal, ArIn.ind, -Multiset.replicate_succ]

section Stages

variable {D : D7} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)

def locOf : LocSt D N j ng := ⟨P.loc, P.ex, P.locB, P.pbKF⟩

def globOf : GlobSt fun p => (P.loc p).Mdl :=
  ⟨P.Xg, P.bc, P.DivG, P.effD, P.noVertD, P.posBdD, P.ampleOnAbelianBase, P.Met, P.nefFibM, P.ampleGen, P.limRA⟩

open PadPkg in

def admissibleStageOfPackage : AdmSt D N j jC :=
  ⟨fun p _ la => P.Mp p la, fun p _ la z => md P p la z, fun p _ la z => P.CurveM p la z,
    fun p _ la z => P.degM p la z, fun p _ la => P.htMdl p la⟩

end Stages

theorem nonempty_flagPt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Z : Model Xo c β) [Nonempty (gen Z)] : Nonempty (FlagPt Z Qb) := by
  have := isProper_genStr Z
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := gen Z)).exists_closed_singleton Set.univ_nonempty
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  let φ := Spec.preimage ((gen Z).fromSpecResidueField x ≫ genStr Z)
  have h1 : IsFinite (Spec.map φ) := by
    rw [Spec.map_preimage]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  let k : Type := (gen Z).residueField x
  let _ : Algebra c.F k := φ.hom.toAlgebra
  have : Module.Finite c.F k := (IsFinite.SpecMap_iff φ).1 h1
  have : Algebra.IsAlgebraic ℚ c.F := have := c.fin; inferInstance
  let em : c.F →+* Qb := (IntermediateField.inclusion (le_algebraicClosure ℚ ℂ c.F)).toRingHom
  let _ : Algebra c.F Qb := em.toAlgebra
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let ψ : k →ₐ[c.F] Qb := IsAlgClosed.lift
  obtain ⟨z, -⟩ := exists_flagPt Z Qb (spMap ψ.toRingHom ≫ (gen Z).fromSpecResidueField x)
  exact ⟨z⟩

section Sign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem grNorm_le_of_smul {X : Scheme.{0}} {t : SAB H X} {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X}
    {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hu : ∀ k, IsTanAtG t x (u k)) {a : C} (ha : a ≠ 0) (h : ∀ w ∈ Λ, spMap (epsMul a) ≫ w ∈ Λ') (i : Fin m)
    (hne : (Guard.grSet t x Λ u i).Nonempty) : ‖a‖ * grNorm t x Λ' u i ≤ grNorm t x Λ u i := by
  refine le_csInf hne ?_
  rintro _ ⟨cf, h0, h1, ⟨w, hw, hc⟩, rfl⟩
  have hb : BddBelow (Guard.grSet t x Λ' u i) := ⟨0, by rintro _ ⟨cf, -, -, -, rfl⟩; positivity⟩
  have := csInf_le hb ⟨fun k => a * cf k, mul_ne_zero ha h0, fun k hk => by simp [h1 k hk],
    ⟨_, h w hw, Guard.comb_smul hu hc a⟩, rfl⟩
  have hp : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [Guard.grNorm_eq]
  refine (mul_le_mul_of_nonneg_left this hp.le).trans_eq ?_
  rw [norm_mul]
  field_simp

theorem lnLie_sub (hB : HTBoundSt) {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] (y : FlagPt Z Ω)
    (p : ℕ) [hp : Fact p.Prime] (io : Ω →+* ℂ_[p]) (τ : E →+* ℂ) (k : ℕ) :
    0 ≤ y.lnLie io p false τ k - y.lnLie io p true τ k ∧
      y.lnLie io p false τ k - y.lnLie io p true τ k ≤ 1 / ((p : ℝ) - 1) * Real.log p := by
  have h1 : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  have hlog : 0 < Real.log p := Real.log_pos h1
  by_cases hk : k < Dw.mult τ
  swap
  · simp only [FlagPt.lnLie, dif_neg hk, sub_self]
    exact ⟨le_rfl, mul_nonneg (by rw [one_div, inv_nonneg]; linarith) hlog.le⟩
  simp only [FlagPt.lnLie, dif_pos hk]
  have hu := fun k => GlobalTheory.FactorDepth.isTanAtG_map _ io (y.tan τ k)
  have hi := (Guard.indep_u y τ).map io (y.tan τ)
  obtain ⟨n1, p1⟩ := Guard.grNorm_latDR_pos Z _ hu hi ⟨k, hk⟩
  obtain ⟨n2, p2⟩ := Guard.grNorm_latHT_pos Z hB p _ hu hi ⟨k, hk⟩
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) hp1
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1.ne'] at ha
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 ha.symm)
  have hla : Real.log ‖a‖ = -(1 / ((p : ℝ) - 1)) * Real.log p := by
    have : ((p : ℝ) - 1) * Real.log ‖a‖ = - Real.log p := by
      rw [← hc, ← Real.log_pow, ← norm_pow, ha, hn, Real.log_inv]
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    linarith
  have hna : ‖a‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [Real.rpow_def_of_pos (by linarith), mul_comm, ← hla, Real.exp_log (norm_pos_iff.2 ha0)]
  have e1 := grNorm_le_of_smul hu (a := 1) one_ne_zero (Λ' := latHT Z.t p _) (fun w hw => by
    rw [sp_epsMul_one, Category.id_comp]; exact latDR_subset_latHT _ p _ hw) _ n1
  obtain ⟨xO, hx, hx'⟩ := Guard.existsUnique_ext Z (spMap io ≫ y.y ≫ genι Z)
  have e2 := grNorm_le_of_smul hu ha0 (Λ' := latDR Z.t _) (fun w hw => by
    have := hB E H _ Z.t p ℂ_[p] hn xO (fun b hb => hx' b (hb.trans hx)) w (hx ▸ hw) a hna.le
    exact hx ▸ this) _ n2
  rw [norm_one, _root_.one_mul] at e1
  have l1 := Real.log_le_log p2 e1
  have l2 := Real.log_le_log (mul_pos (norm_pos_iff.2 ha0) p1) e2
  rw [Real.log_mul (norm_ne_zero_iff.2 ha0) p1.ne', hla] at l2
  simp only [lat]
  constructor <;> linarith

end Sign

section Phi

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem phi_bounds (hB : HTBoundSt) (p : ℕ) [Fact p.Prime] (y : Pt s) (x : DV.Rt D.what₂.Tau N) :
    ((x.2 : ℕ) < j → vDiff D.host.E p * Real.log p ≤ phi s p y x ∧
      phi s p y x ≤ (vDiff D.host.E p + 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    (j ≤ (x.2 : ℕ) → -(1 / ((p : ℝ) - 1) * Real.log p) ≤ phi s p y x ∧ phi s p y x ≤ 0) := by
  rw [phi, Guard.lnAt_eq, Guard.lnAt_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (x.2 : ℕ) < S.Dw.p := by rw [S.p_eq]; exact h
    have := lnLie_sub hB y p (iotaP p) (DV.tauEmb D x.1) x.2
    simp only [FlagPt.lnRoot, if_pos h', if_true, Bool.false_eq_true, if_false]
    constructor <;> linarith [this.1, this.2]
  · have h' : ¬ (x.2 : ℕ) < S.Dw.p := by rw [S.p_eq]; exact h.not_gt
    have := lnLie_sub hB y p (iotaP p) (conjEmb (DV.tauEmb D x.1)) (S.Dw.p + S.Dw.q - 1 - x.2)
    simp only [FlagPt.lnRoot, if_neg h']
    constructor <;> linarith [this.1, this.2]

theorem root_in_range (x : DV.Rt D.what₂.Tau N) :
    ((x.2 : ℕ) < S.Dw.p → (x.2 : ℕ) < S.Dw.mult (DV.tauEmb D x.1)) ∧
    (¬ (x.2 : ℕ) < S.Dw.p → S.Dw.p + S.Dw.q - 1 - x.2 < S.Dw.mult (conjEmb (DV.tauEmb D x.1))) := by
  have h := A.cm x.1
  refine ⟨fun h' => by rwa [Datum.mult, if_pos h], fun h' => ?_⟩
  have hne : conjEmb (DV.tauEmb D x.1) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
    change starRingEnd ℂ (DV.tauEmb D x.1 _) ≠ _
    rw [h]
    intro e
    have him : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 e
    have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
    have h3 : (0 : ℝ) < A.H.d := Nat.cast_pos.2 A.H.d_prime.pos
    simp [pow_two, him] at h2
    nlinarith [mul_self_nonneg A.H.rt0.re]
  have := x.2.2
  have := S.rank_eq
  rw [Datum.mult, if_neg hne]
  omega

def admissibleTrivialStage (D : D7) {N j : ℕ} (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : AdmSt D N j jC where
  admitted _ _ _ := Unit
  mdl p _ la _ := GlobalTheory.trivialAdmissibleModel D p (jC p la) N j hj
  Crv _ _ _ _ := DV.Rt D.what₂.Tau N → ℝ
  deg _ _ _ _ c := c
  ht _ _ _ := ()

end Phi

end GlobalTheory.ShFam.Pad.Test
