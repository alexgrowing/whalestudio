import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictExistsPtIdealEqBot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def eps {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) : Pol n →+* Γ(Z, f ⁻¹ᵁ mchart c) :=
  (f.app (mchart c)).hom.comp (dehomog c)

def gam {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) :
    Pol n →+* MvPolynomial (Fin (m + 1)) Γ(Z, f ⁻¹ᵁ mchart c) :=
  (MvPolynomial.map (f.app (mchart c)).hom).comp (GlobalTheory.CompanionTheory.MPDict.Spec.Phi c)

def ptPrime {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) :
    Ideal Γ(Z, f ⁻¹ᵁ mchart c) :=
  RingHom.ker (Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom

instance {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) :
    (ptPrime f c w hw).IsPrime := RingHom.ker_isPrime _

end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}
open GroundTheory.Heights₂.Heights (coordDeg localQuotLength)
open GlobalTheory.CompanionTheory.MPDict.Spec (mratio Phi)

theorem dehomog_X (c : ∀ k, Bk n k) (p : Σ k, Bk n k) : dehomog c (X p) = mratio c p := by
  simp only [dehomog, coe_eval₂Hom, eval₂_X, mratio]
  exact resG_pullRatio _

theorem eps_X {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (p : Σ k, Bk n k) :
    eps f c (X p) = (f.app (mchart c)).hom (mratio c p) := by
  rw [eps, RingHom.comp_apply, dehomog_X]

theorem eps_X_chart {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (k : Fin (m + 1)) :
    eps f c (X ⟨k, c k⟩) = 1 := by
  rw [eps_X, GlobalTheory.CompanionTheory.MPDict.Spec.mratio_self, map_one]

theorem dehomog_surj (c : ∀ k, Bk n k) : Function.Surjective (dehomog c) := by
  intro v
  have hle : Subring.closure (Set.range (mratio c)) ≤ (dehomog c).range := by
    rw [Subring.closure_le]
    rintro _ ⟨q, rfl⟩
    exact ⟨X q, dehomog_X c q⟩
  exact hle ((GlobalTheory.CompanionTheory.MPDict.Spec.closure_mratio c) ▸ Subring.mem_top v)

theorem eps_surjective {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (c : ∀ k, Bk n k) :
    Function.Surjective (eps f c) := by
  intro v
  obtain ⟨s, rfl⟩ := f.app_surjective _ (GlobalTheory.CompanionTheory.MPDict.Spec.isAffineOpen_mchart c) v
  obtain ⟨F, rfl⟩ := dehomog_surj c s
  exact ⟨F, rfl⟩

@[simp] theorem gam_X {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (p : Σ k, Bk n k) :
    gam f c (X p) = C (eps f c (X p)) * X p.1 := by
  simp [gam, eps_X]

theorem eval_one_gam {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (F : Pol n) :
    eval₂Hom (RingHom.id _) (fun _ => 1) (gam f c F) = eps f c F := by
  have e : (eval₂Hom (RingHom.id Γ(Z, f ⁻¹ᵁ mchart c)) (fun _ => 1)).comp (gam f c) = eps f c :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp)
  exact RingHom.congr_fun e F

theorem gam_of_form {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) {F : Pol n} {d : Fin (m + 1) → ℕ}
    (hF : IsWeightedHomogeneous (coordDeg n) F d) : gam f c F = C (eps f c F) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : ∀ k, ∑ i, e ⟨k, i⟩ = d k := fun k => by
    rw [← GroundTheory.Heights₂.Heights.weight_coordDeg_apply, hF (mem_support_iff.mp he)]
  have hX : ∏ p : Σ k, Bk n k, (X p.1 : MvPolynomial (Fin (m + 1)) Γ(Z, f ⁻¹ᵁ mchart c)) ^ e p = ∏ k, X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial (Fin (m + 1)) Γ(Z, f ⁻¹ᵁ mchart c)) ^ e ⟨k, i⟩ = _
    rw [← he' k, Finset.prod_pow_eq_pow_sum]
  have hm : (monomial e (coeff e F) : Pol n) = C (coeff e F) * ∏ p, X p ^ e p := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hm]
  simp only [map_mul, map_prod, map_pow, gam_X, mul_pow, Finset.prod_mul_distrib, hX]
  have hc : gam f c (C (coeff e F)) = C (eps f c (C (coeff e F))) := by
    simp [gam, eps, Phi, dehomog]
  rw [hc]
  ring
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}
open GroundTheory.Heights₂.Heights (coordDeg localQuotLength)
open GlobalTheory.CompanionTheory.MPDict.Spec (mratio Phi)

theorem mem_ptIdeal_iff_gam {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) (F : Pol n) :
    F ∈ ptIdeal (f w) ↔ MvPolynomial.map (Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom (gam f c F) = 0 := by
  have hw' : f w ∈ mchart c := hw
  rw [GlobalTheory.CompanionTheory.MPDict.Spec.mem_ptIdeal_iff c hw']
  have e : (Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom.comp (f.app (mchart c)).hom =
      (f.residueFieldMap w).hom.comp ((MP ℤ m n).evaluation (mchart c) (f w) hw').hom :=
    RingHom.ext fun s => (Scheme.evaluation_naturality_apply f w hw' s).symm
  have e2 : MvPolynomial.map (Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom (gam f c F) =
      MvPolynomial.map (f.residueFieldMap w).hom
        (MvPolynomial.map ((MP ℤ m n).evaluation (mchart c) (f w) hw').hom (Phi c F)) := by
    simp only [gam, RingHom.comp_apply, MvPolynomial.map_map, e]
  rw [e2]
  exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ (f.residueFieldMap w).hom.injective)).symm

theorem form_mem_iff {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) {F : Pol n} {d : Fin (m + 1) → ℕ}
    (hF : IsWeightedHomogeneous (coordDeg n) F d) : F ∈ ptIdeal (f w) ↔ eps f c F ∈ ptPrime f c w hw := by
  rw [mem_ptIdeal_iff_gam f c w hw, gam_of_form f c hF, ptPrime, RingHom.mem_ker, map_mul, map_C, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact C_eq_zero.1 h
    · exfalso
      simp only [map_prod, map_pow, map_X] at h
      exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h
  · intro h
    exact Or.inl (by rw [h, C_0])

theorem gam_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (hg : genericPoint Z ∈ f ⁻¹ᵁ mchart c) (F : Pol n) :
    gam f c F = 0 ↔ F ∈ ptIdeal (f (genericPoint Z)) := by
  rw [mem_ptIdeal_iff_gam f c _ hg]
  have hinj : Function.Injective (Z.evaluation (f ⁻¹ᵁ mchart c) (genericPoint Z) hg).hom := by
    intro a b h
    have h1 : Function.Injective (Z.presheaf.germ (f ⁻¹ᵁ mchart c) (genericPoint Z) hg).hom :=
      germ_injective_of_isIntegral Z _ hg
    have h2 : Function.Injective (Z.residue (genericPoint Z)).hom := (Z.residue (genericPoint Z)).hom.injective
    exact h1 (h2 h)
  exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ hinj)).symm

theorem map_eps_ptIdeal {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) :
    (ptIdeal (f w)).map (eps f c) = ptPrime f c w hw := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [mem_ptIdeal_iff_gam f c w hw] at hF
    rw [Ideal.mem_comap, ptPrime, RingHom.mem_ker, ← eval_one_gam]
    have e : ((Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom).comp (eval₂Hom (σ := Fin (m + 1)) (RingHom.id Γ(Z, f ⁻¹ᵁ mchart c)) (fun _ => 1)) =
        (eval₂Hom (σ := Fin (m + 1)) (RingHom.id _) (fun _ => 1)).comp (MvPolynomial.map (Z.evaluation (f ⁻¹ᵁ mchart c) w hw).hom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp)
    have := RingHom.congr_fun e (gam f c F)
    simp only [RingHom.comp_apply, hF, map_zero] at this
    exact this
  · intro o ho
    obtain ⟨s, rfl⟩ := f.app_surjective _ (GlobalTheory.CompanionTheory.MPDict.Spec.isAffineOpen_mchart c) o
    obtain ⟨F, a, hF⟩ := GlobalTheory.CompanionTheory.MPDict.Spec.exists_form c s
    have hg : gam f c F = C ((f.app (mchart c)).hom s) * ∏ k, X k ^ a k := by
      simp [gam, hF, map_prod]
    have hmem : F ∈ ptIdeal (f w) := by
      rw [mem_ptIdeal_iff_gam f c w hw, hg, map_mul, map_C]
      rw [ptPrime, RingHom.mem_ker] at ho
      rw [ho, C_0, zero_mul]
    have he : eps f c F = (f.app (mchart c)).hom s := by
      rw [← eval_one_gam, hg]
      simp
    rw [← he]
    exact Ideal.mem_map_of_mem _ hmem
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}
open GroundTheory.Heights₂.Heights (coordDeg localQuotLength)
open GlobalTheory.CompanionTheory.MPDict.Spec (mratio Phi)

theorem app_pullRatio {Z Y : Scheme.{0}} {N : ℕ} (f : Z ⟶ Y) (P : Y ⟶ PSpace ℤ N) (W : Y.Opens) (i j : Fin (N + 1))
    (hi : W ≤ P ⁻¹ᵁ chart ℤ N i) (hi' : f ⁻¹ᵁ W ≤ (f ≫ P) ⁻¹ᵁ chart ℤ N i) :
    (f.app W).hom (pullRatio P W i hi j) = pullRatio (f ≫ P) (f ⁻¹ᵁ W) i hi' j := by
  simp only [pullRatio]
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem germ_sec {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) (k : Fin (m + 1)) (l : Bk n k)
    (hi : w ∈ (pullO (f ≫ prB n k) 1).U (c k)) :
    Z.presheaf.germ _ w hi ((pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)).f (c k)) = Z.presheaf.germ _ w hw (eps f c (X ⟨k, l⟩)) := by
  have hle : f ⁻¹ᵁ mchart c ≤ (f ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) (c k) := fun x hx => mchart_le c k hx
  have e1 : (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)).f (c k) =
      pullRatio (f ≫ prB n k) _ (c k) le_rfl l := by
    show pullForm _ _ _ _ _ _ _ = _
    simp only [pullForm, pullRatio, formOn_eq_aeval, aeval_X]
    rfl
  have e2 : eps f c (X ⟨k, l⟩) = resG Z hle (pullRatio (f ≫ prB n k) _ (c k) le_rfl l) := by
    rw [eps_X, resG_pullRatio]
    exact app_pullRatio f (prB n k) (mchart c) (c k) l (mchart_le c k) hle
  rw [e1, e2]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hle) w hw _).symm

theorem mem_nonzeroLocus_iff_X_notMem (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) (f : Z ⟶ MP ℤ m n) (k : Fin (m + 1)) (l : Bk n k) (w : Z) :
    w ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) ↔ (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f w) := by
  let c : ∀ k, Bk n k := ptChart (f w)
  have hwc : w ∈ f ⁻¹ᵁ mchart c := GlobalTheory.CompanionTheory.MPDict.Spec.mem_mchart_ptChart (f w)
  have hi : w ∈ (pullO (f ≫ prB n k) 1).U (c k) := mchart_le c k hwc
  rw [mem_nonzeroLocus_iff _ (c k) hi, form_mem_iff f c w hwc (isWeightedHomogeneous_X ℤ _ (⟨k, l⟩ : Σ k, Bk n k)),
    ptPrime, RingHom.mem_ker, ← Ne, Scheme.evaluation_ne_zero_iff_mem_basicOpen, Scheme.mem_basicOpen _ _ _ hi,
    Scheme.mem_basicOpen _ _ _ hwc]
  exact iff_of_eq (congrArg IsUnit (germ_sec f c w hwc k l hi))
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}
open GroundTheory.Heights₂.Heights (coordDeg localQuotLength)

theorem length_quot_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Module.length A (A ⧸ Ideal.span {a}) = Module.length B (B ⧸ Ideal.span {e a}) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := e.surjective
  rw [← Module.length_eq_of_surjective (S := A) (R := B) (M := B ⧸ Ideal.span {e a}) hsurj]
  have hI : (Ideal.span {a}).map (e : A →+* B) = Ideal.span {e a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let q : (A ⧸ Ideal.span {a}) ≃+* (B ⧸ Ideal.span {e a}) := Ideal.quotientEquiv _ _ e hI.symm
  let ql : (A ⧸ Ideal.span {a}) ≃ₗ[A] (B ⧸ Ideal.span {e a}) :=
    { q.toAddEquiv with
      map_smul' := fun r x => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        show q (r • Ideal.Quotient.mk _ b) = r • q (Ideal.Quotient.mk _ b)
        have h1 : r • (Ideal.Quotient.mk (Ideal.span {a}) b) = Ideal.Quotient.mk _ (r * b) := rfl
        have h2 : ∀ y : B, r • (Ideal.Quotient.mk (Ideal.span {e a}) y) = Ideal.Quotient.mk _ (e r * y) := fun y => rfl
        have h3 : ∀ y : A, q (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (e y) := fun y => rfl
        rw [h1, h3, h3, h2, map_mul] }
  exact ql.length_eq

theorem length_quot_of_isLocalization {O S : Type*} [CommRing O] [CommRing S] [Algebra O S] (p : Ideal O) [p.IsPrime]
    [IsLocalization.AtPrime S p] (g : O) :
    Module.length S (S ⧸ Ideal.span {algebraMap O S g}) =
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸ Ideal.span {algebraMap O (Localization.AtPrime p) g}) := by
  let e : Localization.AtPrime p ≃ₐ[O] S := IsLocalization.algEquiv p.primeCompl _ _
  rw [length_quot_ringEquiv e.toRingEquiv]
  have : e.toRingEquiv (algebraMap O _ g) = algebraMap O S g := e.commutes g
  rw [this]

theorem atPrime_congr {O S : Type*} [CommRing O] [CommRing S] [Algebra O S] {a b : Ideal O} (h : a = b) [a.IsPrime] [b.IsPrime]
    [IsLocalization.AtPrime S a] : IsLocalization.AtPrime S b := by
  subst h
  infer_instance

theorem length_stalk {Z : Scheme.{0}} (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (c : ∀ k, Bk n k) (w : Z) (hw : w ∈ f ⁻¹ᵁ mchart c) (g : Γ(Z, f ⁻¹ᵁ mchart c)) :
    (Module.length (Z.presheaf.stalk w) (Z.presheaf.stalk w ⧸ Ideal.span {Z.presheaf.germ _ w hw g})).toNat = localQuotLength (ptPrime f c w hw) g := by
  have hU : IsAffineOpen (f ⁻¹ᵁ mchart c) := (GlobalTheory.CompanionTheory.MPDict.Spec.isAffineOpen_mchart c).preimage f
  let x : (f ⁻¹ᵁ mchart c : Z.Opens) := ⟨w, hw⟩
  letI : Algebra Γ(Z, f ⁻¹ᵁ mchart c) (Z.presheaf.stalk w) := TopCat.Presheaf.algebra_section_stalk Z.presheaf x
  haveI inst : IsLocalization.AtPrime (Z.presheaf.stalk w) (hU.primeIdealOf x).asIdeal := hU.isLocalization_stalk x
  have hP : (hU.primeIdealOf x).asIdeal = ptPrime f c w hw := by
    rw [← IsLocalization.AtPrime.comap_maximalIdeal (Z.presheaf.stalk w) (hU.primeIdealOf x).asIdeal]
    ext a
    rw [ptPrime, RingHom.mem_ker, Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have h1 := Scheme.mem_basicOpen Z a w hw
    have h2 := Scheme.evaluation_ne_zero_iff_mem_basicOpen Z w hw a
    have h3 : IsUnit (algebraMap Γ(Z, f ⁻¹ᵁ mchart c) (Z.presheaf.stalk w) a) ↔ (Z.evaluation _ w hw).hom a ≠ 0 :=
      h1.symm.trans h2.symm
    exact not_iff_comm.1 h3.symm
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk w) (ptPrime f c w hw) := atPrime_congr hP
  exact congrArg ENat.toNat (length_quot_of_isLocalization (S := Z.presheaf.stalk w) (ptPrime f c w hw) g)
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}
open GroundTheory.Heights₂.Heights (coordDeg localQuotLength)

theorem localQuot_congr {O : Type*} [CommRing O] {a b : Ideal O} (h : a = b) [a.IsPrime] [b.IsPrime] (g : O) :
    localQuotLength a g = localQuotLength b g := by
  subst h; rfl

theorem mult_eq_multAt (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f]
    (k : Fin (m + 1)) (l : Bk n k) (hs : genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l))) (w : Z) (hw : Order.coheight w = 1) :
    (divOfSec (isLB_pullO (f ≫ prB n k) 1) (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) hs).mult w = (multAt (ptIdeal (f (genericPoint Z)) ⊔ Ideal.span {(X ⟨k, l⟩ : Pol n)}) (ptIdeal (f w)) : ℤ) := by
  classical
  let c : ∀ k, Bk n k := ptChart (f w)
  have hwc : w ∈ f ⁻¹ᵁ mchart c := GlobalTheory.CompanionTheory.MPDict.Spec.mem_mchart_ptChart (f w)
  have hg : genericPoint Z ∈ f ⁻¹ᵁ mchart c := (genericPoint_specializes w).mem_open (f ⁻¹ᵁ mchart c).isOpen hwc
  have hi : w ∈ (pullO (f ≫ prB n k) 1).U (c k) := mchart_le c k hwc
  haveI : Nonempty (f ⁻¹ᵁ mchart c) := ⟨⟨w, hwc⟩⟩
  rw [mult_divOfSec hw hi, germ_sec f c w hwc k l hi, length_stalk f c w hwc]
  have hP : (ptIdeal (f w)).map (eps f c) = ptPrime f c w hwc := map_eps_ptIdeal f c w hwc
  haveI : ((ptIdeal (f w)).map (eps f c)).IsPrime := hP ▸ inferInstance
  haveI hVp : (ptIdeal (f w)).IsPrime := (isMultiProjPrime_ptIdeal m n (f w)).1
  have hVh : Geo.IsMultiHomogIdeal (ptIdeal (f w)) := (isMultiProjPrime_ptIdeal m n (f w)).2.1
  have hXV : ∀ k, (X ⟨k, c k⟩ : Pol n) ∉ ptIdeal (f w) := fun k h =>
    (GlobalTheory.CompanionTheory.MPDict.Spec.ptCoord_ne_zero_iff (f w) k (c k)).2 (mem_ptChart (f w) k)
      ((GlobalTheory.CompanionTheory.MPDict.Spec.X_mem_ptIdeal_iff (f w) _).1 h)
  have key := GroundTheory.Heights₂.Heights.OrbitChartMult.multAt_eq_localQuotLength_of (n := n) (eps f c) (gam f c)
    (fun hF => gam_of_form f c hF) (ptIdeal (f w)) (eps_surjective f c) (ptIdeal (f (genericPoint Z)))
    (gam_eq_zero_iff f c hg)
    (fun v hv e => GroundTheory.Heights₂.Heights.OrbitChartMult.weightedHomogeneousComponent_mem_of_isMultiHomogIdeal hVh hv e)
    (fun hF h => (form_mem_iff f c w hwc hF).2 (hP ▸ h)) c (eps_X_chart f c) hXV
    (s := X ⟨k, l⟩) (a := Pi.single k 1) (isWeightedHomogeneous_X ℤ _ _)
  rw [key, localQuot_congr hP]
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem coheight_eq_one_iff {α : Type*} [Preorder α] {g w : α} (hanti : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (hg : ∀ x, x ≤ g) :
    Order.coheight w = 1 ↔ w ≠ g ∧ ∀ v, w < v → v = g := by
  have hmax : IsMax g := fun x _ => hg x
  have h0 : Order.coheight g = 0 := Order.coheight_eq_zero.2 hmax
  constructor
  · intro h
    refine ⟨fun e => by rw [e, h0] at h; exact zero_ne_one h, fun v hv => ?_⟩
    by_contra hne
    have hvg : v < g := lt_of_le_not_ge (hg v) fun h => hne (hanti _ _ (hg v) h)
    have h1 := Order.coheight_add_one_le hvg
    have h2 := Order.coheight_add_one_le hv
    rw [h] at h2
    have h3 : Order.coheight v = 0 := by
      by_contra h4
      have : (1 : ℕ∞) ≤ Order.coheight v := ENat.one_le_iff_ne_zero.2 h4
      have h5 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left this 1).trans h2
      exact absurd h5 (by norm_num)
    rw [h3] at h1
    have h6 : (1 : ℕ∞) ≤ 0 := by simpa using (le_trans (by simp) h1 : (1 : ℕ∞) ≤ 0)
    exact absurd h6 (by norm_num)
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) ?_
    · rw [h2 y hy, h0]
      exact zero_lt_one
    · rw [ENat.one_le_iff_ne_zero]
      intro h
      exact h1 (hanti _ _ (hg w) (Order.coheight_eq_zero.1 h (hg w)))

theorem no_prime_between {R : Type*} [CommRing R] [IsNoetherianRing R] {V P W : Ideal R} [hV : V.IsPrime] [hP : P.IsPrime] {s : R}
    (hW : W ∈ (V ⊔ Ideal.span {s}).minimalPrimes) (h1 : V < P) (h2 : P < W) : False := by
  have hWp : W.IsPrime := hW.1.1
  have hVW : V ≤ W := h1.le.trans h2.le
  let φ := Ideal.Quotient.mk V
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = V := Ideal.mk_ker
  haveI hPq : (P.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (hker.le.trans h1.le)
  haveI hWq : (W.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (hker.le.trans hVW)
  have cP : (P.map φ).comap φ = P := Ideal.comap_map_mk h1.le
  have cW : (W.map φ).comap φ = W := Ideal.comap_map_mk hVW
  have hmin : W.map φ ∈ (Ideal.span {φ s}).minimalPrimes := by
    refine ⟨⟨hWq, ?_⟩, fun Q hQ hQW => ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s)))
    · haveI := hQ.1
      have hQp : (Q.comap φ).IsPrime := Ideal.comap_isPrime _ _
      have hle : V ⊔ Ideal.span {s} ≤ Q.comap φ := by
        refine sup_le (fun x hx => ?_) ?_
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
          exact Q.zero_mem
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
          exact hQ.2 (Ideal.mem_span_singleton_self _)
      have := hW.2 ⟨hQp, hle⟩ (by rw [← cW]; exact Ideal.comap_mono hQW)
      exact Ideal.map_le_iff_le_comap.2 this
  have hW1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {φ s}) _ hmin
  have hb : (⊥ : Ideal (R ⧸ V)) < P.map φ := by
    refine bot_lt_iff_ne_bot.2 fun e => ?_
    rw [e, ← RingHom.ker_eq_comap_bot, hker] at cP
    exact h1.ne cP
  have hPW : P.map φ < W.map φ := by
    refine lt_of_le_of_ne (Ideal.map_mono h2.le) fun e => ?_
    rw [e, cW] at cP
    exact h2.ne cP.symm
  haveI : IsDomain (R ⧸ V) := Ideal.Quotient.isDomain V
  have l1 := Ideal.height_strict_mono_of_isPrime hPW
  have l2 := Ideal.height_strict_mono_of_isPrime hb
  have l3 : (P.map φ).height = 0 := ENat.lt_one_iff_eq_zero.1 (lt_of_lt_of_le l1 hW1)
  rw [l3] at l2
  exact not_lt_zero' l2
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem isMultiHomog_coord (k : Fin (m + 1)) (l : Bk n k) : IsMultiHomog (X ⟨k, l⟩ : Pol n) (Pi.single k 1) := by
  classical
  intro e he j
  rw [support_X, Finset.mem_singleton] at he
  subst he
  by_cases hj : j = k
  · subst hj
    simp [Finsupp.single_apply]
  · rw [Pi.single_eq_of_ne hj]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hj (congrArg Sigma.fst h).symm

theorem genericPoint_top {Z : Scheme.{0}} [IsIntegral Z] (x : Z) : x ≤ genericPoint Z :=
  genericPoint_specializes x

theorem pt_antisymm {Z : Scheme.{0}} (a b : Z) (h : a ≤ b) (h' : b ≤ a) : a = b :=
  (Specializes.antisymm h' h).eq

theorem point_of_ptIdeal {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] {y : MP ℤ m n}
    (h : ptIdeal (f (genericPoint Z)) ≤ ptIdeal y) : ∃ w, f w = y := by
  have hsp : f (genericPoint Z) ⤳ y := (GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le m n _ _).2 h
  exact hsp.mem_closed f.isClosedEmbedding.isClosed_range ⟨_, rfl⟩

theorem exists_point_of_mem_divSupp (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f]
    (k : Fin (m + 1)) (l : Bk n k) (hs : (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z))) (W : Ideal (Pol n)) (hW : W ∈ divSupp (ptIdeal (f (genericPoint Z))) (X ⟨k, l⟩ : Pol n)) :
    ∃ w : Z, Order.coheight w = 1 ∧ (X ⟨k, l⟩ : Pol n) ∈ ptIdeal (f w) ∧ ptIdeal (f w) = W := by
  have hV := isMultiProjPrime_ptIdeal m n (f (genericPoint Z))
  haveI := hV.1
  have hWp : W.IsPrime := hW.1.1.1
  have hVW : ptIdeal (f (genericPoint Z)) ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : (X ⟨k, l⟩ : Pol n) ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hWh : Geo.IsMultiHomogIdeal W :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes hV.2.1 (isMultiHomog_coord k l) hW.1
  obtain ⟨y, rfl⟩ := GlobalTheory.CompanionTheory.MPDict.Onto.exists_ptIdeal_eq m n W ⟨hWp, hWh, hW.2⟩
  obtain ⟨w, rfl⟩ := point_of_ptIdeal f hVW
  refine ⟨w, (coheight_eq_one_iff pt_antisymm genericPoint_top).2 ⟨?_, fun v hv => ?_⟩, hsW, rfl⟩
  · rintro rfl
    exact hs hsW
  · by_contra hne
    have hvg : v < genericPoint Z := lt_of_le_not_ge (genericPoint_top v) fun h => hne (pt_antisymm _ _ (genericPoint_top v) h)
    have hinj : Function.Injective fun x : Z => ptIdeal (f x) := fun a b h =>
      f.isClosedEmbedding.injective (dict_ptIdeal_injective n h)
    have hmono : ∀ {a b : Z}, a < b → ptIdeal (f b) < ptIdeal (f a) := fun {a b} h =>
      lt_of_le_of_ne (GlobalTheory.CompanionTheory.MPDict.Spec.ptIdeal_le_of_specializes ((show b ⤳ a from h.le).map f.continuous))
        fun e => h.ne (hinj e).symm
    haveI := (isMultiProjPrime_ptIdeal m n (f v)).1
    exact no_prime_between hW.1 (hmono hvg) (hmono hv)

theorem ptIdeal_mem_divSupp (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f]
    (k : Fin (m + 1)) (l : Bk n k) (hs : (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z))) (w : Z) (hw : Order.coheight w = 1) (hv : (X ⟨k, l⟩ : Pol n) ∈ ptIdeal (f w)) :
    ptIdeal (f w) ∈ divSupp (ptIdeal (f (genericPoint Z))) (X ⟨k, l⟩ : Pol n) := by
  have hV := isMultiProjPrime_ptIdeal m n (f (genericPoint Z))
  have hW := isMultiProjPrime_ptIdeal m n (f w)
  haveI := hW.1
  have hVW : ptIdeal (f (genericPoint Z)) ≤ ptIdeal (f w) :=
    GlobalTheory.CompanionTheory.MPDict.Spec.ptIdeal_le_of_specializes ((genericPoint_specializes w).map f.continuous)
  have hle : ptIdeal (f (genericPoint Z)) ⊔ Ideal.span {(X ⟨k, l⟩ : Pol n)} ≤ ptIdeal (f w) :=
    sup_le hVW ((Ideal.span_singleton_le_iff_mem _).2 hv)
  obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hle
  have hQh : Geo.IsMultiHomogIdeal Q :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes hV.2.1 (isMultiHomog_coord k l) hQ
  have hQr : IsRelevant Q := fun j => (hW.2.2 j).imp fun i hi h => hi (hQW h)
  obtain ⟨y, rfl⟩ := GlobalTheory.CompanionTheory.MPDict.Onto.exists_ptIdeal_eq m n Q ⟨hQ.1.1, hQh, hQr⟩
  obtain ⟨v, rfl⟩ := point_of_ptIdeal f (le_sup_left.trans hQ.1.2)
  have hsv : (X ⟨k, l⟩ : Pol n) ∈ ptIdeal (f v) := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hspec : v ⤳ w := f.isClosedEmbedding.isInducing.specializes_iff.1
    ((GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le m n _ _).2 hQW)
  have hwv : w ≤ v := hspec
  obtain ⟨-, h2⟩ := (coheight_eq_one_iff pt_antisymm genericPoint_top).1 hw
  have hvw : v = w := by
    by_contra hne
    have := h2 v (lt_of_le_not_ge hwv fun h => hne (pt_antisymm _ _ h hwv))
    rw [this] at hsv
    exact hs hsv
  subst hvw
  exact ⟨hQ, hW.2.2⟩
end GlobalTheory.CompanionTheory.MixZ.DivCyc

namespace GlobalTheory.CompanionTheory.MixZ.DivCyc

theorem divOfSec_cycle : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k) (hs : genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l))) (u : Ideal (Pol n) → ℤ), ∑ᶠ w, (divOfSec (isLB_pullO (f ≫ prB n k) 1) (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) hs).mult w * u (ptIdeal (f w)) = ∑ᶠ W ∈ divSupp (ptIdeal (f (genericPoint Z))) (X ⟨k, l⟩ : Pol n), (multAt (ptIdeal (f (genericPoint Z)) ⊔ Ideal.span {(X ⟨k, l⟩ : Pol n)}) W : ℤ) * u W := by
  intro m n Z _ _ f _ k l hs u
  classical
  have hs' : (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) := (mem_nonzeroLocus_iff_X_notMem m n Z f k l _).1 hs
  set D := divOfSec (isLB_pullO (f ≫ prB n k) 1) (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) hs with hD
  let S : Set Z := {w | Order.coheight w = 1 ∧ (X ⟨k, l⟩ : Pol n) ∈ ptIdeal (f w)}
  have himg : divSupp (ptIdeal (f (genericPoint Z))) (X ⟨k, l⟩ : Pol n) = (fun w => ptIdeal (f w)) '' S := by
    ext W
    constructor
    · intro hW
      obtain ⟨w, h1, h2, rfl⟩ := exists_point_of_mem_divSupp m n Z f k l hs' W hW
      exact ⟨w, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ptIdeal_mem_divSupp m n Z f k l hs' w h1 h2
  have hinj : Set.InjOn (fun w => ptIdeal (f w)) S := fun a _ b _ h =>
    f.isClosedEmbedding.injective (dict_ptIdeal_injective n h)
  rw [himg, finsum_mem_image hinj]
  have hsupp : Function.support (fun w => D.mult w * u (ptIdeal (f w))) ⊆ S := by
    intro w hw
    have h0 : D.mult w ≠ 0 := fun h => hw (by simp [h])
    refine ⟨CartierDiv.coheight_eq_one_of_mult_ne_zero h0, ?_⟩
    by_contra hv
    have : w ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := (mem_nonzeroLocus_iff_X_notMem m n Z f k l w).2 hv
    exact notMem_supp_divOfSec.2 this (CartierDiv.mem_supp_of_mult_ne_zero h0)
  calc ∑ᶠ w, D.mult w * u (ptIdeal (f w)) = ∑ᶠ w ∈ S, D.mult w * u (ptIdeal (f w)) := by
        rw [finsum_mem_def, Set.indicator_eq_self.2 hsupp]
    _ = _ := finsum_mem_congr rfl fun w hw => by rw [hD, mult_eq_multAt m n Z f k l hs w hw.1]
end GlobalTheory.CompanionTheory.MixZ.DivCyc
