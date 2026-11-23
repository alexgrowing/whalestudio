import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa

noncomputable section

namespace GlobalTheory.FlatLine

theorem isAlgebraic_of_norm_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ = ‖P₀ b‖) : IsAlgebraic K b := by
  by_contra hb
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := IsAlgClosed.lift
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = 2 * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_ofNat] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_two] at h2
  have h3 : P₀ b = 0 := norm_eq_zero.1 (by linarith)
  exact hb ((map_eq_zero P₀).1 h3 ▸ isAlgebraic_zero)

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem liesOn_frMap {Z : Comp Xo c} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (hy : LiesOn Z y) : LiesOn Z z := by
  have e : ptF z = spMap φ.toRingHom ≫ ptF y := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
      congr 1
      ext a
      exact (φ.commutes a).symm
  intro s
  rw [e, Scheme.Hom.comp_apply]
  exact hy _

theorem liesOn_frBor {Z : Comp Xo c} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) (hz : LiesOn Z z) : LiesOn Z y := by
  have e : ptF y = ptF z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]
  intro s
  rw [e]
  exact hz s

theorem secZ_zero_eq : secZ Xo c 0 = sec Xo c 0 0 := by
  rw [← secZ_nat]
  congr 1
  funext i
  cases i <;> rfl

theorem exists_eq_smul_idem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed Xo c) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {b : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ = b) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ = b := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_const (K := c.F) (b := evC h Z g) P₀
    fun P => (key P).trans (key P₀).symm)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem ConstSec.exists_eq_smul (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) :
    ∃ (a : c.F) (ha : a ≠ 0), t = s.smul a ha := by
  have hσ := goodEmb_goodOf c c.F.val.toRingHom
  let u : ConstSec U x Z 0 0 := (t.mul s.symm).copy (add_neg_cancel la) (add_neg_cancel δ)
  obtain ⟨a, ha⟩ := exists_eq_smul_idem (U _) hσ (hU _ hσ) hF (g := u.sig) (exOf_zero (Dw := Dw) ▸ u.sig_mem)
    u.sig_mem_suppOn (b := u.cInf c.F.val.toRingHom) fun z hz => by
      rw [← homN_zero _ x, ← wtOf_zero (Dw := Dw)]; exact u.homN_eq hz
  have ha' : t.sig * s.inv = a • idem Z := ha
  have h : t.sig = a • s.sig :=
    calc t.sig = t.sig * s.inv * s.sig := by
          rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_comm, t.idem_sig]
      _ = a • s.sig := by rw [ha', smul_mul_assoc, s.idem_sig]
  have h0 : a ≠ 0 := fun h0 => t.sig_ne_zero (by rw [h, h0, zero_smul])
  exact ⟨a, h0, ConstSec.ext h⟩

theorem ConstSec.deg_eq (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) : t.deg = s.deg := by
  obtain ⟨a, ha, rfl⟩ := ConstSec.exists_eq_smul hU hF s t
  exact ConstSec.deg_smul a ha s

end GlobalTheory.FlatLine
