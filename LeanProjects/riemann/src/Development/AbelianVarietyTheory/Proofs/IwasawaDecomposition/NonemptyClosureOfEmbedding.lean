import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineChartOfLeftInverseMatrixStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedSubschemeOpenPiecesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpaceStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DRFlag GlobalTheory.ProjSpace
open GlobalTheory.FlagMod (ev ev_spMap le_preimage_comp)

namespace GlobalTheory.SubClosure

section General

variable {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {N : ℕ}

theorem spMap_spMap {S'' : Type} [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := (Spec.map_comp _ _).symm

theorem exists_spMap (w : Sp S' ⟶ Sp S) : ∃ φ : S →+* S', w = spMap φ :=
  ⟨(Spec.preimage w).hom, (Spec.map_preimage w).symm⟩

def IsPt (q : Sp S ⟶ PSpace O N) (v : Fin (N + 1) → S) : Prop := ∃ (g : O →+* S) (hv : _), q = pt g v hv

theorem IsPt.smul {q : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) (u : Sˣ) : IsPt q (u • v) := by
  obtain ⟨g, hv, rfl⟩ := h
  exact ⟨g, _, (pt_units_smul g hv u).symm⟩

theorem IsPt.spMap {q : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) (ψ : S →+* S') :
    IsPt (spMap ψ ≫ q) (ψ ∘ v) := by
  obtain ⟨g, hv, rfl⟩ := h
  exact ⟨_, _, spMap_pt g v hv ψ⟩

theorem IsPt.exists_eq {q : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) {g : O →+* S}
    (e : q ≫ PSpace.str O N = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g) : ∃ hv, q = pt g v hv := by
  obtain ⟨g', hv, rfl⟩ := h
  rw [pt_str] at e
  obtain rfl : g' = g := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  exact ⟨hv, rfl⟩

theorem IsPt.eq {q q' : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) (h' : IsPt q' v)
    (e : q ≫ PSpace.str O N = q' ≫ PSpace.str O N) : q = q' := by
  obtain ⟨g, hv, rfl⟩ := h'
  rw [pt_str] at e
  exact (h.exists_eq e).2

theorem IsPt.ne_zero {K : Type} [Field K] {q : Sp K ⟶ PSpace O N} {v : Fin (N + 1) → K} (h : IsPt q v) : v ≠ 0 := by
  obtain ⟨g, hv, -⟩ := h
  exact span_range_eq_top_iff_ne_zero.1 hv

theorem span_mulVec_eq_top {m n : ℕ} {Q : Matrix (Fin m) (Fin n) S} {Q' : Matrix (Fin n) (Fin m) S} (h : Q' * Q = 1)
    {v : Fin n → S} {c : Fin n} (hc : IsUnit (v c)) : Ideal.span (Set.range (Q.mulVec v)) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hc
  have : v c = ∑ i, Q' c i * Q.mulVec v i := by
    have := congrFun (Matrix.mulVec_mulVec v Q' Q) c
    rw [h, Matrix.one_mulVec] at this
    exact this.symm
  rw [this]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem comp_mulVec {m n : ℕ} (ψ : S →+* S') (Q : Matrix (Fin m) (Fin n) S) (v : Fin n → S) :
    ψ ∘ Q.mulVec v = (Q.map ψ).mulVec (ψ ∘ v) := funext fun i => RingHom.map_mulVec ψ Q v i

theorem exists_isUnit_col {r : ℕ} (v : Fin (r + 1) → S) (c : Fin (r + 1)) (hc : v c = 1) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) S, IsUnit P ∧ ∀ i, P i 0 = v i := by
  refine ⟨((1 : Matrix _ _ S).updateCol c v).submatrix id (Equiv.swap 0 c), ?_, fun i => by simp⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
  simp only [Module.End.one_apply, hc, mul_one]
  exact ((Equiv.Perm.sign (Equiv.swap 0 c)).isUnit.map (Int.castRingHom S))

abbrev cellVec (R : Type) [CommRing R] {r : ℕ} (c : Fin (r + 1)) : Fin (r + 1) → MvPolynomial (Fin r) R :=
  Fin.insertNth (α := fun _ => MvPolynomial (Fin r) R) c 1 MvPolynomial.X

theorem exists_cellVec {K : Type} [Field K] {r : ℕ} (φ : S →+* K) {v : Fin (r + 1) → K} (hv : v ≠ 0) :
    ∃ (c : Fin (r + 1)) (ψ : MvPolynomial (Fin r) S →+* K) (u : Kˣ),
      ψ.comp MvPolynomial.C = φ ∧ ψ ∘ cellVec S c = u • v := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hv
  refine ⟨c, MvPolynomial.eval₂Hom φ fun j => (v c)⁻¹ * v (c.succAbove j), (Units.mk0 _ hc)⁻¹,
    RingHom.ext fun x => by simp, funext fun i => ?_⟩
  refine Fin.succAboveCases c ?_ (fun j => ?_) i
  · simp [Units.smul_def, inv_mul_cancel₀ (show v c ≠ 0 from hc)]
  · simp [Units.smul_def]

instance subsingleton_sp (K : Type) [Field K] : Subsingleton (Sp K) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

theorem exists_field_point (t : Sp S) :
    ∃ (K : Type) (_ : Field K) (ψ : S →+* K), ∀ p : Sp K, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ p = t := by
  obtain ⟨ψ, e⟩ := exists_spMap (S' := (Sp S).residueField t) ((Sp S).fromSpecResidueField t)
  exact ⟨_, inferInstance, ψ, fun p => e ▸ Scheme.fromSpecResidueField_apply t p⟩

theorem exists_fac {X : Scheme.{0}} (χ : Sp S ⟶ X) [IsOpenImmersion χ] [IsLocalRing S'] (w : Sp S' ⟶ X)
    (h : Set.range w ⊆ Set.range χ) : ∃ φ : S →+* S', ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ χ = w := by
  obtain ⟨_, φ, e⟩ := Charts.exists_fac { ι := Unit, R := fun _ => S, χ := fun _ => χ, opn := fun _ => inferInstance } w
    (Set.mem_iUnion.2 ⟨(), h ⟨_, rfl⟩⟩)
  exact ⟨φ, e⟩

theorem normal_stalk_iff {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ↔
      (IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x))) := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨fun ⟨h, h'⟩ => ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩,
    fun ⟨h, h'⟩ => ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩⟩

theorem isReduced_of_normal {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X :=
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := have := (h x).1; inferInstance
  isReduced_of_isReduced_stalk X

theorem smooth_spMap_C (r : ℕ) :
    Smooth (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (MvPolynomial.C : S →+* MvPolynomial (Fin r) S)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.Smooth S (MvPolynomial (Fin r) S) := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.2 this

end General

section Main

variable {O : Type} [CommRing O] {Z : Scheme.{0}} (s : Z ⟶ Sp O) {C : Coc Z} {N : ℕ} (Em : C.Emb N)
  {ch : Charts Z} {r : ℕ} (D : C.Sub ch r)

def gA (a : ch.ι) : O →+* ch.R a := (Spec.preimage (ch.χ a ≫ s)).hom

theorem sub_closure_chart_section (a : ch.ι) : ch.χ a ≫ s = spMap (gA s a) := (Spec.map_preimage _).symm

abbrev Av {S : Type} [CommRing S] (z : Sp S ⟶ Z) (α : C.A) (h : ⊤ ≤ z ⁻¹ᵁ C.B α) :
    Matrix (Fin (N + 1)) (Fin (C.n α)) S := (Em.A α).map (ev z (C.B α) h)

def Qm (a : ch.ι) : Matrix (Fin (N + 1)) (Fin (r + 1)) (ch.R a) := Av Em (ch.χ a) (D.α a) (D.le a) * D.M a

theorem Qm_map {S : Type} [CommRing S] (a : ch.ι) (φ : ch.R a →+* S) {z : Sp S ⟶ Z} (e : spMap φ ≫ ch.χ a = z)
    (h : ⊤ ≤ z ⁻¹ᵁ C.B (D.α a)) : (Qm Em D a).map φ = Av Em z (D.α a) h * (D.M a).map φ := by
  subst e
  rw [Qm, Matrix.map_mul, Av, Av, Matrix.map_map, ev_spMap φ (ch.χ a) _ (D.le a) h]
  rfl

theorem Qm_linv (a : ch.ι) : ∃ Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) (ch.R a), Q' * Qm Em D a = 1 := by
  obtain ⟨A', hA⟩ := Em.linv (D.α a)
  obtain ⟨M', hM⟩ := GlobalTheory.T.exists_left_inverse_of_fibrewise_injective _ _ _ (D.M a) (D.inj a)
  refine ⟨M' * A'.map (ev (ch.χ a) _ (D.le a)), ?_⟩
  have : A'.map (ev (ch.χ a) _ (D.le a)) * Av Em (ch.χ a) (D.α a) (D.le a) = 1 := by
    rw [Av, ← Matrix.map_mul, hA]
    simp
  rw [Qm, Matrix.mul_assoc, ← Matrix.mul_assoc (A'.map _), this, Matrix.one_mul, hM]

theorem isPt_tr {S : Type} [CommRing S] {q : Sp S ⟶ PSpace O N} (z : Sp S ⟶ Z) (α β : C.A)
    (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β) {ξ : Fin (C.n β) → S} (h : IsPt q ((Av Em z β hβ).mulVec ξ)) :
    IsPt q ((Av Em z α hα).mulVec ((C.tr α β z hα hβ).mulVec ξ)) := by
  obtain ⟨u, hu⟩ := Em.compat α β S z hα hβ
  have : (Av Em z α hα).mulVec ((C.tr α β z hα hβ).mulVec ξ) = u • (Av Em z β hβ).mulVec ξ := by
    rw [Matrix.mulVec_mulVec, Av, hu, Matrix.smul_mulVec, Units.smul_def]
  rw [this]
  exact h.smul u

theorem isPt_glue {K : Type} [Field K] {q : Sp K ⟶ PSpace O N} (a a' : ch.ι) (φ : ch.R a →+* K)
    (φ' : ch.R a' →+* K) {z : Sp K ⟶ Z} (e : spMap φ ≫ ch.χ a = z) (e' : spMap φ' ≫ ch.χ a' = z)
    {v' : Fin (r + 1) → K} (h : IsPt q (((Qm Em D a').map φ').mulVec v')) :
    ∃ v, IsPt q (((Qm Em D a).map φ).mulVec v) := by
  have hz : ⊤ ≤ z ⁻¹ᵁ C.B (D.α a) := by rw [← e]; exact le_preimage_comp _ (D.le a)
  have hz' : ⊤ ≤ z ⁻¹ᵁ C.B (D.α a') := by rw [← e']; exact le_preimage_comp _ (D.le a')
  obtain ⟨P, hP⟩ := D.glue a a' K φ φ' z e e' hz hz'
  refine ⟨P.mulVec v', ?_⟩
  rw [Qm_map Em D a' φ' e' hz', ← Matrix.mulVec_mulVec] at h
  have h2 := isPt_tr Em z (D.α a) (D.α a') hz hz' h
  rw [Qm_map Em D a φ e hz]
  convert h2 using 1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hP]

theorem cellVec_self (R : Type) [CommRing R] (c : Fin (r + 1)) : cellVec R c c = 1 :=
  Fin.insertNth_apply_same _ _ _

theorem cell_hv (a : ch.ι) (c : Fin (r + 1)) :
    Ideal.span (Set.range (((Qm Em D a).map MvPolynomial.C).mulVec (cellVec (ch.R a) c))) = ⊤ := by
  obtain ⟨Q', hQ⟩ := Qm_linv Em D a
  refine span_mulVec_eq_top (Q' := Q'.map MvPolynomial.C) ?_ (c := c) (by rw [cellVec_self]; exact isUnit_one)
  rw [← Matrix.map_mul, hQ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def cell (a : ch.ι) (c : Fin (r + 1)) : Sp (MvPolynomial (Fin r) (ch.R a)) ⟶ pullback s (PSpace.str O N) :=
  pullback.lift (spMap MvPolynomial.C ≫ ch.χ a) (pt (MvPolynomial.C.comp (gA s a)) _ (cell_hv Em D a c))
    (by rw [Category.assoc, sub_closure_chart_section, spMap_spMap, pt_str])

@[reassoc] theorem cell_fst (a : ch.ι) (c : Fin (r + 1)) :
    cell s Em D a c ≫ pullback.fst _ _ = spMap MvPolynomial.C ≫ ch.χ a := pullback.lift_fst _ _ _

@[reassoc] theorem cell_snd (a : ch.ι) (c : Fin (r + 1)) :
    cell s Em D a c ≫ pullback.snd _ _ = pt (MvPolynomial.C.comp (gA s a)) _ (cell_hv Em D a c) :=
  pullback.lift_snd _ _ _

theorem isPt_cell {S : Type} [CommRing S] (a : ch.ι) (c : Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R a) →+* S) :
    IsPt ((spMap ψ ≫ cell s Em D a c) ≫ pullback.snd _ _)
      (((Qm Em D a).map (ψ.comp MvPolynomial.C)).mulVec (ψ ∘ cellVec (ch.R a) c)) := by
  have := (show IsPt _ _ from ⟨_, _, rfl⟩ : IsPt (pt (MvPolynomial.C.comp (gA s a)) _ (cell_hv Em D a c)) _).spMap ψ
  rw [comp_mulVec, Matrix.map_map] at this
  rw [Category.assoc, cell_snd]
  exact this

theorem exists_cell {K : Type} [Field K] (a : ch.ι) (φ : ch.R a →+* K) {v : Fin (r + 1) → K}
    (x : Sp K ⟶ pullback s (PSpace.str O N)) (h1 : x ≫ pullback.fst _ _ = spMap φ ≫ ch.χ a)
    (h2 : IsPt (x ≫ pullback.snd _ _) (((Qm Em D a).map φ).mulVec v)) :
    ∃ (c : Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R a) →+* K), spMap ψ ≫ cell s Em D a c = x := by
  have hv : v ≠ 0 := by
    rintro rfl
    exact h2.ne_zero (Matrix.mulVec_zero _)
  obtain ⟨c, ψ, u, hψ, hu⟩ := exists_cellVec φ hv
  have hfst : (spMap ψ ≫ cell s Em D a c) ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ := by
    rw [Category.assoc, cell_fst, ← Category.assoc, spMap_spMap, hψ, h1]
  refine ⟨c, ψ, pullback.hom_ext hfst ?_⟩
  have h3 := isPt_cell s Em D a c ψ
  rw [hψ, hu, Units.smul_def, Matrix.mulVec_smul, ← Units.smul_def] at h3
  refine h3.eq (h2.smul u) ?_
  simp only [Category.assoc, ← pullback.condition]
  simpa only [Category.assoc] using congrArg (· ≫ s) hfst

theorem mem_range_cell {y : ↥(pullback s (PSpace.str O N))}
    (hy : y ∈ ⋃ k : Σ a : ch.ι, Fin (r + 1), Set.range (cell s Em D k.1 k.2)) {a : ch.ι}
    (ha : pullback.fst s (PSpace.str O N) y ∈ Set.range (ch.χ a)) : ∃ c, y ∈ Set.range (cell s Em D a c) := by
  obtain ⟨⟨a', c'⟩, t, rfl⟩ := Set.mem_iUnion.1 hy
  obtain ⟨K, _, ψ, hψ⟩ := exists_field_point t
  have hx : ∀ p, (spMap ψ ≫ cell s Em D a' c') p = cell s Em D a' c' t := fun p => by
    rw [Scheme.Hom.comp_apply, hψ]
  have hx1 : (spMap ψ ≫ cell s Em D a' c') ≫ pullback.fst _ _ = spMap (ψ.comp MvPolynomial.C) ≫ ch.χ a' := by
    rw [Category.assoc, cell_fst, ← Category.assoc, spMap_spMap]
  obtain ⟨φ, hφ⟩ := exists_fac (ch.χ a) ((spMap ψ ≫ cell s Em D a' c') ≫ pullback.fst _ _)
    (by rintro _ ⟨p, rfl⟩; rw [Scheme.Hom.comp_apply, hx]; exact ha)
  obtain ⟨v, hv⟩ := isPt_glue Em D a a' φ (ψ.comp MvPolynomial.C) hφ hx1.symm (isPt_cell s Em D a' c' ψ)
  obtain ⟨c, ψ', e⟩ := exists_cell s Em D a φ _ hφ.symm hv
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  exact ⟨c, spMap ψ' p, by rw [← Scheme.Hom.comp_apply, e, hx]⟩

theorem union_inter (a : ch.ι) :
    (⋃ k : Σ a : ch.ι, Fin (r + 1), Set.range (cell s Em D k.1 k.2)) ∩
      pullback.fst s (PSpace.str O N) ⁻¹' Set.range (ch.χ a) = ⋃ c, Set.range (cell s Em D a c) := by
  ext y
  constructor
  · rintro ⟨hy, ha⟩
    obtain ⟨c, hc⟩ := mem_range_cell s Em D hy ha
    exact Set.mem_iUnion.2 ⟨c, hc⟩
  · intro hy
    obtain ⟨c, t, rfl⟩ := Set.mem_iUnion.1 hy
    refine ⟨Set.mem_iUnion.2 ⟨⟨a, c⟩, t, rfl⟩, ?_⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, cell_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

end Main

theorem normal_sp_of_openImmersion {Z : Scheme.{0}} (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {R : Type}
    [CommRing R] (χ : Sp R ⟶ Z) [IsOpenImmersion χ] : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) :=
  fun x => (normal_stalk_iff χ x).2 (hZ _)

theorem flat_of_cover {X Y : Scheme.{0}} (F : X ⟶ Y) {J : Type} (T : J → Scheme.{0}) (e : ∀ k, T k ⟶ X)
    [∀ k, IsOpenImmersion (e k)] (hc : ⋃ k, Set.range (e k) = Set.univ) (h : ∀ k, Flat (e k ≫ F)) : Flat F := by
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun k => (e k).opensRange) ?_ fun k => ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hc.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  · have e1 : (e k).opensRange.ι = (e k).isoOpensRange.inv ≫ e k := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e1, Category.assoc]
    exact IsZariskiLocalAtSource.comp (h k) _

theorem exists_closure (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O)
    (hproj : IsProjOver s) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (hflat : Flat s) (C : Coc Z) (N : ℕ)
    (hEm : Nonempty (C.Emb N)) (ch : Charts Z) (r : ℕ) (D : C.Sub ch r) : Nonempty (D.Closure s) := by
  obtain ⟨Em⟩ := hEm
  set p₁ := pullback.fst s (PSpace.str O N) with hp₁
  set p₂ := pullback.snd s (PSpace.str O N) with hp₂
  let T : (Σ a : ch.ι, Fin (r + 1)) → Scheme.{0} := fun k => Sp (MvPolynomial (Fin r) (ch.R k.1))
  have H := fun a => GlobalTheory.T.affine_chart_of_left_inverse_matrix O Z (pullback s (PSpace.str O N)) s N r p₁ p₂ (IsPullback.of_hasPullback _ _)
    (ch.R a) (ch.χ a) (gA s a) (Qm Em D a) (Qm_linv Em D a).choose (fun c => cell s Em D a c) inferInstance
    (sub_closure_chart_section s a) (Qm_linv Em D a).choose_spec (fun c => cell_fst s Em D a c) (fun c => ⟨cell_hv Em D a c, cell_snd s Em D a c⟩)
  choose U hU using fun a => (H a).2.1
  choose T₀ hT₀c hT₀ using fun a => (H a).2.2
  let Ω : (pullback s (PSpace.str O N)).Opens := p₁ ⁻¹ᵁ (⨆ a, (ch.χ a).opensRange)
  have hΩ : ∀ y, y ∈ Ω ↔ ∃ a, p₁ y ∈ Set.range (ch.χ a) := fun y => by
    show p₁ y ∈ (⨆ a, (ch.χ a).opensRange) ↔ _
    rw [TopologicalSpace.Opens.mem_iSup]
    rfl
  have hnT : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (T k) := fun k =>
    GlobalTheory.T.isNormal_mvPolynomial_of_isNormal (ch.R k.1) r (normal_sp_of_openImmersion hnorm (ch.χ k.1))
  obtain ⟨Uu, j, e', hj, he', hje, hcov⟩ := GlobalTheory.T.exists_closed_subscheme_open_pieces (pullback s (PSpace.str O N)) _ T
    (fun k => cell s Em D k.1 k.2) Ω (fun k => (H k.1).1 k.2) (fun k => isReduced_of_normal (hnT k))
    (fun k => ⟨U k.1 k.2 ⊓ p₁ ⁻¹ᵁ (ch.χ k.1).opensRange, by
      rw [hU, ← union_inter s Em D k.1]
      ext y
      simp only [Set.mem_inter_iff, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩⟩)
    ⟨closure (⋃ k : Σ a : ch.ι, Fin (r + 1), Set.range (cell s Em D k.1 k.2)), isClosed_closure, by
      ext y
      constructor
      · intro hy
        refine ⟨subset_closure hy, (hΩ y).2 ?_⟩
        obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.1 hy
        refine ⟨k.1, ?_⟩
        rw [← Scheme.Hom.comp_apply, cell_fst, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩
      · rintro ⟨hy, hyΩ⟩
        obtain ⟨a, ha⟩ := (hΩ y).1 hyΩ
        have hV : IsOpen (p₁ ⁻¹' Set.range (ch.χ a)) := (p₁ ⁻¹ᵁ (ch.χ a).opensRange).isOpen
        have h1 := hV.inter_closure ⟨ha, hy⟩
        rw [Set.inter_comm, union_inter s Em D a, hT₀ a] at h1
        have h2 : y ∈ T₀ a := closure_minimal Set.inter_subset_left (hT₀c a) h1
        have h3 : y ∈ ⋃ c, Set.range (cell s Em D a c) := by rw [hT₀ a]; exact ⟨h2, ha⟩
        obtain ⟨c, hc⟩ := Set.mem_iUnion.1 h3
        exact Set.mem_iUnion.2 ⟨⟨a, c⟩, hc⟩⟩
  have hnU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Uu := fun u => by
    obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.1 (hcov.ge (Set.mem_univ u))
    exact (normal_stalk_iff (e' k) t).1 (hnT k t)
  have hflU : Flat (j ≫ Ω.ι ≫ p₁ ≫ s) := flat_of_cover _ T e' hcov fun k => by
    rw [reassoc_of% (hje k), cell_fst_assoc]
    haveI := hflat
    haveI := smooth_spMap_C (S := ch.R k.1) r
    haveI : Flat (spMap (MvPolynomial.C : ch.R k.1 →+* MvPolynomial (Fin r) (ch.R k.1))) := inferInstance
    haveI : Flat (ch.χ k.1) := inferInstance
    exact inferInstance
  have hstr : IsProjOver (PSpace.str O N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨Z', ν, e, hνfin, hnZ', hprojZ', hflZ', Hpb, hdense⟩ :=
    GlobalTheory.T.exists_finite_normal_flat_closure O _ Uu (p₁ ≫ s) Ω j (GlobalTheory.ProjSpace.isProjOver_pullback hproj hstr) hj hnU hflU
  set f := ν ≫ p₁ with hf
  set q := ν ≫ p₂ with hq
  have hqs : q ≫ PSpace.str O N = f ≫ s := by
    rw [hq, hf, Category.assoc, Category.assoc, pullback.condition]
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback Hpb.flip inferInstance
  have hcellν : ∀ k {W : Scheme.{0}} (g : pullback s (PSpace.str O N) ⟶ W), e' k ≫ e ≫ ν ≫ g = cell s Em D k.1 k.2 ≫ g :=
    fun k W g => by rw [← Category.assoc e ν g, ← Category.assoc (e' k), Hpb.w, hje k]
  have hfac : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Set.range e →
      ∃ (k : Σ a : ch.ι, Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R k.1) →+* K), spMap ψ ≫ e' k ≫ e = w := by
    intro K _ w hw
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcov.ge (Set.mem_univ (IsOpenImmersion.lift e w hw p)))
    obtain ⟨ψ, hψ⟩ := exists_fac (e' k) (IsOpenImmersion.lift e w hw) (by
      rintro _ ⟨p', rfl⟩
      rwa [Subsingleton.elim p' p])
    exact ⟨k, ψ, by rw [← Category.assoc, hψ, IsOpenImmersion.lift_fac]⟩
  have hwf : ∀ (K : Type) [Field K] (k : Σ a : ch.ι, Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R k.1) →+* K),
      (spMap ψ ≫ e' k ≫ e) ≫ f = spMap (ψ.comp MvPolynomial.C) ≫ ch.χ k.1 := by
    intro K _ k ψ
    simp only [hf, Category.assoc]
    rw [hcellν, cell_fst, ← Category.assoc, spMap_spMap]
  have hptk : ∀ (K : Type) [Field K] (k : Σ a : ch.ι, Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R k.1) →+* K)
      (hk : ⊤ ≤ ((spMap ψ ≫ e' k ≫ e) ≫ f) ⁻¹ᵁ C.B (D.α k.1)),
      IsPt ((spMap ψ ≫ e' k ≫ e) ≫ q) ((Av Em ((spMap ψ ≫ e' k ≫ e) ≫ f) (D.α k.1) hk).mulVec
        (((D.M k.1).map (ψ.comp MvPolynomial.C)).mulVec (ψ ∘ cellVec (ch.R k.1) k.2))) := by
    intro K _ k ψ hk
    have := isPt_cell s Em D k.1 k.2 ψ
    rw [Qm_map Em D k.1 _ (hwf K k ψ).symm hk, ← Matrix.mulVec_mulVec] at this
    have hwq : (spMap ψ ≫ e' k ≫ e) ≫ q = (spMap ψ ≫ cell s Em D k.1 k.2) ≫ p₂ := by
      simp only [hq, Category.assoc, hcellν]
    rw [hwq]
    exact this
  have hkle : ∀ (K : Type) [Field K] (k : Σ a : ch.ι, Fin (r + 1)) (ψ : MvPolynomial (Fin r) (ch.R k.1) →+* K),
      ⊤ ≤ ((spMap ψ ≫ e' k ≫ e) ≫ f) ⁻¹ᵁ C.B (D.α k.1) := fun K _ k ψ => by
    rw [hwf K k ψ]
    exact le_preimage_comp _ (D.le k.1)
  obtain ⟨L, hL⟩ := GlobalTheory.T.points_of_closure_in_projective_space O Z Z' s f C N Em q (Set.range e) hqs (isReduced_of_normal hnZ') hdense
    (fun K _ w hw α h => by
      obtain ⟨k, ψ, rfl⟩ := hfac K w hw
      have h2 := isPt_tr Em _ α (D.α k.1) h (hkle K k ψ) (hptk K k ψ (hkle K k ψ))
      obtain ⟨g, hg⟩ := exists_spMap ((spMap ψ ≫ e' k ≫ e) ≫ q ≫ PSpace.str O N)
      obtain ⟨hv, he⟩ := h2.exists_eq (by rw [Category.assoc]; exact hg)
      exact ⟨_, g, hv, he⟩)
  have carr : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → K),
      L.Carries w α h ξ ↔ IsPt (w ≫ q) ((Av Em (w ≫ f) α h).mulVec ξ) := by
    intro K _ w α h ξ
    obtain ⟨g, hg⟩ := exists_spMap (w ≫ f ≫ s)
    rw [hL K w α h ξ g hg]
    constructor
    · rintro ⟨hv, he⟩
      exact ⟨g, hv, he⟩
    · intro hp
      exact hp.exists_eq (by rw [Category.assoc, hqs, hg])

  have hcellν0 : ∀ k, e' k ≫ e ≫ ν = cell s Em D k.1 k.2 := fun k => by rw [Hpb.w, hje k]
  have hrange : Set.range e = ν ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Hpb.w, Scheme.Hom.comp_apply]
      have := Set.mem_range_self (f := Ω.ι) (j u)
      rwa [Scheme.Opens.range_ι] at this
    · intro hx
      have hr : Set.range (Z'.fromSpecResidueField x ≫ ν) ⊆ Set.range Ω.ι := by
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
        exact hx
      have hl := Hpb.lift_fst (Z'.fromSpecResidueField x) (IsOpenImmersion.lift Ω.ι _ hr)
        (IsOpenImmersion.lift_fac _ _ _).symm
      obtain ⟨p⟩ : Nonempty (Spec (Z'.residueField x)) := inferInstance
      refine ⟨Hpb.lift (Z'.fromSpecResidueField x) (IsOpenImmersion.lift Ω.ι _ hr)
        (IsOpenImmersion.lift_fac _ _ _).symm p, ?_⟩
      rw [← Scheme.Hom.comp_apply, hl, Scheme.fromSpecResidueField_apply]
  let ch' : Charts Z' := Charts.mk (Σ a : ch.ι, Fin (r + 1)) (fun k => MvPolynomial (Fin r) (ch.R k.1))
    (fun k => e' k ≫ e) (fun k => inferInstance)
  have hcar : ch'.carrier = Set.range e := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, u, rfl⟩ := Set.mem_iUnion.1 hx
      exact ⟨e' k u, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.1 (hcov.ge (Set.mem_univ u))
      exact Set.mem_iUnion.2 ⟨k, t, Scheme.Hom.comp_apply _ _ _⟩
  choose Pm hPm using fun k : Σ a : ch.ι, Fin (r + 1) => exists_isUnit_col (cellVec (ch.R k.1) k.2) k.2 (cellVec_self _ _)
  haveI : Mono j := inferInstance
  haveI := hνfin
  have hproj' : IsProjOver (f ≫ s) := by rw [hf, Category.assoc]; exact hprojZ'
  have hflat' : Flat (f ≫ s) := by rw [hf, Category.assoc]; exact hflZ'
  refine ⟨⟨Z', f, hproj', hnZ', hflat', L, ch', fun k => k.1, fun k => MvPolynomial.C, fun k => smooth_spMap_C r,
    fun k => ?_, Pm, fun k => (hPm k).1, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (e' k ≫ e) ≫ ν ≫ p₁ = _
    simp only [Category.assoc]
    rw [hcellν, cell_fst]
  · rw [hcar, hrange]
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, hΩ, Charts.carrier, Set.mem_iUnion, hf, Scheme.Hom.comp_apply]
  · rw [hcar]
    exact hdense
  · intro k K _ ψ w hw h
    subst hw
    have e1 : (fun i => ψ (Pm k i 0)) = ψ ∘ cellVec (ch.R k.1) k.2 := funext fun i => by rw [(hPm k).2 i]; rfl
    rw [carr, e1]
    exact hptk K k ψ h
  · intro a K _ φ v hv
    have hQv : Ideal.span (Set.range (((Qm Em D a).map φ).mulVec v)) = ⊤ := by
      obtain ⟨Q', hQ⟩ := Qm_linv Em D a
      obtain ⟨c, hc⟩ := Function.ne_iff.1 hv
      refine span_mulVec_eq_top (Q' := Q'.map φ) ?_ (c := c) (isUnit_iff_ne_zero.2 hc)
      rw [← Matrix.map_mul, hQ]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    let x : Sp K ⟶ pullback s (PSpace.str O N) := pullback.lift (spMap φ ≫ ch.χ a) (pt (φ.comp (gA s a)) _ hQv)
      (by rw [Category.assoc, sub_closure_chart_section, spMap_spMap, pt_str])
    have hx1 : x ≫ p₁ = spMap φ ≫ ch.χ a := pullback.lift_fst _ _ _
    have hx2 : IsPt (x ≫ p₂) (((Qm Em D a).map φ).mulVec v) := ⟨_, hQv, pullback.lift_snd _ _ _⟩
    obtain ⟨c, ψ, hψ⟩ := exists_cell s Em D a φ x hx1 hx2
    have hwν : (spMap ψ ≫ e' ⟨a, c⟩ ≫ e) ≫ ν = x := by
      rw [Category.assoc, Category.assoc, hcellν0, hψ]
    have key : ∀ w' : Sp K ⟶ Z', w' ≫ f = spMap φ ≫ ch.χ a →
        ((∀ h, L.Carries w' (D.α a) h (((D.M a).map φ).mulVec v)) ↔ w' ≫ ν = x) := by
      intro w' hw'
      have h0 : ⊤ ≤ (w' ≫ f) ⁻¹ᵁ C.B (D.α a) := by rw [hw']; exact le_preimage_comp _ (D.le a)
      constructor
      · intro H
        have h3 := (carr K w' _ h0 _).1 (H h0)
        rw [Matrix.mulVec_mulVec, ← Qm_map Em D a φ hw'.symm h0] at h3
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc]
          exact hw'.trans hx1.symm
        · rw [Category.assoc]
          refine h3.eq hx2 ?_
          rw [Category.assoc, hqs, ← Category.assoc, hw', Category.assoc x, ← pullback.condition, ← Category.assoc,
            hx1, Category.assoc]
      · intro hν h
        rw [carr, Matrix.mulVec_mulVec, ← Qm_map Em D a φ hw'.symm h]
        have : w' ≫ q = x ≫ p₂ := by rw [hq, ← Category.assoc, hν]
        rw [this]
        exact hx2
    have hwf' : (spMap ψ ≫ e' ⟨a, c⟩ ≫ e) ≫ f = spMap φ ≫ ch.χ a := by
      rw [hf, ← Category.assoc, hwν, hx1]
    refine ⟨spMap ψ ≫ e' ⟨a, c⟩ ≫ e, ⟨hwf', (key _ hwf').2 hwν⟩, fun w' hw' => ?_⟩
    have hν' := (key w' hw'.1).1 hw'.2
    have hw0 : w' ≫ ν = (spMap ψ ≫ e' ⟨a, c⟩ ≫ j) ≫ Ω.ι := by
      rw [hν', ← hψ, ← hje ⟨a, c⟩, Category.assoc, Category.assoc]
    have hl := Hpb.lift_fst w' (spMap ψ ≫ e' ⟨a, c⟩ ≫ j) hw0
    have hl2 : Hpb.lift w' (spMap ψ ≫ e' ⟨a, c⟩ ≫ j) hw0 ≫ j = (spMap ψ ≫ e' ⟨a, c⟩) ≫ j := by
      rw [Hpb.lift_snd, Category.assoc]
    rw [← hl, (cancel_mono j).1 hl2, Category.assoc]
  · intro R K _ _ _ _ _ _ _ z α hz ξ hξ y hy hcarr
    obtain ⟨c, hc⟩ := hξ
    obtain ⟨A', hA⟩ := Em.linv α
    have hv : Ideal.span (Set.range ((Av Em z α hz).mulVec ξ)) = ⊤ := by
      refine span_mulVec_eq_top (Q' := A'.map (ev z _ hz)) ?_ hc
      rw [Av, ← Matrix.map_mul, hA]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    obtain ⟨g, hg⟩ := exists_spMap (z ≫ s)
    let x : Sp R ⟶ pullback s (PSpace.str O N) := pullback.lift z (pt g _ hv) (by rw [hg, pt_str])
    have h0 : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α := by rw [hy]; exact le_preimage_comp _ hz
    have h1 := (carr K y α h0 _).1 (hcarr h0)
    have e1 : Av Em (y ≫ f) α h0 = (Av Em z α hz).map (algebraMap R K) := by
      rw [Av, Av, Matrix.map_map, GlobalTheory.FlagMod.ev_congr hy _ h0 (le_preimage_comp _ hz), ev_spMap _ z _ hz]
      rfl
    have h2 : IsPt (spMap (algebraMap R K) ≫ x ≫ p₂) ((Av Em (y ≫ f) α h0).mulVec fun i => algebraMap R K (ξ i)) := by
      have h3 := (show IsPt (pt g _ hv) _ from ⟨g, hv, rfl⟩).spMap (algebraMap R K)
      rw [comp_mulVec] at h3
      rw [e1]
      have : x ≫ p₂ = pt g _ hv := pullback.lift_snd _ _ _
      rw [this]
      exact h3
    have hyν : y ≫ ν = spMap (algebraMap R K) ≫ x := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, pullback.lift_fst]
        exact hy
      · rw [Category.assoc, Category.assoc]
        refine h1.eq h2 ?_
        rw [Category.assoc, hqs, ← Category.assoc, hy, Category.assoc, Category.assoc, Category.assoc,
          ← pullback.condition, pullback.lift_fst_assoc]
    obtain ⟨z', ⟨hz', -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := K)
      (nonZeroDivisors R) le_rfl ν y x hyν
    exact ⟨z', hz'⟩

theorem _root_.GlobalTheory.nonempty_subClosure : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0})
    (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (C : Coc Z) (N : ℕ),
    Nonempty (C.Emb N) → ∀ (ch : Charts Z) (r : ℕ) (D : C.Sub ch r), Nonempty (D.Closure s) :=
  fun O _ _ _ Z s hproj hnorm hflat C N hEm ch r D => exists_closure O Z s hproj hnorm hflat C N hEm ch r D

end GlobalTheory.SubClosure
