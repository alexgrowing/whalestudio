import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomainStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_change {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat ξ E) {r : ℕ} {b b' : Fin r → E}
    {p : Cpt ξ} (hb : L.IsFrameAt b p) (hb' : L.IsFrameAt b' p) :
    ∃ T : Matrix (Fin r) (Fin r) (X.presheaf.stalk p.1), ∀ q, b' q = ∑ i, genMap ξ p (T i q) • b i := by
  have h : ∀ q, ∃ t : Fin r → X.presheaf.stalk p.1, b' q = ∑ i, genMap ξ p (t i) • b i := fun q => by
    have hm : b' q ∈ L p := by rw [hb'.2]; exact Submodule.subset_span ⟨q, rfl⟩
    rw [hb.2] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
    have h' : ∀ i, ∃ g, genMap ξ p g = (c i : Ω) := fun i => (c i).2
    choose t ht using h'
    exact ⟨t, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [ht]; rfl⟩
  choose T hT using h
  exact ⟨Matrix.of fun i q => T q i, hT⟩

theorem valAt_prod {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {A₀ : Type} (S : Finset A₀)
    {a : A₀ → Ω} {r : A₀ → ℂ} (h : ∀ i, ValAt ξ z (a i) (r i)) :
    ValAt ξ z (∏ i ∈ S, a i) (∏ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CxVal.one hz
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CxVal.mul (h i) ih

theorem valAt_det {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {r : ℕ}
    (T : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z))) :
    ValAt ξ z (T.map (genMap ξ ⟨centre z, hz⟩)).det (T.map (Scheme.stalkClosedPointTo z).hom).det :=
  ⟨hz, T.det, RingHom.map_det _ _, RingHom.map_det _ _⟩

end General

section Quot

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem quot_basis {N j : ℕ} (hj : j ≤ N) {b : Fin N → E} {F : Submodule Ω E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) (hF : Submodule.span Ω (Set.range (b ∘ headIdx hj)) = F) :
    LinearIndependent Ω (fun a => F.mkQ (b (tailIdx hj a))) ∧
      Submodule.span Ω (Set.range fun a => F.mkQ (b (tailIdx hj a))) = ⊤ := by
  have hinj : Function.Injective (tailIdx hj) := fun a a' h => by
    have := congrArg Fin.val h
    simp only [tailIdx] at this
    exact Fin.ext (by omega)
  constructor
  · have hd : Disjoint (Submodule.span Ω (Set.range (b ∘ tailIdx hj))) (LinearMap.ker F.mkQ) := by
      rw [Submodule.ker_mkQ, ← hF, Set.range_comp, Set.range_comp]
      refine hli.disjoint_span_image ?_
      rw [Set.disjoint_left]
      rintro _ ⟨a, rfl⟩ ⟨a', h⟩
      have := congrArg Fin.val h
      simp only [tailIdx, headIdx, Fin.val_castLE] at this
      have := a'.isLt
      omega
    exact (hli.comp _ hinj).map hd
  · rw [eq_top_iff]
    have hall : ∀ i, F.mkQ (b i) ∈ Submodule.span Ω (Set.range fun a => F.mkQ (b (tailIdx hj a))) := fun i => by
      by_cases hi : i.val < j
      · have : b i ∈ F := by
          rw [← hF]
          exact Submodule.subset_span ⟨⟨i.val, hi⟩, by simp [headIdx]⟩
        rw [(Submodule.Quotient.mk_eq_zero F).2 this |> fun h => (show F.mkQ (b i) = 0 from h)]
        exact zero_mem _
      · exact Submodule.subset_span ⟨⟨i.val - j, by have := i.isLt; omega⟩, by
          have : tailIdx hj ⟨i.val - j, by have := i.isLt; omega⟩ = i := Fin.ext (by simp [tailIdx]; omega)
          simp only [this]⟩
    rintro x -
    obtain ⟨e, rfl⟩ := F.mkQ_surjective x
    have he : e ∈ Submodule.span Ω (Set.range b) := by rw [hsp]; trivial
    induction he using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hall i
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add]; exact add_mem h h'
    | smul a x _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

end Quot

theorem sqrt_det_change {n : ℕ} {Γ Γ' Tz : Matrix (Fin n) (Fin n) ℂ} (hΓ : Γ.PosDef)
    (h : Γ' = Tz.conjTranspose * Γ * Tz) :
    Real.sqrt Γ'.det.re = ‖Tz.det‖ * Real.sqrt Γ.det.re := by
  obtain ⟨h0, h1⟩ := Complex.pos_iff.1 hΓ.det_pos
  have hg : Γ.det = ((Γ.det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using h1.symm)
  have e : Γ'.det = (((‖Tz.det‖ ^ 2 * Γ.det.re : ℝ)) : ℂ) := by
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hg]
    have : star Tz.det * Tz.det = ((‖Tz.det‖ ^ 2 : ℝ) : ℂ) := by
      simpa using Complex.conj_mul' Tz.det
    push_cast at this ⊢
    simp only [Complex.ofReal_re]
    linear_combination ((Γ.det.re : ℂ)) * this
  rw [e, Complex.ofReal_re, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem stalk_le_gen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem blocks_disjoint (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem small_frame (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ := by
  have hfr := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  exact (GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (blocks_disjoint Or τ) (fun _ hx => stalk_le_gen _ _ _ hx) (fun _ hx => stalk_le_gen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)).1

theorem class_change (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d d' : MuFrameAt Hd w)
    {s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) (hs' : Or.IsSmallPart d' s')
    (τ : CMType H) (T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω)
    (hT : ∀ q, s' τ q = ∑ p, T p q • s τ p) (q : Fin (Dc.N - Dc.j)) :
    (Hd.F τ).mkQ (d'.b τ (tailIdx Dc.j_le_N q)) =
      ∑ p, T p q • (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N p)) := by
  simp_rw [← map_smul]
  rw [← map_sum]
  refine (Submodule.Quotient.eq (Hd.F τ)).2 ?_
  rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum]
  have e : Or.i τ (d'.b τ (tailIdx Dc.j_le_N q)) - ∑ p, Or.i τ (T p q • d.b τ (tailIdx Dc.j_le_N p)) =
      (Or.i τ (d'.b τ (tailIdx Dc.j_le_N q)) - s' τ q) -
        ∑ p, T p q • (Or.i τ (d.b τ (tailIdx Dc.j_le_N p)) - s τ p) := by
    rw [hT q]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (hs' τ q).2 (sum_mem fun p _ => Submodule.smul_mem _ _ (hs τ p).2)

end Main

theorem norm_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (d d' : MuFrameAt Hd w) (s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (Γ Γ' : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → Or.IsSmallPart d s → Or.IsSmallPart d' s' → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s' τ) (Γ' τ)) → (∀ τ, (Γ τ).PosDef) → ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re = ‖valAt Dc.y d'.u w‖ * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ' τ).det.re := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w d d' s s' Γ Γ' hw hi hs hs' hg hg' hpd
  haveI : CharZero Ω := algebraRat.charZero Ω
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi

  have hch : ∀ τ, ∃ T : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) (Or.𝔐.X.presheaf.stalk (centre z)),
      ∀ q, s' τ q = ∑ i, genMap Or.𝔐.ξ ⟨centre z, h⟩ (T i q) • s τ i := fun τ =>
    exists_change (Or.𝔐.V (Or.sm τ)) (small_frame Or hw d hs τ h) (small_frame Or hw d' hs' τ h)
  choose Ts hTs using hch
  let T : ∀ τ, Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω := fun τ => (Ts τ).map (genMap Or.𝔐.ξ ⟨centre z, h⟩)
  let Tz : ∀ τ, Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ :=
    fun τ => (Ts τ).map (Scheme.stalkClosedPointTo z).hom
  have hT : ∀ τ q, s' τ q = ∑ p, T τ p q • s τ p := hTs

  have hΓ : ∀ τ, Γ' τ = (Tz τ).conjTranspose * Γ τ * Tz τ := fun τ =>
    GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) (s' τ) (Γ τ) (Γ' τ) (T τ) (Tz τ) hpol (hg τ) (hg' τ)
      (hT τ) fun p q => ⟨h, Ts τ p q, rfl, rfl⟩
  have hsq : ∀ τ, Real.sqrt (Γ' τ).det.re = ‖(Tz τ).det‖ * Real.sqrt (Γ τ).det.re := fun τ =>
    sqrt_det_change (hpd τ) (hΓ τ)

  have hΩ : d.u * chartMono Dc.y d.c Hd.aMu = d'.u * chartMono Dc.y d'.c Hd.aMu * ∏ τ, (T τ).det :=
    GlobalTheory.T.tensor_wedge_det_change (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (d.b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (d'.b τ (tailIdx Dc.j_le_N a))) T _ _
      (fun τ => (quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ)
        (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1 (d.adapted τ).2.2).1)
      (fun τ => (quot_basis Dc.j_le_N (b := d.b τ) (F := Hd.F τ)
        (d.adapted τ).1.2.2.2.1 (d.adapted τ).2.1 (d.adapted τ).2.2).2)
      (fun τ q => class_change Or d d' hs hs' τ (T τ) (hT τ) q)
      (d.eq.symm.trans d'.eq)

  have hc' : ∀ k, IsUnit (w ⟨k, d'.c k⟩) := fun k => IsUnit.mk0 _ (d'.inDom.1 k)
  have hy' : ∀ k, Dc.y ⟨k, d'.c k⟩ ≠ 0 := fun k => (hw.2 k _ (hc' k)).1
  have hr : ∀ k, ∃ r : ℂ, ValAt Or.𝔐.ξ z (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) r ∧
      w ⟨k, d.c k⟩ = r * w ⟨k, d'.c k⟩ := fun k => (hw.2 k _ (hc' k)).2 (d.c k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hrw k, h0, zero_mul])
  have hmono : chartMono Dc.y d'.c Hd.aMu ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy' k)
  have hratio : d.u * ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k = d'.u * ∏ τ, (T τ).det := by
    have e : ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k =
        chartMono Dc.y d.c Hd.aMu / chartMono Dc.y d'.c Hd.aMu := by
      simp only [chartMono, div_zpow, Finset.prod_div_distrib]
    rw [e, ← mul_div_assoc, hΩ]
    field_simp

  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hu' := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d'.c d'.f d'.u htie h hw d'.inDom d'.unit
  have hL : ValAt Or.𝔐.ξ z (d.u * ∏ k, (Dc.y ⟨k, d.c k⟩ / Dc.y ⟨k, d'.c k⟩) ^ Hd.aMu k)
      (valAt Dc.y d.u w * ∏ k, r k ^ Hd.aMu k) :=
    CxVal.mul hu.2 (valAt_prod h _ fun k => CxVal.zpow (hrv k) (hr0 k) _)
  have hR : ValAt Or.𝔐.ξ z (d'.u * ∏ τ, (T τ).det) (valAt Dc.y d'.u w * ∏ τ, (Tz τ).det) :=
    CxVal.mul hu'.2 (valAt_prod h _ fun τ => valAt_det h (Ts τ))
  rw [hratio] at hL
  have hv := CxVal.unique hL hR
  have hn : ‖valAt Dc.y d.u w‖ * ∏ k, ‖r k‖ ^ Hd.aMu k = ‖valAt Dc.y d'.u w‖ * ∏ τ, ‖(Tz τ).det‖ := by
    have := congrArg norm hv
    simpa [norm_mul, norm_prod, norm_zpow] using this
  have hw' : ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k =
      (∏ k, ‖r k‖ ^ Hd.aMu k) * ∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul, ← hrw k]
  simp_rw [hsq]
  rw [Finset.prod_mul_distrib, hw']
  calc _ = (‖valAt Dc.y d.u w‖ * ∏ k, ‖r k‖ ^ Hd.aMu k) * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) *
        ∏ τ, Real.sqrt (Γ τ).det.re := by ring
    _ = _ := by rw [hn]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep
