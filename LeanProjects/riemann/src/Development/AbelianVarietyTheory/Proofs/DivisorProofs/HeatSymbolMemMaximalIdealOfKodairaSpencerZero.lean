import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaudStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasisStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueOverChartAbelianLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroMod

theorem intDer {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_basis_isKS_symbol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n vY dd hdd D hD h hb hdef
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  choose v' hv' using fun a => GlobalTheory.ChartKSBracket.tanPt E H (ChartRing k m d) t P Y (vY a)
  obtain ⟨b, hbv⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H (ChartRing k m d) t P Y n vY v' hv'
  have hx : spMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom ≫ 𝟙 (Sp (ChartRing k m d)) =
      chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) := by
    rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rfl
  obtain ⟨b', hb'⟩ := GlobalTheory.TotalFrame.exists_basis_map b _ hx
  have ev : (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left) =
      fun a => (tv (b' a)).left := funext fun a => by rw [hb', hbv]
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => GlobalTheory.ChartKSBracket.isTanAtG_tv E H _ t (v' a), fun w hw => ?_, ?_⟩
  · rw [ev]
    refine ⟨b'.repr (GlobalTheory.LieMet.tanOf hw), (GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).2 (b'.sum_repr _).symm,
      fun a ha => ?_⟩
    rw [(GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).1 ha, Module.Basis.repr_sum_self]
  · obtain ⟨D', hD'⟩ := intDer _ D
    revert h
    rw [← hD']
    intro h hb hdef
    exact GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y n vY dd hdd v' hv' D' h hb hdef

set_option maxHeartbeats 1600000 in

theorem symbol_mem_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hcomb Y n' v' dd hdd D q hq h hb hdef Θ hΘ hm
  letI := H.starRing
  have hD : ∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := fun i => by
    rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨w, hw, hwb, hks⟩ := exists_basis_isKS_symbol E H k m d t P gam hmon hli hab Y n' v' dd hdd D hD h hb hdef
  choose C hC using fun c => (hwb (v c) (hv c)).exists
  have hks' := GlobalTheory.KSFrameChange.isKS_frame_change E H (Sp (ChartRing k m d)) t
    ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i)))
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) n n' v w (Matrix.of C)
    (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ hv hw hC hΘ
  have heq := GlobalTheory.T.kodairaSpencer_matrix_unique_over_chart_abelian_locus E H k m d t P gam hmon hli hab n' w hw hwb D _ _ hks' hks
  intro a b
  have e := congrArg (fun M => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (M a b)) heq
  simp only [Matrix.map_apply, Iso.inv_hom_id_apply] at e
  rw [← e, Matrix.mul_apply, map_sum]
  refine Ideal.sum_mem _ fun c _ => ?_
  rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Ideal.sum_mem _ fun e' _ => ?_
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hm e' c))

end GlobalTheory.KSZeroMod
