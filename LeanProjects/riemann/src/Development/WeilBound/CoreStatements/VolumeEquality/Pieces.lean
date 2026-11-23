import Development.WeilBound.CoreStatements.VolumeEquality.RootBr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSetStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Polynomial Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem cover_seq {α : Type} [TopologicalSpace α] [SecondCountableTopology α] (T : Set α) (P : Set α → Prop) (h0 : P ∅)
    (h : ∀ t ∈ T, ∃ V, IsOpen V ∧ t ∈ V ∧ P V) : ∃ W : ℕ → Set α, (∀ m, IsOpen (W m) ∧ P (W m)) ∧ T ⊆ ⋃ m, W m := by
  obtain ⟨S, hc, hs, he⟩ := TopologicalSpace.isOpen_sUnion_countable {V | IsOpen V ∧ P V} fun _ hV => hV.1
  obtain ⟨W, hW⟩ := (hc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨W, fun m => ?_, fun t ht => ?_⟩
  · rcases (hW ▸ Set.mem_range_self m : W m ∈ insert ∅ S) with e | e
    · exact e ▸ ⟨isOpen_empty, h0⟩
    · exact hs e
  · obtain ⟨V, h1, h2, h3⟩ := h t ht
    obtain ⟨V', hV', ht'⟩ : t ∈ ⋃₀ S := he ▸ ⟨V, ⟨h1, h3⟩, h2⟩
    obtain ⟨m, rfl⟩ : V' ∈ Set.range W := hW ▸ Set.mem_insert_of_mem _ hV'
    exact Set.mem_iUnion.2 ⟨m, ht'⟩

theorem ballDom_preconnected {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : _root_.IsPreconnected (GlobalTheory.CompanionTheory.Ar.Cusp.ballDom q) := by
  have hs : StarConvex ℝ 0 (GlobalTheory.CompanionTheory.Ar.Cusp.ballDom q) := fun t ht a b ha hb hab τ => by
    have e : GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ = (b : ℂ) • GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ := by
      ext x y
      simp [GlobalTheory.CompanionTheory.Ar.Cusp.ballMat]
    have e2 : 1 - (GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q (a • (0 : Fin n → ℂ) + b • t) τ =
        (1 - (GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ) + ((1 - b ^ 2 : ℝ) : ℂ) • ((GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ)ᴴ * GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q t τ) := by
      rw [e, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      module
    rw [e2]
    exact (ht τ).add_posSemidef ((posSemidef_conjTranspose_mul_self _).smul (Complex.zero_le_real.2 (by nlinarith)))
  refine (hs.isPathConnected fun τ => ?_).isConnected.isPreconnected
  rw [show GlobalTheory.CompanionTheory.Ar.Cusp.ballMat q 0 τ = 0 from rfl, Matrix.mul_zero, sub_zero]
  exact PosDef.one

theorem isOpen_of_holTo {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (h : IsHolTo B y) : IsOpen B := by
  simpa using (h ⊤ 0).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

section Pts

variable {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y)

theorem coords_of_sat {z : Sp ℂ ⟶ 𝔐.X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w') (hs : w ∈ torusSat {w'}) :
    CoordsAt 𝔐.ξ y z w := by
  obtain ⟨_, rfl, a, ha, rfl⟩ := hs
  exact (((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), rfl⟩

theorem sat_of_coords {z : Sp ℂ ⟶ 𝔐.X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w') (h' : CoordsAt 𝔐.ξ y z w) :
    w ∈ torusSat {w'} := by
  obtain ⟨a, rfl⟩ := (((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).2 _).1 h'
  exact ⟨_, rfl, fun k => a k, fun k => (a k).ne_zero, rfl⟩

theorem pt_unique {z z' : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w) (h' : CoordsAt 𝔐.ξ y z' w) : z = z' :=
  GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J y 𝔐.tie 𝔐.normal 𝔐.all z z' w h h'

theorem mem_mcPts {z : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} (h : CoordsAt 𝔐.ξ y z w) : w ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => (h.1 k).imp fun _ h => h.ne_zero, fun g hg => by
    rw [MvPolynomial.eval_map]
    exact ((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).2.2 z _ (𝔐.all _) h).1 g hg⟩

theorem exists_pt {w : (Σ k, J k) → ℂ} (h : w ∈ mcPts (mCoordIdeal y)) : ∃ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w :=
  ((tie_points _ _ 𝔐.ξ K J y 𝔐.tie ℂ).1 w (fun k => (h.1 k).imp fun _ h => Ne.isUnit h) fun g hg => by
    have := h.2 g hg
    rwa [MvPolynomial.eval_map] at this).exists.imp fun _ h => h.2

theorem interior_iff (z : Sp ℂ ⟶ 𝔐.X) : centre (z ≫ 𝔐.f) ∈ abLocus Y.t.G ↔ 𝔐.Interior z :=
  abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _

theorem labVal_of_over {z : Sp ℂ ⟶ 𝔐.X} (hz : 𝔐.Interior z) {κ : c.F →+* ℂ}
    (h : z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) (sm : CMType H → CMType H ⊕ CMType H) :
    𝔐.LabVal z sm fun τ => κ.comp (labelEmb c (sm τ)) := by
  obtain ⟨κ', p, hp⟩ := FamEx.exists_isOver E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain rfl : κ' = κ := by
    obtain ⟨x, h1, -, h3⟩ := hp
    have := c.fin
    have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
    rw [← Category.assoc, ← h1, Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, h3, ← Chg.spMap_comp'] at h
    exact IsFractionRing.ringHom_ext (A := 𝓞 c.F) fun a =>
      RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) a
  exact fun τ a => GlobalTheory.T.constants_value_over_point E H D l Xo c Y S Ω K J y 𝔐 z _ p hp _

end Pts

variable {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)
  (B : BaseUnif Y Or.sm Dc.j Dc.j' Dc.n)

structure Sheets (FF : Fin B.np → Set (Fin Dc.n → ℂ)) (d : Fin B.np → ℕ) where
  d_pos : ∃ k, 0 < d k
  pc : ℕ → Fin B.np
  V : ℕ → Set (Fin Dc.n → ℂ)
  Bm : ℕ → Set (Fin Dc.n → ℂ)
  γ : ℕ → (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ
  z : ℕ → (Fin Dc.n → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)
  cover : IsSheetCover Dc.chart V Bm γ
  V_sub : ∀ m, V m ⊆ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F (pc m)).q
  B_sub : ∀ m, Bm m ⊆ FF (pc m)
  count : ∀ k, ∀ᵐ t, t ∈ FF k → {m | pc m = k ∧ t ∈ Bm m}.encard = d k
  z_coords : ∀ m, ∀ t ∈ V m, CoordsAt Or.𝔐.ξ Dc.y (z m t) (γ m t)
  z_over : ∀ m, ∀ t ∈ V m, z m t ≫ Or.𝔐.f = B.pt (pc m) t

open Classical in

def nSheets (U : Y.X.Opens) (k : Fin B.np) : ℕ := if ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U then Or.deg else 0

set_option maxHeartbeats 1600000 in
theorem exists_sheets (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj)
    (FF : Fin B.np → Set (Fin Dc.n → ℂ)) (hF : ∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) :
    ∃ U : Y.X.Opens, genPt Or.𝔐.ξ₀ ∈ U ∧ (∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → genPt Or.𝔐.ξ₀ ⤳ centre p) ∧
      Nonempty (Sheets Or B FF (nSheets Or B U)) := by
  classical
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨U, a, cf, hU, hc⟩ := h4 E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 Or.deg Or.cover
  have hgen : Or.𝔐.f (genPt Or.𝔐.ξ) = genPt Or.𝔐.ξ₀ := by
    show (Or.𝔐.ξ ≫ Or.𝔐.f) (IsLocalRing.closedPoint Ω) = _
    rw [show Or.𝔐.ξ ≫ Or.𝔐.f = _ from Or.𝔐.fn_over]
    exact congrArg (fun x => Or.𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum Or.𝔐.Ω₀) _ _)
  refine ⟨U, hU, fun p hp => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (monicOf fun i => valAt' p U (a i)) fun h =>
      Or.cover.1.ne' ((natDegree_monicOf _).symm.trans (natDegree_eq_of_degree_eq_some h))
    obtain ⟨z, rfl, -⟩ := (hc p hp).2.1 x hx
    exact hgen ▸ (Or.𝔐.all (centre z)).map Or.𝔐.f.continuous
  let T : Fin B.np → Set (Fin Dc.n → ℂ) := fun k => {t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q | ⊤ ≤ B.pt k t ⁻¹ᵁ U}
  let A : Fin B.np → (Fin Dc.n → ℂ) → Fin Or.deg → ℂ := fun k t i => valAt' (B.pt k t) U (a i)
  let w : Fin B.np → (Fin Dc.n → ℂ) → ℂ → (Σ k, J k) → ℂ := fun k t θ s => ∑ i, valAt' (B.pt k t) U (cf s i) * θ ^ (i : ℕ)
  have hW : ∀ k, ∃ Wk : ℕ → Set (Fin Dc.n → ℂ), (∀ m, IsOpen (Wk m) ∧ Wk m ⊆ T k ∧
      (∀ t ∈ Wk m, ∀ t' ∈ Wk m, (B.F k).Eqv (B.Γ k) t t' → t = t') ∧ ∃ θ : Fin Or.deg → (Fin Dc.n → ℂ) → ℂ,
        (∀ i, DifferentiableOn ℂ (θ i) (Wk m)) ∧ ∀ t ∈ Wk m, (Function.Injective fun i => θ i t) ∧
          ∀ x, (monicOf (A k t)).IsRoot x ↔ ∃ i, x = θ i t) ∧ T k ⊆ ⋃ m, Wk m := fun k => by
    refine cover_seq (T k) (fun V => V ⊆ T k ∧ (∀ t ∈ V, ∀ t' ∈ V, (B.F k).Eqv (B.Γ k) t t' → t = t') ∧
      ∃ θ : Fin Or.deg → (Fin Dc.n → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (θ i) V) ∧ ∀ t ∈ V, (Function.Injective fun i => θ i t) ∧
        ∀ x, (monicOf (A k t)).IsRoot x ↔ ∃ i, x = θ i t) ?_ fun t ht => ?_
    · exact ⟨Set.empty_subset _, fun _ h => h.elim, 0, fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    obtain ⟨V, θ, o1, m1, s1, d1, r1⟩ := h3 _ _ (T k) (A k) (B.hol k U 0).1 (differentiableOn_pi.2 fun i => (B.hol k U (a i)).2)
      (fun t ht => (hc _ ht.2).1) t ht
    obtain ⟨V', o2, m2, -, i2⟩ := h5 E H l (B.Di k) _ _ _ _ _ (B.F k) (B.Γ k) (B.form_eq k) (fun γ hγ => (B.mem_Γ k γ).1 hγ) t ht.1
    exact ⟨V ∩ V', o1.inter o2, ⟨m1, m2⟩, Set.inter_subset_left.trans s1, fun t h t' h' => i2 t h.2 t' h'.2, θ,
      fun i => (d1 i).mono Set.inter_subset_left, fun t h => r1 t h.1⟩
  choose Wk hWk hWc using hW
  choose hWo hWs hWi θ hθd hθ using hWk
  have hz : ∀ k m i t, ∃ z : Sp ℂ ⟶ Or.𝔐.X, t ∈ Wk k m → z ≫ Or.𝔐.f = B.pt k t ∧ CoordsAt Or.𝔐.ξ Dc.y z (w k t (θ k m i t)) :=
    fun k m i t => by
      by_cases ht : t ∈ Wk k m
      · exact ((hc _ (hWs k m ht).2).2.1 _ (((hθ k m t ht).2 _).2 ⟨i, rfl⟩)).imp fun _ h _ => h
      · obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.multiprojective_points_nonempty K J Ω Dc.y fun k => by
          obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
          exact ⟨c' k, Finset.prod_ne_zero_iff.1 hc'.1 k (Finset.mem_univ k)⟩
        exact (exists_pt Or.𝔐 hw₀).imp fun _ _ h => absurd h ht
  choose z hz using hz
  have hin : ∀ k m i t, t ∈ Wk k m → Or.𝔐.Interior (z k m i t) := fun k m i t ht =>
    (interior_iff Or.𝔐 _).1 ((hz k m i t ht).1 ▸ B.interior k t (hWs k m ht).1)

  have hsame : ∀ k m i t k' m' i' t', t ∈ Wk k m → t' ∈ Wk k' m' → w k t (θ k m i t) ∈ torusSat {w k' t' (θ k' m' i' t')} →
      z k m i t = z k' m' i' t' ∧ B.pt k t = B.pt k' t' := fun k m i t k' m' i' t' ht ht' h => by
    have e := pt_unique Or.𝔐 (hz k m i t ht).2 (coords_of_sat Or.𝔐 (hz k' m' i' t' ht').2 h)
    exact ⟨e, by rw [← (hz k m i t ht).1, e, (hz k' m' i' t' ht').1]⟩

  have hcov : ∀ b : Fin Dc.nCharts, ∀ᵐ t, t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1 →
      ∃ k m i, ∃ t' ∈ FF k ∩ disjointed (Wk k) m, (Dc.chart b).γ t ∈ torusSat {w k t' (θ k m i t')} := fun b => by
    have hζ : ∀ t, ∃ ζ : Sp ℂ ⟶ Or.𝔐.X, t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1 → CoordsAt Or.𝔐.ξ Dc.y ζ ((Dc.chart b).γ t) := fun t => by
      by_cases ht : t ∈ Metric.ball (0 : Fin Dc.n → ℂ) 1
      · exact (exists_pt Or.𝔐 ((Dc.chart b).mem t ht)).imp fun _ h _ => h
      · exact (exists_pt Or.𝔐 ((Dc.chart b).mem 0 (Metric.mem_ball_self one_pos))).imp fun _ _ h => absurd h ht
    choose ζ hζ using hζ
    have hg : genPt Or.𝔐.ξ ∈ Or.𝔐.f ⁻¹ᵁ U := by
      show (Or.𝔐.ξ ≫ Or.𝔐.f) (IsLocalRing.closedPoint Ω) ∈ U
      rw [show Or.𝔐.ξ ≫ Or.𝔐.f = _ from Or.𝔐.fn_over]
      exact (congrArg (fun x => Or.𝔐.ξ₀ x ∈ U) (Subsingleton.elim (α := PrimeSpectrum Or.𝔐.Ω₀) _ _)).mpr hU
    obtain ⟨t₁, ht₁, z₁, c₁, u₁⟩ := h2 _ Ω Or.𝔐.ξ K J Dc.y _ _ (Dc.chart b) _ Or.𝔐.tie Or.𝔐.all Dc.arith hg
    have n1 := h1 _ _ _ ζ (Or.𝔐.f ⁻¹ᵁ U) Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (GlobalTheory.T.holomorphic_coords_of_generic_point _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie Or.𝔐.all _ _ _ ζ Metric.isOpen_ball (Dc.chart b).analytic.differentiableOn hζ)
      ⟨t₁, ht₁, pt_unique Or.𝔐 c₁ (hζ t₁ ht₁) ▸ u₁⟩
    have n2 : ∀ᵐ t : Fin Dc.n → ℂ, ∀ i, t i ≠ 0 := ae_all_iff.2 fun i => by
      rw [volume_pi]
      exact Measure.ae_eval_ne _ i 0
    filter_upwards [n2, compl_mem_ae_iff.2 n1] with t e1 e2 ht
    have hi : Or.𝔐.Interior (ζ t) := by_contra fun h => by
      obtain ⟨i, -, hi⟩ := ((Dc.chart b).boundary t ht).1 ((Or.bd _ _ (hζ t ht)).2 h)
      exact e1 i hi
    obtain ⟨k, t₂, ht₂, e3⟩ := B.onto _ ((interior_iff Or.𝔐 _).2 hi)
    obtain ⟨t₃, ht₃, e4⟩ := (hF k).2.2.1 t₂ ht₂
    have e5 : ζ t ≫ Or.𝔐.f = B.pt k t₃ := e3.symm.trans ((B.fibre k _ ht₂ _ ((hF k).2.1 ht₃)).2 e4)
    have e6 : t₃ ∈ T k := ⟨(hF k).2.1 ht₃, e5 ▸ by_contra fun h => e2 ⟨ht, h⟩⟩
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (iUnion_disjointed (f := Wk k) ▸ hWc k e6)
    obtain ⟨x, hx, cx⟩ := (hc _ e6.2).2.2.1 _ e5
    obtain ⟨i, rfl⟩ := ((hθ k m t₃ (disjointed_subset _ _ hm)).2 x).1 hx
    exact ⟨k, m, i, t₃, ⟨ht₃, hm⟩, sat_of_coords Or.𝔐 cx (hζ t ht)⟩
  obtain ⟨k₀, m₀, i₀, t₀, ht₀⟩ : ∃ k m, ∃ _ : Fin Or.deg, ∃ t, t ∈ FF k ∩ disjointed (Wk k) m := by
    obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.multiprojective_points_nonempty K J Ω Dc.y fun k => by
      obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
      exact ⟨c' k, Finset.prod_ne_zero_iff.1 hc'.1 k (Finset.mem_univ k)⟩
    obtain ⟨b, -⟩ := Dc.chart_cover w₀ hw₀
    obtain ⟨t, ht, h⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos volume (0 : Fin Dc.n → ℂ) one_pos).ne' (ae_restrict_of_ae (hcov b))
    obtain ⟨k, m, i, t', ht', -⟩ := h ht
    exact ⟨k, m, i, t', ht'⟩
  have : Nonempty (Fin B.np) := ⟨k₀⟩
  have : Nonempty (Fin Or.deg) := ⟨i₀⟩
  obtain ⟨e⟩ : Nonempty (ℕ ≃ Fin B.np × ℕ × Fin Or.deg) := nonempty_equiv_of_countable
  have hT : ∀ {k t}, t ∈ T k → nSheets Or B U k = Or.deg := fun ht => if_pos ⟨_, ht.1, ht.2⟩
  refine ⟨⟨⟨k₀, (hT (hWs k₀ m₀ (disjointed_subset _ _ ht₀.2))).symm ▸ Or.cover.1⟩, fun m => (e m).1, fun m => Wk (e m).1 (e m).2.1,
    fun m => FF (e m).1 ∩ disjointed (Wk (e m).1) (e m).2.1, fun m t => w (e m).1 t (θ (e m).1 (e m).2.1 (e m).2.2 t),
    fun m => z (e m).1 (e m).2.1 (e m).2.2, ⟨fun m => hWo _ _, fun m => ?_, fun m t ht => ?_, fun m t ht t' ht' h => ?_,
      fun m => ⟨(hF _).1.inter (MeasurableSet.disjointed (fun m => (hWo _ m).measurableSet) _),
        Set.inter_subset_right.trans (disjointed_subset _ _)⟩, fun m m' hne t ht h => hne (e.injective ?_), fun b => ?_⟩,
    fun m t ht => (hWs _ _ ht).1, fun m => Set.inter_subset_left, fun k => ?_, fun m t ht => (hz _ _ _ t ht).2,
    fun m t ht => (hz _ _ _ t ht).1⟩⟩
  · exact differentiableOn_pi.2 fun s => DifferentiableOn.fun_sum fun i _ =>
      ((B.hol _ U (cf s i)).2.mono (hWs _ _)).mul ((hθd _ _ _).pow _)
  · exact ⟨mem_mcPts Or.𝔐 (hz _ _ _ t ht).2, fun h => (Or.bd _ _ (hz _ _ _ t ht).2).1 h (hin _ _ _ t ht)⟩
  · exact hWi _ _ t ht t' ht' ((B.fibre _ t (hWs _ _ ht).1 t' (hWs _ _ ht').1).1 (hsame _ _ _ _ _ _ _ _ ht ht' h).2)
  · obtain ⟨_, ⟨t', ht', rfl⟩, h⟩ := h
    generalize e m = x at ht h ⊢
    generalize e m' = x' at ht' h ⊢
    obtain ⟨k, n, i⟩ := x
    obtain ⟨k', n', i'⟩ := x'
    have u := disjointed_subset _ _ ht.2
    have u' := disjointed_subset _ _ ht'.2
    obtain ⟨e1, e2⟩ := hsame _ _ i _ _ _ i' _ u u' ⟨_, rfl, h⟩
    obtain rfl : k = k' := B.disj _ _ t (hWs _ _ u).1 t' (hWs _ _ u').1 e2
    obtain rfl : t = t' := (hF k).2.2.2 t ht.1 t' ht'.1 ((B.fibre k t (hWs _ _ u).1 t' (hWs _ _ u').1).1 e2)
    obtain rfl : n = n' := by_contra fun hn => Set.disjoint_left.1 (disjoint_disjointed (Wk k) hn) ht.2 ht'.2
    obtain rfl : i = i' := (hθ k n t u).1 ((hc _ (hWs _ _ u).2).2.2.2 _ _ _ (((hθ k n t u).2 _).2 ⟨i, rfl⟩)
      (((hθ k n t u).2 _).2 ⟨i', rfl⟩) (hz k n i t u).2 (e1 ▸ (hz k n i' t u).2))
    rfl
  · refine measure_mono_null ?_ (ae_iff.1 (hcov b))
    intro t ht h
    obtain ⟨k, m, i, t', ht', _, rfl, h'⟩ := h ht.1
    exact ht.2 ⟨_, Set.mem_iUnion.2 ⟨e.symm (k, m, i), t', by rwa [e.apply_symm_apply], by simp only [e.apply_symm_apply]⟩, h'⟩
  · by_cases hk : ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U
    · filter_upwards [compl_mem_ae_iff.2 (h1 _ _ _ _ U (isOpen_of_holTo (B.hol k)) (ballDom_preconnected (B.F k).q) (B.hol k) hk)]
        with t e1 ht
      have e2 : t ∈ T k := ⟨(hF k).2.1 ht, by_contra fun h => e1 ⟨(hF k).2.1 ht, h⟩⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (iUnion_disjointed (f := Wk k) ▸ hWc k e2)
      have : {m | (e m).1 = k ∧ t ∈ FF (e m).1 ∩ disjointed (Wk (e m).1) (e m).2.1} =
          (fun i : Fin Or.deg => e.symm (k, n, i)) '' Set.univ := by
        ext m
        obtain ⟨⟨k', n', i⟩, rfl⟩ := e.symm.surjective m
        simp only [Set.mem_setOf_eq, e.apply_symm_apply, Set.image_univ, Set.mem_range, e.symm.injective.eq_iff]
        constructor
        · rintro ⟨rfl, h⟩
          obtain rfl : n = n' := by_contra fun h' => Set.disjoint_left.1 (disjoint_disjointed (Wk k') h') hn h.2
          exact ⟨i, rfl⟩
        · rintro ⟨_, ⟨⟩⟩
          exact ⟨rfl, ht, hn⟩
      rw [this, Function.Injective.encard_image (fun i i' h => by simpa using h), hT e2]
      simp
    · refine ae_of_all _ fun t _ => ?_
      rw [nSheets, if_neg hk, Nat.cast_zero, Set.encard_eq_zero]
      refine Set.eq_empty_of_forall_notMem ?_
      rintro m ⟨rfl, h⟩
      exact hk ⟨t, hWs _ _ (disjointed_subset _ _ h.2)⟩

end SheetDecomposition
