import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnityStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.DatumBasis

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

section Coord

open GlobalTheory.Serre

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (a : OAct O G)
  {g : ℕ} {B : Fin g → (epsR R ⟶ G)} (hB : IsLieBasis B)
include hB

theorem comb_iff_symm (z : Fin g → R) (w : epsR R ⟶ G) :
    IsLieComb z B w ↔ w = ((Lie.basis a hB).equivFun.symm z).hom := by
  have e : B = fun i => (Lie.basis a hB i).hom := funext fun i => (Lie.hom_basis hB i).symm
  rw [Module.Basis.equivFun_symm_apply, ← Lie.isLieComb_iff, ← e]

include a in

theorem exists_comb (z : Fin g → R) : ∃ w, IsTangent w ∧ IsLieComb z B w :=
  ⟨_, Lie.isTangent _, (comb_iff_symm a hB z _).2 rfl⟩

include a in

theorem comb_coord {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (cf : Fin m → R) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  obtain rfl : u = fun k => ((Lie.basis a hB).equivFun.symm (U k)).hom :=
    funext fun k => (comb_iff_symm a hB _ _).1 (hU k)
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  rw [Lie.isLieComb_iff, ← (Lie.basis a hB).equivFun.symm.injective.eq_iff, map_sum]
  simp only [map_smul]
  exact ⟨fun h => Lie.ext h, fun h => congrArg Lie.hom h⟩

theorem eig_coord {x : O} {M : Matrix (Fin g) (Fin g) R} (hM : ∀ i, IsLieComb (M i) B (B i ≫ a.act x))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (s : R) :
    (w ≫ a.act x).left = spMap (epsScaleR s) ≫ w.left ↔ z ᵥ* M = s • z := by
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  have h1 : ∀ i, x • Lie.basis a hB i = (Lie.basis a hB).equivFun.symm (M i) := fun i => Lie.ext (by
    rw [Lie.hom_act_smul, Lie.hom_basis]; exact (comb_iff_symm a hB _ _).1 (hM i))
  have h2 : x • (Lie.basis a hB).equivFun.symm z = (Lie.basis a hB).equivFun.symm (z ᵥ* M) := by
    rw [Matrix.vecMul_eq_sum, map_sum, Module.Basis.equivFun_symm_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm x, h1, map_smul]
  rw [← Lie.hom_act_smul, ← Lie.hom_smul_left, h2, ← map_smul,
    ← (Lie.basis a hB).equivFun.symm.injective.eq_iff]
  exact ⟨fun h => Lie.ext (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem eigBasis_coord {M : O → Matrix (Fin g) (Fin g) R} (hM : ∀ x i, IsLieComb (M x i) B (B i ≫ a.act x))
    {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k)) (ρ : O → R) :
    (∀ w : epsR R ⟶ G, IsTangent w → (∀ x, (w ≫ a.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin m → R, IsLieComb cf u w) ↔
    ∀ z : Fin g → R, (∀ x, z ᵥ* M x = ρ x • z) → ∃! cf : Fin m → R, z = ∑ k, cf k • U k := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hc⟩ := exists_comb a hB z
    exact (existsUnique_congr (comb_coord a hB hU hc)).1
      (h w hw fun x => (eig_coord a hB (hM x) hc _).2 (hz x))
  · intro h w hw he
    obtain ⟨z, hc, -⟩ := hB.2 w hw
    exact (existsUnique_congr (comb_coord a hB hU hc)).2
      (h z fun x => (eig_coord a hB (hM x) hc _).1 (he x))

end Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

section Descent

variable {R S : Type} [CommRing R] [CommRing S] {io : R →+* S} {t : SAB H (Sp R)} {t' : SAB H (Sp S)}
  (m : SABMap t' t (spMap io))

theorem exists_bc (v : epsR R ⟶ t.G) : ∃ q : epsR S ⟶ t'.G, q.left ≫ m.φ = spMap (dualMap io) ≫ v.left := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have cond : (spMap (dualMap io) ≫ v.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, hv, dual_over]
  exact ⟨Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem tangent_of_bc [IsDomain R] (hio : Function.Injective io) {v : epsR R ⟶ t.G} {q : epsR S ⟶ t'.G}
    (h : q.left ≫ m.φ = spMap (dualMap io) ≫ v.left) (hq : IsTangent q) : IsTangent v := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have := t.semi.separated
  have : IsDominant (spMap io) := ⟨by
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le⟩
  refine ext_of_isDominant_of_isSeparated t.G.hom ?_ (spMap io) ?_
  · have a : η[t.G].left ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
    rw [Category.assoc, hv, a, ← spMap_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]
    exact Spec.map_id _
  · have e := m.cm.e_comm
    rw [m.base] at e
    have sq : spMap io ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap io) := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, sq, Category.assoc, ← h, ← Category.assoc]
    exact (congrArg (· ≫ m.φ) hq).trans e

end Descent

theorem eigBasis_descent {K S : Type} [Field K] [CommRing S] [Nontrivial S] {io : PowerSeries K →+* S}
    {t : SAB H (Sp (PowerSeries K))} {t' : SAB H (Sp S)} (m : SABMap t' t (spMap io))
    {g : ℕ} {B : Fin g → (epsR (PowerSeries K) ⟶ t.G)} (hB : IsLieBasis B) {M : 𝓞 E → Matrix (Fin g) (Fin g) K}
    (hM : ∀ x i, IsLieComb (fun k => PowerSeries.C (R := K) (M x i k)) B (B i ≫ t.act.act x))
    {n : ℕ} {U : Fin n → Fin g → K} {v : Fin n → (epsR (PowerSeries K) ⟶ t.G)}
    (hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := K) (U k i)) B (v k)) {q : Fin n → (epsR S ⟶ t'.G)}
    (hq : ∀ k, (q k).left ≫ m.φ = spMap (dualMap io) ≫ (v k).left) (ρ : 𝓞 E → K)
    (he : ∀ k x, (q k ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ (q k).left)
    (hb : ∀ w : epsR S ⟶ t'.G, IsTangent w →
      (∀ x, (w ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ w.left) →
      ∃! cf : Fin n → S, IsLieComb cf q w) :
    (∀ k x, (v k ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ (v k).left) ∧
    ∀ w : epsR (PowerSeries K) ⟶ t.G, IsTangent w →
      (∀ x, (w ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ w.left) →
      ∃! cf : Fin n → PowerSeries K, IsLieComb cf v w := by
  let _ : Algebra K S := (io.comp (PowerSeries.C (R := K))).toAlgebra
  have := t.semi.smooth
  choose B' hB' using fun i => exists_bc m (B i)
  have hBS : IsLieBasis B' := Chart.isLieBasis_baseChange io m.cart hB hB'
  have hMS : ∀ x i, IsLieComb (((M x).map (algebraMap K S)) i) B' (B' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange io m.cart (hM x i) hB' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hB', Category.assoc]; rfl)
  have hUS : ∀ k, IsLieComb (fun j => algebraMap K S (U k j)) B' (q k) := fun k =>
    Chart.comb_baseChange io m.cart (hU k) hB' (hq k)
  have hMR : ∀ x i, IsLieComb (((M x).map (algebraMap K (PowerSeries K))) i) B (B i ≫ t.act.act x) := hM
  have hUR : ∀ k, IsLieComb (fun j => algebraMap K (PowerSeries K) (U k j)) B (v k) := hU
  have key : ∀ (T : Type) [CommRing T] (f : K →+* T) (k : Fin n) (x : 𝓞 E) (j : Fin g),
      f ((U k ᵥ* M x) j) = ((fun j => f (U k j)) ᵥ* (M x).map f) j := fun T _ f k x j =>
    RingHom.map_vecMul f (M x) (U k) j
  have hK : ∀ k x, U k ᵥ* M x = ρ x • U k := fun k x => funext fun j => (algebraMap K S).injective (by
    rw [key, (eig_coord t'.act hBS (hMS x) (hUS k) (algebraMap K S (ρ x))).1 (he k x)]
    simp)
  refine ⟨fun k x => (eig_coord t.act hB (hMR x) (hUR k) (algebraMap K _ (ρ x))).2 (funext fun j => ?_),
    (eigBasis_coord t.act hB hMR hUR fun x => algebraMap K _ (ρ x)).2 ?_⟩
  · rw [← key, hK]; simp
  · exact (GlobalTheory.commonEigenvectors_flat_baseChange K (𝓞 E) g n M ρ).1 S U hK
      ((eigBasis_coord t'.act hBS hMS hUS fun x => algebraMap K S (ρ x)).1 hb) (PowerSeries K)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Push

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  exact ⟨fun h => (Chart.tan_push m.cart w).2 h.2,
    fun h => ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], (Chart.tan_push m.cart w).1 h⟩⟩

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  have sc : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
    rw [← spMap_comp]
    congr 1
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, sc]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w :=
  (Chart.comb_push m.cart cf v w).symm

end Push

end GlobalTheory.ArcQ.DatumBasis

open GlobalTheory.ArcQ.DatumBasis in

theorem GlobalTheory.ArcQ.arcDatum_arcLieBasis : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁), (∀ τ k, GtTanR (d.e τ k)) → ArcLieBasis d.W d.e := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ d htan
  obtain ⟨ζ, -, -, -, hN, -⟩ := GlobalTheory.T.exists_normalForm_arcDatum_framedPoint_rootOfUnity hL hL2 E H Dw l Xo c K₁ d
  obtain ⟨y, hy, -⟩ := hN htan
  obtain ⟨-, G, m1, m2, -, -, -, -, -, -, h, -⟩ := hy
  choose v p hv hp1 hp2 hp3 using h
  let q : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (ArcS Dw K₁) ⟶ G.G) := fun τ k => Over.homMk (p τ k) (hp3 τ k)
  have hq1 : ∀ τ k, (q τ k).left ≫ m1.φ = y.u τ k := hp1
  have hq2 : ∀ τ k, (q τ k).left ≫ m2.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left := hp2
  have hι : Function.Injective (arcι Dw K₁) := (GlobalTheory.ArcConst.algebraMap_injective Dw K₁).comp
    ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  have := GlobalTheory.ArcConst.isDomain Dw K₁
  have tq : ∀ τ k, IsTangent (q τ k) := fun τ k => (tan_iff m1 _).1 (hq1 τ k ▸ y.tan τ k)
  have tv : ∀ τ k, IsTangent (v τ k) := fun τ k => tangent_of_bc m2 hι (hq2 τ k) (tq τ k)
  obtain ⟨g, e₀, B, M, h₀, hB, hc, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W
  have hU : ∀ τ k, ∃ U : Fin g → K₁, IsLieComb (fun i => PowerSeries.C (R := K₁) (U i)) B (v τ k) := fun τ k => by
    obtain ⟨U, hU, -⟩ := hc (d.e τ k)
      (((GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W (d.e τ k)).2 _ (hv τ k)).2 (tv τ k))
    exact ⟨U, (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W g U e₀ (d.e τ k) B (v τ k)
      (fun i => (h₀ i).2) hU).1 (hv τ k)⟩
  choose U hU using hU
  have eig : ∀ (τ : E →+* ℂ) (w : epsR (ArcS Dw K₁) ⟶ G.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (arcι Dw K₁
        (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x))))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← arcS_pin]; exact eig_iff m1 w x _
  refine ⟨v, hv, fun τ => ?_⟩
  have hu : y.u τ = fun k => (q τ k).left ≫ m1.φ := funext fun k => (hq1 τ k).symm
  obtain ⟨a₁, a₂⟩ := eigBasis_descent m2 hB hM (hU τ) (hq2 τ) (fun x => algebraMap c.F K₁ (embK c τ x))
    (fun k => (eig τ _).1 (hq1 τ k ▸ y.eig τ k)) fun w hw he =>
      (existsUnique_congr fun cf => by rw [hu]; exact comb_iff m1 (q τ) cf w).1
        (y.basis τ _ ((tan_iff m1 w).2 hw) ((eig τ w).2 he))
  exact ⟨fun k => ⟨tv τ k, a₁ k⟩, a₂⟩
