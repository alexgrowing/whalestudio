import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstantsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
  GlobalTheory.GoodTransfer

namespace GlobalTheory.ArcFrame

open Matrix GlobalTheory.LieEigen MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem iwasawa_lower {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (L : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ (∀ i j, i < j → L i j = 0) ∧
      (∀ i, L i i ≠ 0) ∧ A = L * k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, e⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) Aᵀ (by rwa [det_transpose])
  refine ⟨kᵀ, Uᵀ, by rwa [det_transpose], fun i j h => hU h, hd, ?_⟩
  rw [← transpose_transpose A, e, transpose_mul, transpose_map]

section Lie

variable {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] (act : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem eig_prodPts (hv : ∀ i, IsTangent (v i)) (x : O) (s : R)
    (he : ∀ i, (v i ≫ act.act x).left = spMap (epsScaleR s) ≫ (v i).left) (c : Fin n → R) :
    (prodPts c v ≫ act.act x).left = spMap (epsScaleR s) ≫ (prodPts c v).left := by
  have := act.hom x
  have e : prodPts c v ≫ act.act x = prodPts c fun i => v i ≫ act.act x := by
    refine (map_list_prod (IsMonHom.monoidHom (act.act x) _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Category.assoc _ (v i) (act.act x))
  have e₁ : ∀ i, v i ≫ act.act x = prodPts (s • Pi.single i 1) v := fun i => by
    rw [prodPts_smul, ← (Chart.isLieComb_iff _ _ _).1 (IntModelExists.isLieComb_single hv i)]
    exact Over.OverMorphism.ext (he i)
  have e₂ : ∑ i, c i • (s • Pi.single i (1 : R) : Fin n → R) = s • c := by
    ext j; simp [Pi.single_apply, mul_comm]
  rw [e, funext e₁, prodPts_prodPts hv, e₂, prodPts_smul]
  rfl

omit [IsLocalRing R] [Smooth G.hom] in

theorem existsUnique_change (hv : ∀ i, IsTangent (v i)) (k : Matrix (Fin n) (Fin n) R) (hk : IsUnit k.det)
    {w : epsR R ⟶ G} (h : ∃! cf : Fin n → R, IsLieComb cf v w) :
    ∃! cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w := by
  have key : ∀ cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w ↔ IsLieComb (cf ᵥ* k) v w := fun cf => by
    rw [Chart.isLieComb_iff, Chart.isLieComb_iff, vecMul_eq_sum]
    exact Eq.congr_right (prodPts_prodPts hv cf fun i => k i)
  obtain ⟨d, hd, hu⟩ := h
  refine ⟨d ᵥ* k⁻¹, (key _).2 ?_, fun cf hcf => ?_⟩
  · rwa [vecMul_vecMul, nonsing_inv_mul _ hk, vecMul_one]
  · rw [← hu _ ((key _).1 hcf), vecMul_vecMul, mul_nonsing_inv _ hk, vecMul_one]

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem arcBasis_change (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)
    (hk : ∀ τ, IsUnit (k τ).det) (he : ∀ τ i, GtComb (k τ i) (e τ) (e' τ i)) :
    ArcBasis W ρ e' ∧ ∀ τ i, GtTanR (e' τ i) := by
  obtain ⟨v, hi, hb⟩ := h
  have := W.t.semi.smooth
  let k' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (PowerSeries A) :=
    fun τ => (k τ).map (PowerSeries.C (R := A))
  have hk' : ∀ τ, IsUnit (k' τ).det := fun τ => by
    have := (hk τ).map (PowerSeries.C (R := A))
    rwa [RingHom.map_det] at this
  have ht : ∀ τ i, IsTangent (v τ i) := fun τ i => ((hb τ).1 i).1
  have img : ∀ τ i, LieImg W (e' τ i) (prodPts (k' τ i) (v τ)) := fun τ i =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ _ (e τ) _ (v τ) _ (hi τ) (he τ i)).2
      ((Chart.isLieComb_iff _ _ _).2 rfl)
  refine ⟨⟨_, img, fun τ => ⟨fun i => ⟨isTangent_prodPts (ht τ) _, fun x => ?_⟩, fun w hw hw' => ?_⟩⟩, fun τ i =>
    ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W _).2 _ (img τ i)).2 (isTangent_prodPts (ht τ) _)⟩
  · exact eig_prodPts W.t.act (ht τ) x _ (fun j => ((hb τ).1 j).2 x) _
  · exact existsUnique_change (ht τ) (k' τ) (hk' τ) ((hb τ).2 w hw hw')

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ V := fun x n hn m h =>
    IntModelExists.mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

theorem exists_arcFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  intro E _ _ _ H Dw l Xo c V Y T io b a χ W ev z hP hb hχ hev hz hj
  letI := io.toAlgebra
  intro y hy
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let em : (E →+* ℂ) → (𝓞 E →+* V) := fun τ => (embK c τ).codRestrict V.toSubring fun x =>
    IntModelExists.mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)
  let ρ : (E →+* ℂ) → (𝓞 E →+* T.V) := fun τ => b.comp (em τ)
  have hρ : ∀ τ x, algebraMap T.V T.Fr (ρ τ x) = io (embK c τ x) := fun τ x => RingHom.congr_fun hb (em τ x)
  have hC : ((algebraMap T.V T.Fr).comp ev).comp (PowerSeries.C (R := T.V)) = algebraMap T.V T.Fr :=
    RingHom.ext fun x => congrArg (algebraMap T.V T.Fr) (hev x)
  have hm : Mono Y.j := by
    have : IsPreimmersion (spMap V.subtype) :=
      IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  obtain ⟨e₁, -, he₁⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ io hb.symm hρ
    (exists_values c V)
  obtain ⟨th, hth, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange a.D₀.P
  obtain ⟨y₁, hx₁, hy₁⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ e₁ th he₁ hth (Or.inr hP)
    T.Fr ((algebraMap T.V T.Fr).comp ev) z (by rw [hC]; exact IntModelExists.flat_of_injective _ hinj) hj
    (by rw [← Category.assoc, hy]; exact y.2)
    (fun τ x => ((RingHom.congr_fun hC (ρ τ x)).trans (hρ τ x)).symm)
  obtain ⟨g, s, hg⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun _ => 1) 1 y₁).2.2.2 y (hx₁.trans hy).symm
  obtain ⟨hgu, hsu⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr g s y₁).2.2.1 y hg
  choose k L hk hL0 hLd hkL using fun τ => iwasawa_lower (V := T.V) (g τ) (hgu τ).ne_zero
  choose e he using fun τ i => ConstLie.exists_gtComb (k τ i) (e₁ τ)
  obtain ⟨hbe, hte⟩ := arcBasis_change hG W he₁ k hk he
  obtain ⟨y₀, hy₀⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun τ => (k τ).map (algebraMap T.V T.Fr)) 1
    y₁).1 (fun τ => by
      have := (hk τ).map (algebraMap T.V T.Fr)
      rwa [RingHom.map_det] at this) isUnit_one
  obtain ⟨hcomp, -, -, hbor⟩ := frChg_calculus E H Dw l Xo c T.Fr
  refine ⟨ρ, e, th, y₀, fun i => match i with
    | none => hsu.unit
    | some p => Units.mk0 _ (hLd p.1 p.2), hbe, hth, hte, fun τ x => (hρ τ x).symm, ?_, ?_⟩
  · refine GlobalTheory.T.arcFrame_change_by_constants hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W e₁ e th th k 1 hth he (ThMul.refl th) T.Fr _ y₁ y₀
      hm hy₁ ?_
    rw [hC, map_one, map_one]
    exact hy₀
  · refine (hbor _ _ _).2 ⟨L, fun _ _ => rfl, hL0, (hcomp _ L _ _ y₁ y₀ y hy₀).2 ?_⟩
    rw [_root_.mul_one, ← funext hkL]
    exact hg

end GlobalTheory.ArcFrame
