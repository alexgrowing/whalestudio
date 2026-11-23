import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetLineTrivialOfToroidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUnit

open GlobalTheory.FlagMod (FlagCover Frames ev ev_res ev_spMap ext_ev tau tau_le spMap_ev ev_tau le_preimage_comp le_preimage_mono
  vec tanPull tanPull_actR tanPull_vec tan_ext_left ev_pull_g)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt IsCombAt IsFrame chi compactOf toF)
open GlobalTheory.DetLine (FrY RuleY SecY NzY)

section Glue

variable {W : Scheme.{0}}

theorem exists_ev_eq (V : W.Opens) (val : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ W), ⊤ ≤ z ⁻¹ᵁ V → R)
    (nat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (z : Sp R ⟶ W) (z' : Sp R' ⟶ W) hz hz',
      spMap φ ≫ z = z' → val R' z' hz' = φ (val R z hz)) :
    ∃ f : Γ(W, V), ∀ (R : Type) [CommRing R] (z : Sp R ⟶ W) hz, ev z V hz f = val R z hz := by
  let A := {A : W.affineOpens // A.1 ≤ V}
  let s : ∀ a : A, Γ(W, a.1.1) := fun a => val _ (tau a.1.2) (tau_le a.1.2 a.2)
  have hs : ∀ (a : A) (R : Type) [CommRing R] (z : Sp R ⟶ W) (ha : ⊤ ≤ z ⁻¹ᵁ a.1.1) hz,
      ev z _ ha (s a) = val R z hz := fun a R _ z ha hz => (nat _ _ _ _ z _ hz (spMap_ev z a.1.2 ha)).symm
  have hc : ∀ y ∈ V, ∃ a : A, y ∈ a.1.1 := fun y hy => by
    obtain ⟨_, ⟨B, hB, rfl⟩, hy', hB'⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hy V.2
    exact ⟨⟨⟨B, hB⟩, hB'⟩, hy'⟩
  obtain ⟨f, hf, -⟩ := DVR.sec_glue V (fun a : A => a.1.1) (fun a => a.2) (fun y hy => Opens.mem_iSup.2 (hc y hy)) s
    fun a b => ext_ev fun R _ z hz => by
      have ha := le_preimage_mono inf_le_left hz
      have hb := le_preimage_mono inf_le_right hz
      exact ((ev_res z _ hz ha _).trans (hs a R z ha (le_preimage_mono a.2 ha))).trans
        ((ev_res z _ hz hb _).trans (hs b R z hb _)).symm
  refine ⟨f, fun R _ z hz => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let φ := algebraMap R (Localization.AtPrime J)
  have hz' := le_preimage_comp (spMap φ) hz
  obtain ⟨a, ha⟩ := hc _ (hz' (Set.mem_univ (IsLocalRing.closedPoint (Localization.AtPrime J))))
  have ha' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ a.1.1 := ((IsLocalRing.closed_point_mem_iff (U := (spMap φ ≫ z) ⁻¹ᵁ a.1.1)).1 ha).ge
  have e := hs a _ _ ha' hz'
  rw [← hf a, nat _ _ φ z _ hz hz' rfl] at e
  have e' := (ev_res _ a.2 ha' hz' f).symm.trans e
  rw [ev_spMap φ z V hz] at e'
  change φ _ = 0
  rw [map_sub, sub_eq_zero]
  exact e'

theorem isGenerated_of_values {L : LB W} (hL : L.IsLB)
    (val : ∀ (k : L.ι) (R : Type) [CommRing R] (z : Sp R ⟶ W), ⊤ ≤ z ⁻¹ᵁ L.U k → Rˣ)
    (nat : ∀ (k : L.ι) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (z : Sp R ⟶ W) (z' : Sp R' ⟶ W) hz hz',
      spMap φ ≫ z = z' → val k R' z' hz' = Units.map φ.toMonoidHom (val k R z hz))
    (chg : ∀ (k k' : L.ι) (R : Type) [CommRing R] (z : Sp R ⟶ W) hz hz' (hh : ⊤ ≤ z ⁻¹ᵁ (L.U k ⊓ L.U k')),
      (val k R z hz).val = ev z _ hh (L.g k k').val * (val k' R z hz').val) : IsGenerated L := by
  choose f hf using fun k => exists_ev_eq (L.U k) (fun R _ z hz => (val k R z hz).val)
    fun R R' _ _ φ z z' hz hz' e => by rw [nat k R R' φ z z' hz hz' e]; rfl
  choose f' hf' using fun k => exists_ev_eq (L.U k) (fun R _ z hz => (val k R z hz)⁻¹.val)
    fun R R' _ _ φ z z' hz hz' e => by rw [nat k R R' φ z z' hz hz' e]; rfl
  have h1 : ∀ k, f k * f' k = 1 := fun k => ext_ev fun R _ z hz => by
    rw [map_mul, hf, hf', map_one, Units.mul_inv]
  refine isGenerated_of_gen hL ⟨fun k => ⟨f k, f' k, h1 k, (mul_comm _ _).trans (h1 k)⟩⟩ fun k k' =>
    Units.ext (ext_ev fun R _ z hz => ?_)
  have ha := le_preimage_mono inf_le_left hz
  have hb := le_preimage_mono inf_le_right hz
  rw [Units.val_mul, map_mul]
  exact ((ev_res z _ hz ha _).trans (hf k R z ha)).trans ((chg k k' R z ha hb hz).trans
    (congrArg (_ * ·) ((ev_res z _ hz hb _).trans (hf k' R z hb)).symm))

end Glue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem existsUnique_sum_vecAt {R : Type} [CommRing R] (j : c.F →+* R) (z : Sp R ⟶ X.YY) (k : X.F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hj : z ≫ X.π ≫ Y.s = spMap j) (σ : E →+* ℂ) (w : TanM (z ≫ X.π) Y.t.G)
    (hw : ∀ a, actR Y.t.act a w = j (embK c σ a) • w) :
    ∃! a : Fin (Dw.mult σ) → R, w = ∑ i, a i • X.F.vecAt k z hz rfl σ i := by
  obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (z ≫ X.π) (X.F.inM hz rfl)).surjective w
  obtain ⟨P, hP⟩ := X.F.uAt_split k z hz σ
  have key : cv = (X.F.uAt k z hz σ).mulVec (P.mulVec cv) := funext fun m => by
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun J hJ => ?_
    let φ := algebraMap R (Localization.AtPrime J)
    have hz' := le_preimage_comp (spMap φ) hz
    have e : spMap φ ≫ z ≫ X.π = (spMap φ ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
    obtain ⟨g, hg⟩ := VarFlag.framesExist_flagCover X _ (φ.comp j) (spMap φ ≫ z) k hz'
      (by rw [Category.assoc, hj, spMap_comp'])
    obtain ⟨a, ha, -⟩ := g.existsUnique_sum σ (tanPull φ e (vec _ _ (X.F.inM hz rfl) cv)) fun b => by
      rw [← tanPull_actR, hw, map_smulₛₗ]; rfl
    have hv : ∀ i, g.vec σ i = X.F.vecAt k _ hz' rfl σ i := fun i => tan_ext_left (hg σ i)
    simp only [hv] at ha
    rw [Frames.sum_vecAt, tanPull_vec _ φ e _ (X.F.inM hz' rfl), X.F.uAt_spMap k φ z hz] at ha
    have h1 := (vec _ _ _).injective ha
    have hm : ∀ {n n' : ℕ} (A : Matrix (Fin n) (Fin n') R) (b : Fin n' → R),
        (A.map φ).mulVec (fun j => φ (b j)) = fun j => φ (A.mulVec b j) := fun A b =>
      funext fun j => (RingHom.map_mulVec φ A b j).symm
    have h2 : a = fun j => φ (P.mulVec cv j) := by
      rw [← hm, h1, Matrix.mulVec_mulVec, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    rw [h2, hm] at h1
    change φ _ = 0
    rw [map_sub, sub_eq_zero]
    exact congrFun h1 m
  have hex : vec (X.F.M k).toMChart (z ≫ X.π) (X.F.inM hz rfl) cv = ∑ i, P.mulVec cv i • X.F.vecAt k z hz rfl σ i := by
    rw [Frames.sum_vecAt, ← key]
  exact ⟨_, hex, fun a ha => funext fun i =>
    (Fintype.linearIndependent_iffₛ.1 (X.F.linearIndependent_vecAt k z hz rfl σ)) _ _ (ha.symm.trans hex) i⟩

def frm {R : Type} [CommRing R] (k : X.F.J) (z : Sp R ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {x : Sp R ⟶ Y.X}
    (hx : z ≫ X.π = x) (σ : E →+* ℂ) {n : ℕ} (h : n = Dw.mult σ) (i : Fin n) : epsAt x ⟶ Y.t.G :=
  tv (X.F.vecAt k z hz hx σ (Fin.cast h i))

theorem isEigBasisAt_frm {R : Type} [CommRing R] (j : c.F →+* R) (k : X.F.J) (z : Sp R ⟶ X.YY)
    (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {x : Sp R ⟶ Y.X} (hx : z ≫ X.π = x) (hj : x ≫ Y.s = spMap j) (σ : E →+* ℂ) {n : ℕ}
    (h : n = Dw.mult σ) : IsEigBasisAt Y.t.act x (IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c σ j) (frm X k z hz hx σ h) := by
  subst hx h
  rw [Category.assoc] at hj
  let g : ShFam.EigFrame Y j (z ≫ X.π) := ShFam.EigFrame.ofVec (fun σ i => X.F.vecAt k z hz rfl σ i)
    (fun σ i a => VarFlag.actR_vecAt X j z k hz hj σ i a) fun σ w hw => existsUnique_sum_vecAt X j z k hz hj σ w hw
  exact (DetLine.EigParts.basis_iff _ _).2 ⟨g.tan σ, g.eig σ, g.basis σ⟩

theorem isCombAt_frm {R : Type} [CommRing R] (k k' : X.F.J) (z : Sp R ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ X.F.U k') (hh : ⊤ ≤ z ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) {x : Sp R ⟶ Y.X} (hx : z ≫ X.π = x)
    (σ : E →+* ℂ) {n : ℕ} (h : n = Dw.mult σ) : ∃ M : Matrix (Fin n) (Fin n) R,
      M.det = (∏ i, X.F.TAt k k' z hh (some ⟨σ, i⟩)).val ∧
      ∀ i, IsCombAt x (M i) (frm X k z hz hx σ h) (frm X k' z hz' hx σ h i) := by
  subst h
  refine ⟨((X.F.B k k' σ).map (ev z _ hh)).transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_of_isUpperTriangular (X.F.B_map_tri k k' σ _), Units.coe_prod]
    rfl
  · exact (DetLine.EigParts.comb_iff _ _ _).2 ((LieMet.isComb_iff _ _ _).2 (X.F.vecAt_eq_sum k k' z hz hz' hh hx σ i))

theorem frm_left {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (k : X.F.J) (z : Sp R ⟶ X.YY)
    (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {z' : Sp R' ⟶ X.YY} (e : spMap φ ≫ z = z') (hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k)
    {x : Sp R ⟶ Y.X} (hx : z ≫ X.π = x) {x' : Sp R' ⟶ Y.X} (hx' : z' ≫ X.π = x') (σ : E →+* ℂ) {n : ℕ}
    (h : n = Dw.mult σ) (i : Fin n) :
    (frm X k z' hz' hx' σ h i).left = spMap (Chart.dualMapR φ) ≫ (frm X k z hz hx σ h i).left := by
  subst e
  have e' : spMap φ ≫ x = x' := by rw [← hx, ← hx', Category.assoc]
  exact congrArg (fun v => (tv v).left) (X.F.tanPull_vecAt k φ z hz hz' hx hx' e' σ (Fin.cast h i)).symm

open Classical in

theorem exOf_unitWt (τ : Psi H) (a : ℤ) : AllWt.exOf Dw (NefWt.unitWt τ a) 0 =
    fun ix => ix.elim 0 fun p => if p.1 = τ.1 then a else if p.1 = conjEmb τ.1 then -a else 0 := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · have h2 : τ'.1 ≠ conjEmb τ.1 := fun h => AllWt.conj_not_mem τ (h ▸ τ'.2)
    simp [NefWt.unitWt, h2, Subtype.ext_iff]
  · have h1 : conjEmb τ'.1 ≠ τ.1 := fun h => AllWt.conj_not_mem τ' (h ▸ τ.2)
    by_cases e : τ' = τ
    · subst e
      simp [NefWt.unitWt, h1]
    · have hc : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← AllWt.conjEmb_conjEmb τ'.1, h, AllWt.conjEmb_conjEmb]))
      simp [NefWt.unitWt, e, h1, hc]

open Classical in
theorem prod_unitWt {R : Type} [CommRing R] (τ : Psi H) (a : ℤ) (t : Ix Dw → Rˣ) :
    ∏ ix, t ix ^ (-AllWt.exOf Dw (NefWt.unitWt τ a) 0 ix) =
      (∏ i, t (some ⟨τ.1, i⟩)) ^ (-a) * (∏ i, t (some ⟨conjEmb τ.1, i⟩)) ^ a := by
  have h1 : conjEmb τ.1 ≠ τ.1 := fun h => AllWt.conj_not_mem τ (h.symm ▸ τ.2)
  rw [exOf_unitWt, Fintype.prod_option, Fintype.prod_sigma, Fintype.prod_eq_mul τ.1 (conjEmb τ.1) h1.symm
    fun σ h => by simp [h.1, h.2]]
  simp [h1, Finset.prod_zpow]

theorem isGenerated_pull {W : Scheme.{0}} (ι : W ⟶ X.YY) (g : W ⟶ gen Y) (hg : ι ≫ X.π = g ≫ genι Y)
    {V : Set (gen Y)} (hV : Set.range g ⊆ V) (τ : Psi H) {s : RuleY Y} (hs : SecY Y V τ.1 s) (hn : NzY Y V τ.1 s)
    (a : ℤ) : IsGenerated ((X.F.LL (AllWt.exOf Dw (NefWt.unitWt τ a) 0)).pull ι) := by
  have hp := (FlagMod.mult_of_mem (Dw := Dw) τ).symm
  have hq := (FlagMod.mult_conj (Dw := Dw) τ).symm
  have hx : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ W), (z ≫ ι) ≫ X.π = (z ≫ g) ≫ genι Y := fun z => by
    rw [Category.assoc, hg, Category.assoc]
  have hk : ∀ {R : Type} [CommRing R] {z : Sp R ⟶ W} {k : PUnit → X.F.J},
      ⊤ ≤ z ⁻¹ᵁ ((X.F.LL (AllWt.exOf Dw (NefWt.unitWt τ a) 0)).pull ι).U k → ⊤ ≤ (z ≫ ι) ⁻¹ᵁ X.F.U (k PUnit.unit) :=
    fun hz p hp => mem_pull.1 (hz hp)
  have fr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ W), ∃ j : c.F →+* R, ∀ k hz,
      FrY Y V τ.1 j (z ≫ g) (frm X k (z ≫ ι) hz (hx z) τ.1 hp) (frm X k (z ≫ ι) hz (hx z) (conjEmb τ.1) hq) := by
    intro R _ z
    obtain ⟨j, hj⟩ : ∃ j : c.F →+* R, spMap j = (z ≫ g) ≫ genStr Y := ⟨_, FlagMod.spMap_ev_top _⟩
    have hj' : ((z ≫ g) ≫ genι Y) ≫ Y.s = spMap j := by rw [hj, VarFlag.genStr_eq, Category.assoc (z ≫ g)]
    refine ⟨j, fun k hz => ⟨hj.symm, ?_, isEigBasisAt_frm X j k _ hz _ hj' _ hp, ?_⟩⟩
    · rintro _ ⟨p, rfl⟩
      exact hV ⟨z p, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rw [DetLine.comp_chi_bar]
      exact isEigBasisAt_frm X j k _ hz _ hj' _ hq
  choose j hj using @fr
  refine isGenerated_of_values (LB.isLB_pull (X.F.isLB_LL _) ι)
    (fun k R _ z hz => (hn R _ _ _ _ (hj z (k PUnit.unit) (hk hz))).unit ^ (-a))
    (fun k R R' _ _ φ z z' hz hz' e => ?_) fun k k' R _ z hz hz' hh => ?_
  · rw [map_zpow]
    congr 1
    have e' : spMap φ ≫ z ≫ ι = z' ≫ ι := by rw [← e, Category.assoc]
    exact Units.ext (DetRatio.sec_pull hs φ (hj z _ (hk hz)) (hj z' _ (hk hz')) (by rw [← e, Category.assoc])
      (frm_left X φ _ _ _ e' _ _ _ _ hp) (frm_left X φ _ _ _ e' _ _ _ _ hq))
  · have hh' := FlagMod.le_preimage_inf (hk hz) (hk hz')
    obtain ⟨M, hM, hM'⟩ := isCombAt_frm X _ _ _ (hk hz) (hk hz') hh' (hx z) τ.1 hp
    obtain ⟨N, hN, hN'⟩ := isCombAt_frm X _ _ _ (hk hz) (hk hz') hh' (hx z) (conjEmb τ.1) hq
    have e := hs.2 R _ _ _ _ _ _ M N (hj z _ (hk hz)) (hj z _ (hk hz')) hM' hN'
    rw [hM, hN] at e
    refine Eq.trans ?_ (congrArg (· * _) ((ev_pull_g (X.F.LL _) ι k k' z hh hh').trans (X.F.ev_LL_g _ _ _ _ hh')).symm)
    rw [prod_unitWt, ← Units.val_mul]
    congr 1
    have e₁ : (hn R _ _ _ _ (hj z (k PUnit.unit) (hk hz))).unit = (∏ i, X.F.TAt _ _ _ hh' (some ⟨conjEmb τ.1, i⟩))⁻¹ *
        ((∏ i, X.F.TAt _ _ _ hh' (some ⟨τ.1, i⟩)) * (hn R _ _ _ _ (hj z (k' PUnit.unit) (hk hz'))).unit) :=
      eq_inv_mul_iff_mul_eq.2 (Units.ext e)
    rw [e₁, mul_zpow, mul_zpow, inv_zpow', neg_neg, mul_left_comm, mul_assoc]

theorem geometricallyConnected_comp (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed Xo c) {U : (Xo.XF c).Opens}
    (hU : (U : Set (Xo.XF c)) = Z.1) : GeometricallyConnected (U.ι ≫ toF Xo c) := by
  obtain ⟨B, j, hB, -⟩ := GenFibreComp.exists_vars E H Dw l Xo c c.F (RingHom.id c.F) TF.Y c.F (RingEquiv.refl _) hF
    (VarFlag.smooth_gen TF.smooth)
  obtain ⟨h1, -, h3, h4⟩ := hB Z
  have := TF.Y.jQ_open
  have hr : Set.range (U.ι ≫ TF.Y.jQ) ⊆ Set.range (j Z) := by
    rintro _ ⟨u, rfl⟩
    exact h4 _ (hU.le u.2)
  let f := IsOpenImmersion.lift (j Z) (U.ι ≫ TF.Y.jQ) hr
  have hf : f ≫ j Z = U.ι ≫ TF.Y.jQ := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (f ≫ j Z) := by rw [hf]; infer_instance
  have : IsOpenImmersion f := IsOpenImmersion.of_comp f (j Z)
  have hid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  rw [hid, Category.comp_id] at h3
  have e : f ≫ (B Z).str = U.ι ≫ toF Xo c := by
    rw [← h3, ← Category.assoc, hf, Category.assoc, TF.Y.jQ_over]
  obtain ⟨u, hu⟩ := Z.2.1.nonempty
  have : Surjective (f ≫ (B Z).str) := ⟨fun p => ⟨⟨u, hU.ge hu⟩, Subsingleton.elim _ _⟩⟩
  have h : GeometricallyIrreducible (f ≫ (B Z).str) := inferInstance
  rw [e] at h
  exact ⟨fun K _ y _ _ _ hp => have := h.1 y _ _ hp; inferInstance⟩

theorem isGenerated_unitWt (hT : Published.ToroidalCompactification) (TF : TorFlag Xo c) (Z : Comp Xo c)
    (hF : FnAlgClosed Xo c) (τ : Psi H) (a : ℤ) : IsGenerated (L₀ TF.X Z (NefWt.unitWt τ a)) := by
  have hZ := TrivOrderTieCompare.isClopen_comp Z
  let U : (Xo.XF c).Opens := ⟨Z.1, hZ.isOpen⟩
  obtain ⟨-, s₀, -, -, -, -, h⟩ := DetLine.detLineTrivial_of_toroidal hT E H Dw l Xo c U hZ.isClosed
    (geometricallyConnected_comp TF Z hF rfl) τ.1 τ.2
  have : GlobalTheory.IsNormalScheme TF.Y.X := GlobalTheory.IsNormalScheme.of_pred TF.Y.normal
  have : GlobalTheory.IsNormalScheme (gen TF.Y) := GlobalTheory.IsNormalScheme.of_isOpenImmersion (genι TF.Y)
  obtain ⟨s, hs, hn, -⟩ := h c.F (RingHom.id c.F) TF.Y (GlobalTheory.IsNormalScheme.pred (gen TF.Y))
  have hg : inc₀ TF.X Z ≫ TF.X.π = (inc₀ TF.X Z ≫ TF.X.π ≫ inv (genι TF.Y)) ≫ genι TF.Y := by simp
  refine isGenerated_pull TF.X _ _ hg ?_ τ hs hn a
  rintro _ ⟨y, rfl⟩
  have hy : (inc₀ TF.X Z ≫ TF.X.π) y ∈ closure (TF.Y.j '' Z.1) := barComp_subset_closure Z y.2
  rw [hg, Scheme.Hom.comp_apply] at hy
  rw [compactOf, (genι TF.Y).isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_image]
  exact hy

theorem isNef_unitWt : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF τ
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hp := (VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  exact ⟨(isGenerated_unitWt hP.p1 TF Z hF τ 1).isNef_of_isProjOver hp,
    (isGenerated_unitWt hP.p1 TF Z hF τ (-1)).isNef_of_isProjOver hp⟩

end GlobalTheory.NefUnit
