import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyPBOfKeyOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrix
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]

def epsIso (R : Type) [CommRing R] : epsR R ≅ epsAt (𝟙 (Sp R)) :=
  Over.isoMk (Iso.refl _) (by simp [spMap])

def tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : epsR R ⟶ G := (epsIso R).hom ≫ M.pt x

theorem tanVec_left (M : LieModel G (𝟙 (Sp R)) E) (x : E) : (tanVec M x).left = (M.pt x).left := by
  simp [tanVec, epsIso]

theorem one_left : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  have h : (toUnit (Over.mk (𝟙 (Sp R)))).left = 𝟙 _ := by
    have := Over.w (toUnit (Over.mk (𝟙 (Sp R))))
    simpa using this
  rw [h]
  exact Category.id_comp _

theorem isTangent_tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : IsTangent (tanVec M x) := by
  have h := M.tan x
  unfold IsTangent
  rw [tanVec_left]
  exact h.trans one_left

theorem exists_tanVec (M : LieModel G (𝟙 (Sp R)) E) (w : epsR R ⟶ G) (hw : IsTangent w) : ∃ x, tanVec M x = w := by
  obtain ⟨x, hx⟩ := M.onto ((epsIso R).inv ≫ w) (by
    unfold IsTanAt
    have e : ((epsIso R).inv ≫ w).left = w.left := by simp [epsIso]
    rw [e]
    exact Eq.trans hw one_left.symm)
  exact ⟨x, by rw [tanVec, hx]; simp⟩

theorem tanVec_injective (M : LieModel G (𝟙 (Sp R)) E) : Function.Injective (tanVec M) := fun a b h =>
  M.inj (Over.OverMorphism.ext (by rw [← tanVec_left, ← tanVec_left, h]))

theorem prod_ofFn_tanVec (M : LieModel G (𝟙 (Sp R)) E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => tanVec M (f j)).prod = tanVec M (∑ j, f j)
  | 0, f => by simp [tanVec, M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_tanVec M, Fin.sum_univ_succ]
    simp only [tanVec, M.add, MonObj.comp_mul]

theorem isLieComb_tanVec_iff (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (c : Fin n → R) (x : E) :
    IsLieComb c (fun i => tanVec M (b i)) (tanVec M x) ↔ x = ∑ i, c i • b i := by
  have hs : ∀ i, (tanVec M (c i • b i)).left = spMap (epsScaleR (c i)) ≫ (tanVec M (b i)).left := fun i => by
    rw [tanVec_left, tanVec_left, M.smul]
    rfl
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tanVec M (c i • b i) := funext fun i =>
      Over.OverMorphism.ext ((hu i).trans (hs i).symm)
    rw [hu', prod_ofFn_tanVec M] at hw
    exact tanVec_injective M hw
  · rintro rfl
    exact ⟨fun i => tanVec M (c i • b i), hs, (prod_ofFn_tanVec M _).symm⟩

theorem isLieBasis_tanVec (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (hli : LinearIndependent R b)
    (hsp : Submodule.span R (Set.range b) = ⊤) : IsLieBasis (fun i => tanVec M (b i)) := by
  refine ⟨fun i => isTangent_tanVec M _, fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := exists_tanVec M w hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp ▸ Submodule.mem_top : x ∈ Submodule.span R (Set.range b))
  refine ⟨c, (isLieComb_tanVec_iff M b c x).2 hc.symm, fun c' h => ?_⟩
  have h' := (isLieComb_tanVec_iff M b c' x).1 h
  have h0 : ∑ i, (c' i - c i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h', hc, sub_self]
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

end Lie

section Sec

variable {X : Scheme.{0}}

theorem mem_basicOpen_map {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

theorem sameSec_ofPow {L : LB X} (s : Out.H0 L 1) : KeyDeg.SameSec s (GlobalTheory.GeneratorFrame.ofPow s) := fun _ => rfl

theorem nonzeroLocus_ofPow {L : LB X} (s : Out.H0 L 1) {y : X} (hy : y ∈ Out.nonzeroLocus s) :
    y ∈ Out.nonzeroLocus (GlobalTheory.GeneratorFrame.ofPow s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, rfl⟩ : ∃ i, k = fun _ => i := ⟨k 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have hU : y ∈ L.U i := GlobalTheory.GeneratorFrame.wchart_le' L (fun _ => i) (X.basicOpen_le _ hk)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (mem_basicOpen_map _ _ y).2 ⟨hU, hk⟩⟩

end Sec

section Main

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Chart.dualMapR f = dualMap f := by
  ext a <;> simp [Chart.dualMapR, dualMap]

theorem mem_basicOpen_appLE {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (f : Γ(X, U))
    {z : Y} (hz : z ∈ V) (hy : φ z ∈ X.basicOpen f) : z ∈ Y.basicOpen ((φ.appLE U V h).hom f) := by
  have e : (φ.appLE U V h).hom f = (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom f) := rfl
  rw [e]
  refine (mem_basicOpen_map h _ z).2 ⟨hz, ?_⟩
  rw [← Scheme.preimage_basicOpen]
  exact hy

theorem exists_keyIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  intro E _ _ _ H L _ _ D hg s e hs hli hsp
  have sm := D.tK.semi.smooth
  have gc := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hnv : KeyDeg.NonVan D.t.G.hom (GlobalTheory.GeneratorFrame.ofPow s) := fun b => by
    obtain ⟨y, hy, hy'⟩ := hs b
    exact ⟨y, hy, nonzeroLocus_ofPow s hy'⟩
  have hv := isLieBasis_tanVec D.MB e hli hsp
  obtain ⟨v', hv', hφ⟩ := GlobalTheory.exists_isLieBasis_baseChange (𝓞 L) L (algebraMap (𝓞 L) L) D.t.G D.tK.G D.m.φ D.m.cart
    D.t.semi.smooth D.g _ hv
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis D.tK.G hd
  have hdg : d = D.g := GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis D.m.cart hu hv'
  rw [hdg] at hd
  obtain ⟨hp, ha, hk⟩ := D.princ
  obtain ⟨w, hw, hr, -⟩ := D.m.lin
  have hw' := (isGen_iff w).1 hw
  obtain ⟨xth, hx⟩ := sec_pull_down hw' D.t.PP.isLB D.tK.PP.isLB (GlobalTheory.GeneratorFrame.ofPow s)
  have hcompat : ∀ (j : (D.t.PP.L.pull D.m.φ).ι) (i : D.tK.PP.L.ι)
      (h : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U (j PUnit.unit)),
      (D.m.φ.appLE _ _ h).hom ((GlobalTheory.GeneratorFrame.ofPow s).f (j PUnit.unit)) =
        (show Γ(D.tK.G.left, (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (xth.f i) := fun j i h => fn_ext fun y hy =>
    (gs_appLE D.m.φ _ _ h (𝟙 _) y hy _).trans ((hx _ (𝟙 _) y _ i (h hy) hy.2).trans
      (Eq.symm ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res (𝟙 _) y _ hy _)))))
  have hne : ∀ s₀ : Sp L, ∃ z : D.tK.G.left, D.tK.G.hom z = s₀ ∧ z ∈ Out.nonzeroLocus xth := fun s₀ => by
    obtain ⟨y, hy, hyn⟩ := hnv (spMap (algebraMap (𝓞 L) L) s₀)
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback D.m.cart.1 y s₀ hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hyn
    obtain ⟨i, hi⟩ := exists_chart D.tK.PP.isLB z
    have hU : D.m.φ z ∈ D.t.PP.L.U l := Scheme.basicOpen_le _ _ hl
    let j : PUnit → D.t.PP.L.ι := fun _ => l
    have hV : z ∈ (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i := ⟨mem_pull.2 hU, hi⟩
    have hle : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U l := fun _ hy => mem_pull.1 hy.1
    have h1 := mem_basicOpen_appLE D.m.φ hle _ hV hl
    have e := hcompat j i hle
    refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
    change z ∈ D.tK.G.left.basicOpen ((D.m.φ.appLE _ _ hle).hom _) at h1
    rw [e, Scheme.basicOpen_mul] at h1
    exact ((mem_basicOpen_map _ _ z).1 h1.2).2
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  refine ⟨KeyBadModel.keyInOf D.tK xth D.g hg v' hv' ⟨inferInstance, sm, hp, gc⟩ hd
    (fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩) ha hk hne, GlobalTheory.GeneratorFrame.ofPow s, rfl,
    fun i => tanVec D.MB (e i), sameSec_ofPow s, hnv, ?_, hv, fun i => tanVec_left _ _⟩
  have he : eSec D.tK.G ≫ D.m.φ = spMap (algebraMap (𝓞 L) L) ≫ eSec D.t.G := by
    have := D.m.cm.e_comm
    rwa [D.m.base] at this
  have hrig : ∀ (e' : (𝟙_ (Over (Sp L))).left ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left) (he' : eSec D.tK.G ≫ D.m.φ = e' ≫ eSec D.t.G),
      e' = D.m.cm.e → rigPullOf D.m.φ e' he' D.t.PP.L D.t.PP.rig = D.m.cm.rigPull D.t.PP.L D.t.PP.rig := by
    rintro _ _ rfl
    rfl
  refine ⟨D.m.φ, he, w, D.m.cart, hw, ?_, hcompat, fun i => ?_⟩
  · have h2 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.tK.G) (fun _ => 1)) D.tK.PP.rig
        (rigPullOf D.m.φ (spMap (algebraMap (𝓞 L) L)) he D.t.PP.L D.t.PP.rig) := by
      rw [hrig _ he D.m.base.symm]
      exact hr
    exact h2
  · exact (hφ i).trans (by rw [dualMapR_eq])

end Main

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum
