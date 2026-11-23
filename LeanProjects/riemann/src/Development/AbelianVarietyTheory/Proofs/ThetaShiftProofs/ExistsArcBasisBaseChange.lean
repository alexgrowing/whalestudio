import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPidStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantEigenbasisIndependentOfWitnessStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.IntModelExists

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem maps_self {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {w : LB.Iso L (L.pull F)}
    (hw : w = isoPullId (idIso L) hF) {h : Y ⟶ Y} (hh : h = 𝟙 Y) {K I : Type} [Fintype K] (φ : I → K → (Y ⟶ X))
    (ε : K → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (ht : ∀ i, (t i).IsGen) {i i' : I} (hi : i' = i) :
    ∃ hψ : ∀ k, φ i k ≫ F = h ≫ φ i' k,
      LB.Gen.Maps (LB.linCombIso w _ ε) (t i) (Out.GeneratorPullback.pullAlong L F h _ ε _ hψ (t i')) := by
  subst hi hw hh
  have hψ : ∀ k, φ i' k ≫ F = 𝟙 Y ≫ φ i' k := fun k => by rw [hF, Category.comp_id, Category.id_comp]
  exact ⟨hψ, (maps_iff _ _ (φ i') ε (t i') (t i') (𝟙 Y) _ (Out.GeneratorPullback.pullAlong_le L F _ _ _ hψ) (fun _ => rfl)).2
    (NoTorus.pmaps_id hF _ _ (ht i'))⟩

open scoped CategoryTheory.Obj in

theorem exists_self {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (h : ∀ χ, PsiUnitOn D χ Set.univ) :
    ∃ p : Out.IsPullDeg (RingHom.id R) D D, (∀ q : D.P.A.left ⟶ D.P.A.left, q ≫ prj p = prj p ≫ q) ∧
      (∀ y, p.xe y = y) ∧ ∀ ν, LetBC p ν ν := by
  have : IsMonHom (Iso.refl D.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.P.A))
  have gp : IsGrpPullback D.P.A D.P.A (Out.specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (Out.specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.P.A.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D h
  obtain ⟨p, h₁, h₂, h₃⟩ := UnifUniq.exists_isPullDeg_id D D ⊤ trivial ψW e me
    (isoPullId (idIso D.P.L) hF') ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.xK x) (fun _ => -1) (D.psi_gen x))
  subst h₁
  have hx : ∀ y, p.xe y = y := fun y => by rw [h₃]; rfl
  have hp : prj p = 𝟙 _ := hF'
  have hs : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [dualMap_id]; exact Spec.map_id (CommRingCat.of (DualNumber R))
  refine ⟨p, fun q => by rw [hp, Category.comp_id, Category.id_comp], hx, fun ν => ⟨?_, fun χ => ?_⟩⟩
  · exact ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _)).trans
      ((congrArg (· ≫ ν.b.left) hs).trans (Category.id_comp _)).symm
  · exact maps_self hF' (eq_of_heq h₂) hs (Out.DegPre.gtφT D (epsR R) ν.b) _ ν.s ν.isGen (hx χ)

theorem isLieComb_trans {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d n : ℕ}
    {v : Fin d → (epsR S ⟶ G)} {u : Fin n → (epsR S ⟶ G)} {w : epsR S ⟶ G} (hv : ∀ i, IsTangent (v i))
    (hu : ∀ i, IsTangent (u i)) (hw : IsTangent w) {U : Fin n → Fin d → S} (hU : ∀ i, IsLieComb (U i) v (u i))
    {a : Fin n → S} (ha : IsLieComb a u w) : IsLieComb (fun j => ∑ i, a i * U i j) v w := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  have tu := fun i => (Chart.isTan_iff _).2 (hu i)
  have tw := (Chart.isTan_iff _).2 hw
  rw [Chart.comb_iff_coord hy _ tv tw, (Chart.comb_iff_coord hy _ tu tw).1 ha]
  simp only [(Chart.comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem isLieComb_single {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d : ℕ}
    {v : Fin d → (epsR S ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin d) : IsLieComb (Pi.single j 1) v (v j) := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  rw [Chart.comb_iff_coord hy _ tv (tv j)]
  simp [Pi.single_apply]

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hf
  show Module.Flat A B
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_matrix (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h₁ : ArcBasis W ρ e₁) (h₂ : ArcBasis W ρ e₂) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A,
      (∀ τ, (g τ).det ≠ 0) ∧ ∀ τ k, GtComb (g τ k) (e₁ τ) (e₂ τ k) := by
  have key := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c O β Y A b a χ W ρ e₁ h₁).2.2
  obtain ⟨v₁, i₁, b₁⟩ := h₁
  obtain ⟨v₂, i₂, b₂⟩ := h₂
  choose g hg using fun τ k => (key τ (e₂ τ k) (v₂ τ k)
    (((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e₂ τ k)).2 _ (i₂ τ k)).2 ((b₂ τ).1 k).1) (i₂ τ k)
    ((b₂ τ).1 k).2).exists
  refine ⟨fun τ => Matrix.of (g τ), fun τ => ?_, hg⟩
  have := W.t.semi.smooth
  have hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := A) (g τ k i)) (v₁ τ) (v₂ τ k) := fun k =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e₁ τ) (e₂ τ k) (v₁ τ) (v₂ τ k) (i₁ τ) (hg τ k)).1 (i₂ τ k)
  choose h hh using fun j => ((b₂ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).exists
  have hm : Matrix.of h * (PowerSeries.C (R := A)).mapMatrix (Matrix.of (g τ)) = 1 := by
    ext1 j k
    have := congrFun (((b₁ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).unique
      (isLieComb_trans (fun i => ((b₁ τ).1 i).1) (fun i => ((b₂ τ).1 i).1) ((b₁ τ).1 j).1 hU (hh j))
      (isLieComb_single (fun i => ((b₁ τ).1 i).1) j)) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  intro h0
  have := congrArg Matrix.det hm
  rw [Matrix.det_mul, ← RingHom.map_det, h0, map_zero, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem exists_arcBasis_baseChange (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A A' : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsPrincipalIdealRing A'] {b : O →+* A} {b' : O →+* A'}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β A' b'} {f : A →+* A'} (hf : Function.Injective f)
    {p : Out.IsPullDeg f a.D₀ a'.D₀} (hp : InBC f a a' p) {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) :
    ∃ (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ))
      (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')),
      (∀ τ k, LetBC p (e τ k) (e' τ k)) ∧ ArcBasis W' (fun τ => f.comp (ρ τ)) e' := by
  obtain ⟨hW, hν, -⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c O β Y A A' b a f hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  choose e' he' using fun τ k => (hν (e τ k)).exists
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.T.tangentVectors_thetaSection_arcWitness_baseChange hL hL₂ E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hp hW'
  have hfl : ((PowerSeries.map f).comp (PowerSeries.C (R := A))).Flat := by
    refine flat_of_injective _ fun x y hxy => hf (PowerSeries.C_injective ?_)
    simpa using hxy
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e h (PowerSeries A')
    (PowerSeries.map f) hfl W'.t m
  refine ⟨W', e', he', u, fun τ k => ?_, fun τ => ?_⟩
  · obtain ⟨v, hv, huv⟩ := hu τ k
    exact hm _ _ v _ (he' τ k) hv huv
  · simpa only [PowerSeries.map_C, RingHom.comp_apply] using hb τ

theorem mem_of_isIntegral {F : Type} [Field F] (V : ValuationSubring F) {x : F} (h : IsIntegral ℤ x) : x ∈ V := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 h.tower_top
  exact hy ▸ y.2

theorem exists_values (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ c.V W := fun x n hn m h =>
    mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

def embV (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c τ).codRestrict (c.V W).toSubring fun x =>
    mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)

end GlobalTheory.IntModelExists
