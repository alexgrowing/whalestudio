import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.ExFr

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem one_eq : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  have := m.cm.e_comm
  rw [m.base] at this
  exact this

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_eq m).symm
    · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw, a, ← spMap_comp]
      have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h).trans (one_eq m)

theorem scale_over (s : S) : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, scale_over]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem exists_lift {T : Over (Sp S)} (v : T.left ⟶ Xo.univ.t.G.left) (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) :
    ∃ w : T ⟶ t'.G, w.left ≫ m.φ = v :=
  ⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem push_prod {n : ℕ} (u : Fin n → (epsR S ⟶ t'.G)) :
    ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (epsR S) (u i)).prod).left := by
  have := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))
    have e : u = fun i => pushHom m.cart (epsR S) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
    · apply m.cart.1.hom_ext
      · rw [Category.assoc]; exact (hu' i).trans (hu i)
      · have hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w (v i)
        rw [Over.w, Category.assoc, hv, scale_over]; rfl
    · apply m.cart.1.hom_ext
      · rw [e] at hw
        exact hw.symm.trans (push_prod m u').symm
      · rw [Over.w, Over.w]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu, Category.assoc]; rfl

end GlobalTheory.ArcQ.ExFr

open GlobalTheory.ArcQ.ExFr in

theorem GlobalTheory.ArcQ.exists_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (z : Sp S ⟶ Xo.XF c), (ι.comp (PowerSeries.C (R := A))).Flat → z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ ≫ Xo.s = sOf c S → (∀ τ x, algebraMap c.F S (embK c τ x) = ι (PowerSeries.C (R := A) (ρ τ x))) → ∃ y : FrPt Xo c S, y.x = z ≫ pullback.fst _ _ ∧ IsArcFr W e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e th hB hth hA S _ _ ι z hfl hz hs hρ
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m1, hm1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap ι ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap ι), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ hz n
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.ArcQ.arcBasis_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB S ι hfl t' m2
  obtain ⟨⟨θ, hθ, -⟩, -⟩ := GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth
  have hnz := fun g => (GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ hA g).2
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2).1 g2) W.t.PP.isLB t'.PP.isLB θ
  have hI2 : IsoMaps w2 σ' (thfPull W.t.PP.L m2.φ θ) := fun (i : PUnit → W.t.PP.L.ι) k => fn_ext fun y hy =>
    (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      ((hσ' _ (𝟙 _) y (i PUnit.unit) k (mem_pull.1 hy.1) hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))
  have nz := GlobalTheory.SectionBaseChange.fibre_nonzero_of_pull t'.PP.isLB hσ' m2.cart.1 hnz
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have hLB : LBIso t'.PP.L (Xo.univ.t.PP.L.pull m1.cm.F) := by
    obtain ⟨w, hw, -⟩ := m1.lin
    exact ⟨w, hw⟩
  have hgen := GlobalTheory.SectionBaseChange.generates hL.secBaseChange (GlobalTheory.Obj.toPolAV Xo.univ) m1.cart.1 t'.PP.isLB hLB σ' nz
  obtain ⟨s, w1, s1, r1, hI1, hg, hsgen⟩ := frame_of_gen Xo _ t' m1 σ' hgen
  have eig : ∀ (τ : E →+* ℂ) (w : epsR S ⟶ t'.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← hρ]; exact eig_iff m1 w x _
  refine ⟨⟨z ≫ pullback.fst _ _, (Category.assoc _ _ _).trans hs, fun τ k => (u τ k).left ≫ m1.φ,
    fun τ k => (tan_iff m1 _).2 ((hu2 τ).1 k).1, fun τ k => (eig τ _).2 ((hu2 τ).1 k).2, fun τ w hw hw' => ?_,
    s, hsgen⟩, rfl, z, t', m1, m2, m.φ, hz, rfl, m.cart.1.w, hm1.symm, hn.symm.trans hm2, fun τ k => ?_,
    θ, w1, w2, σ', s1, _, hθ, r1, ⟨g2, r2⟩, hI1, hI2, fun _ _ => rfl, hg⟩
  · obtain ⟨w', rfl⟩ := exists_lift m1 (T := epsR S) w hw.1
    exact (existsUnique_congr fun cf => comb_iff m1 (u τ) cf w').2
      ((hu2 τ).2 w' ((tan_iff m1 w').1 hw) ((eig τ w').1 hw'))
  · obtain ⟨v, hv, hv'⟩ := hu1 τ k
    exact ⟨v, (u τ k).left, hv, rfl, hv', Over.w (u τ k)⟩
