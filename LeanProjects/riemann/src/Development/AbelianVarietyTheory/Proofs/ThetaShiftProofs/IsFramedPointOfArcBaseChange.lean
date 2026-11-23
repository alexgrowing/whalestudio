import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_cancel {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w'' : LB.Iso L''.L (L.L.pull n.F)) (hw : IsRigIso m L' L w) (hw'' : IsRigIso n L'' L w'') :
    ∃ w' : LB.Iso L''.L (L'.L.pull m'.F), IsRigIso m' L'' L' w' ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G''.left) (y : Y) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        m.F (m'.F (f y)) ∈ L.L.U j → m'.F (f y) ∈ L'.L.U i → f y ∈ L''.L.U k →
        gw w'' f y j k = gw w (f ≫ m'.F) y j i * gw w' f y i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw''
  obtain ⟨g, r⟩ := hw
  obtain ⟨g'', r''⟩ := hw''
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' g g'' L'.isLB L''.isLB
  exact ⟨w', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_cancel L.isLB g g'',
    T.pmaps_cancel L.isLB (fun _ => m'.e_comm) r r''⟩, T⟩

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} {θ : LB.Sec L} (h : IsoMaps w σ s) (p : PullSec F θ s)
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  refine Eq.trans ?_ ((gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _)))))
  rw [p (fun _ => j) le]
  exact (gs_appLE F _ _ le r z (mem_pull.2 hj) _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isoMaps_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {x : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t x) (hx : x = g ≫ f)
    (hφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ)}
    (hw : RigIso m w) (hw'' : RigIso n w'') {θ : LB.Sec t.PP.L} {θ' : LB.Sec t'.PP.L} {σ : LB.Sec t''.PP.L}
    {s : LB.Sec (t.PP.L.pull m.φ)} {s'' : LB.Sec (t.PP.L.pull n.φ)} (i : IsoMaps w θ' s) (p : PullSec m.φ θ s)
    (i'' : IsoMaps w'' σ s'') (p'' : PullSec n.φ θ s'') :
    ∃ w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ), RigIso m' w' ∧ IsoMaps w' σ (thfPull t'.PP.L m'.φ θ') := by
  have he : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, hx]
  obtain ⟨w', r', tri⟩ := exists_rigIso_cancel m.cm m'.cm n.cm hφ he t''.PP t'.PP t.PP w w'' hw hw''
  refine ⟨w', r', fun (a : PUnit → t'.PP.L.ι) k => fn_ext fun y hy => ?_⟩
  have hi : m'.φ y ∈ t'.PP.L.U (a PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (m'.φ y))
  have pt : n.φ y = m.φ (m'.φ y) := congrArg (fun q => q y) hφ
  have e1 := gs_of_isoMaps i p (𝟙 _ ≫ m'.φ) y j (a PUnit.unit) hj hi
  have e2 := gs_of_isoMaps i'' p'' (𝟙 _) y j k (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (a PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m'.φ) ≫ m.φ = 𝟙 _ ≫ n.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m'.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (φ.comp io) = spMap φ ≫ spMap io := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

end GlobalTheory.ArcQ.FrBC

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

open FrBC in

theorem isArcFr_witBC : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A') (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)), Mono Y.j → InBC f a a' p → WitBC f p W W' → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th', (∀ τ k, LetBC p (e τ k) (e' τ k)) → ThBC p th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S), IsArcFr W e th (ι'.comp (PowerSeries.map f)) y → IsArcFr W' e' th' ι' y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W A' _ _ _ _ b' a' f p W' hj hin hwit e e' th th' he hth
    S _ _ ι' y h
  obtain ⟨m, hm, hlie, hθ⟩ := GlobalTheory.ArcBaseChange.main hL hL2 E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hin hwit
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hT, r1, r2, i1, i2, p2, hg⟩ := h
  have hio : spMap (ι'.comp (PowerSeries.map f)) = spMap ι' ≫ spMap (PowerSeries.map f) := spMap_comp' _ _
  have key : ∀ (g : Sp S ⟶ Sp (PowerSeries A)) (n : SABMap G W.t g), g = spMap ι' ≫ spMap (PowerSeries.map f) →
      ∃ m' : SABMap G W'.t (spMap ι'), n.φ = m'.φ ≫ m.φ := by
    intro g n hg
    subst hg
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
  obtain ⟨m', e₂⟩ := key _ m2 hio
  obtain ⟨w, θ', rw', iw⟩ := pull_sec W.t W'.t m θ
  have pw : PullSec m.φ θ (thfPull W.t.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := exists_isoMaps_cancel m m' m2 hio e₂ rw' r2 iw pw i2 p2
  refine ⟨z, G, m1, m', φ, ?_, zx, φb, φ1, ?_, fun τ k => ?_, θ', w1, w', σ, s1, _,
    hθ w th th' θ θ' _ rw' hth hT pw iw, r1, r', i1, i', fun _ _ => rfl, hg⟩
  · rw [zj, hio, Category.assoc]
  · rw [φ2, hm, e₂, Category.assoc]
  · obtain ⟨v, q₀, h1, h2, h3, -⟩ := hu τ k
    have vb : v.left ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
    have pb : (q₀ ≫ G.G.hom) ≫ spMap (ι'.comp (PowerSeries.map f)) =
        spMap (algebraMap S (DualNumber S)) ≫ spMap (ι'.comp (PowerSeries.map f)) := by
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      exact (congrArg (· ≫ W.t.G.hom) h3).trans (by rw [Category.assoc, vb, dual_alg])
    have pz : (q₀ ≫ G.G.hom) ≫ z = spMap (algebraMap S (DualNumber S)) ≫ z := by
      rw [← cancel_mono Y.j, Category.assoc, zj, ← Category.assoc, pb, Category.assoc, Category.assoc, zj]
    let q := m1.cart.1.lift (y.u τ k) _ (y.tan τ k).1
    have hq : q ≫ m1.φ = y.u τ k := m1.cart.1.lift_fst _ _ _
    have qb : q ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := m1.cart.1.lift_snd _ _ _
    have qφ : q ≫ φ = q₀ ≫ φ := by
      apply Y.m0.toSABMap.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        exact ((congrArg _ φ1).trans (hq.trans h2.symm)).trans (congrArg _ φ1.symm)
      · rw [Category.assoc, Category.assoc, φb, ← Category.assoc, ← Category.assoc, qb, pz]
    have q2 : q ≫ m2.φ = q₀ ≫ m2.φ := by
      apply W.m.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        refine (congrArg _ φ2.symm).trans (Eq.trans ?_ (congrArg _ φ2))
        rw [← Category.assoc, qφ, Category.assoc]
      · rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc, ← Category.assoc, qb, pb]
    have cond : (spMap (dualMap (PowerSeries.map f)) ≫ v.left) ≫ W.t.G.hom =
        spMap (algebraMap (PowerSeries A') (DualNumber (PowerSeries A'))) ≫ spMap (PowerSeries.map f) := by
      rw [Category.assoc, vb, dual_alg]
    let v' : epsR (PowerSeries A') ⟶ W'.t.G := Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ cond)
    have hv : v'.left ≫ m.φ = spMap (dualMap (PowerSeries.map f)) ≫ v.left := m.cart.1.lift_fst _ _ cond
    have vb' : v'.left ≫ W'.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A'))) := Over.w v'
    refine ⟨v', q, hlie _ _ v v' (he τ k) h1 hv, hq, ?_, qb⟩
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine (congrArg _ e₂.symm).trans ((q2.trans h3).trans (Eq.trans ?_ (congrArg _ hv.symm)))
      rw [dual_comp, Category.assoc]
    · rw [Category.assoc, Category.assoc, m'.cart.1.w, vb', dual_alg, ← Category.assoc, qb]

end GlobalTheory.ArcQ
