import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem genBC_frameR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S]
    [CommRing K] (x : Sp S ⟶ Xo.X) (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChangeR hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

theorem bcGenR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (c : Coeff l) :
    BcGenRSt Xo c := fun _ _ _ _ ψ y =>
  ⟨secCP (cpS ψ.toRingHom y.x) y.s, fun _ _ => rfl, genBC_frameR hS hT y.x ψ.toRingHom y.s y.gen⟩

theorem bcLieAll (c : Coeff l) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left)
    (hw : IsTanAt (spMap ψ.toRingHom ≫ y.x) w) (he : IsEigAt c τ w) : ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  let x := spMap ψ.toRingHom ≫ y.x
  have tn : ∀ τ i, IsTanAt x (spMap (dualMap ψ.toRingHom) ≫ y.u τ i) := fun τ i => tan_bc ψ.toRingHom (y.tan τ i)
  refine eig_basis_of_full (fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) tn (fun τ i => eig_bc ψ τ (y.eig τ i))
    (fun m => ?_) τ w hw he
  have h := hS (Xo := Xo) x
  choose u' hu' using fun i => push_surj h (tv (tvOf (tn (eB Dw i).1 (eB Dw i).2)))
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback y.x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  have gp := Chart.isGrpPullback_factor y.x (spMap ψ.toRingHom) h
  have bs : IsLieBasis u' := Chart.frameLieBCR _ (uS_basis y) ψ.toRingHom gp (fun a b v hv => push_inj h (by
      have := smT_add x _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc]
      exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (push_uS y i)).symm)
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (uS y i)).symm)
      exact (spMap_comp_spMap _ _).trans ((congrArg spMap (dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)
  obtain ⟨p, hp⟩ := push_surj h (tv m)
  have key : ∀ a, IsLieComb a u' p ↔ m = ∑ k, a ((eB Dw).symm k) • tvOf (tn k.1 k.2) := fun a => by
    rw [isLieComb_iff h, hp, ← (eB Dw).sum_comp]
    simp only [Equiv.symm_apply_apply, hu']
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum]; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum]; rfl)⟩
  obtain ⟨a, ha, hu⟩ := bs.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem m))
  refine ⟨fun k => a ((eB Dw).symm k), (key a).1 ha, fun b hb => ?_⟩
  have := hu (fun i => b (eB Dw i)) ((key _).2 (by simpa using hb))
  funext k; rw [← this]; simp

theorem bcLieR (c : Coeff l) : BcLieRSt Xo c := fun _ _ _ _ ψ y => bcLieAll c ψ y

end ReciprocityTheory.ChartRestriction.G.PullbackSections
