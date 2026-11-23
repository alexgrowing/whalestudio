import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem key_fwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i) :
    ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i := by
  rw [sec_eq_iff] at h
  rw [scal_eq_iff]
  intro J yy hy
  have hp : bcV ψ x yy ∈ (tB ψ x).PP.L.U (fun _ _ => J 0) := (cpV' ψ x).le J hy
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcV ψ x) yy hp (h _ _ hp)
  have A1 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0))
        ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f (fun _ _ => J 0)) =
      gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U (fun _ => J 0)) (s''.f (fun _ => J 0)) :=
    (gs_secCP (cpU' ψ x) s'' (bcV ψ x) yy _ hp).trans (by rw [bcV_bcU]; rfl)
  have hp2 : (bcV ψ x ≫ pullback.fst _ _) yy ∈
      (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).U (fun _ => J 0) := (cpσ ψ x).le _ hp
  have A2 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0)) ((σB ψ x s0).f (fun _ _ => J 0)) =
      gs (bcPm ψ x) yy ((PPx x).U (fun _ => J 0)) (s0.f (fun _ => J 0)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (bcV ψ x) yy _ hp).trans
      ((gs_secCP (cpθ x) s0 _ yy _ hp2).trans (by rw [Category.assoc, bcV_gxU]; rfl))
  have A3 : bcV ψ x ≫ (tB ψ x).G.hom = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := bcV_snd ψ x
  rw [A1, A2, A3] at h1
  have hJ : (fun _ : Fin 1 => J 0) = J := funext fun k => by rw [Subsingleton.elim k 0]
  rw [hJ] at h1
  have e4 : gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U J) ((secCP (cpS ψ x) s0).f J) =
      gs (bcPm ψ x) yy ((PPx x).U J) (s0.f J) :=
    (gs_secCP (cpS ψ x) s0 (𝟙 _) yy J hy).trans (by rw [Category.id_comp]; rfl)
  exact h1.trans (congrArg _ e4.symm)

theorem key_bwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i) :
    ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i := by
  rw [scal_eq_iff] at h
  rw [sec_eq_iff]
  intro i q hq
  have hq' : bcU ψ x q ∈ (PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit) := (cpU' ψ x).le i hq
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcU ψ x) q hq' (h _ _ hq')
  rw [bcU_fst] at h1
  have B0 : gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i) =
      gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        (s''.f (fun _ => i PUnit.unit PUnit.unit)) :=
    (gs_secCP (cpU' ψ x) s'' (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  have B1 : gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        ((secCP (cpS ψ x) s0).f (fun _ => i PUnit.unit PUnit.unit)) =
      gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((σB ψ x s0).f i) := by
    refine (gs_secCP (cpS ψ x) s0 (bcU ψ x) q _ hq').trans ?_
    rw [bcU_bcPm]
    exact ((gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) q i hq).trans
      ((gs_secCP (cpθ x) s0 _ q _ ((cpσ ψ x).le i hq)).trans (by rfl))).symm
  exact B0.trans (h1.trans (congrArg _ B1))

theorem genBC_frame (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    {K : Type} [Field K] (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChange hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

theorem bcGenSt_of (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (c : Coeff l) : BcGenSt Xo c := by
  intro p K _ _ ψ' y
  exact ⟨secCP (cpS ψ'.toRingHom y.x) y.s, fun i h => rfl, genBC_frame y.x hS hT ψ'.toRingHom y.s y.gen⟩

theorem bcEx_of_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (c : Coeff l) (hL : BcLieSt Xo c) (σ : c.F →+* ℂ) : BCEx Xo c σ :=
  bcEx_of (bcGenSt_of hS hT c) hL σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
