import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridge

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

def cpθ : ChartPull (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (PPx x) (gxU x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left).cp
    (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)) (gxU x) (gxU_snd x)

def cpV : ChartPull (PPx x) (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (gxV x) :=
  (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left) (gxV x) (gxV_fst x)

def cpσ : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ)))
    (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (pullback.fst _ (spMap ψ)) :=
  chartPullPull _ _ _ rfl

def cpU' : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (PPx (spMap ψ ≫ x)) (bcU ψ x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left).cp
    ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _) (bcU ψ x) (bcU_snd ψ x)

def cpV' : ChartPull (PPx (spMap ψ ≫ x)) ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (bcV ψ x) :=
  ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (bcV ψ x)
    (bcV_snd' ψ x)

def cpS : ChartPull (PPx (spMap ψ ≫ x)) (PPx x) (bcPm ψ x) :=
  cpSame Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (fun _ => 1) (bcPm ψ x) (fun _ => bcPm_snd ψ x)

def tA : SAB H (Sp S) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t
def mA : SABMap (tA x) Xo.univ.t x := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t

def tB : SAB H (Sp T) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)
def mB : SABMap (tB ψ x) (tA x) (spMap ψ) := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)

def θA (s0 : LB.Sec (PPx x)) : LB.Sec (tA x).PP.L := secCP (cpθ x) s0

def σB (s0 : LB.Sec (PPx x)) : LB.Sec (tB ψ x).PP.L := secCP (cpσ ψ x) (θA x s0)

theorem hθ_of (s0 : LB.Sec (PPx x)) (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i)
    (σ : LB.Sec (tA x).PP.L) : ∃ a : S, ∀ i, σ.f i = constFn (tA x).G.hom _ a * (θA x s0).f i := by
  obtain ⟨a, ha, -⟩ := hgen (secCP (cpV x) σ)
  refine ⟨a, (sec_eq_iff _ σ (θA x s0) a).2 fun i q hq => ?_⟩
  have hJ : gxU x q ∈ (PPx x).U (fun _ => i PUnit.unit) := (cpθ x).le i hq
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (gxU x) q hJ ((scal_eq_iff x _ _ a).1 ha _ (gxU x q) hJ)
  rw [gs_secCP (cpV x) σ (gxU x) q _ hJ, gxU_gxV, gxU_fst] at h2
  have e3 : gs (𝟙 _) q ((tA x).PP.L.U i) ((θA x s0).f i) =
      gs (gxU x) q ((PPx x).U (fun _ => i PUnit.unit)) (s0.f (fun _ => i PUnit.unit)) :=
    (gs_secCP (cpθ x) s0 (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  rw [e3]
  exact h2

theorem hσ_of (s0 : LB.Sec (PPx x)) (y : (tB ψ x).G.left) (j : PUnit → Xo.univ.t.PP.L.ι)
    (k : PUnit → PUnit → Xo.univ.t.PP.L.ι) (hj : (mB ψ x).φ y ∈ (tA x).PP.L.U j) (hk : y ∈ (tB ψ x).PP.L.U k) :
    gs (mB ψ x).φ y _ ((θA x s0).f j) =
      (gw (idIso ((tA x).PP.L.pull (mB ψ x).φ)) (𝟙 _) y j k).val * gs (𝟙 _) y _ ((σB ψ x s0).f k) := by
  have hk' : (mB ψ x).φ y ∈ (tA x).PP.L.U (k PUnit.unit) := mem_pull.1 hk
  have e1 := gm_pull_g (tA x).PP.L (mB ψ x).φ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hk
  rw [Category.id_comp] at e1
  have e2 : gs (𝟙 _) y ((tB ψ x).PP.L.U k) ((σB ψ x s0).f k) =
      gs (mB ψ x).φ y ((tA x).PP.L.U (k PUnit.unit)) ((θA x s0).f (k PUnit.unit)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) y k hk).trans (by rw [Category.id_comp]; rfl)
  rw [e2, gs_compat (θA x s0) (mB ψ x).φ y hj hk']
  exact congrArg (· * _) (congrArg Units.val e1.symm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
