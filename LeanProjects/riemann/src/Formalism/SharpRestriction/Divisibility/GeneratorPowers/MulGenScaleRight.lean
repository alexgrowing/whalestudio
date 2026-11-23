import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

theorem scaleGen_eq {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    scaleGen φ ε u g = scaleGenG Xo.univ.t φ ε u g := rfl

theorem mulGen_scale_right {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ Xo.univ.t.G.left)) (ε' : K' → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')) :
    LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g (scaleGenG Xo.univ.t φ' ε' v g') =
      scaleGenG Xo.univ.t _ _ v (LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g g') := by
  conv_lhs => rw [← FBIdLB.scaleGenG_one Xo.univ.t φ ε g]
  rw [FBIdLB.mulGen_scaleGenG, one_mul]

def tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) : FrTy y d x m :=
  scaleGen _ _ (unitΓ (T m)) (e m)

abbrev sub (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S)
    (T : (Jet S (Fin 2 × Fin d) m)ˣ) : (Jet S (Fin n' × Fin d) m)ˣ :=
  Units.map (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2).toMonoidHom T

theorem pe_tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :
    pe y d x (tw y d x e T) m φ = scaleGenG Xo.univ.t _ _ (unitΓ (sub d m φ (T m))) (pe y d x e m φ) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
    (unitΓ (T m)) (e m) (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  exact h1

theorem tw_zero (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (h0 : T 0 = 1) :
    tw y d x e T 0 = e 0 := by
  have h1 := FBIdLB.scaleGenG_one Xo.univ.t (cφ ![jpt y d x 0 (0 : Fin 2), jpt y d x 0 (1 : Fin 2)]) (cε 2) (e 0)
  have h2 : unitΓ (T 0) = 1 := by rw [h0, FBIdSy.unitΓ_one]
  show scaleGenG Xo.univ.t _ _ (unitΓ (T 0)) (e 0) = e 0
  rw [h2]
  exact h1

theorem tw_isGen (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) (hg : (e m).IsGen) :
    (tw y d x e T m).IsGen := by
  intro i j
  have h := hg i j
  unfold tw scaleGen
  dsimp only
  erw [map_mul, map_mul, ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res', h]
  all_goals first | exact mul_left_comm _ _ _ | exact le_rfl

theorem isFrame_tw [StarRing (𝓞 E)] {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hF : IsFrame y d x F act ph1 ph2 sy ad e)
    (hm1 : ∀ m, sub d m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub d m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub d m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)) :
    IsFrame y d x F act ph1 ph2 sy ad (tw y d x e T) := by
  refine ⟨fun m => tw_isGen y d x e T m (hF.gen m), fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hc⟩ := hF.ph1 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm1 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.ph2 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm2 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.sy m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc (unitΓ (T m))
    have eR : scaleGen _ _ (unitΓ u⁻¹) (pe y d x (tw y d x e T) m
        ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) =
        scaleGenG Xo.univ.t _ _ (unitΓ (T m)) (scaleGen _ _ (unitΓ u⁻¹)
          (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
      rw [pe_tw, hs m, scaleGen_eq, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG, FBIdSy.scaleGenG_scaleGenG,
        _root_.mul_comm]
    rw [eR]
    exact key
  · obtain ⟨wL, hwL, h⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := h m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc
      (unitΓ (sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)))
    rw [pe_tw, pe_tw, hb m a, mulGen_scale_right, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG,
      _root_.mul_comm, ← FBIdSy.scaleGenG_scaleGenG]
    exact key

theorem trunc_tw (e : ∀ m, FrTy y d x m) (T U : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (tw y d x e T (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (tw y d x e T m) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t
    (cφ ![jpt y d x (m + 1) (0 : Fin 2), jpt y d x (m + 1) (1 : Fin 2)]) (cε 2) (unitΓ (T (m + 1))) (e (m + 1))
    (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  have key := FBIdLB.corr_scaleGenG Xo.univ.t (hstep m)
    (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))))
  have hu : unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))) * unitΓ (U m) = unitΓ (T m) := by
    rw [← FBIdSy.unitΓ_mul, hT m]
  have h2 : scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
      (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
        (T (m + 1)))) (scaleGenG Xo.univ.t _ _ (unitΓ (U m)) (e m)) = tw y d x e T m :=
    (FBIdSy.scaleGenG_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) _ _
      (e m)).trans (congrArg (fun v => scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)])
        (cε 2) v (e m)) hu)
  exact (congrArg₂ (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _) h1 h2.symm).mpr key

theorem corr_refl {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε g g := by
  intro j j' _ _ hx
  have : j = j' := funext fun k => hx k k rfl
  subst this
  rfl

theorem fixTw_of [StarRing (𝓞 E)] [Algebra ℚ S] (C : ChartAt Xo c y) (T U : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ)
    (hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m))
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (C.e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (h0 : T 0 = 1) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ (T m)) (C.e m)) := by
  have hfr := isFrame_tw y C.d C.x C.e T C.frame hm1 hm2 hs hb
  have h0' := tw_zero y C.d C.x C.e T h0
  have hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act (tw y C.d C.x C.e T) C.wP 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
    simp only [eL, pe]
    rw [h0']
    exact C.rig0
  refine ⟨tw y C.d C.x C.e T, hfr, hrig, fun m => trunc_tw y C.d C.x C.e T U hstep hT m, fun m => ?_⟩
  exact corr_refl _ _ _

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
