import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def IntFramesSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    (letI := io.toAlgebra; ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1)

def GenFibreSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt),
      ∃ (t' : SAB H (Sp T.Fr)) (_m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
        (_m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), True

def LieFreeSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X)
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    letI := io.toAlgebra
    ∀ u₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left),
    (∀ τ i, IsTanAt x (u₀ τ i)) → (∀ τ i, IsEigAt c τ (u₀ τ i)) →
    (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u₀ τ) a w) →
    ∃ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
        (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
          ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
        ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u τ i ∧
          u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
      (∀ τ i, IsTanAt x (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧
      (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u τ) a w) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u τ i)

def ThetaFrameSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i

def SpreadSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem genFibre (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) : GenFibreSt Xo c := by
  intro T io O _ β Y yt z h1 h2 G m
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ := sabPull hC (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt _ m m2
  rw [← h1] at n
  have n' : SABMap _ Y.t (z ≫ (Y.jQ ≫ pullback.fst _ _)) := n
  obtain ⟨m1, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t _ _ z Y.m n'
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ _ z Y.m0.toSABMap m1
  exact ⟨_, n2, m2, trivial⟩

set_option maxHeartbeats 1000000 in

theorem intFrames_of (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hG : GenFibreSt Xo c) (hL : LieFreeSt Xo c)
    (hT : ThetaFrameSt Xo c) (hS : SpreadSt Xo c) : IntFramesSt Xo c := by

  have e : ∀ (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (v : Γ(X, U)),
      (Scheme.Hom.appLE (𝟙 X) U U h).hom v = v := by
    intro X U h v
    simp [Scheme.Hom.appLE]
    first
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; rfl)
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; simp; done)
      | (erw [CategoryTheory.Functor.map_id]; simp; done)
  have key : ∀ {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s0 : LB.Sec (PPx x)) (a : S),
      (∀ i, s.f i = scal x a i * s0.f i) → ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx x).U i ≤ (𝟙 (Gx x)) ⁻¹ᵁ (PPx x).U i),
        (Scheme.Hom.appLE (𝟙 (Gx x)) _ _ h).hom (scal x a i * s0.f i) = s.f i := by
    intro S _ x s s0 a ha i h
    rw [ha i]
    exact e _ _ _ _
  intro T io O _ β Y hP yt z h1 h2
  letI := io.toAlgebra
  intro y₀ hy₀
  obtain ⟨x0, hx0, u0, tan0, eig0, basis0, s0, gen0⟩ := y₀
  dsimp only at hy₀
  subst hy₀
  obtain ⟨PP', cub, sym, adj, prim, mG, -⟩ := sabPull hC yt Y.t
  obtain ⟨t', m1, m2, -⟩ := hG T io O β Y yt z h1 h2 _ mG
  obtain ⟨ub, u, ⟨hub1, hub2, hub3, hub4⟩, hu1, hu2, hu3, hu4⟩ :=
    hL T io _ t' _ m1 m2 hx0 u0 tan0 eig0 basis0
  obtain ⟨θ, s, hθ1, hθ2, hs, a, ha⟩ := hT T io O β Y hP yt z h1 h2 _ mG t' m1 m2 s0 gen0
  choose cf hcf1 hcf2 hcf3 using hu4
  let y : FrPt Xo c T.Fr :=
    { x := _, x_over := hx0, u := u, tan := hu1, eig := hu2, basis := hu3, s := s, gen := hs }
  refine ⟨⟨y, hS T.Fr y, _, t', m1, m2, ⟨ub, hub1, hub2, hub3, hub4⟩, θ, hθ1, hθ2⟩,
    fun k => match k with | none => a | some p => (hcf1 p.1 p.2).unit, rfl, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · intro τ i
    exact ⟨cf τ i, (hcf1 τ i).unit_spec.symm, hcf2 τ i, hcf3 τ i⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · exact key _ s s0 _ ha

theorem intFrames (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hL : LieFreeSt Xo c) (hT : ThetaFrameSt Xo c)
    (hS : SpreadSt Xo c) : IntFramesSt Xo c :=
  intFrames_of Xo c hC (genFibre Xo c hC) hL hT hS

end Formalism.L2.Pj
