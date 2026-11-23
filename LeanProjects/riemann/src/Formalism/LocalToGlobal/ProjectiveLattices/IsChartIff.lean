import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section ChartG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

abbrev jOG (m n : ℕ) : Over X0 := overAt x0 (Jet S (Fin n × Fin d) m)

abbrev tEpsG : Over X0 := Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x0)

def IsTanAtG (v : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 ∧
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x0 ⟶ t.G).left

def IsCombAtG {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∃ u : Fin m → (tEpsG x0 ⟶ t.G), (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ v i) ∧
    ((List.ofFn u).prod).left = w

def jptG (x : ∀ m, jOG x0 d m 1 ⟶ t.G) {n : ℕ} (m : ℕ) (i : Fin n) : jOG x0 d m n ⟶ t.G :=
  homAt x0 (jetCopy d m i) ≫ x m

structure IsChartG {κ : Type} [Fintype κ] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ t.act.act a =
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : κ, IsCombAtG t x0
    (fun j : Fin d => (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (tg ℓ)

  basis : ∀ v : Fin d → S, ∃! a : κ → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j

end ChartG

section FrameG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

def cφG {T : Over X0} {n : ℕ} (xs : Fin n → (T ⟶ t.G)) :
    ULift (Finset (Fin n)) → (T.left ⟶ t.G.left) :=
  fun I => (psum t.G xs I.down).left

def scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.Gen (LB.LinComb t.PP.L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

def genPowG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) :
    LB.Gen (LB.LinComb t.PP.L φ fun i => (k : ℤ) * ε i) :=
  ⟨fun j => g.s j ^ k⟩

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev FrTyG (m : ℕ) : Type :=
  LB.Gen (cubeLB t.G ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] t.PP.L)

def peG (e : ∀ m, FrTyG t x0 d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left

structure IsFrameG (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u)
          (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end FrameG

section GermG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def jBaseG (m n : ℕ) : jOG x0 d m n ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl

abbrev PrimTyG : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (cφG t ![𝟙 t.G, t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I))

def IsPrimG (wP : PrimTyG t) : Prop :=
  wP.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ wP (eSec t.G)) t.PP.rig

def eLG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (m : ℕ) :=
  LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wP (x m).left)
    (peG t x0 d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])

def IsGermG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m)
    (wP : PrimTyG t) (k : ℕ)
    (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow t.G t.PP.L k (jOG x0 d m 1)))
    (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec t.G t.PP.L k (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr t.PP.L _ _ _ _ τ (genPowG t _ _ (eLG t x0 d x act e wP m) k) ∧
    IsValueAt t.G t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end GermG

section Link

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)

theorem isChart_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) :
    IsChart y d F act uvec x ↔ IsChartG Xo.univ.t y.x d F act (fun ℓ => y.u ℓ.1 ℓ.2) uvec x :=
  ⟨fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩,
    fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩⟩

set_option maxHeartbeats 1000000 in

theorem isFrame_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) :
    IsFrame y d x F act ph1 ph2 sy ad e ↔ IsFrameG Xo.univ.t y.x d x F act ph1 ph2 sy ad e :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩⟩

theorem isPrim_iff (wP : PrimTy H Xo) : IsPrim wP ↔ IsPrimG Xo.univ.t wP := Iff.rfl

set_option maxHeartbeats 1000000 in

theorem isGerm_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo)
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : MvPowerSeries (Fin 1 × Fin d) S) :
    IsGerm y d x act e wP k F f ↔ IsGermG Xo.univ.t y.x d x act e wP k F f := Iff.rfl

end Link

end Formalism.L2.Pj
