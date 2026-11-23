import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Comp1Scalar

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChartCmp

section Series
variable {R : Type} [CommRing R]

def JEq {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ e : σ →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g

structure JRel {d : ℕ} {O : Type} [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) : Prop where
  inv : IsInvPair φ φi
  unit : IsUnit (MvPowerSeries.constantCoeff ε)
  law : ∀ i, B'.G.F i = transF B.G.F φ φi i
  act : ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)
  ph1 : JEq m (B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt R (n := 3) d 0) (pt R (n := 3) d 1), pt R (n := 3) d 2] ε)
    (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph1 *
      (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε * ev (n := 3) ![pt R (n := 3) d 1, pt R (n := 3) d 2] ε))
  ph2 : JEq m (B'.ph2 * ev (n := 3) ![pt R (n := 3) d 0, addOf B'.G.F (pt R (n := 3) d 1) (pt R (n := 3) d 2)] ε)
    (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph2 *
      (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 1] ε * ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε))
  sy : JEq m (B'.sy * ε)
    (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] B.sy * ev (n := 2) ![pt R (n := 2) d 1, pt R (n := 2) d 0] ε)
  ad : ∀ a, JEq m (B'.ad a * ev (n := 2) ![pt R (n := 2) d 0, comp1 (B'.A.act (star a)) (pt R (n := 2) d 1)] ε)
    (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] (B.ad a) *
      ev (n := 2) ![comp1 (B'.A.act a) (pt R (n := 2) d 0), pt R (n := 2) d 1] ε)

structure Biadd {d : ℕ} {O : Type} [CommRing O] [StarRing O] (m : ℕ) (B : FB R d O) (k : Type) [CommRing k] [Algebra R k]
    (g : PS k 2 d) : Prop where
  ax0 : JEq m (ev (n := 1) ![0, pt k (n := 1) d 0] g) 0
  ax1 : JEq m (ev (n := 1) ![pt k (n := 1) d 0, 0] g) 0
  add1 : JEq m (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] g)
    (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g)
  add2 : JEq m (ev (n := 3) ![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k (n := 3) d 2)] g)
    (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g)
  sym : JEq m (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] g) g
  bal : ∀ a : O, JEq m (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k (n := 2) d 1] g)
    (ev (n := 2) ![pt k (n := 2) d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] g)

def bilSer {d n : ℕ} (β : Matrix (Fin d) (Fin d) R) (x z : Pt R n d) : PS R n d :=
  ∑ i, ∑ j, MvPowerSeries.C (β i j) * (x i * z j)
end Series

section Bundles

def Carries {X X' Y : Scheme.{0}} {L' : LB X'} (L : LB X) (F : X' ⟶ X) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) : Prop :=
  LB.Gen.Maps (LB.linCombIso w φ ε) g (flatGen L F φ ε g')
end Bundles

section Geo
variable {V : Type} [CommRing V]

def CoordRel {G : Over (Sp V)} {d : ℕ} (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (φ : Pt V 1 d) : Prop :=
  ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ x m

def dirs {G : Over (Sp V)} {d : ℕ} (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) : Fin d → (Sp (DualNumber V) ⟶ G.left) :=
  fun j => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ x 1).left
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def FrRel (t : SAB H (Sp V)) {d : ℕ} (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m)
    (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d) (m : ℕ) (ε : PS V 2 d) : Prop :=
  ∃ u : (Jet V (Fin 2 × Fin d) m)ˣ, (u : Jet V (Fin 2 × Fin d) m) = psJet m ε ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e' m)
      (scaleGenG t _ _ (unitΓ u) (peG t (𝟙 (Sp V)) d x e m ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]))

def PushFr {t t' : SAB H (Sp V)} (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) {d : ℕ}
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m) : Prop :=
  ∀ m, (e' m).IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
    c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c (e' m) ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) c

def CubIso {t t' : SAB H (Sp V)} (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (thφ t.G (x3 t.G)) thε) t.cub.t (n.cm.thetaPull t'.PP.L t'.cub.t)
end Geo

section Families
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def FamPh1 (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (ph1 : MvPowerSeries (Fin 3 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def FamPh2 (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (ph2 : MvPowerSeries (Fin 3 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def FamSy (sy : MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))

def FamAd (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L
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

theorem isFrameG_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) :
    IsFrameG t x0 d x F act ph1 ph2 sy ad e ↔ (∀ m, (e m).IsGen) ∧ FamPh1 t x0 d x F ph1 e ∧ FamPh2 t x0 d x F ph2 e ∧
      FamSy t x0 d x sy e ∧ FamAd t x0 d x act ad e := by
  constructor
  · intro h
    exact ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
end Families

section Depth
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def nuAlg (Dw : Datum H) [StarRing (𝓞 E)] (T : CDVR) {d : ℕ} (B : FB T.V d (𝓞 E)) (h : PS T.Fr 2 d) (u : Lt1 Dw → Fin d → T.Fr)
    (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.V n d),
    nval T.V e (nabValN B T.Fr h H.w0 k (MvPowerSeries.map (algebraMap T.V T.Fr) f) (fun ℓ => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P)
end Depth

theorem JEq.refl {R : Type} [CommRing R] {σ : Type} (m : ℕ) (f : MvPowerSeries σ R) : JEq m f f := by
  intro e _
  rfl

end GlobalTheory.ChartCmp

end

noncomputable section
namespace GlobalTheory.ChartCmp.Inh
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.AdditiveBiext

abbrev addInt : FB ℤ 1 ℤ := additiveFB ℤ 1

def refl1 : Pt ℤ 1 1 := fun i => C (-1) * X ((0 : Fin 1), i)

def xz : PS ℤ 2 1 := X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1))

section Depth
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem nuLocC_eq_nuAlg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntChart T io y)
    (B : FB T.V (chD Ch.ch) (𝓞 E)) (hF : B.G.F = Ch.FT) (hA : B.A.act = Ch.actT) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    nuLocC Ch e k a n = letI := io.toAlgebra; nuAlg Dw T B Ch.ch.h Ch.ch.uvec e k a n := by
  letI := io.toAlgebra
  have hFK : Ch.ch.B.FK T.Fr = B.FK T.Fr := by
    funext j
    show MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.G.F j) =
      MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)
    rw [gt_map_id, hF, Ch.gen.1.1 j]
  have hAK : ∀ b, Ch.ch.B.actK T.Fr b = B.actK T.Fr b := by
    intro b
    funext j
    show MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act b j) =
      MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act b j)
    rw [gt_map_id, hA, Ch.gen.1.2.1 b j]
  have hB : ∀ {ι : Type} [Fintype ι] (f : PS T.Fr n (chD Ch.ch)) (cp : ι → Fin n)
      (u : ι → Fin (chD Ch.ch) → T.Fr) (P : MvPolynomial ι T.Fr),
      nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f cp u P = nabValN B T.Fr Ch.ch.h H.w0 k f cp u P := by
    intro ι _ f cp u P
    simp only [nabValN, FB.hL, hFK, hAK]
  dsimp only [nuLocC, nuAlg]
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    have hmem : IsIntPS T (MvPowerSeries.map (algebraMap T.V T.Fr) g) := fun m =>
      RingHom.mem_range.mpr ⟨MvPowerSeries.coeff m g, by simp⟩
    exact (iInf₂_le _ hmem).trans_eq (by rw [hB])
  · refine le_iInf fun f => le_iInf fun hf => ?_
    have hf' := fun m => RingHom.mem_range.mp (hf m)
    choose g hg using hf'
    have hfg : MvPowerSeries.map (algebraMap T.V T.Fr) (g : PS T.V n (chD Ch.ch)) = f := by
      ext m
      exact hg m
    exact (iInf_le _ (g : PS T.V n (chD Ch.ch))).trans_eq (by rw [hfg, hB])
end Depth

end GlobalTheory.ChartCmp.Inh
