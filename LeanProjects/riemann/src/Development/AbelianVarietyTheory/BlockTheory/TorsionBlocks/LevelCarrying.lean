import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev LevelMod (Dw : Datum H) (l : Level H) : Type :=
  Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

abbrev LevelAut (Dw : Datum H) (l : Level H) : Type := LevelMod Dw l ≃ₗ[𝓞 E] LevelMod Dw l

def IsRigCubIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (ν : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull ν.φ)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (ν.cm.thetaPull t.PP.L t.cub.t)

def MovesLevel (Xo : Moduli Dw l) (g : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ρ ≫ Xo.s = Xo.s ∧
    (∀ a b : Dw.La, Submodule.Quotient.mk b = g (Submodule.Quotient.mk a) →
      (Xo.univ.eta b).left ≫ ν.φ = ρ ≫ (Xo.univ.eta a).left) ∧
    ∀ a : Dw.La, (Xo.univ.etaA a).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left

variable {Xo : Moduli Dw l} {c : Coeff l}

def Carries {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ))
    {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ≫ ρ ∧
    (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
    ∃ pm : Gx y.x ⟶ Gx y'.x,
      pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
      pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
      ∀ (i i' : Fin 1 → Xo.univ.t.PP.L.ι) (V : (Gx y.x).Opens)
        (h : V ≤ (PPx y.x).U i) (h' : V ≤ pm ⁻¹ᵁ (PPx y'.x).U i')
        (hw : V ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
          (LB.div (Xo.univ.t.PP.L.pull ν.φ) Xo.univ.t.PP.L).U (fun _ => i' 0, i 0)),
        (pm.appLE _ V h').hom (y'.s.f i') =
          ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE _ V hw).hom (w.s (fun _ => i' 0, i 0)).val *
            resG (Gx y.x) h (y.s.f i)

def LevelMove (g : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ)),
    MovesLevel Xo g ρ ν ∧ IsRigCubIso ν w ∧ Carries ν w y y'

abbrev RelFam (Xo : Moduli Dw l) (c : Coeff l) (G : Type) : Type 1 :=
  G → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → FrPt Xo c S → Prop

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

def Total : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ y', R g S y y'

def Functional : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y y₁ y₂ : FrPt Xo c S), R g S y y₁ → R g S y y₂ → y₁ = y₂

def Unital : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), R 1 S y y

def Multiplicative' : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S),
    R g S y y' → R h S y' y'' → R (g * h) S y y''

def Natural : Prop :=
  ∀ (g : G) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S')
    (y y' : FrPt Xo c S) (z z' : FrPt Xo c S'), FrMap φ y z → R g S y y' → R g S' z z' → FrMap φ y' z'

def Triangular : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S),
    FrBor t y z → R g S y y' → R g S z z' → FrBor t y' z'

def ActionLaws : Prop :=
  Total R ∧ Functional R ∧ Unital R ∧ Multiplicative' R ∧ Natural R ∧ Triangular R

variable {R}

theorem ActionLaws.comap (h : ActionLaws R) {G' : Type} [Group G'] (f : G' →* G) :
    ActionLaws (fun g => R (f g) : RelFam Xo c G') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun g => h1 (f g), fun g => h2 (f g), fun S _ _ y => ?_, fun g k S _ _ y y' y'' a b => ?_,
    fun g => h5 (f g), fun g => h6 (f g)⟩
  · show R (f 1) S y y
    rw [map_one]; exact h3 S y
  · show R (f (g * k)) S y y''
    rw [map_mul]; exact h4 _ _ S y y' y'' a b

theorem ActionLaws.exists_mulAction (h : ActionLaws R) (S : Type) [CommRing S] [Algebra c.F S] :
    ∃ _ : MulAction Gᵐᵒᵖ (FrPt Xo c S), ∀ (g : G) (y y' : FrPt Xo c S), R g S y y' ↔ y' = MulOpposite.op g • y := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h
  choose a ha using fun g => h1 g S
  refine ⟨{ smul := fun g y => a g.unop y
            one_smul := fun y => h2 1 S y _ _ (ha 1 y) (h3 S y)
            mul_smul := fun g k y => h2 _ S y _ _ (ha _ y) (h4 _ _ S _ _ _ (ha k.unop y) (ha g.unop _)) },
    fun g y y' => ⟨fun r => h2 g S y _ _ r (ha g y), fun e => e ▸ ha g y⟩⟩

example : ActionLaws (fun _ _ _ _ y y' => y' = y : RelFam Xo c G) :=
  ⟨fun _ _ _ _ y => ⟨y, rfl⟩, fun _ _ _ _ _ _ _ a b => a.trans b.symm, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ a b => b.trans a, fun _ _ _ _ _ _ _ _ _ _ _ _ m a b => by subst a b; exact m,
    fun _ _ _ _ _ _ _ _ _ m a b => by subst a b; exact m⟩

end Laws

def levelRel (Xo : Moduli Dw l) (c : Coeff l) : RelFam Xo c (LevelAut Dw l) :=
  fun g _ _ _ y y' => LevelMove g y y'

example (g : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevelMove g y y') :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MovesLevel Xo g ρ ν ∧ y'.x = y.x ≫ ρ := by
  obtain ⟨ρ, ν, w, h1, -, h2⟩ := h
  exact ⟨ρ, ν, h1, h2.1⟩

def LevelActionOver (Xo : Moduli Dw l) (c : Coeff l) : Prop := ActionLaws (levelRel Xo c)

end General

def PrincipalLevelAction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), l.A = 1 → LevelActionOver Xo c

variable {D : D7}

def LevelActionAt (T : Core D) (j : ℕ) : Prop :=
  LevelActionOver (T.Q.Xo j) T.Q.c ∧ ∀ c' : Coeff T.Q.l, T.Q.c.F ≤ c'.F → LevelActionOver (T.Q.Xo j) c'

def LevelActionSt (D : D7) : Prop :=
  ∀ T : Core D, T.Q.Pins → ∀ j, InR D j → LevelActionAt T j

theorem levelActionSt_of_principal (h : PrincipalLevelAction) (D : D7) : LevelActionSt D :=
  fun _ hp _ _ => ⟨h _ _ _ _ _ _ hp.2.1.2, fun _ _ => h _ _ _ _ _ _ hp.2.1.2⟩

theorem LevelActionAt.matrixGroup {T : Core D} {j : ℕ} (h : LevelActionAt T j)
    (f : G0g D.nd →* LevelAut (T.Q.Dw j) T.Q.l) :
    ActionLaws (fun g => levelRel (T.Q.Xo j) T.Q.c (f g) : RelFam (T.Q.Xo j) T.Q.c (G0g D.nd)) ∧
      ∀ c' : Coeff T.Q.l, T.Q.c.F ≤ c'.F →
        ActionLaws (fun g => levelRel (T.Q.Xo j) c' (f g) : RelFam (T.Q.Xo j) c' (G0g D.nd)) :=
  ⟨ActionLaws.comap h.1 f, fun c' hc => ActionLaws.comap (h.2 c' hc) f⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms
