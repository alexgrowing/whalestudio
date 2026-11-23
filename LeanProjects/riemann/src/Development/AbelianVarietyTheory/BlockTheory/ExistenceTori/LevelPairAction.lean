import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.RhoWApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsRigCubIso {S' S : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.cm.F)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (m.cm.thetaPull t.PP.L t.cub.t)

def IsLevelAut (Xo : Moduli Dw l) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (r : Xo.X ≅ Xo.X)
    (ν : SABMap Xo.univ.t Xo.univ.t r.hom) : Prop :=
  r.hom ≫ Xo.s = Xo.s ∧
    (∀ a, (Xo.univ.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo.univ.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA a).left)

def CarriesSec {Xo : Moduli Dw l} {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull φ)) {x x' : Sp S ⟶ Xo.X}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) : Prop :=
  ∃ pm : Gx x ⟶ Gx x',
    pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ ∧
    pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ∧
    ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens)
      (hi : W ≤ (PPx x).U (fun _ => i))
      (hj : W ≤ pm ⁻¹ᵁ (PPx x').U (fun _ => j))
      (hw : W ≤ (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
        (LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U (fun _ => j, i)),
      (pm.appLE _ W hj).hom (s'.f (fun _ => j)) =
        ((snd (Over.mk x) Xo.univ.t.G).left.appLE _ W hw).hom (w.s (fun _ => j, i)).val *
          ((Gx x).presheaf.map (homOfLE hi).op).hom (s.f (fun _ => i))

variable {Xo : Moduli Dw l} {c : Coeff l}

def LevAct (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  ∃ (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
    IsLevelAut Xo gM gA r ν ∧ IsRigCubIso ν w ∧
      y'.x = y.x ≫ r.hom ∧ (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧ CarriesSec ν.cm.F w y.s y'.s

def CongM (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, g a - g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)

def CongN (n : ℕ) (g g' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop := ∀ a, ∃ b, g a - g' a = n • b

def IsLevelPair (l : Level H) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∃ k : ℕ → (Dw.La →ₗ[𝓞 E] Dw.La),
    (∀ n m, 0 < n → 0 < m → CongN n (k (n * m)) (k n)) ∧
    (∀ n : ℕ, 0 < n → ∀ a b, Dw.EF (k n a) (k n b) ≡ Dw.EF a b [ZMOD (n : ℤ)]) ∧
    CongM l gM (k l.M) ∧ CongN l.A gA (k l.A)

def LevelAutExistsSt (Xo : Moduli Dw l) : Prop :=
  ∀ gM gA : Dw.La →ₗ[𝓞 E] Dw.La, IsLevelPair l gM gA →
    ∃ (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom), IsLevelAut Xo gM gA r ν

def IsLevelRep (l : Level H) {Γ : Type} [Group Γ] (ρM ρA : Γ → (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  (∀ g, IsLevelPair l (ρM g) (ρA g)) ∧
    CongM l (ρM 1) LinearMap.id ∧ CongN l.A (ρA 1) LinearMap.id ∧
    (∀ g h, CongM l (ρM (g * h)) (ρM g ∘ₗ ρM h)) ∧ (∀ g h, CongN l.A (ρA (g * h)) (ρA g ∘ₗ ρA h))

def LevActLawsSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (Γ : Type) [Group Γ] (ρM ρA : Γ → (Dw.La →ₗ[𝓞 E] Dw.La)), IsLevelRep l ρM ρA →
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun (g : Γ) y y' => LevAct (ρM g) (ρA g) y y')

theorem LevAct.congr {gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La} (hM : CongM l gM' gM) (hA : CongN l.A gA' gA)
    {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevAct gM gA y y') : LevAct gM' gA' y y' := by
  obtain ⟨r, ν, w, ⟨h0, h1, h2⟩, h3⟩ := h
  refine ⟨r, ν, w, ⟨h0, fun a => ?_, fun a => ?_⟩, h3⟩
  · have e : Xo.univ.eta (gM' a) = Xo.univ.eta (gM a) := by
      rw [show gM' a = (gM' a - gM a) + gM a by abel, Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
    rw [e]; exact h1 a
  · obtain ⟨b, hb⟩ := hA a
    have e : Xo.univ.etaA (gA' a) = Xo.univ.etaA (gA a) := by
      rw [show gA' a = (gA' a - gA a) + gA a by abel, Xo.univ.etaA_add, hb, Xo.univ.etaA_ker, _root_.one_mul]
    rw [e]; exact h2 a

end GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
