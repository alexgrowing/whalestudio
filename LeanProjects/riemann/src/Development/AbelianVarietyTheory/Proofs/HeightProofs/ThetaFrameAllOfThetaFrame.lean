import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaFramePullback

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ThetaFrameCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaFramePullback

section Scalars

variable {X Y : Scheme.{0}}

theorem resG_resG {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_resG_top (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : Γ(X, ⊤)) :
    (g.appLE U V h).hom (resG X le_top a) = resG Y le_top (g.appTop.hom a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]; rfl

theorem appTop_appTop {Z : Scheme.{0}} (g : Z ⟶ Y) (p : Y ⟶ X) (a : Γ(X, ⊤)) :
    g.appTop.hom (p.appTop.hom a) = (g ≫ p).appTop.hom a := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem spMap_appTop_toΓ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    (spMap f).appTop.hom (toΓ R a) = toΓ S (f a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

def mulSec {L : LB X} (a : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top a * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j]
    exact (congrArg (· * _) ((resG_resG _ _ a).trans (resG_resG _ _ a).symm)).trans (mul_left_comm _ _ _)

theorem isoMaps_mulSec {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (a : Γ(X, ⊤)) : IsoMaps w (mulSec a s) (mulSec a s') := by
  intro i k
  show resG X _ (resG X le_top a * s'.f i) = _ * resG X _ (resG X le_top a * s.f k)
  rw [map_mul, map_mul, h i k]
  exact (congrArg (· * _) ((resG_resG _ _ a).trans (resG_resG _ _ a).symm)).trans (mul_left_comm _ _ _)

end Scalars

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) :=
  mulSec ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a)) s

theorem scalSec_f {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    (scalSec x a s).f i = scal x a i * s.f i := rfl

theorem exists_unit_of_isGenAt {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {s s₀ : LB.Sec (PPx x)}
    (hs : IsGenAt x s) (h₀ : IsGenAt x s₀) : ∃ u : Sˣ, ∀ i, s.f i = scal x (u : S) i * s₀.f i := by
  obtain ⟨a, ha, -⟩ := h₀ s
  obtain ⟨b, hb, -⟩ := hs s₀
  have h1 : b * a = 1 := (h₀ s₀).unique
    (fun i => by rw [scal_mul, _root_.mul_assoc, ← ha i, ← hb i]) (fun i => by rw [scal_one, _root_.one_mul])
  exact ⟨⟨a, b, (_root_.mul_comm a b).trans h1, h1⟩, ha⟩

theorem isGenAt_scalSec {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {s : LB.Sec (PPx x)} (hs : IsGenAt x s)
    (u : Sˣ) : IsGenAt x (scalSec x (u : S) s) := by
  intro s'
  obtain ⟨a, ha, hu⟩ := hs s'
  refine ⟨a * (u⁻¹ : Sˣ), fun i => ?_, fun b hb => ?_⟩
  · rw [scalSec_f, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right, ha i]
  · refine (Units.eq_mul_inv_iff_mul_eq u).2 (hu _ fun i => ?_)
    rw [hb i, scalSec_f, ← _root_.mul_assoc, ← scal_mul]

theorem exists_unit_of_isGenOver {V : Type} [CommRing V] {G : SAB H (Sp V)} {θ θ₀ : LB.Sec G.PP.L}
    (h : IsGenOver G θ) (h₀ : IsGenOver G θ₀) :
    ∃ u : Vˣ, ∀ i, θ.f i = resG G.G.left le_top (G.G.hom.appTop.hom (toΓ V (u : V))) * θ₀.f i := by
  obtain ⟨a, ha, -⟩ := h₀ θ
  obtain ⟨b, hb, -⟩ := h θ₀
  have h1 : b * a = 1 := (h₀ θ₀).unique
    (fun i => by rw [map_mul, map_mul, map_mul, _root_.mul_assoc, ← ha i, ← hb i])
    (fun i => by rw [map_one, map_one, map_one, _root_.one_mul])
  exact ⟨⟨a, b, (_root_.mul_comm a b).trans h1, h1⟩, ha⟩

variable {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G : SAB H (Sp T.V)}

theorem genMatch_scal {t' : SAB H (Sp T.Fr)} {m₁ : SABMap t' Xo.univ.t x}
    {m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))} {θ θ' : LB.Sec G.PP.L} {s : LB.Sec (PPx x)}
    (h : GenMatch m₁ m₂ θ s) (a : T.V)
    (ha : ∀ i, θ'.f i = resG G.G.left le_top (G.G.hom.appTop.hom (toΓ T.V a)) * θ.f i) :
    GenMatch m₁ m₂ θ' (scalSec x (algebraMap T.V T.Fr a) s) := by
  obtain ⟨w₁, w₂, σ, s₁, θ₂, r₁, r₂, i₁, i₂, hp, hg⟩ := h
  let b : Γ(t'.G.left, ⊤) := t'.G.hom.appTop.hom (toΓ T.Fr (algebraMap T.V T.Fr a))
  refine ⟨w₁, w₂, mulSec b σ, mulSec b s₁, mulSec b θ₂, r₁, r₂, isoMaps_mulSec i₁ b, isoMaps_mulSec i₂ b,
    fun j hj => ?_, fun g e₁ e₂ j hj => ?_⟩
  · have e : m₂.φ.appTop.hom (G.G.hom.appTop.hom (toΓ T.V a)) = b := by
      rw [appTop_appTop, m₂.cart.1.w, ← appTop_appTop, spMap_appTop_toΓ]
    rw [ha, map_mul, appLE_resG_top, e, ← hp j hj]
    rfl
  · have e : g.appTop.hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom
        (toΓ T.Fr (algebraMap T.V T.Fr a))) = b := by
      rw [appTop_appTop, e₂]
    show resG _ le_top b * s₁.f j = (g.appLE _ _ hj).hom (resG _ le_top _ * s.f _)
    rw [map_mul, appLE_resG_top, e, ← hg g e₁ e₂ j hj]

variable (x G) in

def FrameGiven : Prop :=
  ∀ (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (s₀ : LB.Sec (PPx x)), IsGenAt x s₀ →
    ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx x)), IsGenOver G θ ∧ GenMatch m₁ m₂ θ s ∧ IsGenAt x s ∧
      ∃ a : T.Frˣ, ∀ i, s.f i = scal x (a : T.Fr) i * s₀.f i

variable (x G) in

def FrameUniform : Prop :=
  ∃ θ : LB.Sec G.PP.L, IsGenOver G θ ∧
    ∀ (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      ∃ s : LB.Sec (PPx x), GenMatch m₁ m₂ θ s ∧ IsGenAt x s ∧
        ∀ s₀ : LB.Sec (PPx x), IsGenAt x s₀ → ∃ u : T.Frˣ, ∀ i, s.f i = scal x (u : T.Fr) i * s₀.f i

theorem FrameUniform.frameGiven (h : FrameUniform x G) : FrameGiven x G := by
  obtain ⟨θ, hθ, h⟩ := h
  intro t' m₁ m₂ s₀ h₀
  obtain ⟨s, hm, hs, hu⟩ := h t' m₁ m₂
  exact ⟨θ, s, hθ, hm, hs, hu s₀ h₀⟩

theorem frame_iff {t₀ : SAB H (Sp T.Fr)} (n₁ : SABMap t₀ Xo.univ.t x)
    (n₂ : SABMap t₀ G (spMap (algebraMap T.V T.Fr))) :
    FrameUniform x G ↔ FrameGiven x G ∧ ∃ s₀, IsGenAt x s₀ := by
  refine ⟨fun h => ⟨h.frameGiven, ?_⟩, fun ⟨h, s₀, h₀⟩ => ?_⟩
  · obtain ⟨θ, -, h⟩ := h
    obtain ⟨s, -, hs, -⟩ := h t₀ n₁ n₂
    exact ⟨s, hs⟩
  · obtain ⟨θ, -, hθ, -⟩ := h t₀ n₁ n₂ s₀ h₀
    refine ⟨θ, hθ, fun t' m₁ m₂ => ?_⟩
    obtain ⟨θ', s, hθ', hm, hs, -⟩ := h t' m₁ m₂ s₀ h₀
    obtain ⟨u, hu⟩ := exists_unit_of_isGenOver hθ hθ'
    have hs' := isGenAt_scalSec hs (Units.map (algebraMap T.V T.Fr).toMonoidHom u)
    exact ⟨_, genMatch_scal hm u hu, hs', fun s₁ h₁ => exists_unit_of_isGenAt hs' h₁⟩

variable {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_coeffMap {S : Type} [CommRing S] (z : Sp S ⟶ Xo.XF c) :
    ∃ io : c.F →+* S, z ≫ pullback.snd _ _ = spMap io :=
  ⟨(Spec.preimage (z ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩

theorem exists_tied (Y : Model Xo c β) {ξ : Sp T.V ⟶ Y.X} {z : Sp T.Fr ⟶ Xo.XF c}
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ ξ) (mG : SABMap G Y.t ξ) (t' : SAB H (Sp T.Fr))
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) :
    ∃ m₁ : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _), Tied Y z mG m₁ m₂ := by
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ ξ (spMap (algebraMap T.V T.Fr)) mG m₂
  have cancel : ∀ (p : Sp T.Fr ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro p hp n; subst hp
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨m', hm'⟩ := cancel _ hz.symm n
  obtain ⟨m₁, h₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  exact ⟨m₁, m'.φ, m'.cart.1.w, h₁.symm, hm'.symm.trans hn⟩

end Point

def GenFibreAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), GenFibreSt Xo c

def ThetaFrameAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), ThetaFrameSt Xo c

def FibreGenerator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (_ : SABMap G Y.t ξ), ∃ s₀, IsGenAt x s₀

theorem genericFibre_iff : GenericFibre ↔ GenFibreAll := by
  constructor
  · intro h E _ _ _ H Dw l Xo c T io O _ β Y yt z hz _ G m
    obtain ⟨⟨t', ⟨m₂⟩⟩, h₂⟩ := h E H Dw l Xo c O β Y T yt z _ ⟨hz, rfl⟩ G m
    obtain ⟨m₁, -⟩ := h₂ t' m₂
    exact ⟨t', m₁, m₂, trivial⟩
  · rintro h E _ _ _ H Dw l Xo c O _ β Y T ξ z x ⟨hz, rfl⟩ G mG
    obtain ⟨io, hio⟩ := exists_coeffMap z
    obtain ⟨t', -, m₂, -⟩ := h E H Dw l Xo c T io O β Y ξ z hz hio G mG
    exact ⟨⟨t', ⟨m₂⟩⟩, exists_tied Y hz mG⟩

theorem thetaFrameAll_of_thetaFrame (h : ThetaFrame) : ThetaFrameAll := by
  intro E _ _ _ H Dw l Xo c T io O _ β Y hP yt z hz _ G m
  exact FrameUniform.frameGiven (h E H Dw l Xo c O β Y hP T yt z _ ⟨hz, rfl⟩ G m)

theorem thetaFrame_iff (hG : GenFibreAll) : ThetaFrame ↔ ThetaFrameAll ∧ FibreGenerator := by
  refine ⟨fun h => ⟨thetaFrameAll_of_thetaFrame h, ?_⟩, fun ⟨h, h₀⟩ => ?_⟩
  · rintro E _ _ _ H Dw l Xo c O _ β Y hP T ξ z x ⟨hz, rfl⟩ G mG
    obtain ⟨io, hio⟩ := exists_coeffMap z
    obtain ⟨t', m₁, m₂, -⟩ := hG E H Dw l Xo c T io O β Y ξ z hz hio G mG
    exact ((frame_iff m₁ m₂).1 (h E H Dw l Xo c O β Y hP T ξ z _ ⟨hz, rfl⟩ G mG)).2
  · rintro E _ _ _ H Dw l Xo c O _ β Y hP T ξ z x ⟨hz, rfl⟩ G mG
    obtain ⟨io, hio⟩ := exists_coeffMap z
    obtain ⟨t', m₁, m₂, -⟩ := hG E H Dw l Xo c T io O β Y ξ z hz hio G mG
    exact (frame_iff m₁ m₂).2 ⟨h E H Dw l Xo c T io O β Y hP ξ z hz hio G mG,
      h₀ E H Dw l Xo c O β Y hP T ξ z _ ⟨hz, rfl⟩ G mG⟩

theorem claim_iff : Claim ↔ (ThetaFrameAll ∧ GenFibreAll) ∧ FibreGenerator := by
  refine ⟨fun ⟨h, hG⟩ => ?_, fun ⟨⟨h, hG⟩, h₀⟩ => ⟨(thetaFrame_iff hG).2 ⟨h, h₀⟩, genericFibre_iff.2 hG⟩⟩
  have hG' := genericFibre_iff.1 hG
  exact ⟨⟨((thetaFrame_iff hG').1 h).1, hG'⟩, ((thetaFrame_iff hG').1 h).2⟩

theorem fibreGenerator : FibreGenerator :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => Formalism.L2.Pj.gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x

theorem typings_iff : Claim ↔ ThetaFrameAll ∧ GenFibreAll := claim_iff.trans (and_iff_left fibreGenerator)

end GlobalTheory.ThetaFrameCompare
