import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndCompStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def NormPin {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
    (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
      pt ≫ Formalism.L2.PjFree.gxFst y.x = (F.ex k Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
    MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

def Pinned (U : Formalism.L2.PjFree.Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
      (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)

def MarkRel (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) {A A' : Datum H} {Λ Λ' : Submodule (𝓞 E) (Fin r → E)}
    (φ : A.La ≃ₗ[𝓞 E] Λ) (φ' : A'.La ≃ₗ[𝓞 E] Λ') (t : Dw.La →ₗ[𝓞 E] A.La) (t' : Dw.La →ₗ[𝓞 E] A'.La)
    (γ : Dw.La →ₗ[𝓞 E] Dw.La) (δ : GL (Fin r) E) : Prop :=
  ∃ gam : A.La ≃ₗ[𝓞 E] A'.La,
    (∀ a, (φ' (gam a) : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E)) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ v, gam (t (γ a)) = t' a + l.M • v

def MoveMatch (U U' : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (k' : U'.Comp) {δ : GL (Fin r) E}
    (h : GlobalTheory.LevelCusp.IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)), FrMove ρ ν (U.un k x) y' →
    y'.x = (U'.un k' ⟨_, h.mem_dom x.2⟩).x ∧ y'.u = (U'.un k' ⟨_, h.mem_dom x.2⟩).u

theorem MarkRel.div {A A' : Datum H} {Λ Λ' : Submodule (𝓞 E) (Fin r → E)}
    {φ : A.La ≃ₗ[𝓞 E] Λ} {φ' : A'.La ≃ₗ[𝓞 E] Λ'} {t : Dw.La →ₗ[𝓞 E] A.La} {t' : Dw.La →ₗ[𝓞 E] A'.La}
    {γ : Dw.La →ₗ[𝓞 E] Dw.La} {δ δ' : GL (Fin r) E} (h : MarkRel l φ φ' t t' γ δ) (h' : MarkRel l φ φ' t t' γ δ') :
    MarkRel l φ' φ' t' t' LinearMap.id (δ' * δ⁻¹) := by
  obtain ⟨g, hg, hm⟩ := h
  obtain ⟨g', hg', hm'⟩ := h'
  refine ⟨g.symm.trans g', fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨b, rfl⟩ := g.surjective a
    rw [LinearEquiv.trans_apply, g.symm_apply_apply, hg', hg, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · obtain ⟨v, hv⟩ := hm a ha
    obtain ⟨v', hv'⟩ := hm' a ha
    refine ⟨v' - g' (g.symm v), ?_⟩
    have : t' a = g (t (γ a)) - l.M • v := by rw [hv, add_sub_cancel_right]
    rw [LinearMap.id_apply, LinearEquiv.trans_apply]
    conv_lhs => rw [this]
    rw [map_sub, map_sub, g.symm_apply_apply, hv', map_nsmul, map_nsmul, smul_sub, add_sub_assoc]

theorem exists_frBor_gen (z y : FrPt Xo c (CAt σ)) (hx : y.x = z.x) (hu : y.u = z.u) :
    ∃ t₀ : (CAt σ)ˣ, FrBor (fun i => Option.elim i t₀ (fun _ => 1)) z y := by
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 hx
  refine ⟨a, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hbc⟩⟩
  rw [hu]
  exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) z z z).1.2.1 τ i

theorem exists_pinned_of_isUnf {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Pinned U e F ik φ ∧
      ∀ k (x : (U.X k).dom) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)),
        (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) →
        GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → NormPin F (ik k) Pm (U.un k x) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, h1, h2⟩ := hU
  refine ⟨g, e, F, ik, φ, ⟨h1, fun k x => ?_⟩, fun k x Pm hPm hx => ?_⟩
  · obtain ⟨P, a, b, c, d, -⟩ := h2 k x
    exact ⟨P, a, b, c, d⟩
  · obtain ⟨P, a, -, -, -, d⟩ := h2 k x
    obtain rfl : Pm = P := AddMonoidHom.ext fun v => funext fun j => (hPm v j).trans (a v j).symm
    exact d hx

end GlobalTheory.GeoLevel
