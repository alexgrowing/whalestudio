import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.ModelIntFr

set_option maxHeartbeats 1000000 in

theorem exists_intFr_of_modelPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → (∀ a : c'.V W, a ≠ 0 → IsUnit (β a)) → ∀ (T₀ : CDVR) (α : A →+* T₀.V), Function.Injective α → ∀ yy₀ : Sp T₀.Fr ⟶ Xo'.XF c', yy₀ ≫ Y.j = spMap ((algebraMap T₀.V T₀.Fr).comp α) ≫ ξ → ∃ (T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr), (∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) ∧ Function.Injective i ∧ IsLocalHom i ∧ ∃ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = spMap iF ≫ yy₀ ≫ r) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hr A _ _ ξ β hξ hβ T₀ α _hα yy₀ hyy
  obtain ⟨io', hio'⟩ : ∃ io' : c'.F →+* T₀.Fr, spMap io' = yy₀ ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy₀ ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  let io : c.F →+* T₀.Fr := io'.comp (IntermediateField.inclusion hle).toRingHom
  let yt : Sp T₀.V ⟶ Y.X := spMap α ≫ ξ
  have hz : yy₀ ≫ Y.j = spMap (algebraMap T₀.V (FractionRing T₀.V)) ≫ yt := by
    rw [hyy]
    simp only [yt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T₀.V), Nonempty (SABMap G Y.t yt) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m2⟩⟩ : ∃ t' : SAB H (Sp T₀.Fr), Nonempty (SABMap t' G (spMap (algebraMap T₀.V T₀.Fr))) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T₀.V T₀.Fr)) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ :=
    GlobalTheory.DepthSum.thetaCore_trait E H Dw l' Xo' c' _ _ Y T₀.V yt yy₀ hz G m t' m2
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp T₀.Fr ⟶ Y.X) (_ : p = yy₀ ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t yy₀) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨m1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m3
  letI := io.toAlgebra
  have hx : (yy₀ ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c T₀.Fr := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc r, hr, Category.assoc,
      ← Category.assoc yy₀, ← hio']
    simp only [sOf, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨y, hy⟩ := GlobalTheory.AnyLevelFrame.exists_intFr T₀ io _ hx G t' m1 m2 θ hθ w2 σ' ⟨g2, r2⟩ hcl hgen
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  have key : io'.comp (c'.V W).subtype = ((algebraMap T₀.V T₀.Fr).comp α).comp β := by
    have e := congrArg (· ≫ Y.s) hyy
    simp only [Category.assoc, hjs, hξ] at e
    rw [← Category.assoc, ← hio'] at e
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at e
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hunit : ∀ b : c'.F, b ≠ 0 → b ∈ c'.V W → vV T₀.V (io' b) = 0 := by
    intro b hb hbV
    have e := RingHom.congr_fun key ⟨b, hbV⟩
    simp only [RingHom.comp_apply] at e
    have hu : IsUnit (α (β ⟨b, hbV⟩)) := (hβ _ fun h => hb (congrArg Subtype.val h)).map α
    have ev : valV T₀.V (algebraMap T₀.V T₀.Fr (α (β ⟨b, hbV⟩))) = 1 := by
      rw [valV, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu
    rw [show io' b = _ from e]
    simp [vV, ev]
  refine ⟨T₀, RingHom.id _, RingHom.id _, fun a => rfl, Function.injective_id, inferInstance, io, y, ?_, ?_⟩
  · intro a ha
    have hb : (IntermediateField.inclusion hle a : c'.F) ≠ 0 := by
      intro h; exact ha (by simpa using congrArg Subtype.val h)
    show vV T₀.V (io' (IntermediateField.inclusion hle a)) = 0
    rcases (c'.V W).mem_or_inv_mem (IntermediateField.inclusion hle a) with h | h
    · exact hunit _ hb h
    · have := hunit _ (inv_ne_zero hb) h
      rw [map_inv₀] at this
      unfold vV at this ⊢
      rw [map_inv₀, WithZero.log_inv] at this
      omega
  · show GlobalTheory.AllWt.ptF y.1 = spMap (RingHom.id T₀.Fr) ≫ yy₀ ≫ r
    rw [show spMap (RingHom.id T₀.Fr) = 𝟙 _ by simp [spMap], Category.id_comp]
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hr, ← Category.assoc, ← hio']
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.ModelIntFr
