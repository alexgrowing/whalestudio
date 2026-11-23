import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormTies.LevelMove

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg.ChartInhab

attribute [local instance] Over.cartesianMonoidalCategory

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

theorem integral_of_levR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, levR (Xo := Xo) (c := c) g y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c gl T io
  letI := io.toAlgebra
  rintro y y' ⟨ρ, ν, -, -, hx, hu, pm, w, p₁, p₂, hw, hs⟩
    ⟨G, t', m1, m2, ⟨ub, b₁, b₂, b₃, b₄⟩, θ, hθ, w1, w2, σ, s1, θ2, r₁, r₂, i₁, i₂, hp, hg⟩
  obtain ⟨n, hn, w', hw', tri⟩ := exists_comp_rig ν m1 y'.x hx ⟨hw.1, hw.2.1⟩ r₁
  have g' := (isGen_iff w').1 hw'.1
  obtain ⟨s', hs'⟩ := thf_secUp g' Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', n, m2, ⟨ub, b₁, b₂, b₃, fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, hw', r₂, ?_, i₂, hp, ?_⟩
  · obtain ⟨u', h₁, h₂⟩ := b₄ τ i
    exact ⟨u', by rw [hn, ← Category.assoc, h₁, hu], h₂⟩
  · exact fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((hs' _ (𝟙 _) p i k hp.1 hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))
  · intro q e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB p
    obtain ⟨i, hi⟩ := exists_chart Xo.univ.t.PP.isLB (m1.φ p)
    have hp' : ν.φ (m1.φ p) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) hn).mp (mem_pull.1 hp)
    have eg : 𝟙 _ ≫ q = (𝟙 _ ≫ toGx m1) ≫ pm := by
      rw [Category.id_comp, Category.id_comp]
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [Category.assoc, p₂, e₁, hn, ← Category.assoc, toGx_snd]
      · rw [Category.assoc, p₁, e₂, toGx_fst]
    let W : (Gx y.x).Opens := (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
      ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
    have h₁ : W ≤ pm ⁻¹ᵁ (PPx y'.x).U (fun _ => J PUnit.unit) := fun z hz => Set.mem_iInter.2 fun _ =>
      (congrArg (fun u => u z ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) p₂).mpr (mem_pull.1 hz.1)
    have h₂ : W ≤ (PPx y.x).U (fun _ => i) := fun z hz => Set.mem_iInter.2 fun _ => hz.2
    have es : (𝟙 _ ≫ toGx m1) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ ≫ m1.φ := by
      rw [Category.assoc, toGx_snd]
    have hz₀ : (𝟙 _ ≫ m1.φ) p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i) :=
      ⟨mem_pull.2 hp', hi⟩
    have hz : (𝟙 _ ≫ toGx m1) p ∈ W :=
      (congrArg (fun u => u p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
        es).mpr hz₀
    have e := congrArg (gs (𝟙 _ ≫ toGx m1) p W) (hs (J PUnit.unit) i W rfl le_rfl h₁ h₂)
    rw [gs_appLE pm _ _ h₁ _ p hz, gs_mul _ p W hz, gs_appLE _ _ _ _ _ p hz, gs_res _ p h₂ hz, es,
      gs_unit _ p _ hz₀] at e
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ toGx m1 ⁻¹ᵁ (PPx y.x).U (fun _ => i) :=
      fun z hz => le_toGx m1 i (mem_pull.1 hz)
    have k₂ : gs (𝟙 _) p _ (s1.f (fun _ => i)) = gs (𝟙 _ ≫ toGx m1) p ((PPx y.x).U (fun _ => i)) (y.s.f (fun _ => i)) :=
      (congrArg (gs (𝟙 _) p _) (hg (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => i) le)).trans
        (gs_appLE (toGx m1) _ _ le (𝟙 _) p (mem_pull.2 hi) _)
    have k₃ := gs_of_isoMaps i₁ _ (𝟙 _) p i k hi hk
    rw [hs' _ (𝟙 _) p J k hp hk, gs_appLE q _ _ hJ (𝟙 _) p hp, eg, e, ← k₂, k₃,
      tri _ (𝟙 _) p _ i k hp' hi hk, Units.val_mul, _root_.mul_assoc]
    rfl

end GlobalTheory.FormTies.LevelMove
