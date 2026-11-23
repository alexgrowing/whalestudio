import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridge
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem mem_transKer_of_geometric
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G)
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) :
    a ∈ transKer Xo.univ.t.G Ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
    show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  have : IsReduced (Over.mk x).left := (affine_isReduced_iff _).2 ‹IsReduced T›
  have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
  have hT : ∀ {Y : Scheme.{0}} (y : Y ⟶ Xo.X) (c : Over.mk y ⟶ Xo.univ.t.G),
      (translT Xo.univ.t.G c).left ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y) Xo.univ.t.G).left :=
    fun y c => by rw [← Over.comp_left, translT, lift_fst]
  rw [mem_transKer]
  refine hom_ext_of_geometric_points (Gx x) (Gx x') (Sp T) (fst (Over.mk x') Xo.univ.t.G).left _ _
    (by rw [Category.assoc, hΨ, hT]) fun Ω _ _ q => ?_
  let φ : CommRingCat.of T ⟶ CommRingCat.of Ω := Spec.preimage (q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
  let χ : T →+* Ω := φ.hom
  have hχ : spMap χ = q ≫ (fst (Over.mk x) Xo.univ.t.G).left := Spec.map_preimage _
  obtain ⟨Ψ₁, pm, pm', hp, hp', hc, h1⟩ :=
    exists_isFib χ (x₁ := spMap χ ≫ x) (x₁' := spMap χ ≫ x') rfl rfl Ψ hΨ
  obtain ⟨b, hb, hba⟩ := hk Ω χ _ _ Ψ₁ ⟨pm, pm', hp, hp', hc, h1⟩
  let q₁ : Sp Ω ⟶ Gx (spMap χ ≫ x) := ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift (spMap χ ≫ x) (𝟙 _)
    (q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_w x, ← Category.assoc, ← hχ, Category.id_comp])
  have hq₁ : q₁ ≫ pm = q := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_ext x _ _ ?_ ?_
    · rw [Category.assoc, hp.2.2, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_fst, Category.id_comp, hχ]
    · rw [Category.assoc, hp.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_snd]
  let pmO : Over.mk (spMap χ ≫ x) ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm (by
    rw [← Over.w (fst (Over.mk x) Xo.univ.t.G), ← Over.w (fst (Over.mk (spMap χ ≫ x)) Xo.univ.t.G),
      ← Category.assoc, hp.2.2]
    rfl)
  let φo : Over.mk (spMap χ ≫ x) ⟶ Over.mk x := Over.homMk (spMap χ) rfl
  have hb' : b = φo ≫ a := Over.OverMorphism.ext hba
  have hpf : pmO ≫ fst (Over.mk x) Xo.univ.t.G = fst _ Xo.univ.t.G ≫ φo := Over.OverMorphism.ext hp.2.2
  have hps : pmO ≫ snd (Over.mk x) Xo.univ.t.G = snd _ Xo.univ.t.G := Over.OverMorphism.ext hp.2.1
  have tp : ∀ {Y : Over Xo.X} (c : Y ⟶ Xo.univ.t.G),
      translPt Xo.univ.t.G c = (fst Y Xo.univ.t.G ≫ c) * snd Y Xo.univ.t.G := fun _ => rfl
  have key : translT Xo.univ.t.G b ≫ pmO = pmO ≫ translT Xo.univ.t.G a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, translT, lift_fst, lift_fst_assoc, hpf]
    · simp only [Category.assoc, translT, lift_snd, lift_snd_assoc, hps, tp, MonObj.comp_mul, reassoc_of% hpf, hb']
  have keyL : (translT Xo.univ.t.G b).left ≫ pm = pm ≫ (translT Xo.univ.t.G a).left :=
    congrArg (fun f => f.left) key
  rw [← hq₁, Category.assoc, Category.assoc, ← reassoc_of% keyL, ← hc, reassoc_of% (mem_transKer.1 hb)]

end GlobalTheory.HeckeEx
