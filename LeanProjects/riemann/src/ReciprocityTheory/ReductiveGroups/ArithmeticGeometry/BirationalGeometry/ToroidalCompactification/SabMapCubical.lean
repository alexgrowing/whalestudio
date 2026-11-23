import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cubical {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) (ψ : t₁.G ≅ t₂.G) [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ m₂.φ = m₁.φ) :
    (CubeMap.ofHom ψ.hom).IsPullCubical t₁.cub t₂.cub := by
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  have h3 : m₁.cm.F3 = (CubeMap.ofHom ψ.hom).F3 ≫ m₂.cm.F3 := hom_ext_triple _ fun i => by
    rw [cubeMap_comp_proj_three, Category.assoc, cubeMap_comp_proj_three]
    show _ = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ≫ _
    rw [← Category.assoc, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, Category.assoc, hφ']
  exact pullCubCancel _ _ _ _ _ _ m₂.cm (CubeMap.ofHom ψ.hom) m₁.cm _ _ _ t.cub t₂.cub t₁.cub hφ'.symm h3
    (by show m₁.cm.e = 𝟙 _ ≫ m₂.cm.e; rw [Category.id_comp, m₁.base, m₂.base]) m₂.lin m₁.lin

theorem sabMap_iso {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) {L₁ : RigLB t₁.G} {L₂ : RigLB t₂.G} (h₁ : L₁ = t₁.PP) (h₂ : L₂ = t₂.PP) :
    ∃ ψ : t₁.G ≅ t₂.G, IsMonHom ψ.hom ∧ ψ.hom.left ≫ m₂.φ = m₁.φ ∧
      (∀ x, t₁.act.act x ≫ ψ.hom = ψ.hom ≫ t₂.act.act x) ∧
      ∃ (he : eSec t₁.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec t₂.G) (wL : LB.Iso L₁.L (L₂.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec t₁.G) (fun _ => 1)) L₁.rig
          (rigPullOf ψ.hom.left (𝟙 _) he L₂.L L₂.rig) := by
  subst h₁ h₂
  obtain ⟨ψ, hψ, hφ⟩ := grpPullback_iso m₁.cart m₂.cart
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  refine ⟨ψ, hψ, hφ, fun x => ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, m₂.act, reassoc_of% hφ', hφ', m₁.act]
    · rw [Over.w, Over.w]
  · have := hψ
    obtain ⟨w, h₀, hg, hm⟩ := rigIso_congr rfl (CubeMap.ofHom ψ.hom) (sabMap_cubical m₁ m₂ ψ hφ) rfl rfl
    exact ⟨h₀, w, hg, hm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem ArcWit.uwIso {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W W' : ArcWit Y a I f u χ) :
    ∃ ψ : W.t.G ≅ W'.t.G, ψ.hom.left ≫ W'.m.φ = W.m.φ ∧ IsMonHom ψ.hom ∧
      (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y.m.φ) ∧
      ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G)
        (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
          (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) := by
  obtain ⟨ψ, hmon, hφ, hact, he, wL, hgen, hmaps⟩ :=
    sabMap_iso W.m W'.m (L₁ := W.P.U.LG) (L₂ := W'.P.U.LG) W.P.bundle W'.P.bundle
  refine ⟨ψ, hφ, hmon, hact, fun T g g₁ g₂ h1 h2 h3 => ?_, he, wL, hgen, hmaps⟩
  rw [hφ, h1]

  have hc := Y.m0.toSABMap.cart
  unfold IsGrpPullback at hc
  unfold SABMap.φ at h2
  rw [hc.1.hom_ext h2 h3]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
