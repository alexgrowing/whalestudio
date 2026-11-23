import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem fibre_ext_of_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F]
    (t : Sp F ⟶ S) {n : ℕ} (hn : 2 ≤ n) (hF : (n : F) ≠ 0) {Y : Over S} [IsSeparated Y.hom]
    (f g : Over.mk t ⊗ P.A ⟶ Y)
    (h : ∀ (j : ℕ) (b : Over.mk t ⟶ P.A), b ^ n ^ j = 1 → lift (𝟙 _) b ≫ f = lift (𝟙 _) b ≫ g)
    (b : Over.mk t ⟶ P.A) : lift (𝟙 _) b ≫ f = lift (𝟙 _) b ≫ g := by
  obtain ⟨P', β, hβ, -, hm, -⟩ := hL.polBaseChange S _ t P
  have hD := PrimePowerTorsion.dense_torsion hL.ample hL.kerPow hL.irred F P' n hn hF
  have := polAV_isIntegral_of_isAlgClosed F P'
  let X : Over S := Over.mk (P'.A.hom ≫ t)
  have : AlgebraicGeometry.IsReduced X.left := inferInstanceAs (AlgebraicGeometry.IsReduced P'.A.left)
  let s : X ⟶ Over.mk t := Over.homMk P'.A.hom rfl
  let c : X ⟶ P.A := Over.homMk β hβ.w
  let m : X ⟶ Over.mk t ⊗ P.A := lift s c
  have hpt : ∀ (y : Sp F ⟶ P'.A.left) (b : Over.mk t ⟶ P.A), y ≫ P'.A.hom = 𝟙 _ → b.left = y ≫ β →
      (lift (𝟙 _) b).left = y ≫ m.left := fun y b hy hb => by
    let y' : Over.mk t ⟶ X := Over.homMk y (by
      change y ≫ P'.A.hom ≫ t = t
      rw [← Category.assoc, hy, Category.id_comp])
    have e : lift (𝟙 _) b = y' ≫ m := by
      rw [comp_lift]
      congr 1
      · exact Over.OverMorphism.ext hy.symm
      · exact Over.OverMorphism.ext hb
    rw [e]; rfl
  have key : m.left ≫ f.left = m.left ≫ g.left := by
    suffices IsDominant (equalizer.ι (m.left ≫ f.left) (m.left ≫ g.left)) from
      ext_of_isDominant_of_isSeparated Y.hom ((Over.w (m ≫ f)).trans (Over.w (m ≫ g)).symm)
        (equalizer.ι (m.left ≫ f.left) (m.left ≫ g.left)) (equalizer.condition _ _)
    refine ⟨Dense.mono (fun y hy => ?_) hD⟩
    obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
    let ρ : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp F))).hom ≫ t) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    let Φ : (𝟙_ (Over (Sp F)) ⟶ P'.A) →* (Over.mk t ⟶ P.A) :=
      MonoidHom.mk' (fun y => ρ ≫ toBase hβ.w y) (fun a b => by rw [hm, MonObj.comp_mul])
    have hΦ : (Φ x).left = x.left ≫ β := Category.id_comp _
    have e := hpt x.left (Φ x) (Over.w x) hΦ
    have h₁ := congrArg Over.Hom.left (h j (Φ x) (by rw [← map_pow, hx, map_one]))
    rw [Over.comp_left, Over.comp_left, e, Category.assoc, Category.assoc] at h₁
    exact ⟨equalizer.lift (f := m.left ≫ f.left) (g := m.left ≫ g.left) x.left h₁ q, by
      rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have hb : b.left ≫ P.A.hom = 𝟙 _ ≫ t := (Over.w b).trans (Category.id_comp _).symm
  have e := hpt (hβ.lift b.left (𝟙 _) hb) b (hβ.lift_snd _ _ _) (hβ.lift_fst _ _ _).symm
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, Over.comp_left, e, Category.assoc, Category.assoc, key]

theorem actV_compat_of_torsion : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB), GeoIso ν ν' I → ∀ (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (n : ℕ), n.Prime → (n : F) ≠ 0 → ∀ x : O, (∀ (j : ℕ) (b : N.A), b ^ n ^ j = 1 → I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b)) → ∀ b, I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b) := by
  intro hL R _ _ D D' F _ _ _ N N' ν ν' I ⟨φ, _, _, _, _, hφ, _⟩ O _ _ oa oa' n hn hF x h b
  have := D'.P.isAb.proper
  have e₁ : ∀ b, lift (𝟙 _) (ν.eA b) ≫ (_ ◁ oa.act x) ≫ φ.hom ≫ snd _ _ = ν'.eA (I.φ (actV ν oa x b)) := fun b => by
    rw [lift_whiskerLeft_assoc, ← ν.eA.apply_symm_apply (ν.eA b ≫ oa.act x), reassoc_of% hφ, lift_snd]
    rfl
  have e₂ : ∀ b, lift (𝟙 _) (ν.eA b) ≫ φ.hom ≫ snd _ _ ≫ oa'.act x = ν'.eA (actV ν' oa' x (I.φ b)) := fun b => by
    rw [reassoc_of% hφ, lift_snd_assoc, actV, MulEquiv.apply_symm_apply]
  refine ν'.eA.injective ?_
  rw [← e₁, ← e₂]
  refine fibre_ext_of_torsion hL D.P _ hn.two_le hF _ _ (fun j c hc => ?_) _
  obtain ⟨c, rfl⟩ := ν.eA.surjective c
  exact (e₁ c).trans ((congrArg ν'.eA (h j c (ν.eA.injective (by rw [map_pow, hc, map_one])))).trans (e₂ c).symm)

end GlobalTheory.Relabel
