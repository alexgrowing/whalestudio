import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffine
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsAdmissibleKernelScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_etale_cover_lists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk), ∃ (T' : Type) (_ : CommRing T') (_ : Algebra T T') (n : ℕ) (σ : Fin n → (Sp T' ⟶ Xo.univ.t.G.left)), Algebra.Etale T T' ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap T T')) ∧ (∀ j, σ j ≫ Xo.univ.t.G.hom = spMap (algebraMap T T') ≫ h ≫ Z.π₁) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T' →+* Ω) (x₁ : Sp Ω ⟶ Xo.X) (C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)), Z.Carries (spMap χ ≫ spMap (algebraMap T T') ≫ h) x₁ C → ∃ e : Fin n ≃ C, ∀ j, (e j).1.left = spMap χ ≫ σ j := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h
  haveI := Z.isReduced
  obtain ⟨S', π, o', m, τ, hfin, het, hsur, hL⟩ :=
    GlobalTheory.exists_cover_lists_heckeSet E H Dw l P p i Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.K hA Z.et Z.hecke
  obtain ⟨B, _, _, h', -, hBet, hh', hBsur, -⟩ := exists_finiteEtale_algebra_pullback Z.Hk S' π hfin het T h
  have wτ : ∀ a, (τ a).left ≫ o'.t.G.hom = 𝟙 S' := fun a => by simpa using Over.w (τ a)
  have wm : m.toSABMap.φ ≫ Z.o₁.t.G.hom = o'.t.G.hom ≫ π := m.cart.1.w
  have wm₁ : Z.m₁.toSABMap.φ ≫ Xo.univ.t.G.hom = Z.o₁.t.G.hom ≫ Z.π₁ := Z.m₁.cart.1.w
  have key : ∀ (X : Scheme.{0}) (w : X ⟶ S') a, (w ≫ (τ a).left ≫ m.toSABMap.φ) ≫ Z.o₁.t.G.hom = w ≫ π := by
    intro X w a
    rw [Category.assoc, Category.assoc, wm, reassoc_of% (wτ a)]; simp
  refine ⟨B, inferInstance, inferInstance, _, fun j => h' ≫ (τ j).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ, hBet,
    hBsur hsur, fun j => ?_, ?_⟩
  · have := congrArg (· ≫ Z.π₁) (key _ h' j)
    simp only [Category.assoc] at this
    simp only [Category.assoc, wm₁, this, reassoc_of% hh']
  intro Ω _ _ χ x₁ C hC
  obtain ⟨hz, hC⟩ := hC
  subst hz
  have hw' : (spMap χ ≫ h') ≫ π = spMap χ ≫ spMap (algebraMap T B) ≫ h := by rw [Category.assoc, hh']
  have hq : ∀ a, (spMap χ ≫ h' ≫ (τ a).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      (spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁ := fun a => by
    have := congrArg (· ≫ Z.π₁) (key _ (spMap χ ≫ h') a)
    simp only [Category.assoc] at this hw'
    simp only [Category.assoc, wm₁, this, reassoc_of% hw']
  have mem : ∀ a, (Over.homMk (spMap χ ≫ h' ≫ (τ a).left ≫ m.toSABMap.φ ≫ Z.m₁.toSABMap.φ) (hq a) :
      Over.mk ((spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁) ⟶ Xo.univ.t.G) ∈ C := by
    intro a
    have hu := (key _ (spMap χ ≫ h') a).trans hw'
    refine (hC (Over.homMk ((spMap χ ≫ h') ≫ (τ a).left ≫ m.toSABMap.φ) hu) _ (by simp)).1 ?_
    rintro _ ⟨q, rfl⟩
    have h1 : ((spMap χ ≫ h') ≫ (τ a).left) q ∈ m.toSABMap.φ ⁻¹' Z.K := by
      rw [hL.2.1]
      exact Set.mem_iUnion.2 ⟨a, _, (Scheme.Hom.comp_apply _ _ _).symm⟩
    simpa [Scheme.Hom.comp_apply] using h1
  let f : Fin _ → C := fun a => ⟨_, mem a⟩
  have inj : Function.Injective f := by
    intro a b hab
    have e := congrArg (fun z : C => z.1.left) hab
    simp only [f, Over.homMk_left] at e
    refine hL.2.2 Ω (spMap χ ≫ h') ?_
    refine m.cart.1.hom_ext ?_ (by simp only [Category.assoc, wτ, Category.comp_id])
    refine Z.m₁.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simpa only [Category.assoc] using (key _ (spMap χ ≫ h') a).trans (key _ (spMap χ ≫ h') b).symm
  have surj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    have vw : v.left ≫ Xo.univ.t.G.hom = (spMap χ ≫ spMap (algebraMap T B) ≫ h) ≫ Z.π₁ := Over.w v
    let u₀ : Sp Ω ⟶ Z.o₁.t.G.left := Z.m₁.cart.1.lift v.left (spMap χ ≫ spMap (algebraMap T B) ≫ h) vw
    have u₀₁ : u₀ ≫ Z.m₁.toSABMap.φ = v.left := Z.m₁.cart.1.lift_fst _ _ _
    have u₀₂ : u₀ ≫ Z.o₁.t.G.hom = spMap χ ≫ spMap (algebraMap T B) ≫ h := Z.m₁.cart.1.lift_snd _ _ _
    have rK : Set.range u₀ ⊆ Z.K := (hC (Over.homMk u₀ u₀₂) v u₀₁.symm).2 hv
    let u₁ : Sp Ω ⟶ o'.t.G.left := m.cart.1.lift u₀ (spMap χ ≫ h') (u₀₂.trans hw'.symm)
    have u₁₁ : u₁ ≫ m.toSABMap.φ = u₀ := m.cart.1.lift_fst _ _ _
    have u₁₂ : u₁ ≫ o'.t.G.hom = spMap χ ≫ h' := m.cart.1.lift_snd _ _ _
    have q : Sp Ω := IsLocalRing.closedPoint Ω
    have hq1 : u₁ q ∈ m.toSABMap.φ ⁻¹' Z.K := by
      show (u₁ ≫ m.toSABMap.φ) q ∈ Z.K
      rw [u₁₁]; exact rK ⟨q, rfl⟩
    rw [hL.2.1] at hq1
    obtain ⟨a, g, hg⟩ := Set.mem_iUnion.1 hq1
    have := o'.proper
    have : IsClosedImmersion (τ a).left := by
      have hw : (τ a).left ≫ o'.t.G.hom = 𝟙 _ := Over.w _
      have : IsClosedImmersion ((τ a).left ≫ o'.t.G.hom) := by rw [hw]; infer_instance
      exact IsClosedImmersion.of_comp _ o'.t.G.hom
    obtain ⟨c, hc⟩ := GlobalTheory.HkFam.IndexZero.lift_closed (T := Sp Ω) u₁ (τ a).left (by
      rintro _ ⟨q', rfl⟩
      rw [Subsingleton.elim q' q]
      exact ⟨g, hg⟩)
    have hc' : c = spMap χ ≫ h' := by
      rw [← u₁₂, ← hc, Category.assoc, wτ]; simp
    refine ⟨a, Subtype.ext (Over.OverMorphism.ext ?_)⟩
    simp only [f, Over.homMk_left]
    rw [← u₀₁, ← u₁₁, ← hc, hc']
    simp only [Category.assoc]
  exact ⟨(Equiv.ofBijective f ⟨inj, surj⟩), fun j => rfl⟩

end GlobalTheory.HeckeEx
