import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

set_option backward.isDefEq.respectTransparency false

private theorem lift_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) (k : Type) [Field k]
    (w : Spec (.of k) ⟶ X) (h : (w ≫ f) (closedPoint k) = y) :
    ∃ w' : Spec (.of k) ⟶ f.fiber y, w' ≫ f.fiberι y = w := by
  subst h
  exact ⟨pullback.lift w _
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y (w ≫ f)).symm,
    pullback.lift_fst _ _ _⟩

theorem UpperTheory.points_generic_fibre_components :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.ShFam.Pad.NModel O) (k : Type) [Field k], Function.Injective (fun w : Σ C : Z.Comp, (Sp k ⟶ (Z.comp C).toBase.genFibre) => w.2 ≫ (Z.comp w.1).toBase.genFibreι ≫ Z.compι w.1) ∧ ∀ w : Sp k ⟶ Z.X, w (closedPoint k) ∈ Z.gen → ∃ (C : Z.Comp) (w' : Sp k ⟶ (Z.comp C).toBase.genFibre), w' ≫ (Z.comp C).toBase.genFibreι ≫ Z.compι C = w := by
  intro O _ _ _ Z k _
  refine ⟨?_, fun w hw => ?_⟩
  · rintro ⟨C, a⟩ ⟨C', b⟩ h
    dsimp only at h
    have hm (D : Z.Comp) (c : Sp k ⟶ (Z.comp D).toBase.genFibre) :
        (c ≫ (Z.comp D).toBase.genFibreι ≫ Z.compι D) (closedPoint k) ∈ D.opens :=
      ((c ≫ (Z.comp D).toBase.genFibreι) (closedPoint k)).2
    obtain rfl : C = C' := Subtype.ext
      (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents C.2 C'.2 (hm C a) (h ▸ hm C' b))
    haveI : Mono (Z.compι C) := inferInstanceAs (Mono C.opens.ι)
    haveI : Mono (Z.comp C).toBase.genFibreι :=
      inferInstanceAs (Mono ((Z.comp C).toBase.f.fiberι _))
    rw [(cancel_mono _).1 h]
  · obtain ⟨C, hC⟩ := Z.exists_comp (w (closedPoint k))
    have hr : Set.range w ⊆ Set.range C.opens.ι := by
      rintro _ ⟨x, rfl⟩
      obtain rfl : x = closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact ⟨⟨_, hC⟩, rfl⟩
    let v : Sp k ⟶ (Z.comp C).X := IsOpenImmersion.lift C.opens.ι w hr
    have hv : v ≫ Z.compι C = w := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w', hw'⟩ := lift_fiber (Z.comp C).toBase.f (genericPoint _) k v (by
      have e : v ≫ (Z.comp C).toBase.f = w ≫ Z.str := by
        rw [← hv, Category.assoc]; rfl
      rw [e]
      refine Eq.trans ?_ (genericPoint_eq_bot_of_affine (.of O)).symm
      exact PrimeSpectrum.ext (GlobalTheory.ShFam.Pad.NModel.mem_gen_iff_eq_bot.1 hw))
    exact ⟨C, w', by rw [← hv, ← hw', Category.assoc]; rfl⟩
