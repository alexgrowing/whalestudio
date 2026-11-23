import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagRoot

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime]
  [CharZero O] {Z : GlobalTheory.Vert.Model O}

theorem isIso_genRes_smulHom {g : Γ(Z.X, ⊤)} {a : ℕ} (ha : 0 < a) (h : IsRootOfP p g a)
    (F : Z.X.Modules) : IsIso (Z.genRes.map (smulHom F g)) := by
  rw [VB.pullback_map_smulHom]
  have hp : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (Z.const (p : O))) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top Z.gen.ι _).le
        (Z.gen_le_basicOpen (natCast_ne_zero O p) x.2))
  obtain ⟨u, hu⟩ := h
  have hc : Z.const (p : O) = (p : Γ(Z.X, ⊤)) := map_natCast _ p
  rw [hc] at hp
  have hpow : IsUnit (((Scheme.Hom.appTop Z.gen.ι).hom g) ^ a) := by
    rw [← map_pow, hu, map_mul]
    exact (u.isUnit.map _).mul hp
  have hg := (isUnit_pow_iff ha.ne').1 hpow
  exact (isUnit_iff_isIso _).1 (hg.map (smulEnd _))

def pair {E E' : Z.X.Modules} {r : ℕ} (φ : Z.GenIso E E') (e : E' ≅ E) (g : Γ(Z.X, ⊤))
    (hg : ∀ F : Z.X.Modules, IsIso (Z.genRes.map (smulHom F g)))
    (hφ : φ.inv = Z.genRes.map (e.hom ≫ smulHom E g)) (fl : GlobalTheory.Vert.Flag E r) :
    GlobalTheory.Vert.Model.FlagPair φ r where
  fl := fl
  fl' := fl.ofIso e.symm
  gen i := @GlobalTheory.Vert.Model.GenIso.ofHom _ _ _ _ Z (fl.F i) (fl.F i) (smulHom (fl.F i) g) (hg (fl.F i))
  gen_ι i := by
    have := hg (fl.F i)
    change inv (Z.genRes.map (smulHom (fl.F i) g)) ≫ Z.genRes.map (fl.ι i ≫ e.inv) =
      Z.genRes.map (fl.ι i) ≫ φ.hom
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← Iso.comp_inv_eq, hφ,
      ← Functor.map_comp, ← Functor.map_comp, smulHom_comp, Category.assoc,
      Iso.inv_hom_id_assoc]

end GlobalTheory.FlagRoot

open GlobalTheory.FlagRoot in

theorem GlobalTheory.MixedLocalChains.exists_flagPair_of_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (E E' : Z.X.Modules) (r : ℕ) (φ : Z.GenIso E E') (e : E' ≅ E) (g : Γ(Z.X, ⊤)) (a : ℕ), 0 < a → IsRootOfP p g a → φ.inv = Z.genRes.map (e.hom ≫ smulHom E g) → ∀ fl : GlobalTheory.Vert.Flag E r, ∃ P : GlobalTheory.Vert.Model.FlagPair φ r, P.fl = fl ∧ ∀ i, ∃ ei : P.fl'.gr i ≅ P.fl.gr i, (P.grIso i).inv = Z.genRes.map (ei.hom ≫ smulHom (P.fl.gr i) g) := by
  intro O _ _ _ p _ _ _ Z E E' r φ e g a ha hg hφ fl
  have hiso := isIso_genRes_smulHom ha hg
  refine ⟨pair φ e g hiso hφ fl, rfl, fun i => ⟨Iso.refl _, ?_⟩⟩
  have h := (pair φ e g hiso hφ fl).π_grIso_hom i
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
  change Z.genRes.map (smulHom (fl.F i.succ) g) ≫ Z.genRes.map (fl.π i) =
    Z.genRes.map (fl.π i) ≫ _ at h
  have key : ∀ ψ : Z.genRes.obj (fl.gr i) ⟶ Z.genRes.obj (fl.gr i),
      Z.genRes.map (smulHom (fl.F i.succ) g) ≫ Z.genRes.map (fl.π i) =
        Z.genRes.map (fl.π i) ≫ ψ → ψ = Z.genRes.map (𝟙 (fl.gr i) ≫ smulHom (fl.gr i) g) := by
    intro ψ hψ
    rw [Category.id_comp, ← cancel_epi (Z.genRes.map (fl.π i)), ← Functor.map_comp,
      ← smulHom_comp, Functor.map_comp]
    exact hψ.symm
  exact key _ h
