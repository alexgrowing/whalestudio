import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfMkEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelModStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

theorem eq_of_gPt_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {p : ℕ} [Fact p.Prime]
    {y y' : Sp (OO p) ⟶ M.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' := by
  haveI := M.sep
  haveI : IsDominant (gPt p) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 fun x hx => by
      rw [show x = 0 from Subtype.ext hx]
      exact Submodule.zero_mem _⟩
  exact ext_of_isDominant_of_isSeparated M.s
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem val_part_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ (y' : Sp (OO p) ⟶ D.X.M.Z) (h' : y' ≫ D.q = c.y), y' (cPt p) = z₂ → ∀ yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y' h') yy' → D.Compat yy₁ yy' → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy' a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) = D.X.M.val (gPt p ≫ y') (U κ * GSum.part D z₁ z₂ a' κ) := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  obtain ⟨U, hU, hgal⟩ := GlobalTheory.T.galois_permutes_weightParts_up_to_roots g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  refine ⟨U, hU, ?_⟩
  intro p _ c yy₁ hl₁ y h hy yy hl hc y' h' hy' yy' hl' hc' a a' ν ν' κ ha ha' hcong
  haveI := D.fd
  haveI := D.gal
  obtain ⟨σ, s, hs, hys, hval⟩ := GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q (@GlobalTheory.IsNormalScheme.pred _ X₁.normal)
    (@GlobalTheory.IsNormalScheme.pred _ D.X.normal) D.fin D.gen
    (PadicAlgCl p) (gPt p ≫ y) (gPt p ≫ y') (by rw [Category.assoc, Category.assoc, h, h'])
  obtain rfl : y ≫ s = y' := eq_of_gPt_comp_eq D.X.M (by rw [← Category.assoc, hys])
  obtain ⟨b, hb, hfix, hperm⟩ := hgal σ
  have hlb := GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D σ s hs b hb p z₁ c y h h' yy hl
  have hcb : D.Compat yy₁ (yy.comp b.toAddMonoidHom) := fun x μ hx => by
    have := hc x μ hx
    rw [← hfix x] at this
    exact this
  have hyy : ∀ x, yy' x = yy (b x) := fun x =>
    DFunLike.congr_fun (GalLab.rigid D c yy₁ hl₁ (y ≫ s) h' _ yy' hlb hcb hl' hc') x
  have hk := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl).2
  have hk' := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl').2
  replace hk := hk.trans (congrArg (D.X.S.HH D.X.M) hy)
  replace hk' := hk'.trans (congrArg (D.X.S.HH D.X.M) hy')
  have hHH : ∀ x, b x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂ := fun x => by
    have h1 : b x ∈ yy.ker ↔ x ∈ yy'.ker := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy]
    rwa [hk, hk'] at h1
  rw [hval, hperm hHH,
    GlobalTheory.T.weightPart_depends_on_label_mod g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz p c y h hy yy hl a (b a') ν ν' κ ha
      ((hyy a').symm.trans ha') hcong]

end GlobalTheory.Poinc.GSum
