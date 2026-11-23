import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsTripleWithcharpolyFrob

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem frobMatch_Tgl_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hχ : IsChars C art ρ) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (Tgl i s)
      (((D.R.r : ℝ) / 2 + -((D.R.t : ℝ) / 2)) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  have hk : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)
  have hμ := mu_unr C (jIdx s) hk fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  obtain ⟨h1, h2⟩ := twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv
  obtain ⟨n, hn⟩ := hχ.chiS
  have h3 := hn.frob ha (Or.inl hl) (fun x hx => by
    rw [blockChar, GlobalTheory.GalChar.block_loc (C.isEta.unr P) hx]; exact hμ x hx) hB hg
  have h4 := h.charpoly_frob ha hl hk hB hg
  rw [← Matrix.charpoly_map] at h4
  have h5 : (Tmat i s g).map ρ.toC = (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) •
      ((D.ntw.rhoS i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map ρ.toC := by
    ext x y
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_units_inv]
    rw [ρ.toC_apply ((chiS i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), h3, inv_inv]
  have h6 := charpoly_smul_of_prod _ (((D.naut.frobEig (D.naut.locG π P)).map fun a =>
    a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹))
    (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) (by rw [h4, Multiset.map_map]; rfl)
  rw [← h5, Matrix.charpoly_map] at h6
  rw [Tgl_coe]
  refine h6.trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, blockChar_val, cpow_add_real, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv,
    Units.val_inv_eq_inv_val]
  congr 2
  have := (C.eta.val P).ne_zero
  have := cpow_ne_zero' P (((D.R.t : ℝ) / 2 : ℝ) : ℂ)
  field_simp
end Triple
end GlobalTheory.TripleLocal
end
end
