import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalToGlobal.Columns.AdelicLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BaseCosetPt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem lat_eq_of_carries {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N₁ N₂ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : Submodule.IsLattice E N₁) (h₂ : Submodule.IsLattice E N₂)
    (c₁ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₁) (c₂ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₂) :
    N₁ = N₂ := by
  have key : ∀ N : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E N → ∀ x : Fin n → E,
      (x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N) := by
    intro N hN x
    have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [key N₁ h₁, key N₂ h₂, c₁, c₂]

end Gen

section Pt

open Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {w : Sp X.E (R.N j)}
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N) : (frsF sel mu p P).symm w ∈ stdAt X.E (R.N j) P.1 := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).1 (by simpa using hw)

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {x : Sp X.E (R.N j)}
    (hx : x ∈ stdAt X.E (R.N j) P.1) : frsF sel mu p P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).2 hx

theorem cosetIn_eq_of {u : Pr.Word} {j : ℕ} (r : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : Sp X.E (R.N j)) (e : rowSG Pr sel mu → ℤ) (he : e P = 0)
    (hY : r.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) r.1.1.deco.1.N e}) :
    cosetIn r P = {z | z - (frsF sel mu r.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1} := by
  classical
  ext z
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq, hY]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : y' - y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal r.1.1.deco.1.N := by
      have := (Submodule.mem_iInf _).1 hy' P
      simpa [Submodule.mem_comap, he] using this
    have := add_mem hz (frsF_symm_mem r.1.1 P h1)
    rwa [map_sub, sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, by simp, hz⟩

end Pt

end GlobalTheory.BaseCosetPt

namespace GlobalTheory.BaseCosetPt

open Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

end GlobalTheory.BaseCosetPt
