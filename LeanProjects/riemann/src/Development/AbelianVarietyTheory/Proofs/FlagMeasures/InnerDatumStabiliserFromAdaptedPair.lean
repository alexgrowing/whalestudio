import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LsubGmapOfMapXspEq

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem onto_gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem onto_gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem onto_side {T : D.host.E} {A B : LFlag (VS D) D.R.rS T} {M : LV D} {G h : GV D}
    (hG : Adapt G A B) (hh : Adapt h B B)
    (hL : Lsub (Formalism.HermitianLatticesTheory.gmap h (Formalism.HermitianLatticesTheory.gmap G M)) B = Lsub (Formalism.HermitianLatticesTheory.gmap G M) B)
    (hs : ∀ σ, Adapt σ A A → Lsub (Formalism.HermitianLatticesTheory.gmap σ M) A = Lsub M A →
      ∃ n ∈ NRat A, Formalism.HermitianLatticesTheory.gmap (n * σ) M = M) :
    ∃ n ∈ NRat A, n * (G⁻¹ * h * G) ∈ Aut0 A M ∧
      ∀ x ∈ orth (VS D) (Xsp B), h x - (G * (n * (G⁻¹ * h * G)) * G⁻¹) x ∈ Xsp B := by
  have hGi : Adapt G⁻¹ B A := adapt_inv hG
  have hσ : Adapt (G⁻¹ * h * G) A A := by
    have h2 : Adapt (G⁻¹ * (h * G)) A A := adapt_mul (adapt_mul hG hh) hGi
    rwa [mul_assoc]
  have hGiso : G ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hG.1
  have hmap : (Xsp A).map (G : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := adapt_xsp hG

  have hinj : ∀ X Y : LV D, Formalism.HermitianLatticesTheory.gmap G X = Formalism.HermitianLatticesTheory.gmap G Y → X = Y := by
    intro X Y hXY
    have hXY' := congrArg (Formalism.HermitianLatticesTheory.gmap G⁻¹) hXY
    rwa [← onto_gmap_mul, ← onto_gmap_mul, inv_mul_cancel, onto_gmap_one, onto_gmap_one] at hXY'
  have e : G * (G⁻¹ * h * G) = h * G := by group
  have hLσ : Lsub (Formalism.HermitianLatticesTheory.gmap (G⁻¹ * h * G) M) A = Lsub M A := by
    apply hinj
    rw [← lsub_gmap_of_map_Xsp_eq D T A B G _ hGiso hmap, ← lsub_gmap_of_map_Xsp_eq D T A B G M hGiso hmap,
      ← onto_gmap_mul, e, onto_gmap_mul]
    exact hL
  obtain ⟨n, hn, hnM⟩ := hs _ hσ hLσ
  refine ⟨n, hn, ?_, ?_⟩
  · have hA : Adapt (n * (G⁻¹ * h * G)) A A := adapt_mul hσ (adapt_nrat hn)
    show Adapt _ A A ∧ Formalism.HermitianLatticesTheory.gmap _ M = M
    exact ⟨hA, hnM⟩
  · intro x hx

    obtain ⟨-, -, hm3⟩ := nrat_conj hG hn
    have hhx : h x ∈ orth (VS D) (Xsp B) := mem_of_map_eq (adapt_orth hh) hx
    have e' : G * (n * (G⁻¹ * h * G)) * G⁻¹ = G * n * G⁻¹ * h := by group
    rw [e']
    show h x - (G * n * G⁻¹) (h x) ∈ Xsp B
    rw [← neg_sub]
    exact neg_mem (hm3 (h x) hhx)

theorem stab_onto : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h hγ hlam hg hg' hΛ hs hs' hstab
  obtain ⟨hH0, hdat⟩ := hstab
  have hL1 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F = Lsub Λ F := congrArg Prod.fst hdat
  have hL2 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F' = Lsub Λ F' := congrArg (fun p => p.2.1) hdat
  obtain ⟨hhF, hhF'⟩ := frameAdaptedIsometry_of_fixing_both_frames hH0
  have hgγ : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have e2 : Formalism.HermitianLatticesTheory.gmap (g * γ) lam' = Λ := by rw [onto_gmap_mul, hlam, hΛ]
  obtain ⟨n, hn, hb1, hx1⟩ := onto_side (M := lam) hg hhF (by rw [← hΛ]; exact hL1) hs
  obtain ⟨n', hn', hb2, hx2⟩ := onto_side (M := lam') hgγ hhF' (by rw [e2]; exact hL2) hs'

  have key : n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹ = n * γ * n'⁻¹ := by group
  have e3 : g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹ =
      g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * (g * γ)⁻¹ := by group
  have hx2' : ∀ x ∈ orth (VS D) (Xsp F'),
      h x - (g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹) x ∈ Xsp F' := by
    rw [e3]; exact hx2
  have hI := (GlobalTheory.T.innerDatum_stable_iff_identifications_compatible D T T' F0 F F0' F' lam lam' Λ γ g h (n * (g⁻¹ * h * g))
    (n' * ((g * γ)⁻¹ * h * (g * γ))) hγ hlam hg hg' hΛ hb1 hb2 hH0 hx1 hx2').mp hdat
  have e4 : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) = 1 := by group
  have hF : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F := by rw [e4]; exact nrat_one F
  have hF' : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F' := by rw [e4]; exact nrat_one F'
  have hKey : KeyEq F0 F0' lam γ (n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹) :=
    ⟨⟨n, hn, n'⁻¹, nrat_inv hn', key⟩, hI⟩
  refine ⟨(n * (g⁻¹ * h * g), n' * ((g * γ)⁻¹ * h * (g * γ))), ?_, ?_⟩
  · exact ⟨hb1, hb2, hKey⟩
  · exact ⟨hH0, n, hn, n'⁻¹, nrat_inv hn', key, hF, hF'⟩

end GlobalTheory.StabCnt
