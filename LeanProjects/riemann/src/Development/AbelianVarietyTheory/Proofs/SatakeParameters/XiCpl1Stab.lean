import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.StabLaw

section
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem rhoS_one (i : ℕ) (P : rowSG Pr sel mu) : rhoS Ch sel mu i P 1 = 1 := by
  unfold rhoS LocE.unitV
  simp [TopStep.reduction_one₂]
end

theorem xiCpl1_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (al : L.β m2) (b : L.β (m2 + 1)) (p : ChPt (R := R) sel mu u m2) (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (a : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)), Y ∈ ybSet sel mu cst p'.deco.1.N → a • p' = p' → (fun v => a.1.1 v) '' Y = Y → ∀ x, XiCpl1 Ch sel mu cst L m2 al p p' Y (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (m2 + 1) b).chr a.2.1 * (L.levQ (m2 + 1) b).chr a.2.2 : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u al b p p' Y a hp1 hfix hY x
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd a p'
  have hp2 : (fun v => a.1.1 v) '' Y ∈ ybSet sel mu cst (a • p').deco.1.N := (ybSet_gmap sel mu cst _ a.1.1 Y).2 hp1
  have ha : ∀ P, TopLaw.LevAt (L.levG m2 al) (L.levQ m2 al) P ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P) ((fun _ => 1 : rowSG Pr sel mu → X.Kˣ) P) := by
    intro P
    refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
    · refine ⟨by rw [Pi.one_apply, map_one]; exact one_mem _, ?_⟩
      exact (map_one _).symm.trans (congrArg _ (Subtype.ext (map_one _).symm))
    · exact ⟨one_mem _, (map_one _).symm⟩
  have hκ : ∀ P, frsF sel mu ((1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) P =
      (1 : UF X.E (R.N m2)).1 * (frsF sel mu p P * (((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P)⁻¹).1) := fun P => by
    rw [one_smul]; simp
  have law := CoupledLaw.xiCpl1_law (G := G) (q := (1 : FrmG (L.levG m2 al) (L.levQ m2 al)) • p) hX hPr hL hp1 hp2 hκ hκ' ha ha' x
    (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [one_smul, hfix, hY] at law
  rw [hfix] at hκ'
  have hdet : ∀ P, (LinearEquiv.det a.1.1 : X.Eˣ) = LinearEquiv.det (κ' P).1 := fun P => by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [map_mul, map_mul, InvMemClass.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    exact mul_inv_eq_one.mp (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have hprod : ∀ P, muAt Ch sel mu cst m2 P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) =
      rhoS Ch sel mu m2 P ((LinearEquiv.det ((1 : GLQ X.E (R.N m2) (rowSG Pr sel mu)) P).1 : X.Eˣ) : X.E) *
        rhoT Ch sel mu m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E) := fun P => by
    rw [hdet P, MatLaw.muAt_det, Pi.inv_apply, TopLaw.rhoT_inv, Pi.one_apply, OneMemClass.coe_one, map_one,
      Units.val_one, rhoS_one, one_mul]
  have e : x ∘ₗ ((1 : UF X.E (R.N m2)) : Sp X.E (R.N m2) ≃ₗ[X.E] Sp X.E (R.N m2)).symm.toLinearMap = x :=
    LinearMap.ext fun v => rfl
  rw [e, Finset.prod_const_one, inv_one, inv_one, mul_one, ea'] at law
  rw [Finset.prod_congr rfl fun P _ => hprod P]
  exact law

end GlobalTheory.StabLaw
