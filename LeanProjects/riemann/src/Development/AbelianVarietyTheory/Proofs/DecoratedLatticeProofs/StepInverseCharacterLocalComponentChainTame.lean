import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QTw.StepChar

open Formalism.L2.Col Formalism.L2.DIV
open Formalism.L2.Host (HChar)

theorem locK_unif {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q :=
  χ.val_eq hu _ ((Formalism.UG.P.levelaf_valued_algebraMap Q (k : L)).trans hk)

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem g_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (P : rowSG Pr sel mu)
    (hP : P.1 ∉ Pr.vGs) (k : Fin 2) : ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)

theorem res_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (hx : (x : X.E) = (y : X.E))
    (hc : (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y) :
    σ ((resChar (mu : Chr X.F X.E X.K) P.1 c : X.Kˣ) : X.K) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ) := by
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hu : P.1.valuation X.E (x : X.E) = 1 := by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  have e1 : (m0 j * ξ).locK P.1 x = (m0 j).locK P.1 x * ξ.locK P.1 x := rfl
  rw [e1, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ (g_notMem hX hPr hsel hg P hP)) hu, one_mul,
    GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm]

theorem map_muAt (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (h : GlobalTheory.Mem.Col2.Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : cst.muq (j.1 + 1) P = (((Ch.muVal j P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)) (a : X.Eˣ) :
    σ (muAt Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.TwistVal.main X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hg' := g_notMem hX hPr hsel hg P hP
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j * ξ).locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  rw [← hm]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · have e1 : (m0 j * ξ).locK P.1 q = (m0 j).locK P.1 q * ξ.locK P.1 q := rfl
    rw [hm, e1, Units.val_mul, ← hq q hq', hQ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul,
      map_inv₀, map_inv₀, ht.muVal j P.1 hg', ← locK_unif (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
        (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2), mul_inv]
    rfl
  · rw [hm, if_neg hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, res_eq hX hPr hsel hg ht h j P hP x y c hx hc]

end General

theorem comp_eq_muAt_and_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  intro B X I hI l Z a P hP k _ _ _ _ q hq hint hden i hi χ hχ μ hμ
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hμ' : (ofSplit q).IsComp χ μ⁻¹ := fun x b hb => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hμ x b hb, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  constructor
  · intro x u hu
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA (I.rec7 l Z))).map_zero)
    have h1 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q hq hχ hx0 u hu
    have h2 := map_muAt hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP
      ((hI.idx_ok a).muqQ i hi P hP) (Units.mk0 x hx0)
    have h3 := hμ u (GlobalTheory.LocMod.SplitHecke.idlU q u) rfl
    rw [MonoidHom.inv_apply, Circle.coe_inv, h1] at h3
    exact h3.trans h2.symm
  · have hr : IsRes (D := I.rec7 l Z) (I.C.mu0 ⟨i, hi⟩ * I.xi a) P.1
        ((Units.map (B.embLL : B.fields.K →* ℂ)).comp (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) P.1)) :=
      fun y x c hx hc => Units.ext (res_eq hX hPr hI.sel_ok hI.g_mem hI.ch_tied (hI.xi_reads a) ⟨i, hi⟩ P hP x y c hx hc)
    have ht := (GlobalTheory.LocMod.SplitHecke.tame_and_res (I.rec7 l Z) k q P.1 hq hint hden χ _ _ μ⁻¹ hχ hr hμ').1
    intro x hx
    have := ht x hx
    rwa [MonoidHom.inv_apply, inv_eq_one] at this

end GlobalTheory.QTw.StepChar

end
