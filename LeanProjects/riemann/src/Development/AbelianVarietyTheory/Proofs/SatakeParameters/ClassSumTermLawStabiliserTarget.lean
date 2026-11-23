import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiEntryStab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiCpl1Stab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLawStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawTopLevelStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem gmap_of_fix {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {Λ : LevFam X.E X.K n SG}
    {Θ : LevQFam X.E X.K n Q} (a : FrmG Λ Θ) (p : DecoF X.E n ST SG Q) (h : a • p = p) :
    gmap a.1.1 p.deco.1.N = p.deco.1.N :=
  congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) h

theorem mulLat_mul_le {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (a b : ℕ)
    (M : Submodule (𝓞 E) H) : mulLat (a * b) M ≤ mulLat b M := by
  rintro z ⟨w, hw, rfl⟩
  refine ⟨((a : 𝓞 E)) • w, M.smul_mem _ hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Nat.cast_mul, mul_comm]

theorem term_law : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  intro D L hT Gi Gl K Y cX ex t hC u μ G hG i hi c c' g hg
  have hok := t.idx_ok μ
  have hm := hok.hm
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  obtain ⟨pt, ix, yb, pT, hN, hyb, hE, hC1, hTop, hGi, hGm, hGT⟩ := hG
  have dat := GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw D L hT Gi Gl K Y cX ex t hC.fields hC.sel hC.bad.1 hC.bad.2.1 hC.bad.2.2.1 hC.bad.2.2.2 hC.chars u μ i hi c c'
  have fin : ∀ (f : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) → t.X.K) (N : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)))
      (N' : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N (i + 1)))) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K),
      (t.rd u μ).N i c = N → (t.rd u μ).N (i + 1) c' = N' → (∀ x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (f x)) →
      gmap γ.1 N' = N' →
      (∀ x z, z ∈ mulLat (cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) (homAt (Sall t.sel (t.tup μ) (t.word u)) N N') → f (x + z) = f x) →
      (∀ x, f (γ.1.toLinearMap ∘ₗ x) * ∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) = k * f x) →
      TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
    intro f N N' γ k hN1 hN2 hf hγ hinv hlaw
    subst hN1 hN2
    refine dat γ k hγ (fun x z hz => ?_) fun x => ?_
    · rw [hlev, hSS] at hz
      rw [hf, hf, hinv x z (mulLat_mul_le _ _ _ hz)]
    · rw [hf, hf, ← map_mul, ← map_mul, hlaw]
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · rw [hGi (i + 1) (by omega) (by omega) c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN i (by omega) c) (hN (i + 1) (by omega) c') (hE i hlt c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiEntry_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok i hlt _ _ _ _ x z hz)
      (GlobalTheory.FiLaw.xiEntry_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) i hlt _ _ _ _ a hfix)
  · subst heq
    obtain ⟨b, -⟩ := hok.last_uniq
    rw [hGm b c'] at hg
    obtain ⟨a, hfix, hY, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ (Nat.le_succ _) c) (hN _ le_rfl c') (hC1 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => xiCpl1_invA t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.pr_ok hok _ _ _ _ x z hz)
      (GlobalTheory.StabLaw.xiCpl1_stab t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob _ hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (t.word u) _ b _ _ _ a (hyb c') hfix hY)
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    rw [hGT c'] at hg
    obtain ⟨a, hfix, -, rfl⟩ := hg
    exact fin _ _ _ a.1 _ (hN _ le_rfl c) (hTop.1 c') (hTop.2 c c') (gmap_of_fix a _ hfix)
      (fun x z hz => GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok
        (t.word u) _ _ _ x z (hyb c) hz)
      (GlobalTheory.T.lastStepDatum_law_topLevelStabilizer t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hC.fields t.pr_ok hC.sel hC.bad.1 hC.bad.2.1 hok hC.chOk
        (hC.sharp μ) (hC.deep μ).1 (hC.repOne μ) (hC.deep μ).2 (t.word u) _ _ _ a (hyb c) hfix)

end GlobalTheory.KerJ
