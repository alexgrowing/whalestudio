import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientReductionBijectiveOfFlatStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoZeroSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsosStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsG

open CrystallineSemistableComparison.Ls

theorem seq_flat {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) : ∃ (ψ : ∀ n, Cx.Hom (Kt l (B.schFn M.p) r.ρ n) (quo l (Kt l (B.schFn M.p) r.ρ (n + 1)) n) (RingHom.id _))
      (_ : ∀ n j, Function.Bijective ((ψ n).mapH j)),
      (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) ∧
      ∀ n j x, (ψ n).mapH j (resF l (B.schFn M.p) r.ρ n j ((Wc.HS l (B.schFn M.p) r.ρ j).r n x)) =
        (prj l (Kt l (B.schFn M.p) r.ρ (n + 1)) n).mapH j (resF l (B.schFn M.p) r.ρ (n + 1) j x) := by
  obtain ⟨ψ, hψ, hc⟩ := LsQ.seqflat0_pf r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  exact ⟨ψ, hψ, fun m b h j => GlobalTheory.T.quotient_reduction_bijective_of_flat _ l _ _ m (ψ m) (hfl m) (hfl (m + 1)) (hψ m) b h j, hc⟩

theorem ls_seq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) :
    Nonempty (CrystallineSemistableComparison.Tw.LSeq l (Wc.HS l (B.schFn M.p) r.ρ j) (Wc.HS l (B.schFn M.p) r.ρ (j + 1))) := by
  obtain ⟨ψ, hψ, hq, hc⟩ := seq_flat r M hM
  have hf := GlobalTheory.T.smooth_model_restriction_bijective r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  have fwd : ∀ i n x, (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i).r n (resF l (B.schFn M.p) r.ρ (n + 1) i x) =
      resF l (B.schFn M.p) r.ρ n i ((Wc.HS l (B.schFn M.p) r.ρ i).r n x) := by
    intro i n x
    change (LinearEquiv.ofBijective _ (hψ n i)).symm ((prj l _ n).mapH i (resF l (B.schFn M.p) r.ρ (n + 1) i x)) = _
    rw [← hc n i x]
    exact (LinearEquiv.ofBijective _ (hψ n i)).symm_apply_apply _
  let E : ∀ i n, (Wc.HS l (B.schFn M.p) r.ρ i).M n ≃ₗ[WittVector l r.k] (Kt l (B.schFn M.p) r.ρ n).H i :=
    fun i n => LinearEquiv.ofBijective _ (hf n i)
  let e : ∀ i, Sys.Hom (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i) (Wc.HS l (B.schFn M.p) r.ρ i) (RingHom.id _) := fun i =>
    { f := fun n => (E i n).symm.toLinearMap
      comm := fun n y => by
        apply (E i n).injective
        change E i n ((Wc.HS l (B.schFn M.p) r.ρ i).r n ((E i (n + 1)).symm y)) = E i n ((E i n).symm _)
        rw [LinearEquiv.apply_symm_apply]
        have h1 := fwd i n ((E i (n + 1)).symm y)
        have h2 : resF l (B.schFn M.p) r.ρ (n + 1) i ((E i (n + 1)).symm y) = y := (E i (n + 1)).apply_symm_apply y
        exact h1.symm.trans (congrArg _ h2) }
  exact GlobalTheory.T.lseq_of_level_isos _ l _ _ _ _ (e j) (e (j + 1)) (fun n => (E j n).symm.bijective) (fun n => (E (j + 1) n).symm.bijective)
    (GlobalTheory.T.lseq_of_flat_tower _ l _ ψ hψ hfl hq j).some

end CrystallineSemistableComparison.Pb.LsG

end
