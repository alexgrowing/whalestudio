import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerNonzeroRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockInducedRepDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockInducedRepIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CellColumn

theorem exists_subquotient_column : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
    (g : ∀ j, (Σ i, c j i) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (∀ j, GlobalTheory.SmGL.Levi k (c j)) W) (ψ : (∀ j, GlobalTheory.SmGL.Levi k (c j)) →* ℂˣ),
    (∀ z w, τ z w = (ψ z : ℂ) • w) → ∀ (j₀ : β) (ν : GlobalTheory.SmGL.Levi k m' →* ℂˣ)
    {W' Vy : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Vy] [Module ℂ Vy]
    (Q : Representation ℂ (GL (m' j₀) k) W') (Y : Representation ℂ (GL (m' j₀) k) Vy),
    GlobalTheory.SmGL.IsSubquotient Q
      ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀)) →
    ∀ F : Q.IntertwiningMap Y, F ≠ 0 →
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ (GL (m' j₀) k) V'),
      GlobalTheory.SmGL.IsSubquotient Q' (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.parInd (g j₀)
        (GlobalTheory.SmGL.ofChar (ψ.comp (MonoidHom.mulSingle (fun j => GlobalTheory.SmGL.Levi k (c j)) j₀))))
        (ν.comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀))) ∧
      ∃ F' : Q'.IntertwiningMap Y, F' ≠ 0 := by
  intro k _ _ _ _ α β _ _ _ _ _ m' _ _ c _ _ g W _ _ τ ψ hτ j₀ ν W' Vy _ _ _ _ Q Y hQ F hF
  obtain ⟨S, q, hq⟩ := hQ
  obtain ⟨w, hw⟩ : ∃ w, F w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨s, rfl⟩ := hq w
  obtain ⟨ι, _, y, l, R, hsR, hR⟩ := GlobalTheory.T.block_induced_rep_intertwining k g τ ψ hτ j₀ ν (s : _)
  choose E hE using fun i => GlobalTheory.T.block_induced_rep_decomposition k g τ ψ hτ j₀ ν (y i) (l i)
  obtain ⟨S', φ', hφ'⟩ := GlobalTheory.T.intertwiner_nonzero_restriction _ _ Y E R S (F.comp q) s hsR hw
    (fun v hv h0 => hR v hv fun i x => by rw [← hE i v x, h0 i]; rfl)
  exact ⟨_, _, _, S'.toRepresentation, ⟨S', .id _, Function.surjective_id⟩, φ', hφ'⟩

end GlobalTheory.CellColumn
