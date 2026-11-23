import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorphStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemmaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCountsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellLeviTensorDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquivStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoAssembly

def equivComp {G H V V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (ψ : H →* G) : Representation.Equiv (ρ.comp ψ) (ρ'.comp ψ) :=
  Representation.Equiv.mk' ⟨e.toLinearEquiv.toLinearMap, fun h => by
      ext x; exact LinearMap.congr_fun (e.isIntertwining' (ψ h)) x⟩ e.invFun
    e.left_inv e.right_inv

set_option maxHeartbeats 1000000 in

theorem jacquetOfInducedFiltration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  intro k _ _ _ _ α β n _ _ _ _ _ _ m _ _ m' _ _ e e'
  let N := Fintype.card n
  let ι : n ≃ Fin N := Fintype.equivFin n
  let E := e.trans ι
  let E' := e'.trans ι
  obtain ⟨βF, hβ⟩ := GlobalTheory.T.exists_strict_block_order m E
  obtain ⟨γF, hγ⟩ := GlobalTheory.T.exists_strict_block_order m' E'
  obtain ⟨φ, hφ, -, hφsc⟩ := GlobalTheory.T.levi_block_homeomorph k E βF hβ
  obtain ⟨φ', hφ', -, -⟩ := GlobalTheory.T.levi_block_homeomorph k E' γF hγ
  obtain ⟨K, w, hcov, hfilt⟩ := GlobalTheory.T.bernstein_zelevinsky_geometric_lemma k N βF γF
  let sz : Equiv.Perm (Fin N) → α → β → ℕ := fun v i j =>
    (Finset.univ.filter fun x : Fin N => blk E x = i ∧ blk E' (v.symm x) = j).card
  let toSM : Fin K → SizeMatrix m m' := fun t => ⟨sz (w t), GlobalTheory.T.permutation_block_counts E E' (w t)⟩
  have hsz : ∀ v v' : Equiv.Perm (Fin N), permGL k v' ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) ↔ sz v = sz v' := by
    intro v v'
    rw [GlobalTheory.T.double_coset_block_matrix k E βF hβ E' γF hγ v v']
    exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => congrFun (congrFun h i) j⟩
  have hself : ∀ v : Equiv.Perm (Fin N), permGL k v ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) := fun v =>
    (hsz v v).2 rfl
  have inj : Function.Injective toSM := by
    intro t t' h
    have h1 : sz (w t) = sz (w t') := congrArg Subtype.val h
    obtain ⟨j, -, huniq⟩ := hcov (permGL k (w t'))
    exact (huniq t ((hsz _ _).2 h1)).trans (huniq t' (hself _)).symm
  have surj : Function.Surjective toSM := by
    intro B
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_perm_block_matrix E E' B
    obtain ⟨t, ht, -⟩ := hcov (permGL k v)
    refine ⟨t, Subtype.ext ?_⟩
    show sz (w t) = B.1
    rw [(hsz _ _).1 ht]
    exact funext fun i => funext fun j => hv i j
  refine ⟨K, Equiv.ofBijective toSM ⟨inj, surj⟩, ?_⟩
  intro W _ _ ρ hρ
  let σ := ρ.comp φ.symm.toMonoidHom
  have hσ : GroundTheory.Automorphic.IsSmooth σ := GlobalTheory.T.isSmooth_comp_continuous φ.symm.toMonoidHom hφsc ρ hρ
  have hF := hfilt W σ hσ
  obtain ⟨V, hF⟩ := hF
  obtain ⟨hV0, hF⟩ := hF
  obtain ⟨hVK, hF⟩ := hF
  obtain ⟨hVmono, hV, hΨ⟩ := hF
  have e1' := GlobalTheory.T.induction_reindex_equiv k e e' ι ρ
  obtain ⟨e1⟩ := e1'
  have e2' := GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv k E' γF hγ φ' hφ' (V := IndSp E ρ) (parInd E ρ)
  obtain ⟨e2⟩ := e2'
  have e3' := GlobalTheory.T.parabolicInd_equiv_levi_transport k E βF hβ φ hφ ρ
  obtain ⟨e3⟩ := e3'
  have e4' := GlobalTheory.T.jacquet_module_equiv k N γF (V := IndSp E ρ) (parInd E ρ) _ e3
  obtain ⟨e4⟩ := e4'
  have e12 := e1.trans e2
  have e45 := equivComp e4 φ'.toMonoidHom
  have e5 := e12.trans e45
  have hT := GlobalTheory.T.filtration_transport_equiv φ'.toMonoidHom _ _ e5 K _
    (fun j => indRep (cellLeviSub k βF γF (w j)) (normInducing σ γF (w j))) V hV0 hVK hVmono hV hΨ
  obtain ⟨S, hT⟩ := hT
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hT
  refine ⟨S, hS1, hS2, hS3, fun t f g => ?_⟩
  have q1' := hS4 t
  obtain ⟨q1⟩ := q1'
  have c' := GlobalTheory.T.levi_intersection_conjugate k E βF hβ φ hφ E' γF hγ φ' hφ' ρ (w t)
  obtain ⟨f0, g0, c'⟩ := c'
  obtain ⟨q2⟩ := c'
  have q3' := GlobalTheory.T.cell_levi_tensor_decomposition (fun i j => by rw [Fintype.card_fin, Fintype.card_fin]; rfl) f0 g0 f g ρ
  obtain ⟨q3⟩ := q3'
  exact ⟨q1.trans (q2.trans q3)⟩

end GlobalTheory.CompanionTheory.GeoAssembly
