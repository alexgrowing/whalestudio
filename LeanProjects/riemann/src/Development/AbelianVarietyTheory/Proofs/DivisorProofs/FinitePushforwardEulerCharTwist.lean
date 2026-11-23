import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PushTwistChi

theorem eventually_isFiniteQC_and_chi_pushforward_twist : ∀ (k : Type) [Field k] (T T' : Scheme.{0}) [Algebra k Γ(T, ⊤)] [Algebra k Γ(T', ⊤)], IsProjSurface k T → IsProjSurface k T' → ∀ (ρ : T' ⟶ T), ρ ≫ strHom k T = strHom k T' → ∀ (L : LB T'), IsAmpleLB L → ∀ (H : T'.Modules), QCoh.IsFiniteQC H → ∀ᶠ n in atTop, QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) ∧ chi k ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) = chi k (twist H (lbPow L n)) := by
  intro k _ T T' _ _ hT hT' ρ hρ L hL H hH
  have hPT := (isProper_and_exists_isAmpleLB_of_isProjOver hT.isProjOver).1
  have hPT' := (isProper_and_exists_isAmpleLB_of_isProjOver hT'.isProjOver).1
  have : IsProper (ρ ≫ strHom k T) := hρ ▸ hPT'
  have : IsProper ρ := .of_comp ρ (strHom k T)
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (strHom k T)
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (strHom k T)
  have := isAffineHom_diagonal_of_isSeparated (strHom k T)
  have hπ : ∀ r : k, ρ.appTop (algebraMap k Γ(T, ⊤) r) = algebraMap k Γ(T', ⊤) r := fun r => by
    rw [algebraMap_eq_strHom k T, algebraMap_eq_strHom k T', ← hρ, Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := T) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hV : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist H (lbPow L n)) (ρ ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI =>
      GlobalTheory.ProperFinite.eventually_subsingleton_cohOn ρ hL H (hD' I hI)
  filter_upwards [hV] with n hn
  have := GlobalTheory.Twist.isFiniteQC_twist (F := H) (isLB_lbPow hL.isLB n)
  have hF := GlobalTheory.ProperFinite.isFiniteQC_pushforward ρ hL (twist H (lbPow L n))
  refine ⟨hF, chi_eq_of_linearEquiv k fun p => ?_⟩
  exact (GlobalTheory.ProperFinite.nonempty_coh_pushforward_equiv k ρ hπ _ hc hD' hn p).some

end GlobalTheory.PushTwistChi
