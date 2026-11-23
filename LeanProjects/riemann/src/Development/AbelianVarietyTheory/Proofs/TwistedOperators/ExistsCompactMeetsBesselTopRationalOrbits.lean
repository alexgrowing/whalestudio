import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

namespace GlobalTheory.BesCover

open GlobalTheory.Per GlobalTheory.Per.Inhab

theorem exists_compact_cover {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ}
    {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hnorm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e)
    {t : GA D A → GA D B} (ht : ∀ h, EmbRel B A ι (t h) h) :
    ∃ Ω : Set (GA D B), IsCompact Ω ∧ ∀ (h : GA D A) (n : NFlag B e), ∃ γ ∈ GQ B, γ * ((n : GA D B) * t h) ∈ Ω := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, hc, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain rfl : t = s := funext fun h => (hs h _).1 (ht h)
  refine ⟨(fun q : GA D A × NFlag B e => (q.2 : GA D B) * s q.1) '' (K ×ˢ K'),
    (hK.prod hK').image ((continuous_subtype_val.comp continuous_snd).mul (hc.comp continuous_fst)), fun g n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hnorm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine ⟨(s γ * γ')⁻¹, inv_mem (mul_mem (hq γ hγ) hγ'), (k, k'), ⟨hk, hk'⟩, ?_⟩
  rw [e1]
  simp only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem bplus_cover : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  intro D T L sc G W M _
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  exact exists_compact_cover G.besTop.e_iso hι hA
    (fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1) hs

end GlobalTheory.BesCover
