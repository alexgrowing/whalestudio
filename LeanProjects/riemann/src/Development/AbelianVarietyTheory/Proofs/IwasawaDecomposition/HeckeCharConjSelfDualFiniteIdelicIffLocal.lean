import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense GlobalTheory.CuspRep.NormTriv

namespace GlobalTheory.CuspRep.CsdFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation "𝐜" => AlgEquiv.toRingEquiv (IsCMField.complexConj L)

theorem loc_of_idelic (χ : HChar L)
    (h : ∀ u : (Af L)ˣ, χ.1 (finId L (Units.map (conjFin 𝐜).toMonoidHom u)⁻¹) = χ.1 (finId L u))
    {w w' : HeightOneSpectrum (𝓞 L)} (hc : GlobalTheory.Mem.Chr.ConjPl 𝐜 w w') (k : Lˣ) :
    χ.locK w' (cU 𝐜 k) = (χ.locK w k)⁻¹ := by
  have h1 := h (Units.map (Neutral.B1.finiteSingle L w) (atFin w k))
  rw [conjFin_finSingle 𝐜 hc, map_inv, finId_finSingle, finId_finSingle, map_inv] at h1
  change χ.1 (localIdele L w' (atFin w' (cU 𝐜 k))) = (χ.1 (localIdele L w (atFin w k)))⁻¹
  rw [← h1, inv_inv]

theorem idelic_of_loc (χ : HChar L)
    (h : ∀ w w', GlobalTheory.Mem.Chr.ConjPl 𝐜 w w' → ∀ k : Lˣ, χ.locK w' (cU 𝐜 k) = (χ.locK w k)⁻¹) (u : (Af L)ˣ) :
    χ.1 (finId L (Units.map (conjFin 𝐜).toMonoidHom u)⁻¹) = χ.1 (finId L u) := by
  have h1 : ∀ v x, normFin 𝐜 χ (localIdele L v x) = 1 := fun v => by
    obtain ⟨v', hv', -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl 𝐜 v
    refine loc_eq_one_of_prod (continuous_normFin _ χ) {v} (fun k => ?_) (Finset.mem_singleton_self v)
    rw [Finset.prod_singleton, normFin_loc _ χ hv' k, h v v' hv' k, mul_inv_cancel]
  have h3 := GlobalTheory.FrobDense.eq_one_of_local _ (continuous_normFin 𝐜 χ) (finId L u) (by
    change (1 : InfiniteAdeleRing L) - 0 + 0 = 1
    simp) fun v => h1 v _
  have e : Units.map (pFin L).toMonoidHom (finId L u) = u := Units.ext (by
    change (1 : Af L) - 1 + u = u
    simp)
  change χ.1 (finId L (Units.map (pFin L).toMonoidHom (finId L u) *
    Units.map (conjFin 𝐜).toMonoidHom (Units.map (pFin L).toMonoidHom (finId L u)))) = 1 at h3
  rw [e, map_mul, map_mul] at h3
  rw [map_inv, map_inv]
  exact (eq_inv_of_mul_eq_one_left h3).symm

end GlobalTheory.CuspRep.CsdFin

open GlobalTheory.CuspRep.CsdFin in

theorem GlobalTheory.CuspRep.csdFin_iff : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) =
      χ.1 (finId H.E u)) ↔
    ∀ w w', Formalism.BasicNotions.IsConjPl H w w' → ∀ k : H.Eˣ,
      χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have hk : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      cU (IsCMField.complexConj H.E).toRingEquiv k := fun k => Units.ext (host_complexConj H k).symm
  have hp : ∀ w w', Formalism.BasicNotions.IsConjPl H w w' ↔ GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj H.E).toRingEquiv w w' :=
    fun w w' => by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      exact ⟨fun hc x y e => hc x y (e.trans (host_complexConj H _)),
        fun hc x y e => hc x y (e.trans (host_complexConj H _).symm)⟩
  constructor
  · intro h w w' hc k
    rw [hk]
    exact loc_of_idelic χ h ((hp w w').1 hc) k
  · intro h
    exact idelic_of_loc χ fun w w' hc k => by rw [← hk]; exact h w w' ((hp w w').2 hc) k
