import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0

open HodgeChar0

theorem ht_eq_dR_of_not_inFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (p : ℕ), p ∈ S → ∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) →
      𝔐.HT p s q = 𝔐.dR s q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp s q hq
  classical
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  haveI hchar : CharZero Ω := charZero_of_injective_ringHom hcst
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  have htop : (⨆ s, 𝔐.Vgen s) = ⊤ := hint.submodule_iSup_eq_top
  have hind : iSupIndep 𝔐.Vgen := hint.submodule_iSupIndep
  have hreg : ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := fun s a q =>
    HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom)
  have hnat := unitAt_natCast (q := q) hq
  have hV : ∀ s, 𝔐.V s q = 𝔐.dR s q := fun s =>
    Lat.patch_of_not S _ _ fun p hp => hq p (𝔐.S_prime p hp)
  have hint' : ∀ (s : CMType H ⊕ CMType H) a, IsIntegral ℤ (𝔐.emb s a) := fun s a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom
  have hsep : ∀ s t, s ≠ t → ∃ a, 𝔐.emb s a ≠ 𝔐.emb t a ∧ (𝔐.emb s a - 𝔐.emb t a)⁻¹ ∈ regAt 𝔐.ξ q := by
    intro s t hst
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (fun e => hst (hinj e))
    exact ⟨a, ha, inv_mem_regAt hnat (sub_mem (hreg s a q) (hreg t a q)) ((hint' s a).sub (hint' t a))⟩
  have hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
    refine le_antisymm (fun e he => ?_) (iSup_le fun s => inf_le_left)
    have he' : e ∈ ⨆ s, 𝔐.Vgen s := by rw [htop]; trivial
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 he'
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at he ⊢
    have h1 := mem_of_sum_mem (𝔐.M.lat q) 𝔐.ρ 𝔐.emb
      (fun a e he => lat_stable 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act q a he) (fun s a => hreg s a q) hsep Finset.univ f
      (fun s _ => hf s) he
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.mem_iSup_of_mem s ⟨h1 s (Finset.mem_univ s), hf s⟩
  have hbi : ∀ x, (∀ w ∈ 𝔐.M.omLat q, w x ∈ regAt 𝔐.ξ q) → x ∈ 𝔐.M.lat q := by
    intro x hx
    choose U hU b hb hfr using fun s => 𝔐.vb s q trivial
    rw [hlat]
    refine mem_iSup_of_dual 𝔐.Vgen hind htop (labelRk D) b (fun s => (hfr s q trivial (hU s)).1) hb
      (fun s => 𝔐.dR s q) (fun s => (hV s).symm.trans (hfr s q trivial (hU s)).2) x fun w hw =>
        hx w (show ∀ e ∈ 𝔐.M.lat q, w e ∈ regAt 𝔐.ξ q from fun e he => by
          rw [hlat] at he
          exact Submodule.iSup_induction _ (motive := fun e => w e ∈ regAt 𝔐.ξ q) he hw
            (by simpa using zero_mem _) (fun a b ha hb => by simpa using add_mem ha hb))
  have hpp : p.Prime := 𝔐.S_prime p hp
  have hn : unitAt 𝔐.ξ q ((p ^ 𝔐.R p : ℕ) : Ω) := hnat _ (pow_ne_zero _ hpp.ne_zero)
  have hd : ∀ s, 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q = 𝔐.dR s q := fun s =>
    htDual_eq_eigLat 𝔐.M 𝔐.ρ _ 𝔐.t.PP.isLB hn hbi
  cases s with
  | inl τ =>
    have hbot : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
    exact htW_eq_eigLat 𝔐.M 𝔐.ρ _ (hd _) (fun d => hreg _ d q) _ (Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
      (Ideal.absNorm_mem _) (hnat _ (by simpa [Ideal.absNorm_eq_zero_iff] using hbot))
  | inr τ => exact hd _

end GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0
