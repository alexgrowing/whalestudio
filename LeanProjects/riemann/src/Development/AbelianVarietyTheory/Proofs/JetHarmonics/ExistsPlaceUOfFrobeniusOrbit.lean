import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardOrthogonalIdempotentsLeNcardPrimesOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowOfFiniteField
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsCongruentEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TauBasisUnitDeterminant
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.OrbitPlace

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs in

theorem mem_emb_of_congr_pow (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] (O : Type)
    [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O] (hp : ¬ IsUnit (p : O))
    (e : ℤ_[p] ⊗[ℤ] A) (he : e * e = e) (σ σ' : A →+* O)
    (h : ∀ x, σ' x - σ x ^ p ∈ IsLocalRing.maximalIdeal O) (hσ : σ ∈ Emb (O := O) e) :
    σ' ∈ Emb (O := O) e := by
  obtain ⟨s, x, hx⟩ := GlobalTheory.CharDepth.padicTensor_eq_mul_add A p e
  have hp0 : IsLocalRing.residue O (p : O) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hp
  have key : ∀ ρ : A →+* O,
      IsLocalRing.residue O (tauExt ρ e) = IsLocalRing.residue O (ρ x) := by
    intro ρ
    have h1 : tauExt (p := p) ρ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) = ρ x := by simp [tauExt]
    rw [hx, map_add, map_mul, map_natCast, h1, map_add, map_mul, hp0, zero_mul, zero_add]
  have h1 : IsLocalRing.residue O (σ x) = 1 := by
    have : tauExt σ e = 1 := hσ
    rw [← key, this, map_one]
  have h2 : IsLocalRing.residue O (tauExt σ' e) = 1 := by
    have := (IsLocalRing.residue_eq_zero_iff _).2 (h x)
    rw [map_sub, map_pow, h1, one_pow, sub_eq_zero] at this
    rw [key, this]
  have hu : IsUnit (tauExt σ' e) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, h2]
    exact one_ne_zero
  have hid : tauExt σ' e * tauExt σ' e = tauExt σ' e * 1 := by rw [← map_mul, he, mul_one]
  exact hu.mul_left_cancel hid

theorem exists_placeU_of_frobenius_orbit : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [IsLocalRing O] [Algebra ℤ_[p] O], ¬ IsUnit (p : O) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (τ : ZMod d → (𝓞 E →+* O)), Function.Injective τ → (∀ s x, τ (s + 1) x - τ s x ^ p ∈ IsLocalRing.maximalIdeal O) → ∃ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p (𝓞 E)) (_ : w.n = d) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e), (∀ j : Fin w.n, ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) = τ ((j.val : ℕ) : ZMod d)) ∧ ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (b i : ℤ_[p] ⊗[ℤ] 𝓞 E))) := by
  intro E _ _ p hpp C _ _ _ v O _ _ hv _ _ hp hd d _ τ hτ hfr
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (τ 0)
  have hsep := GlobalTheory.ringOfIntegers_hom_eq_of_congr_maximalIdeal E p hpp.out hd C v O hv hp
  have hmem : ∀ k : ℕ, τ (k : ZMod d) ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [Nat.cast_succ]
      exact mem_emb_of_congr_pow _ p O hp w.e w.idem _ _ (hfr _) ih
  have hpow : ∀ (k : ℕ) x, IsLocalRing.residue O (τ (k : ZMod d) x) =
      IsLocalRing.residue O (τ 0 x) ^ (p ^ k) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      have := (IsLocalRing.residue_eq_zero_iff _).2 (hfr (k : ZMod d) x)
      rw [map_sub, map_pow, sub_eq_zero] at this
      rw [Nat.cast_succ, this, ih, ← pow_mul, pow_succ]
  have hsurj : ∀ σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e, ∃ s, τ s = σ := by
    intro σ hσ
    obtain ⟨i, hi⟩ := GlobalTheory.EmbFrob.exists_frobenius_pow p (𝓞 E) C v O hv hp w (τ 0) σ hw hσ
    refine ⟨(i : ZMod d), hsep _ _ fun x => ?_⟩
    have h1 : σ x - τ 0 x ^ (p ^ i) ∈ IsLocalRing.maximalIdeal O := by
      intro hu
      exact (hi x).ne (hv.one_of_isUnit hu)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h1
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hpow, this, sub_self]
  have hmem' : ∀ s : ZMod d, τ s ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro s
    have := hmem s.val
    rwa [ZMod.natCast_zmod_val] at this
  have hbij : Function.Bijective
      (fun s : ZMod d => (⟨τ s, hmem' s⟩ : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e)) :=
    ⟨fun a b h => hτ (congrArg Subtype.val h), fun σ => by
      obtain ⟨s, hs⟩ := hsurj σ.1 σ.2
      exact ⟨s, Subtype.ext hs⟩⟩
  obtain ⟨⟨t₀⟩, -⟩ := GlobalTheory.EmbCount.card_emb E p C v O hv w.e w.idem
  have hn : w.n = d := by
    have h1 := Nat.card_congr (t₀.trans (Equiv.ofBijective _ hbij).symm)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  have hcast : Function.Bijective (fun j : Fin w.n => ((j.val : ℕ) : ZMod d)) := by
    refine ⟨fun a b h => ?_, fun s => ⟨⟨s.val, hn ▸ ZMod.val_lt s⟩, ZMod.natCast_zmod_val s⟩⟩
    have h' := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at h'
    rw [Nat.mod_eq_of_lt (hn ▸ a.2), Nat.mod_eq_of_lt (hn ▸ b.2)] at h'
    exact Fin.ext h'
  let t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e :=
    (Equiv.ofBijective _ hcast).trans (Equiv.ofBijective _ hbij)
  refine ⟨w, hn, t, fun j => rfl, ?_⟩
  exact GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det p (𝓞 E) O w (fun j => (t j).1) (fun j => (t j).2)
    (fun j j' h => t.injective (Subtype.ext (hsep _ _ h)))

end GlobalTheory.OrbitPlace
