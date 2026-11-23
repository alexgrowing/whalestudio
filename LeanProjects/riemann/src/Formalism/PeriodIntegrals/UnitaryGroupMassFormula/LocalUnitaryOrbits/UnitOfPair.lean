import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def FixLoc : Prop :=
  IsCMExt F E σ → ∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, sigR (Fv F v) σ x = x → sigR (Fv F v) σ y = y →
    IsU v (x + y) → IsU v x ∨ IsU v y

def TrNd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ π : Fv F v, IsUnif v π → ∀ c ∈ OEv (E := E) v,
    sc (E := E) v (π⁻¹) * c ∉ OEv (E := E) v → ∃ t ∈ OEv (E := E) v, IsU v (t * c + sigR (Fv F v) σ (t * c))

def PrimPerp : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ π : Fv F v, IsUnif v π ∧ ∃ p ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ

theorem isU_neg {z : Fv F v ⊗[F] E} (h : IsU v (-z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨-w, oev_neg v hw0, by rw [mul_neg, ← neg_mul]; exact hw⟩

theorem isU_of_mul {a z : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (h : IsU v (a * z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨a * w, (oSub v).2 _ ha _ hw0, by rw [← hw]; ring⟩

theorem unit_of_pair (hF : FixLoc σ v) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E)
    (p q : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hq : q ∈ PerpG σ J v Λ X)
    (t : Fv F v ⊗[F] E) (ht : t ∈ OEv (E := E) v)
    (hu : IsU v (t * hR (Fv F v) σ J q p + sigR (Fv F v) σ (t * hR (Fv F v) σ J q p))) :
    ∃ r ∈ PerpG σ J v Λ X, IsU v (hR (Fv F v) σ J r r) := by
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  set s := sigR (Fv F v) σ t with hs
  have hs0 : s ∈ OEv (E := E) v := sigR_mem σ v ht
  have hss : sigR (Fv F v) σ s = t := sigR_invol σ v hcm t
  set r := p + s • q with hr
  have hrP : r ∈ PerpG σ J v Λ X := by
    refine ⟨Submodule.add_mem _ hp.1 (oSmul v Λ hL s hs0 q hq.1), fun i => ?_⟩
    rw [hr, hR_add_right', hR_smul_right, hp.2 i, hq.2 i, mul_zero, add_zero]
  set α := hR (Fv F v) σ J p p
  set β := hR (Fv F v) σ J q q
  set c := hR (Fv F v) σ J q p
  have hpq : hR (Fv F v) σ J p q = sigR (Fv F v) σ c := (hR_conj σ J v hcm hJ q p).symm
  have hrr : hR (Fv F v) σ J r r = (t * c + sigR (Fv F v) σ (t * c)) + (α + t * s * β) := by
    rw [hr, hR_add_left', hR_add_right', hR_add_right', hR_smul_left, hR_smul_left, hR_smul_right,
      hR_smul_right, hpq, hss, map_mul]
    rw [hs]; ring
  have hα0 : α ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  have hβ0 : β ∈ OEv (E := E) v := (hsd q).1 hq.1 q hq.1
  have hr0 : hR (Fv F v) σ J r r ∈ OEv (E := E) v := (hsd r).1 hrP.1 r hrP.1
  have hαf : sigR (Fv F v) σ α = α := hR_conj σ J v hcm hJ p p
  have hβf : sigR (Fv F v) σ β = β := hR_conj σ J v hcm hJ q q
  have hrf : sigR (Fv F v) σ (hR (Fv F v) σ J r r) = hR (Fv F v) σ J r r := hR_conj σ J v hcm hJ r r
  have hts0 : t * s ∈ OEv (E := E) v := (oSub v).2 _ ht _ hs0
  have htsβ0 : t * s * β ∈ OEv (E := E) v := (oSub v).2 _ hts0 _ hβ0
  have htsβf : sigR (Fv F v) σ (t * s * β) = t * s * β := by
    rw [map_mul, map_mul, hss, hβf, hs]; ring
  have hm0 : -(α + t * s * β) ∈ OEv (E := E) v := oev_neg v (oev_add v hα0 htsβ0)
  have hmf : sigR (Fv F v) σ (-(α + t * s * β)) = -(α + t * s * β) := by
    rw [map_neg, map_add, hαf, htsβf]
  have hsum : hR (Fv F v) σ J r r + -(α + t * s * β) = t * c + sigR (Fv F v) σ (t * c) := by
    rw [hrr]; ring
  rcases hF hcm _ hr0 _ hm0 hrf hmf (by rw [hsum]; exact hu) with h | h
  · exact ⟨r, hrP, h⟩
  · have h' : IsU v (-α + -(t * s * β)) := by rw [← neg_add]; exact h
    rcases hF hcm _ (oev_neg v hα0) _ (oev_neg v htsβ0) (by rw [map_neg, hαf]) (by rw [map_neg, htsβf]) h'
      with h2 | h2
    · exact ⟨p, hp, isU_neg v h2⟩
    · exact ⟨q, hq, isU_of_mul v hts0 (isU_neg v h2)⟩

theorem partner (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ) (hU : UniG σ J v X) (π : Fv F v)
    (p : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hpn : sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ) :
    ∃ q ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) * hR (Fv F v) σ J q p ∉ OEv (E := E) v := by
  have h1 : ¬ ∀ x ∈ latLoc (E := E) v Λ, hR (Fv F v) σ J x (sc (E := E) v (π⁻¹) • p) ∈ OEv (E := E) v :=
    fun h => hpn ((hsd _).2 h)
  push_neg at h1
  obtain ⟨x, hx, hxn⟩ := h1
  obtain ⟨c, -, hc⟩ := splitG σ J v Λ hL hsd X hX hU x hx
  refine ⟨_, hc, ?_⟩
  rw [← hR_smul_right, hR_sub_left', hR_sum_left']
  have : ∀ i, hR (Fv F v) σ J (c i • X i) (sc (E := E) v (π⁻¹) • p) = 0 := by
    intro i
    rw [hR_smul_left, hR_smul_right, hp.2 i, mul_zero, mul_zero]
  simp only [this, Finset.sum_const_zero, sub_zero]
  exact hxn

theorem unitNorm_of (hF : FixLoc σ v) (hT : TrNd σ J ψ v) (hP : PrimPerp σ J ψ v Λ) : UnitNorm σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨π, hπ, p, hp, hpn⟩ := hP hstd hL hsd hun ι X hX hUX hc
  obtain ⟨q, hq, hqp⟩ := partner σ J v Λ hL hsd X hX hUX π p hp hpn
  obtain ⟨t, ht0, htu⟩ := hT hstd hun π hπ _ ((hsd p).1 hp.1 q hq.1) hqp
  obtain ⟨r, hr, u', hu'0, hu'⟩ := unit_of_pair σ J ψ v Λ hF hstd hL hsd X p q hp hq t ht0 htu
  exact ⟨r, hr, u', hu'0, hu'⟩

end PI.OmLocU.UnN
