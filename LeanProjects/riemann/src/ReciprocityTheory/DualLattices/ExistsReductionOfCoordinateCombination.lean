import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y

lemma red_mulVec (H : HodgeTateDatum p g v R O σ cp) (a : O) (t : TT p g) :
    red p g (H.ρ a *ᵥ t) = nbAct H a (red p g t) := by
  funext i
  exact RingHom.map_mulVec PadicInt.toZMod (H.ρ a) t i

lemma red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma comp_mem (H : HodgeTateDatum p g v R O σ cp) (a : O) {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    (fun y => f (nbAct H a y)) ∈ H.AA.carrier := by
  obtain ⟨f', hf', hf'e⟩ := H.h3 a f hf
  have hfun : (fun y => f (nbAct H a y)) = f' := by
    funext y
    obtain ⟨t, rfl⟩ := red_surj y
    rw [hf'e, red_mulVec]
  rw [hfun]
  exact hf'

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

private lemma smul_cancel_lemma {S K : Type*} [CommRing S] [Field K] [Algebra S K]
    (hinj : Function.Injective (algebraMap S K)) {ι κ : Type*} {M : Matrix ι κ S} (hM : M ≠ 0)
    {a b : S} (h : a • M = b • M) : a = b := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext fun x y => by simpa using hc x y)
  have h2 : a * M x y = b * M x y := by
    have := congrFun (congrFun h x) y
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  have h3 : algebraMap S K (a - b) * algebraMap S K (M x y) = 0 := by
    rw [← map_mul, sub_mul, h2, sub_self, map_zero]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (hinj (by rw [h4, map_zero]))
  · exact absurd (hinj (by rw [h4, map_zero])) hxy

end Lift

end ReciprocityTheory.PGsh.Up
