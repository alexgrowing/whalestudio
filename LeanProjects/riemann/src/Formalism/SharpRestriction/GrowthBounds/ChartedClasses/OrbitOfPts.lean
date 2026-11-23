import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p}

def CompInj (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) : Prop :=
  ∀ (i i' : G.comp) (δ : GL (Fin n) E), δ ∈ UJ (σ : E →+* E) J →
    (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) ((A.yG i')⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * A.yG i) ∈ S.Uloc w) → i = i'

variable {A : LocAt F E n G} {S : StepLevel F E σ J T f bad}

variable (H : LocGood σ J A) (hW : LocInt A) (hHc : LocHypC S A) (hA : A.ActB)
  (hΓ : ∀ i (γ : (G.lev i).Γ), (A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i ∈
        UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w)
        ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i) ∈ S.Uloc w)

include H hA hΓ in

theorem pt_smul (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ₀ : GL (Fin n) E) (κ₀ : S.U)
    (hx : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1)) (γ : (G.lev i).Γ) :
    ∃ κ₁ : S.U, A.IsPt i (fun v => (G.lev i).act v γ * g v)
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * y * κ₁.1) := by
  obtain ⟨κ, hκ⟩ := awayEx_of H S hΓ i γ
  have hx' := A.isPt_smul hA i g _ κ.1 hx γ hκ
  refine ⟨κ₀ * κ⁻¹, ?_⟩
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * y * (κ₀ * κ⁻¹ : S.U).1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) * κ.1⁻¹ := by
    rw [map_mul]
    show _ * _ * (κ₀.1 * κ.1⁻¹) = _
    group
  rw [e]
  exact hx'

set_option maxHeartbeats 2000000 in
include H hW hHc hA hΓ in

theorem orbit_of_pts (hci : CompInj S A) (hon : ∀ i, GamOnto S A i) (i i' : G.comp) (L L' : G.P.Tup)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hL' : ∀ v, L' v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ₀ γ₁ : GL (Fin n) E)
    (hγ₀ : γ₀ ∈ UJ (σ : E →+* E) J) (hγ₁ : γ₁ ∈ UJ (σ : E →+* E) J) (κ₀ κ₁ : S.U)
    (h0 : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1))
    (h1 : A.IsPt i' g' (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * y * κ₁.1)) :
    i = i' ∧ ∃ γ : (G.lev i).Γ, A.gamI i γ = γ₁ * γ₀⁻¹ ∧ L' = (G.lev i).smul γ L := by
  have hδ : γ₁ * γ₀⁻¹ ∈ UJ (σ : E →+* E) J := Subgroup.mul_mem _ hγ₁ (Subgroup.inv_mem _ hγ₀)
  have hκU : κ₀.1⁻¹ * κ₁.1 ∈ S.U := S.U.mul_mem (S.U.inv_mem κ₀.2) κ₁.2
  have hrel : (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * y * κ₁.1)⁻¹ *
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₁ * γ₀⁻¹) *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) = (κ₀.1⁻¹ * κ₁.1)⁻¹ := by
    rw [map_mul, map_inv]; group
  have hoff : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) ((A.yG i')⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ₁ * γ₀⁻¹) * A.yG i) ∈ S.Uloc w := by
    intro w hw
    have h2 := ((S.U_eq _).1 (S.U.inv_mem hκU)).2 w
    rw [← hrel, map_mul (bc (prV (E := E) w)), map_mul (bc (prV (E := E) w)), map_inv (bc (prV (E := E) w)), h0.1 w hw, h1.1 w hw] at h2
    rw [map_mul (bc (prV (E := E) w)), map_mul (bc (prV (E := E) w)), map_inv (bc (prV (E := E) w))]
    exact h2
  obtain rfl := hci i i' _ hδ hoff
  refine ⟨rfl, ?_⟩
  obtain ⟨γ, hγ⟩ := hon i _ hδ hoff
  refine ⟨γ, hγ, ?_⟩
  obtain ⟨κ, hκ⟩ := awayEx_of H S hΓ i γ
  have hx' := A.isPt_smul hA i g _ κ.1 h0 γ hκ
  have hmU : (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) * κ.1⁻¹)⁻¹ *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * y * κ₁.1) ∈ S.U := by
    have e : (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * y * κ₀.1) * κ.1⁻¹)⁻¹ *
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₁ * y * κ₁.1) = κ.1 * (κ₀.1⁻¹ * κ₁.1) := by
      have hγ' : A.gamI i γ = γ₁ * γ₀⁻¹ := hγ
      rw [hγ', map_mul, map_inv]; group
    rw [e]
    exact S.U.mul_mem κ.2 hκU
  funext v
  have hloc := ((S.U_eq _).1 hmU).2 (A.pl v).1
  obtain ⟨k1, k2⟩ := hHc v _ hloc
  rw [ff_quot i _ g' _ _ hx' h1 v] at k1 k2
  rw [← map_inv, ← map_inv] at k2
  have hst : ((G.lev i).act v γ * g v)⁻¹ * g' v ∈ stabStd (k := G.P.m + 1) (Qq := G.P.Qq v) (G.P.W v) :=
    (stabStd_iff _ _).2 ⟨int_of_eQ hW v _ k1, int_of_eQ hW v _ k2⟩
  rw [smul_colSpan i γ L g hL v, hL' v, colSpan_eq, colSpan_eq]
  exact (gMap_std_eq_iff _ _ _).2 hst

end Gen

end Formalism.MainNotions.G.KAat

end
