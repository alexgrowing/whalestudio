import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.TorusAverage

variable {K : Type} [Field K] [NumberField K]

noncomputable def mulHomeo (v : Pl) (u : (Qv v)ˣ) : (Qv v × Qv v) ≃ₜ (Qv v × Qv v) where
  toFun x := x * ((u : Qv v), ((u⁻¹ : (Qv v)ˣ) : Qv v))
  invFun x := x * (((u⁻¹ : (Qv v)ˣ) : Qv v), (u : Qv v))
  left_inv x := by
    ext <;> simp [mul_assoc]
  right_inv x := by
    ext <;> simp [mul_assoc]
  continuous_toFun := by
    exact continuous_id.mul continuous_const
  continuous_invFun := by
    exact continuous_id.mul continuous_const

theorem tw_ok {c : HeckeCharacter K} {v : Pl} (L : LM c v) (hL : L.ok) (u : (Qv v)ˣ) : (L.tw u).ok := by
  cases L with
  | sp w₁ w₂ Φ =>
    obtain ⟨h1, h2, h3⟩ := hL
    refine ⟨h1, ?_, ?_⟩
    · exact h2.comp_continuous (mulHomeo v u).continuous
    · exact h3.comp_homeomorph (mulHomeo v u)
  | ns w σ η Φ => exact hL

theorem tw_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.tw 1 = L := by
  cases L with
  | sp w₁ w₂ Φ =>
    simp only [LM.tw]
    congr 1
    funext x
    have : x * (((1 : (Qv v)ˣ) : Qv v), (((1 : (Qv v)ˣ)⁻¹ : (Qv v)ˣ) : Qv v)) = x := by
      ext <;> simp
    rw [this]
  | ns w σ η Φ => rfl

theorem tw_plus {c : HeckeCharacter K} {v : Pl} (L : LM c v) (u : (Qv v)ˣ) : (L.tw u).plus = L.plus := by
  cases L <;> rfl

theorem tu_off (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl}
    (h1 : v ∉ m.support) (h2 : v ∉ Sv) : tu Sv m u v = 1 := by
  have : m v = 0 := by simpa using h1
  simp [tu, this, h2]

theorem admissible_twisted_local_data {c : HeckeCharacter K} {M : ∀ v : Pl, LM c v} (hM : AdmM M) (Sv : Finset Pl)
    (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) : AdmM (twM M Sv m u) := by
  classical
  obtain ⟨hok, S0, hS0⟩ := hM
  refine ⟨fun v => tw_ok _ (hok v) _, S0 ∪ m.support ∪ Sv, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨h0, h1⟩, h2⟩ := hv
  obtain ⟨hU, hs⟩ := hS0 v h0
  refine ⟨hU, ?_⟩
  simp only [twM, tu_off Sv m u h1 h2, tw_one]
  exact hs

theorem Gp_twM {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v) (Sv : Finset Pl)
    (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) : Gp (twM M Sv m u) = Gp M := by
  ext g
  simp only [Gp, twM, tw_plus, Set.mem_setOf_eq]

theorem avg (K : Type) [Field K] [NumberField K] : Ad3.K.QuadraticBaseChangeGL3.Th.AVG K := by
  intro hT h2 hcx DK c n t S hc M hM R Sv γ hγ g hg
  unfold thA
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  funext u
  rw [hT h2 hcx DK c n t S hc (twM M Sv m u) (admissible_twisted_local_data hM Sv m u) γ hγ g
    (by rw [Gp_twM]; exact hg)]

end GlobalTheory.CompanionTheory.TorusAverage
