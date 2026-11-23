import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.StdLocal

variable {K : Type} [Field K] [NumberField K]

theorem ct_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.ct 1 = 1 := by
  cases L <;> simp [LM.ct]

theorem tw_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.tw 1 = L := by
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    have e : (((1 : (Qv v)ˣ) : Qv v), (((1 : (Qv v)ˣ)⁻¹ : (Qv v)ˣ) : Qv v)) = 1 := by
      simp [Prod.ext_iff]
    have e' : (fun x : Qv v × Qv v =>
        Φ (x * (((1 : (Qv v)ˣ) : Qv v), (((1 : (Qv v)ˣ)⁻¹ : (Qv v)ˣ) : Qv v))))  = Φ := by
      funext x
      rw [e, mul_one]
    simp only [LM.tw, e']
  | @ns w h σ η Φ => rfl

theorem degreeOneEmbedding_integral_unit (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (κ : Kˣ)
    (h : ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w])
    (h' : (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) :
    dg1 v w (κ : K) ≠ 0 ∧ dg1 v w (κ : K) ∈ 𝒪[Qv v] ∧ (dg1 v w (κ : K))⁻¹ ∈ 𝒪[Qv v] := by
  have hb := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1
  have e : ∀ ξ : K, algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
    fun ξ => Function.rightInverse_invFun hb.2 _
  have hmul : dg1 v w (κ : K) * dg1 v w ((κ⁻¹ : Kˣ) : K) = 1 := by
    apply hb.1
    rw [map_mul, e, e, map_one, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one hmul, (GlobalTheory.CompanionTheory.StdSphVal.degreeOneEmbedding_mem_integers_iff v w h1 _).2 h, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hmul]
  refine (GlobalTheory.CompanionTheory.StdSphVal.degreeOneEmbedding_mem_integers_iff v w h1 _).2 ?_
  have e2 : atW w κ⁻¹ = (atW w κ)⁻¹ := map_inv _ _
  change ((atW w κ⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]
  rw [e2]
  exact h'

theorem not_integral {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : a⁻¹ ∈ 𝒪[F]) (hb : b⁻¹ ∈ 𝒪[F]) {j : ℤ} (hj : j ≠ 0)
    (h1 : a * ((unifUnit F ^ j : Fˣ) : F) ∈ 𝒪[F])
    (h2 : b * (((unifUnit F ^ j)⁻¹ : Fˣ) : F) ∈ 𝒪[F]) : False := by
  have t0 : ((unifUnit F ^ j : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have p1 : ((unifUnit F ^ j : Fˣ) : F) ∈ 𝒪[F] := by
    have := mul_mem ha h1
    rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
  have p2 : ((unifUnit F ^ j : Fˣ) : F)⁻¹ ∈ 𝒪[F] := by
    have := mul_mem hb h2
    rwa [← mul_assoc, inv_mul_cancel₀ hb0, one_mul, Units.val_inv_eq_inv_val] at this
  have := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.ord_of_unit t0 p1 p2
  rw [ord_unifUnit_zpow] at this
  exact hj this

set_option maxHeartbeats 1000000 in

theorem fL_std : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → Unr c v → L.std → ∀ k ∈ integralGL (Qv v) 2, ∀ κ : Kˣ,
  (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧
    (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) →
  fL L k (κ : K) 1 = 1 ∧ (L.IsSp → ∀ j : ℤ, j ≠ 0 → fL L k (κ : K) (unifUnit (Qv v) ^ j) = 0) := by
  intro K _ _ h2 c v L hok hU hstd k hk κ hκ
  refine ⟨?_, ?_⟩
  · have h := (GlobalTheory.CompanionTheory.StdSphVal.val_std K h2 c v L hok hstd hU k hk (κ : K)).1
      (fun w hw => (hκ w hw).1)
    simp only [fL, ct_one, tw_one, h, one_mul]
  · intro hsp j hj
    cases L with
    | @ns w i σ η Φ => exact hsp.elim
    | @sp w₁ w₂ i₁ i₂ Φ =>
      haveI := i₁
      haveI := i₂
      obtain ⟨hne, -, -⟩ := hok
      have hΦ : Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1 := hstd
      subst hΦ
      obtain ⟨-, d₁, d₂⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne
      have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
      obtain ⟨hχc, hχ1, hχ0⟩ :=
        (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
      have r₁ : IsUnramifiedChar (cAt c v w₁) :=
        GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
      have hfix := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.piks
        (GlobalTheory.CompanionTheory.SphTheta.SplitRWK.rwks GlobalTheory.CompanionTheory.SplitRep.sRep) (Qv v) _ hχc hχ1 hχ0 _ r₁ k hk
      obtain ⟨a0, -, a1⟩ := degreeOneEmbedding_integral_unit v w₁ d₁ κ (hκ w₁ i₁).1 (hκ w₁ i₁).2
      obtain ⟨b0, -, b1⟩ := degreeOneEmbedding_integral_unit v w₂ d₂ κ (hκ w₂ i₂).1 (hκ w₂ i₂).2
      have e := GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) k
        (Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1) (unifUnit (Qv v) ^ j)
        (dg1 v w₁ (κ : K), dg1 v w₂ (κ : K))
      have hnot : (dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) *
          (((unifUnit (Qv v) ^ j : (Qv v)ˣ) : Qv v), (((unifUnit (Qv v) ^ j)⁻¹ : (Qv v)ˣ) : Qv v)) ∉
          {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} :=
        fun h => not_integral a0 b0 a1 b1 hj h.1 h.2
      simp only [fL, LM.tw, LM.val]
      rw [e, hfix, Set.indicator_of_notMem hnot, mul_zero]

end GlobalTheory.CompanionTheory.FexTheta.StdLocal
