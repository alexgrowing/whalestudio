import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartLevels

theorem linIndep_rows_iff_map {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) :
    LinearIndependent k₁ y.row ↔ LinearIndependent k₂ (y.map ι).row := by
  have key : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row ↔ ∀ c : Fin m → k, c ᵥ* y = 0 → c = 0 := by
    intro k _ y
    rw [Fintype.linearIndependent_iff]
    have h : ∀ c : Fin m → k, ∑ i, c i • y.row i = c ᵥ* y := fun c => by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    simp only [h]
    exact ⟨fun H c hc => funext (H c hc), fun H c hc i => congrFun (H c hc) i⟩
  have inv : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row → ∃ B : Matrix (Fin n) (Fin m) k, y * B = 1 := by
    intro k _ y hy
    rw [key] at hy
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear y)
      (LinearMap.ker_eq_bot.2 fun a b hab => sub_eq_zero.1 (hy _ (by
        rw [Matrix.sub_vecMul]
        exact sub_eq_zero.2 hab)))
    refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
    have hc : ∀ c : Fin m → k, c ᵥ* (y * (LinearMap.toMatrix' g)ᵀ) = c := fun c => by
      rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
      exact congrArg (fun f => f c) hg
    refine Matrix.ext fun i j => ?_
    have := congrFun (hc (Pi.single i 1)) j
    rw [Matrix.single_one_vecMul] at this
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
  constructor
  · intro hy
    obtain ⟨B, hB⟩ := inv y hy
    rw [key]
    intro c hc
    have : c ᵥ* ((y.map ι) * B.map ι) = c := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ ι.map_zero ι.map_one, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul] at this
    exact this.symm
  · intro hy
    rw [key] at hy ⊢
    intro c hc
    have h1 := hy (ι ∘ c) (funext fun j => by
      rw [← RingHom.map_vecMul, hc]
      simp)
    funext i
    exact ι.injective ((congrFun h1 i).trans ι.map_zero.symm)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem residue_eq_zero_iff (x : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx fun h1 => hnu ?_
    have h0 : (x : Fv D.host.F v) ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (x : Fv D.host.F v)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, h1, inv_one])
    refine IsUnit.of_mul_eq_one (a := x) ⟨_, hmem⟩ (Subtype.ext ?_)
    show (x : Fv D.host.F v) * (x : Fv D.host.F v)⁻¹ = 1
    exact mul_inv_cancel₀ h0
  · intro hlt hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h2 := congrArg (fun t : GlobalTheory.SplitHecke.Ov D v => Valued.v (t : Fv D.host.F v)) hw
    have hw1 : Valued.v (w : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 w.2
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
    have : Valued.v (x : Fv D.host.F v) * Valued.v (w : Fv D.host.F v) < 1 :=
      (mul_le_of_le_one_right' hw1).trans_lt hlt
    rw [h2] at this
    exact lt_irrefl _ this

theorem resS_surjective (PP : Pl D.host.E) : Function.Surjective (resS D.host.F PP) := by
  rw [resS, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp Ideal.Quotient.mk_surjective

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem prim_map_eq {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) : prim (y.map ι) = prim y := by
  unfold prim
  by_cases h : LinearIndependent k₁ y.row
  · rw [if_pos h, if_pos ((linIndep_rows_iff_map ι y).1 h)]
  · rw [if_neg h, if_neg (mt (linIndep_rows_iff_map ι y).2 h)]

theorem gl_map_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (β : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.map f β)⁻¹).1 = (β⁻¹).1.map f := by
  rw [← map_inv]
  rfl

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem frame_of_baseFrame {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (φ : Datum.EAf D →+* Fv D.host.F v) (hφ : ∀ a, φ (toEAf D a) = π a)
    (hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N))
    (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ : Lev.IsBaseFrame V β Λ 1) : GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro y
  have hL := (GlobalTheory.FinAdIdent.lamHat_good hβ (f := 1) ⟨mul_one 1, 1, by simp⟩).2
  have hL' : ∀ x, x ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => Lev.swapAE D (x a)) ∈ Formalism.L2.Herm.hatL Λ :=
    fun x => by simpa only [one_smul, one_mul] using hL x
  refine (hL' _).trans ((hβ.1 _).trans (forall_congr' fun i => ?_))
  have e2 : (fun a => Lev.swapAE D (finPart D (e * y a))) = toEAf D e • (fun a => toEAf D (y a)) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    rfl
  have e4 : (φ ∘ fun a => toEAf D (y a)) = fun k => π (y k) := funext fun k => hφ (y k)
  rw [e2, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hint, RingHom.map_mulVec, e4, gl_map_inv_val]

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem chart_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro D e P v π he hπ
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e P he
  have hπe : π e = 1 := hπ.map_e he.1.1
  have hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N) := by
    intro N
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) N
    rw [hφ, ← (hπ.2.2.2 a), ← RingHom.map_mul]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  refine ⟨φ, hφ, hint, ?_, ?_⟩
  · have hR : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := fun s =>
      GlobalTheory.SplitHecke.isInt_Ov.1 ((hint s).1 (mul_mem hi s.2))
    let φR : Formalism.L2.Herm.intAf D.host.F D.host.E →+* GlobalTheory.SplitHecke.Ov D v :=
      (φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hR
    let ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (IsLocalRing.residue _).comp φR
    have hker : RingHom.ker (resS D.host.F P) ≤ RingHom.ker ρ := by
      intro s hs
      rw [RingHom.mem_ker] at hs ⊢
      exact (residue_eq_zero_iff (φR s)).2 (hres s hs)
    let ι : kP P →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (resS D.host.F P).liftOfRightInverse _ (Function.rightInverse_surjInv (resS_surjective P)) ⟨ρ, hker⟩
    have hι : ∀ s, ι (resS D.host.F P s) = ρ s := fun s =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
    intro m n N hN z hz
    have e1 : z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) = (redM P N).map ι := by
      ext i j
      have hzij : z i j = φR ⟨N i j, hN i j⟩ := Subtype.ext (congrFun (congrFun hz i) j)
      simp only [Matrix.map_apply, redM, dif_pos (hN i j), hι, hzij]
      rfl
    rw [e1]
    exact (prim_map_eq ι _).symm
  · exact frame_of_baseFrame φ hφ hint

end GlobalTheory.ChartLevels
