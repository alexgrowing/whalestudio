import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

set_option autoImplicit false

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef
open GlobalTheory.CuspRep (pLoc)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw mat)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem small_of_nhds {E : Type} [Field E] [NumberField E] (w : Plc E) {U : Set (w.adicCompletion E)}
    (hU : U ∈ 𝓝 (0 : w.adicCompletion E)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : w.adicCompletion E, Valued.v x ≤ Valued.v (M : w.adicCompletion E) → x ∈ U := by
  obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_iff.1 hU
  have hball := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_of_mem (i := γ) trivial
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hlt : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) < 1 := by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w _).2 hm
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E)) =
        w.valuation E (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) =
        ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) := by simp
    rw [h3] at h2
    rw [h2]
    exact h1
  obtain ⟨m, hm⟩ := ((Valued.tendsto_zero_pow_of_v_lt_one hlt).eventually hball).exists
  refine ⟨Ideal.absNorm w.asIdeal ^ m, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), fun x hx => hγ ?_⟩
  have hx' : Valued.v x ≤ Valued.v (((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) ^ m) := by
    simpa using hx
  exact lt_of_le_of_lt ((Valuation.restrict_le_iff _).2 hx') hm

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.facCont :
    UpperTheory.Gal.Spc.FacCont := by
  intro E _ _ _ A n p _ S F w L hL
  have hI := pKNIff (pLatCoord pRepLaws)
  have key : ∀ M : ℕ, 0 < M → ∀ k ∈ S.L.KN M, Cong1 M w.1 (F.a w.1 * L.pr k * (F.a w.1)⁻¹) := by
    intro M hM k hk
    obtain ⟨g, rfl⟩ := F.surj k
    have h1 : S.L.CongOne M (F.tr.j g) := by rw [← F.j_tr]; exact hk.1
    have h2 := ((hI E A n p S F.tr g).2 M hM).1 h1 w.1 w.2.2
    have h3 : UpperTheory.Gal.CertificateRingHomMap.comp w.1 g = GeneralLinearGroup.map (pLoc E w.1) (mat g) := rfl
    rw [hL.1 g, F.a_tr, h3]
    simpa [map_mul, map_inv] using h2
  have hopen : ∀ M : ℕ, 0 < M → (S.L.KN M : Set S.G.GAf) ∈ 𝓝 (1 : S.G.GAf) := by
    intro M hM
    obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p S.D S.G S.L M hM
    have ho : IsOpen (S.L.KN M : Set S.G.GAf) := hK ▸ K.K.isOpen
    exact ho.mem_nhds (one_mem _)

  have hent : ∀ i j, Filter.Tendsto (fun k => ((F.a w.1 * L.pr k * (F.a w.1)⁻¹).val - 1) i j) (𝓝 (1 : S.G.GAf)) (𝓝 0) := by
    intro i j U hU
    obtain ⟨M, hM, hsm⟩ := small_of_nhds w.1 hU
    exact Filter.mem_map.2 (Filter.mem_of_superset (hopen M hM) fun k hk => hsm _ (key M hM k hk i j))
  have hmat : Filter.Tendsto (fun k => (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val) (𝓝 (1 : S.G.GAf))
      (𝓝 (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (hent i j).add_const ((1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j)
    simpa [Matrix.sub_apply] using this
  have hval : ContinuousAt (fun k => (L.pr k).val) (1 : S.G.GAf) := by
    have h := ((tendsto_const_nhds (x := ((F.a w.1)⁻¹).val)).mul hmat).mul (tendsto_const_nhds (x := (F.a w.1).val))
    have h1 : ((F.a w.1)⁻¹).val * 1 * (F.a w.1).val = (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := by
      rw [mul_one]; exact (F.a w.1).inv_mul
    rw [h1] at h
    have h2 : ∀ k, ((F.a w.1)⁻¹).val * (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val * (F.a w.1).val = (L.pr k).val := by
      intro k
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    simp only [h2] at h
    simpa [ContinuousAt] using h
  have hinv : ContinuousAt (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) (1 : S.G.GAf) := by
    have h : ContinuousAt (fun k : S.G.GAf => k⁻¹) 1 := continuous_inv.continuousAt
    have h' : ContinuousAt (fun k => (L.pr k).val) ((1 : S.G.GAf)⁻¹) := by simpa using hval
    have h2 : (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) =
        (fun k => (L.pr k).val) ∘ (fun k : S.G.GAf => k⁻¹) := by
      funext k
      simp only [Function.comp, map_inv]
    rw [h2]
    exact ContinuousAt.comp h' h
  refine continuous_of_continuousAt_one L.pr ?_
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact hval.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
