import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemAct :
    MemSum → SumDoset → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → MemAct := by
  intro hMS hSD hTF hS X M M' _ _ _ T L' Kw hfT hap K KM htr hfK hK0 hKM hidx hnor t z h hz hh hc
  have hKMK : KM ≤ K := hKM.trans hK0
  have hcK : ∀ u ∈ KM, h * u * h⁻¹ ∈ K := fun u hu => hK0 (by simpa using hc 1 K.one_mem u hu)
  obtain ⟨hmem, -, hsum⟩ := hMS X K KM T.K₀ h hK0 hidx hnor hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [map_mul, hap.1 t, hz.2, one_mul]
  · intro V _ _ Φ hΦ
    have hΦK : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g := by
      intro k hk g
      rw [hΦ k (htr.1 hk) g, htr.2 k hk, Units.val_one, one_smul]
    have hΦ0 : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g := fun k hk g => hΦK k (hK0 hk) g
    funext g
    rw [Pi.smul_apply, hsum V Φ hΦ0 g, hSD X K KM h hKMK hidx hcK V Φ hΦK hnor g,
      hTF X M M' T L' Kw hfT hap t z hz V Φ hΦ g]
    congr 1
    refine Eq.trans ?_ (hS X M' L' K Kw hfK t V (fun y => Φ (g * z * y)) ?_)
    · show ∑ᶠ x : X ⧸ K, dosetInd ℂ K h⁻¹ x.out • Φ (g * x.out) =
        ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Φ (g * z * y.out)
      rw [hh, ← finsum_comp_equiv (MulAction.toPerm z : Equiv.Perm (X ⧸ K))]
      refine finsum_congr fun q => ?_
      have hzq : (MulAction.toPerm z q : X ⧸ K) = ((z * q.out : X) : X ⧸ K) := by
        rw [MulAction.toPerm_apply]
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (z * q.out)
      have e1 : Φ (g * (z * q.out * k)) = Φ (g * z * q.out) := by
        rw [← mul_assoc, hΦK _ k.2, ← mul_assoc]
      have hmem2 : z * q.out * k ∈ DoubleCoset.doubleCoset (L'.loc t * z) (K : Set X) K ↔
          q.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
        simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
        constructor
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * (k : X)⁻¹, K.mul_mem hb (K.inv_mem k.2), ?_⟩
          have hw : a * (L'.loc t * z) * b = z * (a * L'.loc t * b) := by
            rw [← mul_assoc a, ← hz.1, mul_assoc z]
          calc q.out = z⁻¹ * (z * q.out * k) * (k : X)⁻¹ := by group
            _ = z⁻¹ * (z * (a * L'.loc t * b)) * (k : X)⁻¹ := by rw [e, hw]
            _ = a * L'.loc t * (b * (k : X)⁻¹) := by group
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * k, K.mul_mem hb k.2, ?_⟩
          rw [e, ← mul_assoc a, ← hz.1]
          group
      have e2 : dosetInd ℂ K (L'.loc t * z) (z * q.out * k) = dosetInd ℂ K (L'.loc t) q.out := by
        unfold dosetInd
        simp only [Set.indicator_apply, hmem2, Pi.one_apply]
      rw [hzq, hk, e1, e2]
    · intro k hk y
      show Φ (g * z * (y * k)) = Φ (g * z * y)
      rw [← mul_assoc]
      exact hΦK k hk _
