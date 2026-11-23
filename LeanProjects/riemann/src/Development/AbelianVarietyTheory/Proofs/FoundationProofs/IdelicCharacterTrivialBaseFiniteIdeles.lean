import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseIdeleTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem adele_algebraMap_apply (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k := rfl

theorem adele_mul_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a * b) v = a v * b v := rfl

theorem adele_sub_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a - b) v = a v - b v := rfl

theorem adele_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem close_scaled (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : FiniteAdeleRing (𝓞 F) F) (k m : F) (hm : m ≠ 0) (n : ℕ)
    (h : Valued.v (a v - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) * v.valuation F m) :
    Valued.v (f a P - algebraMap E _ (algebraMap F E k)) ≤
      WithZero.exp (-(n : ℤ)) * P.valuation E (algebraMap F E m) := by
  have hm1 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
  have hm2 : P.valuation E (algebraMap F E m) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simpa using hm)
  have h1 := h0 ((a - algebraMap F _ k) * algebraMap F _ m⁻¹) n (by
    rw [adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply, map_mul, val_algebraMap,
      map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm1)).2 h)
  rw [map_mul, map_sub, hf, hf, adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply,
    map_mul, val_algebraMap, map_inv₀, map_inv₀] at h1
  exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm2)).1 h1

theorem val_eq_one (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (h : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    Valued.v (f a P) = 1 := by
  have e1 : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← adele_mul_apply, Units.mul_inv, adele_one_apply, map_one]
  have e2 : Valued.v (f a P) * Valued.v (f (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) P) = 1 := by
    rw [← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]
  rw [h, one_mul] at e1
  have l1 := h0 a 0 (by simp [h])
  have l2 := h0 (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) 0 (by simp [e1])
  simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero] at l1 l2
  refine le_antisymm l1 ?_
  rw [← e2]
  exact mul_le_of_le_one_right' l2

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem algebraMap_tmul_one {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (k : R) : (algebraMap R A k) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B k) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_approx (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : FiniteAdeleRing (𝓞 F) F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (χ : HChar E) (hχ : χ.TrivOn F) (N : ℕ) (hN : 0 < N) (α : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ),
      (∀ P ∈ S, Valued.v (f α P) = P.valuation E (k P : E) ∧
        Valued.v (f α P - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E)) ∧
      (∀ P, P ∉ S → Valued.v (f α P) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) ∧
      ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) = 1 := by
  classical
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx F N hN α
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨S.biUnion (aboveF (L := E) F), fun P => upF F (k (P.under (𝓞 F))), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨v, hv, hPv⟩ := Finset.mem_biUnion.1 hP
    obtain rfl := (mem_aboveF v P).1 hPv
    obtain ⟨-, b1, b2⟩ := hS _ hv
    beta_reduce
    set kk := k (P.under (𝓞 F)) with hkk
    have hk : ((upF F kk : Eˣ) : E) = algebraMap F E kk := rfl
    rw [hk]
    have c1 := close_scaled f hf P _ (h0 P) α kk (N * kk) (mul_ne_zero hNF kk.ne_zero) 0 (by simpa using b1)
    have c2 := close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)
    refine ⟨?_, by simpa using c1⟩
    rw [← val_algebraMap]
    apply Valuation.map_eq_of_sub_lt
    rw [val_algebraMap]
    refine c2.trans_lt ?_
    have hm2 : P.valuation E (algebraMap F E kk) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp)
    refine mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro P hP
    have hv : P.under (𝓞 F) ∉ S := fun h =>
      hP (Finset.mem_biUnion.2 ⟨_, h, (mem_aboveF _ P).2 rfl⟩)
    obtain ⟨b1, b2⟩ := hS' _ hv
    refine ⟨val_eq_one f P _ (h0 P) α b1, fun h => b2 ?_⟩
    change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    simpa using h
  · rw [Finset.prod_biUnion]
    · refine Finset.prod_eq_one fun v _ => ?_
      have := hχ.1 v (k v)
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at this
      rw [← Units.coe_prod, Units.val_eq_one, ← this]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← (mem_aboveF v P).1 hP]; rfl
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]

end General

theorem finite_idele_base_trivial : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  intro D c χ hc hχ a ha
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let α : (Af D.host.F)ˣ := Units.map (sndA D.host.F).toRingHom.toMonoidHom a
  let f : Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))
  have hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ => rfl
  have hf : ∀ k : D.host.F, f (algebraMap D.host.F _ k) = algebraMap D.host.E _ (algebraMap D.host.F D.host.E k) := by
    intro k
    rw [hfa, ← h1, algebraMap_tmul_one]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (b : Af D.host.F) (n : ℕ),
      Valued.v (b (P.under (𝓞 D.host.F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)) := by
    intro P b n h
    have := h3 b 0 P n (by rwa [map_zero, sub_zero])
    rwa [map_zero, map_zero, sub_zero] at this
  have hfin : ι (finPart D (idF D a : AE D)) = f α := rfl
  obtain ⟨S, k, hS, hS', hp⟩ := exists_approx f hf h0 χ hχ N hN α
  rw [← hfin] at hS hS'
  exact Circle.ext ((hprod (idF D a) ha S k hS hS').trans hp)

end GlobalTheory.BaseIdeleTriv
