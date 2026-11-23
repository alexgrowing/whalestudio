import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PExistsUniqueRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)

noncomputable section

namespace JoinDivCycle

variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinIdxEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      have : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst this
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

def joinPolyEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+* Polynomial (MRing ι R) :=
  ((renameEquiv R (joinIdxEquiv (ι := ι))).trans (optionEquivLeft R (Σ k, ι k))).toRingEquiv

theorem joinPolyEquiv_comp_rename :
    (joinPolyEquiv (R := R) (ι := ι)).toRingHom.comp (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [joinPolyEquiv, optionEquivLeft_C]
  · intro p
    simp [joinPolyEquiv, joinIdxEquiv, liftVar, optionEquivLeft_X_some]

theorem rename_eq_symm_comp_C :
    (rename (R := R) (liftVar (ι := ι) ptIdx)).toRingHom =
      (joinPolyEquiv (R := R) (ι := ι)).symm.toRingHom.comp Polynomial.C := by
  rw [← joinPolyEquiv_comp_rename, ← RingHom.comp_assoc]
  ext x <;> simp

set_option hygiene false in

local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)

set_option hygiene false in

local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)

theorem joinPolyEquiv_rename (x : MRing ι R) : joinPolyEquiv (ε x) = Polynomial.C x :=
  RingHom.congr_fun joinPolyEquiv_comp_rename x

theorem map_rename_eq (I : Ideal (MRing ι R)) :
    I.map ε = (I.map (Polynomial.C : MRing ι R →+* _)).comap (joinPolyEquiv (R := R) (ι := ι)).toRingHom := by
  have h : I.map ε = I.map (ε).toRingHom := rfl
  rw [h, rename_eq_symm_comp_C, ← Ideal.map_map]
  exact Ideal.map_symm _

theorem mem_map_rename_iff (I : Ideal (MRing ι R)) (x) :
    x ∈ I.map ε ↔ joinPolyEquiv x ∈ I.map (Polynomial.C : MRing ι R →+* _) := by
  rw [map_rename_eq]
  rfl

theorem rename_mem_map_rename_iff (I : Ideal (MRing ι R)) (x : MRing ι R) : ε x ∈ I.map ε ↔ x ∈ I := by
  rw [mem_map_rename_iff, joinPolyEquiv_rename, ← Ideal.mem_comap, comap_C_map_C_polynomial]

theorem comap_map_rename (I : Ideal (MRing ι R)) : (I.map ε).comap ε = I := by
  ext x
  exact rename_mem_map_rename_iff I x

theorem isPrime_map_rename (Q : Ideal (MRing ι R)) [Q.IsPrime] : (Q.map ε).IsPrime := by
  rw [map_rename_eq]
  infer_instance

theorem mem_minimalPrimes_map_rename_iff (J : Ideal (MRing ι R))
    (W : Ideal (MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R)) :
    W ∈ (J.map ε).minimalPrimes ↔ ∃ Q ∈ J.minimalPrimes, Q.map ε = W := by
  constructor
  · intro hW
    have : W.IsPrime := hW.1.1
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hW.1.2)
    have : Q.IsPrime := hQ.1.1
    have hle : Q.map ε ≤ W := Ideal.map_le_iff_le_comap.mpr hQle
    exact ⟨Q, hQ, le_antisymm hle (hW.2 ⟨isPrime_map_rename Q, Ideal.map_mono hQ.1.2⟩ hle)⟩
  · rintro ⟨Q, hQ, rfl⟩
    have : Q.IsPrime := hQ.1.1
    refine ⟨⟨isPrime_map_rename Q, Ideal.map_mono hQ.1.2⟩, fun W hW hWle => ?_⟩
    have : W.IsPrime := hW.1
    have h1 : W.comap ε ≤ Q := (Ideal.comap_mono hWle).trans (comap_map_rename Q).le
    exact Ideal.map_le_iff_le_comap.mpr (hQ.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hW.2⟩ h1)

theorem isRelevant_map_rename_iff (Q : Ideal (MRing ι R)) (hQ : Q ≠ ⊤) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (Q.map ε) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h (.inl k)
    refine ⟨i, fun hx => hi ?_⟩
    have hX : (X ⟨.inl k, i⟩ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) = ε (X ⟨k, i⟩) := by
      simp [liftVar]
    rw [hX]
    exact Ideal.mem_map_of_mem _ hx
  · intro h k
    rcases k with k | u
    · obtain ⟨i, hi⟩ := h k
      refine ⟨i, fun hx => hi ?_⟩
      rw [← rename_mem_map_rename_iff Q]
      simpa [liftVar] using hx
    · refine ⟨(0 : Fin 1), fun hx => hQ ?_⟩
      rw [mem_map_rename_iff] at hx
      have hX : joinPolyEquiv (R := R) (ι := ι)
          (X ⟨.inr u, (0 : Fin 1)⟩ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) = Polynomial.X := by
        cases u
        simp [joinPolyEquiv, joinIdxEquiv, optionEquivLeft_X_none]
      rw [hX, Ideal.mem_map_C_iff] at hx
      have h1 := hx 1
      rw [Polynomial.coeff_X_one] at h1
      exact (Ideal.eq_top_iff_one Q).mpr h1

theorem multAt_map_rename (P Q : Ideal (MRing ι R)) [Q.IsPrime] (hPQ : P ≤ Q) (f : MRing ι R) :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (P.map ε ⊔ Ideal.span {ε f}) (Q.map ε) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {f}) Q := by
  have hm : ∀ I : Ideal (MRing ι R),
      I.map ε = (I.map (Polynomial.C : MRing ι R →+* _)).map ((ψ).symm : Polynomial (MRing ι R) →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) := by
    intro I
    rw [map_rename_eq]
    exact (Ideal.map_symm (joinPolyEquiv (R := R) (ι := ι))).symm
  have hf : ε f = (ψ).symm (Polynomial.C f) := by
    rw [← joinPolyEquiv_rename, RingEquiv.symm_apply_apply]
  haveI : (Q.map (Polynomial.C : MRing ι R →+* _)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hQp : ((Q.map (Polynomial.C : MRing ι R →+* _)).map ((ψ).symm : Polynomial (MRing ι R) →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R)).IsPrime := by
    rw [← hm]
    exact isPrime_map_rename Q
  haveI := hQp
  have key := GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.length_map (ψ).symm
    (P.map (Polynomial.C : MRing ι R →+* _)) (Q.map (Polynomial.C : MRing ι R →+* _)) (Ideal.map_mono hPQ)
    (Polynomial.C f)
  have hsup : P.map (Polynomial.C : MRing ι R →+* _) ⊔ Ideal.span {Polynomial.C f} =
      (P ⊔ Ideal.span {f}).map (Polynomial.C : MRing ι R →+* _) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hsup, PolynomialLocalizedLength.full (MRing ι R) Q (P ⊔ Ideal.span {f})] at key
  rw [hm P, hm Q, hf]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt
  rw [dif_pos hQp, dif_pos ‹Q.IsPrime›]
  exact congrArg ENat.toNat key

end JoinDivCycle

open JoinDivCycle in

theorem JoinDivCycle.proof : JoinDivCycle.Statement := by
  intro R _ _ K _ ι _ P f
  classical
  have hinj : Function.Injective (Ideal.map (rename (R := R) (liftVar (ι := ι) ptIdx))) := fun I I' h => by
    rw [← comap_map_rename I, ← comap_map_rename I']
    exact congrArg (Ideal.comap (rename (R := R) (liftVar (ι := ι) ptIdx))) h
  have hsup : P.map (rename (R := R) (liftVar (ι := ι) ptIdx)) ⊔
      Ideal.span {rename (R := R) (liftVar (ι := ι) ptIdx) f} =
      (P ⊔ Ideal.span {f}).map (rename (R := R) (liftVar (ι := ι) ptIdx)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hsupp : ∀ Q, Q.map (rename (R := R) (liftVar (ι := ι) ptIdx)) ∈
      ReciprocityTheory.ChartRestriction.G.Geo.divSupp (P.map (rename (R := R) (liftVar (ι := ι) ptIdx)))
        (rename (R := R) (liftVar (ι := ι) ptIdx) f) ↔ Q ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P f := by
    intro Q
    show (_ ∈ _ ∧ _) ↔ (_ ∈ _ ∧ _)
    rw [hsup, mem_minimalPrimes_map_rename_iff]
    constructor
    · rintro ⟨⟨Q₀, hQ₀, h⟩, hr⟩
      obtain rfl := hinj h
      exact ⟨hQ₀, (isRelevant_map_rename_iff Q₀ hQ₀.1.1.ne_top).1 hr⟩
    · rintro ⟨hQ, hr⟩
      exact ⟨⟨Q, hQ, rfl⟩, (isRelevant_map_rename_iff Q hQ.1.1.ne_top).2 hr⟩
  ext W
  by_cases hW : ∃ Q : Ideal (MRing ι R), Q.map (rename (R := R) (liftVar (ι := ι) ptIdx)) = W
  · obtain ⟨Q, rfl⟩ := hW
    rw [Finsupp.mapDomain_apply hinj]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    by_cases hQ : Q ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P f
    · haveI : Q.IsPrime := hQ.1.1.1
      rw [if_pos ((hsupp Q).2 hQ), if_pos hQ,
        multAt_map_rename P Q (le_sup_left.trans hQ.1.1.2) f]
    · rw [if_neg (fun h => hQ ((hsupp Q).1 h)), if_neg hQ]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨Q, hQ⟩; exact hW ⟨Q, hQ⟩)]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    rw [hsup, mem_minimalPrimes_map_rename_iff] at hmin
    obtain ⟨Q, -, hQ⟩ := hmin
    exact hW ⟨Q, hQ⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
