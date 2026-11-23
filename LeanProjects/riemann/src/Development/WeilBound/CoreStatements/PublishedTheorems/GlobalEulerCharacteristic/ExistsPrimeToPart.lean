import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroReal

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.GlobalEulerCharacteristicAlt

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 1000000 in
theorem exists_prime_to_part (ℓ : ℕ) [Fact ℓ.Prime]
    (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (L : FiniteSubfield) [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (L' : FiniteSubfield) [Fact (K ≤ L')] (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hle : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (hcyc : IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) :
    ∃ (K'' : FiniteSubfield) (_ : Fact (K ≤ K''))
      (hK'' : ∀ x : K''.1, algebraMap K''.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧
      IsCyclic ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ∧
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ ∧
      ∃ hnorm : ((gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).Normal,
      (haveI := hnorm; IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) ∧
      ∃ a : ℕ, Nat.card ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) = ℓ ^ a  := by
  classical
  have hUi : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ≠ 0 := by
    rw [index_gsOpenSubgroup]
    exact Module.finrank_pos.ne'
  have hUo : IsOpen (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
      Set (galUnramifiedOutside K.1 ℚ̄ S)) := (gsOpenSubgroup S hL).isOpen
  generalize (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = U at hN hle hcyc hUi hUo ⊢
  generalize (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = W at hle hcyc ⊢
  haveI : U.FiniteIndex := ⟨hUi⟩
  haveI : (U.subgroupOf W).FiniteIndex := inferInstance
  haveI : Finite (W ⧸ U.subgroupOf W) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcomm : ∀ x y : W ⧸ U.subgroupOf W, x * y = y * x := fun x y =>
    (IsCyclic.commGroup (α := W ⧸ U.subgroupOf W)).mul_comm x y
  obtain ⟨n, hndef⟩ : ∃ n, n = Nat.card (W ⧸ U.subgroupOf W) := ⟨_, rfl⟩
  have hn : n ≠ 0 := hndef ▸ Nat.card_pos.ne'
  have hog : orderOf g = n := hndef ▸ orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨a, hadef⟩ : ∃ a, a = n.factorization ℓ := ⟨_, rfl⟩
  have hdvd : ℓ ^ a ∣ n := hadef ▸ Nat.ordProj_dvd n ℓ
  let C : Subgroup (W ⧸ U.subgroupOf W) := Subgroup.zpowers (g ^ (ℓ ^ a))
  have hCcard : Nat.card C = n / ℓ ^ a := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero) (hog ▸ hdvd), hog]
  have hCN : C.Normal := ⟨fun c hc q => by rw [hcomm q c, mul_assoc, mul_inv_cancel, mul_one]; exact hc⟩
  clear_value C
  let D : Subgroup W := C.comap (QuotientGroup.mk' (U.subgroupOf W))
  have hDN : D.Normal := hCN.comap _
  let V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S) := D.map W.subtype
  have hUV : U ≤ V := by
    intro u hu
    refine ⟨⟨u, hle hu⟩, ?_, rfl⟩
    show QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ ∈ C
    have h1 : QuotientGroup.mk' (U.subgroupOf W) ⟨u, hle hu⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨u, hle hu⟩ : W)).2 hu
    rw [h1]
    exact C.one_mem
  have hVW : V ≤ W := Subgroup.map_subtype_le D
  have hVopen : IsOpen (V : Set (galUnramifiedOutside K.1 ℚ̄ S)) :=
    Subgroup.isOpen_mono hUV hUo
  obtain ⟨K'', hK''f, hK'', hEq⟩ := exists_gsOpenSubgroup_eq (K := K) (S := S) (V := ⟨V, hVopen⟩)
  refine ⟨K'', hK''f, hK'', ?_⟩
  have hV : (gsOpenSubgroup S hK'' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = V := by
    rw [hEq]
  rw [hV]
  have hVD : V.subgroupOf W = D := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective W) D

  let ψ0 : V →* W ⧸ U.subgroupOf W := (QuotientGroup.mk' (U.subgroupOf W)).comp (Subgroup.inclusion hVW)
  have hψ0 : ∀ v : V, ψ0 v ∈ C := by
    intro v
    obtain ⟨w, hw, hwv⟩ := v.2
    have h1 : Subgroup.inclusion hVW v = w := Subtype.ext hwv.symm
    show QuotientGroup.mk' (U.subgroupOf W) (Subgroup.inclusion hVW v) ∈ C
    rw [h1]
    exact hw
  let ψ : V →* C := ψ0.codRestrict C hψ0
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H w =>
      refine ⟨⟨w.1, ⟨w, hq, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hker : ψ.ker = U.subgroupOf V := by
    ext v
    constructor
    · intro h
      have h1 : ψ0 v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 h)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).1 h1
    · intro h
      refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVW v)).2 h
  let e : V ⧸ U.subgroupOf V ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hcardVU : Nat.card (V ⧸ U.subgroupOf V) = n / ℓ ^ a := (Nat.card_congr e.toEquiv).trans hCcard
  refine ⟨hUV, hVW, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_, ?_⟩
  · show Nat.Coprime (Nat.card (V ⧸ U.subgroupOf V)) ℓ
    rw [hcardVU]
    rw [hadef]; exact (Nat.coprime_ordCompl (Fact.out : ℓ.Prime) hn).symm
  · rw [hVD]
    refine ⟨hDN, ?_, a, ?_⟩
    · let f : (W ⧸ U.subgroupOf W) →* W ⧸ D :=
        QuotientGroup.map (U.subgroupOf W) D (MonoidHom.id W) (by
          intro w hw
          show QuotientGroup.mk' (U.subgroupOf W) w ∈ C
          have h1 : QuotientGroup.mk' (U.subgroupOf W) w = 1 := (QuotientGroup.eq_one_iff w).2 hw
          rw [h1]
          exact C.one_mem)
      refine isCyclic_of_surjective f ?_
      intro x
      induction x using QuotientGroup.induction_on with
      | H w => exact ⟨QuotientGroup.mk w, rfl⟩
    · show D.index = ℓ ^ a
      have h1 : D.index = C.index := Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h2 : Nat.card C * C.index = n := hndef ▸ Subgroup.card_mul_index C
      have h3 : ℓ ^ a * (n / ℓ ^ a) = n := hadef ▸ Nat.ordProj_mul_ordCompl_eq_self n ℓ
      have hpos : 0 < n / ℓ ^ a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (pow_pos (Fact.out : ℓ.Prime).pos _)
      rw [hCcard] at h2
      rw [h1]
      have : (n / ℓ ^ a) * C.index = (n / ℓ ^ a) * ℓ ^ a := by rw [h2, mul_comm, h3]
      exact Nat.eq_of_mul_eq_mul_left hpos this

end PositivityTheory.Lit1.GEN.GlobalEulerCharacteristicAlt
