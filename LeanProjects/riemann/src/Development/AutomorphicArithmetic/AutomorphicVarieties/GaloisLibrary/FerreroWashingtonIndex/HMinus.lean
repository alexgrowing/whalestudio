import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RealGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Mk0PrincipalEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

section

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {ι : Type}

private theorem hMinus_im (φ : K →+* ℂ) {a : K} (ha : cE K a = a) : (φ a).im = 0 := by
  have h := IsCMField.complexEmbedding_complexConj K φ a
  have h2 : IsCMField.complexConj K a = a := ha
  rw [h2] at h
  exact Complex.conj_eq_iff_im.1 h.symm

private theorem hMinus_re (φ : K →+* ℂ) {a : K} (ha : cE K a = a) (h0 : a ≠ 0) : (φ a).re ≠ 0 := by
  intro hre
  apply h0
  have h : φ a = 0 := Complex.ext hre (hMinus_im φ ha)
  exact φ.injective (by rw [h, map_zero])

private theorem hMinus_mul (e : ι → K →+* ℂ) {a b : K} (ha : cE K a = a) (ha0 : a ≠ 0) (hb : cE K b = b) (hb0 : b ≠ 0) :
    sgn e (a * b) = sgn e a + sgn e b := by
  funext i
  simp only [sgn, Pi.add_apply, map_mul, Complex.mul_re, hMinus_im (e i) ha, hMinus_im (e i) hb,
    mul_zero, sub_zero]
  have h1 := hMinus_re (e i) ha ha0
  have h2 := hMinus_re (e i) hb hb0
  rcases h1.lt_or_gt with p | p <;> rcases h2.lt_or_gt with q | q
  · rw [if_neg (not_lt.mpr (mul_pos_of_neg_of_neg p q).le), if_pos p, if_pos q]
    decide
  · rw [if_pos (mul_neg_of_neg_of_pos p q), if_pos p, if_neg (not_lt.mpr q.le)]
    decide
  · rw [if_pos (mul_neg_of_pos_of_neg p q), if_neg (not_lt.mpr p.le), if_pos q]
    decide
  · rw [if_neg (not_lt.mpr (mul_pos p q).le), if_neg (not_lt.mpr p.le), if_neg (not_lt.mpr q.le)]
    decide

private theorem hMinus_neg (f : ι → ZMod 2) : -f = f := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

private theorem hMinus_ne (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) ≠ 0 := by
  intro h
  apply u.ne_zero
  exact RingOfIntegers.ext (h.trans (by simp))

private theorem hMinus_unit (e : ι → K →+* ℂ) {f : ι → ZMod 2} (hf : f ∈ sgnE e) :
    ∃ u : (𝓞 K)ˣ, cE K ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K) ∧ f = sgn e ((u : 𝓞 K) : K) := by
  unfold sgnE at hf
  induction hf using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨1, by simp, ?_⟩
    funext i
    simp [sgn]
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨u * v, ?_, ?_⟩
    · push_cast
      rw [map_mul, hu, hv]
    · push_cast
      rw [hMinus_mul e hu (hMinus_ne u) hv (hMinus_ne v)]
  | neg x _ hx =>
    rwa [hMinus_neg]

private theorem hMinus_pos (e : ι → K →+* ℂ) (he : Function.Surjective e) {a : K} (ha : cE K a = a) (h0 : a ≠ 0)
    (h : sgn e a = 0) (φ : K →+* ℂ) : 0 < (φ a).re := by
  obtain ⟨i, rfl⟩ := he φ
  have hi := congr_fun h i
  simp only [sgn, Pi.zero_apply] at hi
  split_ifs at hi with hlt
  · exact absurd hi (by decide)
  · exact lt_of_le_of_ne (not_lt.mp hlt) (hMinus_re (e i) ha h0).symm

end

private theorem idMap_complexConj_involutive {K : Type} [Field K] [NumberField K] [IsCMField K] (I : ↥(Ideal (𝓞 K))⁰) :
    idMap (cE K) (idMap (cE K) I) = I := by
  apply Subtype.ext
  show Ideal.map (RingOfIntegers.mapRingEquiv (cE K))
    (Ideal.map (RingOfIntegers.mapRingEquiv (cE K)) (I : Ideal (𝓞 K))) = I
  have hs : (RingOfIntegers.mapRingEquiv (cE K)).symm = RingOfIntegers.mapRingEquiv (cE K) := by
    ext x
    simp only [cE, RingOfIntegers.mapRingEquiv_symm_apply, RingOfIntegers.mapRingEquiv_apply]
    simp
    rw [AlgEquiv.symm_apply_eq, IsCMField.complexConj_apply_apply]
  have h := Ideal.map_of_equiv (I := (I : Ideal (𝓞 K))) (RingOfIntegers.mapRingEquiv (cE K))
  rw [hs] at h
  exact h

private theorem classGroup_inv_mul_mem_difR_of_sign {K : Type} [Field K] [NumberField K] [IsCMField K] {ι : Type} (e : ι → K →+* ℂ)
    (hU : UnrFin K) (he : Function.Surjective e) (I J : ↥(Ideal (𝓞 K))⁰) (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (har : cE K (a : K) = a) (hbr : cE K (b : K) = b)
    (hIa : ((I * idMap (cE K) I : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {a})
    (hJb : ((J * idMap (cE K) J : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {b})
    (hx : ClassGroup.mk0 I ∈ minK (clMap (cE K))) (hs : sgn e (a : K) + sgn e (b : K) ∈ sgnE e) :
    (ClassGroup.mk0 I)⁻¹ * ClassGroup.mk0 J ∈ difR (clMap (cE K)) := by
  obtain ⟨u, hu, hsu⟩ := hMinus_unit e hs
  have ha0' : (a : K) ≠ 0 := fun h => ha0 (RingOfIntegers.ext (h.trans (by simp)))
  have hb0' : (b : K) ≠ 0 := fun h => hb0 (RingOfIntegers.ext (h.trans (by simp)))
  have habr : cE K ((a : K) * b) = (a : K) * b := by rw [map_mul, har, hbr]
  have hab0 : (a : K) * b ≠ 0 := mul_ne_zero ha0' hb0'
  have hcr : cE K (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = ((a * b * (u : 𝓞 K) : 𝓞 K) : K) := by
    push_cast
    rw [map_mul, habr, hu]
  have hc0 : (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hab0 (hMinus_ne u)
  have hcs : sgn e (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = 0 := by
    have e1 : (((a * b * (u : 𝓞 K) : 𝓞 K)) : K) = (a : K) * b * ((u : 𝓞 K) : K) := by push_cast; rfl
    rw [e1, hMinus_mul e habr hab0 hu (hMinus_ne u), hMinus_mul e har ha0' hbr hb0', hsu]
    calc sgn e ((u : 𝓞 K) : K) + sgn e ((u : 𝓞 K) : K)
        = -sgn e ((u : 𝓞 K) : K) + sgn e ((u : 𝓞 K) : K) := by rw [hMinus_neg]
      _ = 0 := neg_add_cancel _
  have hpos : ∀ φ : K →+* ℂ, 0 < (φ (((a * b * (u : 𝓞 K) : 𝓞 K)) : K)).re :=
    hMinus_pos e he hcr hc0 hcs
  have hL : ((idMap (cE K) I * J) * idMap (cE K) (idMap (cE K) I * J) : ↥(Ideal (𝓞 K))⁰) =
      (I * idMap (cE K) I) * (J * idMap (cE K) J) := by
    rw [map_mul, idMap_complexConj_involutive]
    ac_rfl
  have hLs : (((idMap (cE K) I * J) * idMap (cE K) (idMap (cE K) I * J) : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      Ideal.span {a * b * (u : 𝓞 K)} := by
    rw [hL, Submonoid.coe_mul, hIa, hJb, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_right_unit u.isUnit]
  have hmem := hasse K (a * b * (u : 𝓞 K)) (idMap (cE K) I * J) hU hcr hpos hLs
  have hinv : clMap (cE K) (ClassGroup.mk0 I) = (ClassGroup.mk0 I)⁻¹ := by
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply] at hx
    exact eq_inv_of_mul_eq_one_left hx
  rwa [map_mul, ← class_map_mk0, hinv] at hmem

theorem UpperTheory.V.FW.hMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Finite ι] (e : ι → K →+* ℂ) (V : AddSubgroup (ι → ZMod 2)), UnrFin K → Function.Surjective (IsCMField.unitsMulComplexConjInv K) → Function.Surjective e → (∀ a : K, cE K a = a → sgn e a ∈ V) → (difR (clMap (cE K))).relIndex (minK (clMap (cE K))) ≤ (sgnE e).relIndex V := by
  intro K _ _ _ ι _ e V hU hsurj he hV
  have hx : ∀ x : minK (clMap (cE K)), ∃ (I : ↥(Ideal (𝓞 K))⁰) (a : 𝓞 K),
      ClassGroup.mk0 I = (x : ClassGroup (𝓞 K)) ∧ a ≠ 0 ∧ cE K (a : K) = a ∧
      ((I * idMap (cE K) I : ↥(Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {a} :=
    fun x => realGen K x hsurj x.2
  choose I a hI ha0 har hIa using hx
  let g : minK (clMap (cE K)) → V := fun x => ⟨sgn e (a x : K), hV _ (har x)⟩
  let F : minK (clMap (cE K)) ⧸ (difR (clMap (cE K))).subgroupOf (minK (clMap (cE K))) →
      V ⧸ (sgnE e).addSubgroupOf V := fun c => ((g c.out : V) : V ⧸ (sgnE e).addSubgroupOf V)
  have hinj : Function.Injective F := by
    intro c d hcd
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := QuotientAddGroup.eq.mp hcd
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : sgn e (a c.out : K) + sgn e (a d.out : K) ∈ sgnE e := by
      have e2 : ((-g c.out + g d.out : V) : ι → ZMod 2) = -sgn e (a c.out : K) + sgn e (a d.out : K) := rfl
      rw [e2, hMinus_neg] at h1
      exact h1
    have hm : ClassGroup.mk0 (I c.out) ∈ minK (clMap (cE K)) := by
      rw [hI c.out]
      exact c.out.2
    have key := classGroup_inv_mul_mem_difR_of_sign e hU he (I c.out) (I d.out) (a c.out) (a d.out) (ha0 _) (ha0 _) (har _) (har _)
      (hIa _) (hIa _) hm h2
    rw [hI, hI] at key
    simpa using key
  show ((difR (clMap (cE K))).subgroupOf (minK (clMap (cE K)))).index ≤ ((sgnE e).addSubgroupOf V).index
  exact Nat.card_le_card_of_injective F hinj
