import Mathlib

namespace GlobalTheory.ValExt

theorem ker_isMaximal (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) : (RingHom.ker h).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
  have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
  have hinv := hloc a ha'
  have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
  have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
  rw [this]
  exact J.mul_mem_left _ haJ

theorem exists_ext_local (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k) :
    ∃ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k), (∀ b : B, h' b ≠ 0 → (b : Ω)⁻¹ ∈ B) ∧
      ∀ a : A, h' (Subring.inclusion hAB a) = h a := by
  let p := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  let L := Localization.AtPrime p
  have hs : ∀ s : p.primeCompl, h s ≠ 0 := fun s e => s.2 (RingHom.mem_ker.2 e)
  have hs' : ∀ s : p.primeCompl, ((s : A) : Ω) ≠ 0 := fun s e =>
    hs s (by rw [show (s : A) = 0 from Subtype.ext e, map_zero])
  let ι : L →+* Ω := IsLocalization.lift (M := p.primeCompl) (g := A.subtype) (fun s => (hs' s).isUnit)
  let hL : L →+* k := IsLocalization.lift (M := p.primeCompl) (g := h) (fun s => (hs s).isUnit)
  have hι : ∀ a : A, ι (algebraMap A L a) = a := fun a => IsLocalization.lift_eq _ _
  have hhL : ∀ a : A, hL (algebraMap A L a) = h a := fun a => IsLocalization.lift_eq _ _
  have hmk : ∀ (a : A) (s : p.primeCompl), ι (IsLocalization.mk' L a s) * ((s : A) : Ω) = a := by
    intro a s
    rw [← hι, ← map_mul, IsLocalization.mk'_spec, hι]
  have hmkL : ∀ (a : A) (s : p.primeCompl), hL (IsLocalization.mk' L a s) * h s = h a := by
    intro a s
    rw [← hhL, ← map_mul, IsLocalization.mk'_spec, hhL]
  have hinj : Function.Injective ι := by
    intro z z' e
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z'
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    apply Subtype.ext
    have h1 := hmk a s
    have h2 := hmk a' s'
    simp only [Subring.coe_mul]
    rw [← h1, ← h2, e]
    ring
  let B : Subring Ω := ι.range
  let e : L ≃+* B := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b e' => hinj (congrArg Subtype.val e'), ι.rangeRestrict_surjective⟩
  have hAB : A ≤ B := fun a ha => ⟨algebraMap A L ⟨a, ha⟩, hι _⟩
  refine ⟨B, hAB, hL.comp e.symm.toRingHom, fun b hb => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z, e z = b := e.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have ha : h a ≠ 0 := fun e0 => hb (by
      have := hmkL a s
      rw [e0] at this
      exact (mul_eq_zero.1 this).resolve_right (hs s))
    let t : p.primeCompl := ⟨a, fun e0 => ha (RingHom.mem_ker.1 e0)⟩
    refine ⟨IsLocalization.mk' L (s : A) t, ?_⟩
    show ι _ = (ι (IsLocalization.mk' L a s))⁻¹
    have h1 := hmk a s
    have h2 := hmk (s : A) t
    have ha0 : ((a : A) : Ω) ≠ 0 := hs' t
    apply eq_inv_of_mul_eq_one_left
    have : ι (IsLocalization.mk' L (s : A) t) * ι (IsLocalization.mk' L a s) * (((a : A) : Ω) * ((s : A) : Ω)) =
        1 * (((a : A) : Ω) * ((s : A) : Ω)) := by
      calc _ = (ι (IsLocalization.mk' L (s : A) t) * ((t : A) : Ω)) * (ι (IsLocalization.mk' L a s) * ((s : A) : Ω)) := by
              simp only [t]; ring
        _ = _ := by rw [h1, h2]; ring
    exact mul_right_cancel₀ (mul_ne_zero ha0 (hs' s)) this
  · have : e.symm (Subring.inclusion hAB a) = algebraMap A L a := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact Subtype.ext (hι a).symm
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this, hhL]

theorem exists_ext_adjoin (Ω k : Type) [Field Ω] [Field k] [IsAlgClosed k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (y : Ω) (M : Ideal (Algebra.adjoin A {y})) [M.IsMaximal]
    (hM : RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y}))) :
    ∃ h' : Algebra.adjoin A {y} →+* k, ∀ a : A, h' (algebraMap A _ a) = h a := by
  haveI := ker_isMaximal Ω k A h hloc
  let K₀ := A ⧸ RingHom.ker h
  let K₁ := (Algebra.adjoin A {y}) ⧸ M
  letI : Field K₁ := Ideal.Quotient.field M
  letI : Field K₀ := Ideal.Quotient.field _
  let f₀ : K₀ →+* K₁ := Ideal.quotientMap M (algebraMap A (Algebra.adjoin A {y})) hM
  letI : Algebra K₀ K₁ := f₀.toAlgebra
  let hb : K₀ →+* k := Ideal.Quotient.lift (RingHom.ker h) h (fun a ha => ha)
  letI : Algebra K₀ k := hb.toAlgebra
  haveI : IsScalarTower A K₀ K₁ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (Algebra.adjoin A {y}) := .adjoin_of_finite (Set.finite_singleton y)
  haveI : Algebra.FiniteType A K₁ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K₀ K₁ := Algebra.FiniteType.of_restrictScalars_finiteType A K₀ K₁
  haveI : Module.Finite K₀ K₁ := finite_of_finite_type_of_isJacobsonRing K₀ K₁
  haveI : Algebra.IsIntegral K₀ K₁ := Algebra.IsIntegral.of_finite K₀ K₁
  haveI : Module.IsTorsionFree K₀ K₁ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree K₀ k := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic K₀ K₁ := Algebra.IsIntegral.isAlgebraic
  let L : K₁ →ₐ[K₀] k := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  have e1 : Ideal.Quotient.mk M (algebraMap A (Algebra.adjoin A {y}) a) = algebraMap K₀ K₁ (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, L.commutes]
  rfl

theorem dichotomy (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (x : Ω) (hx : x ≠ 0) :
    ∃ y : Ω, (y = x ∨ y = x⁻¹) ∧ ∃ M : Ideal (Algebra.adjoin A {y}), M.IsMaximal ∧
      RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y})) := by
  have hmax : (RingHom.ker h).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
    have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
    have hinv := hloc a ha'
    have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
    have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
    rw [this]
    exact J.mul_mem_left _ haJ
  by_cases hT : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) = ⊤
  · letI := invertibleOfNonzero hx
    have htop : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) ⊔
        Ideal.span {⟨x, Algebra.subset_adjoin rfl⟩} = ⊤ := by rw [hT]; exact top_sup_eq _
    obtain ⟨p, hp, hpx⟩ :=
      Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _ hmax.ne_top htop
    have hlc : h p.leadingCoeff ≠ 0 := by
      intro e
      have h1 := sub_mem (RingHom.mem_ker.2 e) hp
      simp only [sub_sub_cancel] at h1
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hu : IsUnit p.leadingCoeff := by
      have hinv := hloc _ hlc
      have h0 : (p.leadingCoeff : Ω) ≠ 0 := fun e => hlc (by
        rw [show p.leadingCoeff = 0 from Subtype.ext e, map_zero])
      exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : A) (Subtype.ext (by simp [mul_inv_cancel₀ h0]))
    have hint : IsIntegral A x⁻¹ := by
      refine ⟨Polynomial.C (hu.unit⁻¹ : Aˣ).1 * p, ?_, ?_⟩
      · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by simp)
      · rw [← Polynomial.aeval_def, map_mul]
        rw [invOf_eq_inv] at hpx
        rw [hpx, mul_zero]
    haveI : Algebra.IsIntegral A (Algebra.adjoin A {x⁻¹}) := Algebra.IsIntegral.adjoin (by simpa using hint)
    have hker : RingHom.ker (algebraMap A (Algebra.adjoin A {x⁻¹})) ≤ RingHom.ker h := by
      intro a ha
      have e := congrArg Subtype.val (RingHom.mem_ker.1 ha)
      have : a = 0 := Subtype.ext (by simpa using e)
      rw [this]; exact zero_mem _
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker h) hker
    exact ⟨x⁻¹, Or.inr rfl, Q, hQ, hQc.ge⟩
  · obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hT
    exact ⟨x, Or.inl rfl, M, hM, Ideal.map_le_iff_le_comap.1 hle⟩

theorem exists_valuationSubring_ext : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k]
    (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U)
      (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  intro W Ω k _ _ _ _ j hj g
  let S : Set (Subring (Ω × k)) :=
    {G | (∀ a ∈ G, ∀ b ∈ G, a.1 = b.1 → a.2 = b.2) ∧ ∀ w, (j w, g w) ∈ G}
  have G0 : (RingHom.prod j g).range ∈ S := by
    refine ⟨?_, fun w => ⟨w, rfl⟩⟩
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ e
    have : w = w' := hj e
    subst this; rfl
  obtain ⟨G, -, hG⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, fun w => le_sSup hy ((hcS hy).2 w)⟩, fun z hz => le_sSup hz⟩
    intro a ha b hb e
    obtain ⟨s₁, hs₁, ha₁⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 ha
    obtain ⟨s₂, hs₂, hb₂⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 hb
    obtain ⟨s₃, hs₃, h13, h23⟩ := hd s₁ hs₁ s₂ hs₂
    exact (hcS hs₃).1 a (h13 ha₁) b (h23 hb₂) e) _ G0
  obtain ⟨⟨hGf, hGb⟩, hGm⟩ := hG
  let π : G →+* Ω := (RingHom.fst Ω k).comp G.subtype
  have hπ : Function.Injective π := fun p q e =>
    Subtype.ext (Prod.ext e (hGf p.1 p.2 q.1 q.2 e))
  let A : Subring Ω := π.range
  let e : G ≃+* A := RingEquiv.ofBijective π.rangeRestrict
    ⟨fun a b e' => hπ (congrArg Subtype.val e'), π.rangeRestrict_surjective⟩
  let h : A →+* k := ((RingHom.snd Ω k).comp G.subtype).comp e.symm.toRingHom
  have hA : ∀ a : A, ((a : Ω), h a) ∈ G := fun a => by
    have e1 : π (e.symm a) = a := congrArg Subtype.val (e.apply_symm_apply a)
    have : ((a : Ω), h a) = ((e.symm a : G) : Ω × k) := Prod.ext e1.symm rfl
    rw [this]; exact (e.symm a).2
  have hG2 : ∀ p ∈ G, ∃ a : A, (a : Ω) = p.1 ∧ h a = p.2 := fun p hp =>
    ⟨π.rangeRestrict ⟨p, hp⟩, rfl, by
      show ((e.symm (e ⟨p, hp⟩) : G) : Ω × k).2 = p.2
      rw [e.symm_apply_apply]⟩
  have ext_le : ∀ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k),
      (∀ a : A, h' (Subring.inclusion hAB a) = h a) → B ≤ A := by
    intro B hAB h' hh' b hb
    let G' : Subring (Ω × k) := (RingHom.prod B.subtype h').range
    have hG' : G' ∈ S := by
      refine ⟨?_, fun w => ?_⟩
      · rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩ e'
        have : b₁ = b₂ := Subtype.ext e'
        subst this; rfl
      · obtain ⟨a, ha1, ha2⟩ := hG2 _ (hGb w)
        refine ⟨Subring.inclusion hAB a, ?_⟩
        exact Prod.ext ha1 ((hh' a).trans ha2)
    have hle : G ≤ G' := fun p hp => by
      obtain ⟨a, ha1, ha2⟩ := hG2 p hp
      exact ⟨Subring.inclusion hAB a, Prod.ext ha1 ((hh' a).trans ha2)⟩
    have hmem : ((b : Ω), h' ⟨b, hb⟩) ∈ G := hGm hG' hle ⟨⟨b, hb⟩, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl⟩
  have hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A := by
    intro a ha
    obtain ⟨B, hAB, h', hB, hh'⟩ := exists_ext_local Ω k A h
    have := hB (Subring.inclusion hAB a) (by rw [hh']; exact ha)
    exact ext_le B hAB h' hh' this
  have hval : ∀ x : Ω, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ zero_mem A)
    obtain ⟨y, hy, M, hM, hMc⟩ := dichotomy Ω k A h hloc x hx
    obtain ⟨h', hh'⟩ := exists_ext_adjoin Ω k A h hloc y M hMc
    let B : Subring Ω := (Algebra.adjoin A {y}).toSubring
    have hAB : A ≤ B := fun a ha => (Algebra.adjoin A {y}).algebraMap_mem (⟨a, ha⟩ : A)
    have hyA : y ∈ A := ext_le B hAB h' hh' (Algebra.subset_adjoin rfl)
    rcases hy with rfl | rfl
    · exact Or.inl hyA
    · exact Or.inr hyA
  let U : ValuationSubring Ω := { A with mem_or_inv_mem' := hval }
  have hU : ∀ w, j w ∈ U := fun w => by
    obtain ⟨a, ha1, -⟩ := hG2 _ (hGb w)
    show j w ∈ A
    rw [← show (a : Ω) = j w from ha1]; exact a.2
  refine ⟨U, hU, h.comp (Subring.inclusion (le_refl A)), fun w => ?_⟩
  have m1 := hA ⟨j w, hU w⟩
  exact hGf _ m1 _ (hGb w) rfl

end GlobalTheory.ValExt
