import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem le_iff {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [Normal k Ω] (F : IntermediateField k Ω)
    (hF : Normal k F) : (∀ a b : F ≃ₐ[k] F, a * b = b * a) ↔ ∀ a b : Ω ≃ₐ[k] Ω, a * b * a⁻¹ * b⁻¹ ∈ F.fixingSubgroup := by
  haveI := hF
  constructor
  · intro hcomm a b
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have key : AlgEquiv.restrictNormalHom F (a * b * a⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm (AlgEquiv.restrictNormalHom F a)]
      group
    have := AlgEquiv.restrictNormalHom_apply F (a * b * a⁻¹ * b⁻¹) ⟨x, hx⟩
    rw [key] at this
    simpa using this.symm
  · intro h a b
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := F) Ω a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := F) Ω b
    have key : AlgEquiv.restrictNormalHom F (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
      refine AlgEquiv.ext fun x => Subtype.ext ?_
      rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
      exact (IntermediateField.mem_fixingSubgroup_iff F _).1 (h a' b') x x.2
    simp only [map_mul, map_inv] at key
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at key
    exact key

private theorem le_field {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω))
    (ho : IsOpen (H : Set (G ℚ Ω))) (hc : ∀ a b : G ℚ Ω, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hr : ∀ (φ : Ω →+* ℂ) (σ : G ℚ Ω), ComplexEmbedding.IsConj φ σ → σ ∈ H) :
    ∃ F : IntermediateField ℚ Ω, F.fixingSubgroup = H ∧ NumberField F ∧ IsTotallyReal F ∧ IsAbelianGalois ℚ F := by
  let Hc : ClosedSubgroup (G ℚ Ω) := ⟨H, Subgroup.isClosed_of_isOpen H ho⟩
  let F := IntermediateField.fixedField H
  have hfix : F.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hfd : FiniteDimensional ℚ F :=
    (InfiniteGalois.isOpen_iff_finite F).1 (by rw [hfix]; exact ho)
  have hnorm : H.Normal := ⟨fun n hn g => by
    have := H.mul_mem (hc g n) hn
    simpa using this⟩
  have hgal : IsGalois ℚ F := (InfiniteGalois.normal_iff_isGalois F).1 (by rw [hfix]; exact hnorm)
  have hcomm := (le_iff F hgal.to_normal).2 (by rw [hfix]; exact hc)
  refine ⟨F, hfix, @NumberField.mk _ _ inferInstance hfd, ⟨fun v => ?_⟩, ?_⟩
  · rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    set ψ := v.embedding
    letI : Algebra F ℂ := ψ.toAlgebra
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
    let φ₀ : Ω →ₐ[F] ℂ := IsAlgClosed.lift (M := ℂ) (R := F) (S := Ω)
    let φ : Ω →+* ℂ := φ₀.toRingHom
    letI : Algebra Ω ℂ := φ.toAlgebra
    haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ ℂ), map_ratCast]
    let σ : G ℚ Ω := (Complex.conjAe.restrictScalars ℚ).restrictNormal Ω
    have hσ : ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := fun x =>
      AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) Ω x
    have hconj : NumberField.ComplexEmbedding.IsConj φ σ := RingHom.ext fun x => by
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact (hσ x).symm
    have hmem : σ ∈ F.fixingSubgroup := by
      rw [hfix]
      exact hr φ σ hconj
    refine RingHom.ext fun y => ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have h1 : ψ y = φ (y : Ω) := (φ₀.commutes y).symm
    rw [h1, ← hσ, (IntermediateField.mem_fixingSubgroup_iff F σ).1 hmem y y.2]
  · exact @IsAbelianGalois.mk _ _ _ _ _ hgal ⟨⟨fun a b => hcomm a b⟩⟩

private theorem le_pow {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]ˣ) (m : ℕ) :
    (u ^ (l - 1)) ^ l ^ m ∈ KStar.TotallyRealRoots.princ l (m + 1) := by
  haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  show KStar.TotallyRealRoots.redPow l (m + 1) ((u ^ (l - 1)) ^ l ^ m) = 1
  rw [map_pow, map_pow, ← pow_mul, mul_comm]
  have ht : (l ^ (m + 1)).totient = l ^ m * (l - 1) := by
    rw [Nat.totient_prime_pow hl.out (by omega), Nat.add_sub_cancel]
  rw [← ht]
  exact ZMod.pow_totient _

private theorem le_one {l : ℕ} [hl : Fact l.Prime] (u : ℤ_[l]ˣ) (h : ∀ m, u ∈ KStar.TotallyRealRoots.princ l m) : u = 1 := by
  refine KStar.TotallyRealRoots.mem_of_isClosed (U := ⊥) isClosed_singleton fun b => ⟨1, one_mem _, ?_⟩
  rw [map_one]
  exact (h b).symm

private theorem le_compact {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {l : ℕ} [Fact l.Prime] (χ : Γ →* ℤ_[l]ˣ) (hχ : Continuous χ) (H U : Subgroup Γ) (hH : IsClosed (H : Set Γ))
    (hU : IsOpen (U : Set Γ)) (h : ∀ g ∈ H, χ g = 1 → g ∈ U) :
    ∃ m, ∀ g ∈ H, χ g ∈ KStar.TotallyRealRoots.princ l m → g ∈ U := by
  by_contra hne
  push_neg at hne
  let t : ℕ → Set Γ := fun m =>
    ((H : Set Γ) ∩ (U : Set Γ)ᶜ) ∩ χ ⁻¹' (KStar.TotallyRealRoots.princ l m : Set ℤ_[l]ˣ)
  have hcl : ∀ m, IsClosed (t m) := fun m =>
    (hH.inter hU.isClosed_compl).inter
      ((Subgroup.isClosed_of_isOpen _ (KStar.TotallyRealRoots.isOpen_princ m)).preimage hχ)
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun m => Set.inter_subset_inter_right _
      (Set.preimage_mono fun x hx => KStar.TotallyRealRoots.princ_anti (Nat.le_succ m) hx))
    (fun m => by
      obtain ⟨g, hgH, hgm, hgU⟩ := hne m
      exact ⟨g, ⟨hgH, hgU⟩, hgm⟩)
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hg
  have h1 : χ g = 1 := le_one _ (fun m => (hg m).2)
  exact (hg 0).1.2 (h g (hg 0).1.1 h1)

theorem UpperTheory.V.Ws.layerEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → TameL l T.F → ∀ n : ℕ, ∃ (T' : Tower D) (m : ℕ), T.Le T' ∧ IsLayer l m T.F T'.F ∧ T'.Deep ∧ n ≤ T'.d := by
  intro Ω _ _ _ l _ c D hD T hfit htame n
  obtain ⟨ho, -⟩ := hfit
  haveI := T.abF
  haveI := T.nF
  haveI := T.nK
  haveI := T.cmK
  haveI := T.realF
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  have hl2le := hlp.two_le
  have hχc : Continuous (cycZ ℚ Ω l) := (contTw ℚ Ω l).1
  let χ' : G ℚ Ω →* ℤ_[l]ˣ := (cycZ ℚ Ω l) ^ (l - 1)
  have hχ' : ∀ g, χ' g = cycZ ℚ Ω l g ^ (l - 1) := fun g => MonoidHom.pow_apply _ _ _
  have hχ'c : Continuous χ' := by
    have : (χ' : G ℚ Ω → ℤ_[l]ˣ) = fun g => cycZ ℚ Ω l g ^ (l - 1) := funext hχ'
    rw [this]
    exact hχc.pow _
  obtain ⟨mk, hmk, hkc⟩ := ho.kc
  have hcop : l.Coprime (l - 1) :=
    (Nat.Prime.coprime_iff_not_dvd hlp).2 fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
  have he : l.Coprime ((l - 1) * mk) := Nat.Coprime.mul_right hcop hmk
  let U : Subgroup (G ℚ Ω) := (D.ψ ^ ((l - 1) * mk)).ker
  have hU : IsOpen (U : Set (G ℚ Ω)) := Subgroup.isOpen_mono (fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      rw [MonoidHom.pow_apply, hg, one_pow]) hD.psi_open
  have hHc : IsClosed (T.F.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isClosed T.F
  obtain ⟨m0, hm0⟩ := le_compact χ' hχ'c T.F.fixingSubgroup U hHc hU (fun g hg h1 => by
    let g1 : G T.F Ω := IntermediateField.fixingSubgroupEquiv T.F ⟨g ^ (l - 1), pow_mem hg _⟩
    have hres : resQ T.F g1 = g ^ (l - 1) := by
      ext x
      simp [g1, IntermediateField.fixingSubgroupEquiv]
    have hcyc : cycZ T.F Ω l g1 = 1 := by
      show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G T.F Ω) Ω g1) = 1
      have : MulSemiringAction.toRingAut (G T.F Ω) Ω g1 =
          MulSemiringAction.toRingAut (G ℚ Ω) Ω (g ^ (l - 1)) := RingEquiv.ext fun x => by
        show g1 x = (g ^ (l - 1)) x
        rw [← hres]
        rfl
      rw [this]
      show cycZ ℚ Ω l (g ^ (l - 1)) = 1
      rw [map_pow, ← hχ']
      exact h1
    show (D.ψ ^ ((l - 1) * mk)) g = 1
    rw [MonoidHom.pow_apply, pow_mul, ← map_pow, ← hres]
    exact hkc g1 hcyc)
  have hs0 : (D.s0 : G ℚ Ω) ∈ Ine (D.pl l) := hD.decompSigma_mem.1.1
  obtain ⟨k, hk, hsk⟩ := htame (D.pl l) (hD.pl_over l hlp) _ hs0
  obtain ⟨s, hs⟩ : ∃ s : G ℚ Ω, s = (D.s0 : G ℚ Ω) ^ k := ⟨_, rfl⟩
  rw [← hs] at hsk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hk
    omega
  have hsinf : ¬ IsOfFinOrder (cycZ ℚ Ω l s) := by
    intro hfin
    apply hD.decompSigma_ord
    rw [hs, map_pow] at hfin
    exact hfin.of_pow hk0
  have hnt : ∀ t, 0 < t → χ' (s ^ t) ≠ 1 := by
    intro t ht h1
    apply hsinf
    rw [hχ', map_pow, ← pow_mul] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨t * (l - 1), Nat.mul_pos ht (by omega), h1⟩
  have hfar : ∀ t, ∃ M, 0 < t → χ' (s ^ t) ∉ KStar.TotallyRealRoots.princ l M := by
    intro t
    by_cases ht : 0 < t
    · by_contra hall
      push_neg at hall
      exact hnt t ht (le_one _ fun M => (hall M).2)
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using hfar
  obtain ⟨m, hm⟩ : ∃ m, m = m0 + ∑ t ∈ Finset.range n, f t := ⟨_, rfl⟩
  have hm0' : m0 ≤ m + 1 := by omega
  have hmt : ∀ t, 0 < t → t < n → χ' (s ^ t) ∉ KStar.TotallyRealRoots.princ l (m + 1) := by
    intro t ht htn hmem
    apply hf t ht
    refine KStar.TotallyRealRoots.princ_anti ?_ hmem
    have := Finset.single_le_sum (f := f) (fun i _ => Nat.zero_le _) (Finset.mem_range.2 htn)
    omega
  let Hm : Subgroup (G ℚ Ω) := T.F.fixingSubgroup ⊓ (KStar.TotallyRealRoots.princ l (m + 1)).comap χ'
  have hHm : ∀ g, g ∈ Hm ↔ g ∈ T.F.fixingSubgroup ∧ cycZ ℚ Ω l g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (m + 1) := by
    intro g
    rw [← hχ']
    rfl
  have hopen : IsOpen (Hm : Set (G ℚ Ω)) :=
    (IntermediateField.fixingSubgroup_isOpen T.F).inter ((KStar.TotallyRealRoots.isOpen_princ (m + 1)).preimage hχ'c)
  have hcomm : ∀ a b : G ℚ Ω, a * b * a⁻¹ * b⁻¹ ∈ Hm := by
    intro a b
    rw [hHm]
    have hN : Normal ℚ T.F := T.abF.toIsGalois.to_normal
    have hcT : ∀ x y : T.F ≃ₐ[ℚ] T.F, x * y = y * x := fun x y => T.abF.toIsMulCommutative.is_comm.comm x y
    refine ⟨(le_iff T.F hN).1 hcT a b, ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (cycZ ℚ Ω l a), mul_inv_cancel,
      one_mul, mul_inv_cancel, one_pow]
    exact one_mem _
  have hreal : ∀ (φ : Ω →+* ℂ) (σ : G ℚ Ω), NumberField.ComplexEmbedding.IsConj φ σ → σ ∈ Hm := by
    intro φ σ hσ
    have hφσ : ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := hσ.eq
    have hsq : σ * σ = 1 := by
      ext x
      apply φ.injective
      rw [AlgEquiv.mul_apply, hφσ, hφσ, Complex.conj_conj, AlgEquiv.one_apply]
    rw [hHm]
    constructor
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply φ.injective
      rw [hφσ]
      have h1 := NumberField.ComplexEmbedding.isReal_iff.1
        (NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp T.F.val.toRingHom))
      have h2 := RingHom.congr_fun h1 ⟨x, hx⟩
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      exact h2
    · have h2 : cycZ ℚ Ω l σ ^ 2 = 1 := by rw [sq, ← map_mul, hsq, map_one]
      obtain ⟨r, hr⟩ := hlp.even_sub_one hl2
      rw [hr, ← two_mul, pow_mul, h2, one_pow]
      exact one_mem _
  obtain ⟨F', hF'fix, hF'nf, hF'real, hF'ab⟩ := le_field Hm hopen hcomm hreal
  haveI := hF'nf
  haveI := hF'real
  haveI := hF'ab
  have hpowmem : ∀ g ∈ T.F.fixingSubgroup, g ^ l ^ m ∈ F'.fixingSubgroup := by
    intro g hg
    rw [hF'fix, hHm]
    refine ⟨pow_mem hg _, ?_⟩
    rw [map_pow, ← pow_mul, mul_comm (l ^ m), pow_mul]
    exact le_pow _ m
  have hg0mem : resQ T.F T.g0 ∈ T.F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => T.g0.commutes ⟨x, hx⟩
  let g0' : G F' Ω := IntermediateField.fixingSubgroupEquiv F' ⟨_, hpowmem _ hg0mem⟩
  have hK : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec A ≤ T.K.fixingSubgroup :=
    fun A hA => ho.split l hD.l_mem A hA
  obtain ⟨T', hpr, hKK, hFF, hg0⟩ := mkTower D hD T.pr T.K F' T.degK hK g0'
  have hfixT' : T'.F.fixingSubgroup = Hm := by rw [hFF, hF'fix]
  refine ⟨T', m, ⟨hpr, hKK, ?_, ⟨m, ?_⟩, ⟨m, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [hFF]
    intro x hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup F', IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [hF'fix, hHm] at hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ.1 x hx
  · intro g hg
    rw [hFF]
    exact hpowmem g hg
  · rw [hg0]
    ext x
    simp [g0', IntermediateField.fixingSubgroupEquiv]
  · intro g
    rw [hfixT', hHm]
  · refine ⟨(l - 1) * mk, he, fun g => ?_⟩
    have hg : resQ T'.F g ∈ Hm := by
      rw [← hfixT']
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
    rw [hHm] at hg
    have hmemU : resQ T'.F g ∈ U :=
      hm0 _ hg.1 (KStar.TotallyRealRoots.princ_anti hm0' (by rw [hχ']; exact hg.2))
    rw [MonoidHom.mem_ker, MonoidHom.pow_apply] at hmemU
    exact hmemU
  · show n ≤ Module.finrank ℚ T'.F
    rw [hFF]
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    rw [← AlgHom.card ℚ F' Ω]
    let emb : Fin n → (F' →ₐ[ℚ] Ω) := fun t => ((s ^ (t : ℕ) : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp F'.val
    have key : ∀ a b : ℕ, a < b → b < n →
        ((s ^ a : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp F'.val = ((s ^ b : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp F'.val → False := by
      intro a b hab hbn heq
      apply hmt (b - a) (by omega) (by omega)
      have hmem : s ^ (b - a) ∈ F'.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have h1 := AlgHom.congr_fun heq ⟨x, hx⟩
        change (s ^ a) x = (s ^ b) x at h1
        have hb : s ^ b = s ^ a * s ^ (b - a) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hb, AlgEquiv.mul_apply] at h1
        exact ((s ^ a).injective h1).symm
      rw [hF'fix, hHm] at hmem
      rw [hχ']
      exact hmem.2
    have hinj : Function.Injective emb := by
      intro a b hab
      rcases lt_trichotomy (a : ℕ) b with h | h | h
      · exact (key a b h b.2 hab).elim
      · exact Fin.ext h
      · exact (key b a h a.2 hab.symm).elim
    have := Fintype.card_le_of_injective emb hinj
    simpa using this
