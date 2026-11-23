import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerLiftOfEmbedding
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.PreFamExt

open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

section Spans

variable {O O' Ω' C : Type} [CommRing O] [CommRing O'] [Field Ω'] [Field C] [Algebra O Ω'] [Algebra O' C]
  [Algebra Ω' C]

theorem span_span {V₀ V₁ V₂ : Type} [AddCommGroup V₁] [Module Ω' V₁] [AddCommGroup V₂] [Module C V₂]
    (R₁ : Subalgebra O Ω') (RC : Subalgebra O' C) (hR : ∀ a ∈ R₁, algebraMap Ω' C a ∈ RC) (g : V₁ →+ V₂)
    (hg : ∀ (a : Ω') (v : V₁), g (a • v) = algebraMap Ω' C a • g v) (h : V₀ → V₁) (S : Set V₀) :
    spanOver RC (g '' (spanOver R₁ (h '' S) : Set V₁)) = spanOver RC ((fun v => g (h v)) '' S) := by
  have key : ∀ t ∈ RC, ∀ x ∈ spanOver R₁ (h '' S), t • g x ∈ spanOver RC ((fun v => g (h v)) '' S) := by
    intro t ht x hx
    unfold spanOver at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [hg, smul_smul]
      exact AddSubgroup.subset_closure ⟨_, RC.mul_mem ht (hR a ha), _, ⟨e, he, rfl⟩, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, smul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      rw [map_neg, smul_neg]
      exact neg_mem hx
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, _, ⟨x, hx, rfl⟩, rfl⟩
    exact key t ht x hx
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, _, ⟨e, he, rfl⟩, rfl⟩
    exact AddSubgroup.subset_closure ⟨t, ht, _, ⟨h e, mem_spanOver_of_mem R₁ ⟨e, he, rfl⟩, rfl⟩, rfl⟩

end Spans

section Transfer

variable {O O' Ω : Type} [CommRing O] [CommRing O'] [Field Ω] [Algebra O O'] [Algebra O Ω] [Algebra O' Ω]
  [IsScalarTower O O' Ω] {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem base_of_restrict (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra O' Ω) (p : ℕ) (w : Ω)
    (h : D.Base (R.restrictScalars O) p w) : D.Base R p w :=
  ⟨h.freeM, h.M_le, h.le_M, h.one_mem, h.free, h.incl, h.stable, h.gam, h.del, h.th⟩

theorem facts_of_restrict (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra O' Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω)
    (φ : Equiv.Perm Sg) (h : D.Facts (R.restrictScalars O) p w χ φ) : D.Facts R p w χ φ :=
  ⟨h.le_af, h.im, h.ker, h.dx, h.onto, h.inj⟩

end Transfer

section BC

variable {O O' Ω Ω' C : Type} [CommRing O] [CommRing O'] [Field Ω] [Field Ω'] [Field C] [Algebra O O']
  [Algebra O Ω] [Algebra Ω Ω'] [Algebra O Ω'] [Algebra O' Ω'] [Algebra O C] [Algebra O' C] [Algebra Ω C]
  [Algebra Ω' C] [IsScalarTower O O' C] [IsScalarTower Ω Ω' C]
  {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem bcMap_smul (ι : Type) (a : Ω') (v : ι → Ω') :
    bcMap Ω' C ι (a • v) = algebraMap Ω' C a • bcMap Ω' C ι v := by
  funext i
  simp [bcMap]

omit [Algebra O' C] [Algebra O C] in
variable (Ω' C) in
theorem bcMap_bcMap (ι : Type) (v : ι → Ω) : bcMap Ω' C ι (bcMap Ω Ω' ι v) = bcMap Ω C ι v := by
  funext i
  simp [bcMap, ← IsScalarTower.algebraMap_apply]

theorem bc_bc (D : LieLatticeData Ω F n Sg r s) (R₁ : Subalgebra O Ω') (RC : Subalgebra O' C)
    (hR : ∀ a ∈ R₁, algebraMap Ω' C a ∈ RC) : (D.bc R₁).bc RC = D.bc (RC.restrictScalars O) := by
  have key1 : ∀ (ι : Type) (L : AddSubgroup (ι → Ω)),
      spanOver RC (bcMap Ω' C ι '' (spanOver R₁ (bcMap Ω Ω' ι '' (L : Set (ι → Ω))) : Set (ι → Ω'))) =
        spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))) := by
    intro ι L
    have := span_span R₁ RC hR (bcMap Ω' C ι).toAddMonoidHom (bcMap_smul ι) (bcMap Ω Ω' ι) (L : Set (ι → Ω))
    refine this.trans ?_
    congr 2
    funext v
    exact bcMap_bcMap Ω' C ι v
  have key2 : ∀ (ι κ : Type) (L : AddSubgroup ((ι → Ω) × (κ → Ω))),
      spanOver RC (Prod.map (bcMap Ω' C ι) (bcMap Ω' C κ) ''
        (spanOver R₁ (Prod.map (bcMap Ω Ω' ι) (bcMap Ω Ω' κ) '' (L : Set ((ι → Ω) × (κ → Ω)))) :
          Set ((ι → Ω') × (κ → Ω')))) =
        spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) '' (L : Set ((ι → Ω) × (κ → Ω)))) := by
    intro ι κ L
    have := span_span R₁ RC hR
      ((bcMap Ω' C ι).toAddMonoidHom.prodMap (bcMap Ω' C κ).toAddMonoidHom)
      (fun a v => Prod.ext (bcMap_smul ι a v.1) (bcMap_smul κ a v.2))
      (Prod.map (bcMap Ω Ω' ι) (bcMap Ω Ω' κ)) (L : Set ((ι → Ω) × (κ → Ω)))
    refine this.trans ?_
    congr 2
    funext v
    exact Prod.ext (bcMap_bcMap Ω' C ι v.1) (bcMap_bcMap Ω' C κ v.2)
  simp only [LieLatticeData.bc, key1, key2]
  rfl

end BC

theorem bcMap_smul' {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι : Type} (a : Ω) (v : ι → Ω) :
    bcMap Ω Ω' ι (a • v) = algebraMap Ω Ω' a • bcMap Ω Ω' ι v := by
  funext i
  simp [bcMap]

section Family

variable {O O' Ω Ω' : Type} [CommRing O] [CommRing O'] [Field Ω] [Field Ω'] [Algebra O O'] [Algebra O Ω]
  [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω']
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

omit [∀ k, Fintype (J k)] in
theorem mseg_map (y : (Σ k, J k) → Ω) (c : ∀ k, J k) :
    mseg (fun v => algebraMap Ω Ω' (y v)) c = algebraMap Ω Ω' (mseg y c) := by
  simp [mseg, map_prod]

omit [∀ k, Fintype (J k)] in

theorem map_mem_chartRing (y : (Σ k, J k) → Ω) (c : ∀ k, J k) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) :
    algebraMap Ω Ω' a ∈ chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    refine Algebra.subset_adjoin ⟨j, ?_⟩
    simp only [mseg_map, map_div₀]
  | algebraMap o =>
    rw [← IsScalarTower.algebraMap_apply O Ω Ω', IsScalarTower.algebraMap_apply O O' Ω']
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem chart_shift {ι : Type} (x : ι → Ω') {s t : ι} (hs : x s ≠ 0) (ht : x t ≠ 0) {a : Ω'}
    (ha : a ∈ chartRing O' x s) : ∃ m : ℕ, (x s / x t) ^ m * a ∈ chartRing O' x t := by
  have hu : x s / x t ∈ chartRing O' x t := Algebra.subset_adjoin ⟨s, rfl⟩
  induction ha using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    refine ⟨1, ?_⟩
    have : (x s / x t) ^ 1 * (x j / x s) = x j / x t := by field_simp
    rw [this]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap o => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ o⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨m + l, ?_⟩
    have : (x s / x t) ^ (m + l) * (a + b) =
        (x s / x t) ^ l * ((x s / x t) ^ m * a) + (x s / x t) ^ m * ((x s / x t) ^ l * b) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hu _) hm) (mul_mem (pow_mem hu _) hl)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨m + l, ?_⟩
    have : (x s / x t) ^ (m + l) * (a * b) = ((x s / x t) ^ m * a) * ((x s / x t) ^ l * b) := by ring
    rw [this]
    exact mul_mem hm hl

theorem isLatFamily_span {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (y : (Σ k, J k) → Ω) (h : V → V') (hh : ∀ (a : Ω) (v : V), h (a • v) = algebraMap Ω Ω' a • h v)
    {Γ : (∀ k, J k) → AddSubgroup V} (hΓ : IsLatFamily O y Γ) :
    IsLatFamily O' (fun v => algebraMap Ω Ω' (y v))
      fun c => spanOver (chartRing O' (mseg fun v => algebraMap Ω Ω' (y v)) c) (h '' (Γ c : Set V)) := by
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, fun s t hs ht v hv => ?_⟩
  have hs0 : mseg y s ≠ 0 := fun h0 => hs (by rw [mseg_map, h0, map_zero])
  have ht0 : mseg y t ≠ 0 := fun h0 => ht (by rw [mseg_map, h0, map_zero])
  have hu : mseg (fun v => algebraMap Ω Ω' (y v)) s / mseg (fun v => algebraMap Ω Ω' (y v)) t ∈
      chartRing O' (mseg fun v => algebraMap Ω Ω' (y v)) t := Algebra.subset_adjoin ⟨s, rfl⟩
  have hue : mseg (fun v => algebraMap Ω Ω' (y v)) s / mseg (fun v => algebraMap Ω Ω' (y v)) t =
      algebraMap Ω Ω' (mseg y s / mseg y t) := by
    rw [mseg_map, mseg_map, map_div₀]
  have hv' := hv
  unfold spanOver at hv'
  induction hv' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hx
    obtain ⟨m, hm⟩ := chart_shift (O' := O') (mseg fun v => algebraMap Ω Ω' (y v)) hs ht ha
    obtain ⟨l, hl⟩ := hΓ.2 s t hs0 ht0 e he
    refine ⟨m + l, ?_⟩
    have : (mseg (fun v => algebraMap Ω Ω' (y v)) s / mseg (fun v => algebraMap Ω Ω' (y v)) t) ^ (m + l) •
        a • h e = ((mseg (fun v => algebraMap Ω Ω' (y v)) s / mseg (fun v => algebraMap Ω Ω' (y v)) t) ^ m * a) •
          h ((mseg y s / mseg y t) ^ l • e) := by
      rw [hh, map_pow, ← hue, smul_smul, smul_smul]
      congr 1
      ring
    rw [this]
    exact AddSubgroup.subset_closure ⟨_, hm, _, ⟨_, hl, rfl⟩, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb iha ihb =>
    obtain ⟨m, hm⟩ := iha ha
    obtain ⟨l, hl⟩ := ihb hb
    refine ⟨m + l, ?_⟩
    have : ∀ u : Ω', u ^ (m + l) • (a + b) = u ^ l • (u ^ m • a) + u ^ m • (u ^ l • b) := fun u => by
      rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm l m]
    rw [this]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hu _) hm) (smul_mem_spanOver _ _ (pow_mem hu _) hl)
  | neg a ha iha =>
    obtain ⟨m, hm⟩ := iha ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

end Family

theorem not_unit_of_mem_maximalIdeal {O' C : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [Field C] [Algebra O' C] (RC : Subalgebra O' C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {p : ℕ} (hp : v (p : C) < 1) (hp0 : (p : O') ≠ 0) (hpn : ¬ IsUnit (p : O')) {m : O'}
    (hm : m ∈ IsLocalRing.maximalIdeal O') (u : C) (hu : u ∈ RC) : u * algebraMap O' C m ≠ 1 := by
  by_cases hm0 : m = 0
  · simp [hm0]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  obtain ⟨f, hf⟩ := IsDiscreteValuationRing.associated_pow_irreducible hm0 hϖ
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hf
  have he0 : e ≠ 0 := by
    rintro rfl
    have h1 : IsUnit ((p : O') * (a : O')) := by rw [ha]; simp
    exact hpn (isUnit_of_mul_isUnit_left h1)
  have hf0 : f ≠ 0 := by
    rintro rfl
    have hu' : IsUnit m := isUnit_of_mul_isUnit_left (by simpa [hb] using b.isUnit : IsUnit (m * (b : O')))
    exact (IsLocalRing.mem_maximalIdeal m).1 hm hu'

  have hrel : m ^ e = ((↑(a ^ f) : O') * (↑(b ^ e)⁻¹ : O')) * (p : O') ^ f := by
    have h1 : (m * (b : O')) ^ e = ((p : O') * (a : O')) ^ f := by
      rw [hb, ha, ← pow_mul, ← pow_mul, mul_comm]
    rw [mul_pow, mul_pow] at h1
    have h2 : m ^ e = ((p : O') ^ f * (a : O') ^ f) * (↑(b ^ e)⁻¹ : O') := by
      rw [← h1, mul_assoc]
      have : (b : O') ^ e * (↑(b ^ e)⁻¹ : O') = 1 := by
        rw [← Units.val_pow_eq_pow_val]; exact Units.mul_inv _
      rw [this, mul_one]
    rw [h2, Units.val_pow_eq_pow_val]
    ring
  have hmap : ∀ x : O', v (algebraMap O' C x) ≤ 1 := fun x => (hv _).1 (Subalgebra.algebraMap_mem RC x)
  have hvm : v (algebraMap O' C m) < 1 := by
    by_contra hcon
    have h1 : 1 ≤ v (algebraMap O' C m) := not_lt.1 hcon
    have h2 : 1 ≤ v (algebraMap O' C m) ^ e := one_le_pow₀ h1
    have h3 : v (algebraMap O' C m) ^ e ≤ v (p : C) ^ f := by
      rw [← map_pow, ← map_pow, hrel, map_mul, map_mul, map_pow, map_natCast]
      calc _ ≤ 1 * v ((p : C) ^ f) := mul_le_mul_left (hmap _) _
        _ = _ := by rw [one_mul, map_pow]
    have h4 : v (p : C) ^ f < 1 := pow_lt_one₀ zero_le' hp hf0
    exact absurd (h2.trans h3) (not_le.2 h4)
  intro hone
  have h1 : v u * v (algebraMap O' C m) = 1 := by rw [← map_mul, hone, map_one]
  have h2 : v u ≤ 1 := (hv _).1 hu
  have h3 : v u * v (algebraMap O' C m) < 1 := by
    calc _ ≤ 1 * v (algebraMap O' C m) := mul_le_mul_left h2 _
      _ < 1 := by rwa [one_mul]
  exact absurd h1 h3.ne

section Steps

variable {O O' Ω Ω' : Type} [CommRing O] [CommRing O'] [Field Ω] [Field Ω'] [Algebra O O'] [Algebra O Ω]
  [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω']
  {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem base_bc (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra O Ω) (R' : Subalgebra O' Ω')
    (hR : ∀ a ∈ R, algebraMap Ω Ω' a ∈ R') {p : ℕ} (hp2 : 2 ≤ p) (hpΩ : (p : Ω) ≠ 0) (w : O) {u : O}
    (hu : IsUnit u) (hwu : w ^ (p - 1) = u * (p : O)) (hb : D.Base R p (algebraMap O Ω w)) :
    (D.bc (R'.restrictScalars O)).Base R' p (algebraMap O' Ω' (algebraMap O O' w)) := by
  classical
  have hchar : CharData R p (algebraMap O Ω w)
      (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ w, ?_, zero_ne_one, fun τ => ⟨by simp, by simp, fun a => ?_⟩⟩
    · obtain ⟨v, rfl⟩ := hu
      refine ⟨algebraMap O Ω ((↑v⁻¹ : O) * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      rw [← map_natCast (algebraMap O Ω), ← map_mul]
      congr 1
      have h1 : w ^ (p - 2) * w = w ^ (p - 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [mul_assoc, h1, hwu, ← mul_assoc, Units.inv_mul, one_mul]
    · show (if a = 0 then (0 : Ω) else 1) ∈ R
      split_ifs
      · exact zero_mem _
      · exact one_mem _
  have hb' := (GlobalTheory.T.lattice_base_change_larger_ring_holds D R p (algebraMap O Ω w) _ hchar hb Ω' (R'.restrictScalars O) hR).2
  have hw : algebraMap Ω Ω' (algebraMap O Ω w) = algebraMap O' Ω' (algebraMap O O' w) := by
    rw [← IsScalarTower.algebraMap_apply O Ω Ω', ← IsScalarTower.algebraMap_apply O O' Ω']
  rw [hw] at hb'
  exact base_of_restrict _ _ _ _ hb'

theorem test_bc [IsLocalRing O] [IsDomain O'] [IsDiscreteValuationRing O'] [IsLocalHom (algebraMap O O')]
    (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra O Ω) (R' : Subalgebra O' Ω')
    (hR : ∀ a ∈ R, algebraMap Ω Ω' a ∈ R') {p : ℕ} (hp0' : (p : O') ≠ 0) (hpn' : ¬ IsUnit (p : O'))
    (σ : Sg → F →+* IsLocalRing.ResidueField O) (χ₀ : Sg → F →*₀ O')
    (hχ₀ : ∀ τ a, IsLocalRing.residue O' (χ₀ τ a) =
      ((IsLocalRing.ResidueField.map (algebraMap O O')).comp (σ τ)) a) (φ : Equiv.Perm Sg) (w : O)
    (H : ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
      (RC : Subalgebra O C), IsTestPt p R RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      (D.bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ) :
    (D.bc (R'.restrictScalars O)).TestFacts R' p (algebraMap O' Ω' (algebraMap O O' w))
      (fun τ a => algebraMap O' Ω' (χ₀ τ a)) φ := by
  intro C _ _ _ _ RC hT
  obtain ⟨hcl, ⟨v, hv, hvp⟩, hadic, hmap⟩ := hT
  letI aOC : Algebra O C := ((algebraMap O' C).comp (algebraMap O O')).toAlgebra
  letI aΩC : Algebra Ω C := ((algebraMap Ω' C).comp (algebraMap Ω Ω')).toAlgebra
  haveI t1 : IsScalarTower O O' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower Ω Ω' C := IsScalarTower.of_algebraMap_eq' rfl
  have hOC : ∀ o : O, algebraMap O C o = algebraMap Ω' C (algebraMap O' Ω' (algebraMap O O' o)) := fun o => by
    rw [← IsScalarTower.algebraMap_apply O' Ω' C]; rfl
  haveI t3 : IsScalarTower O Ω C := IsScalarTower.of_algebraMap_eq fun o => by
    rw [hOC, ← IsScalarTower.algebraMap_apply O O' Ω', IsScalarTower.algebraMap_apply O Ω Ω']; rfl
  have hT0 : IsTestPt p R (RC.restrictScalars O) :=
    ⟨hcl, ⟨v, hv, hvp⟩, hadic, fun a ha => hmap _ (hR a ha)⟩
  have hfacts := H C (RC.restrictScalars O) hT0
    (fun τ => (algebraMap O' C).toMonoidWithZeroHom.comp (χ₀ τ)) (by
      intro τ a o ho
      have hm : χ₀ τ a - algebraMap O O' o ∈ IsLocalRing.maximalIdeal O' := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hχ₀, RingHom.comp_apply, ← ho,
          IsLocalRing.ResidueField.map_residue, sub_self]
      have he : (((algebraMap O' C).toMonoidWithZeroHom.comp (χ₀ τ)) a : C) - algebraMap O C o =
          algebraMap O' C (χ₀ τ a - algebraMap O O' o) := by
        rw [map_sub]; rfl
      rw [he]
      exact ⟨Subalgebra.algebraMap_mem RC _, fun t ht =>
        not_unit_of_mem_maximalIdeal RC v hv hvp hp0' hpn' hm t ht⟩)
  rw [bc_bc (O := O) (O' := O') (Ω' := Ω') D (R'.restrictScalars O) RC hmap]
  refine facts_of_restrict (O := O) (O' := O') (Ω := C) _ RC _ _ _ _ ?_
  have hw : algebraMap Ω' C (algebraMap O' Ω' (algebraMap O O' w)) = algebraMap O C w := (hOC w).symm
  have hχ : (fun (τ : Sg) (a : F) => algebraMap Ω' C (algebraMap O' Ω' (χ₀ τ a))) =
      fun τ a => ((algebraMap O' C).toMonoidWithZeroHom.comp (χ₀ τ)) a := by
    funext τ a
    rw [← IsScalarTower.algebraMap_apply O' Ω' C]; rfl
  rw [hw, hχ]
  exact hfacts

end Steps

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O'), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ (n : ℕ) (Sg : Type) (r s : Sg → ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg) (Df : (∀ k, J k) → LieLatticeData Ω F n Sg r s), IsPreFamily O y p w σ φ Df → ∃ (χ : Sg → F → O') (Df' : (∀ k, J k) → LieLatticeData Ω' F n Sg r s), IsLatticeFamily O' (fun v => algebraMap Ω Ω' (y v)) p (algebraMap O O' w) χ φ Df' ∧ ∀ c, mseg y c ≠ 0 → ∀ τ, (Df' c).lie τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).lie τ) ∧ (Df' c).W τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).W τ) ∧ (Df' c).om τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).om τ) ∧ (Df' c).omHT τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).omHT τ) := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hmod hint O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj F _ _ p _ _ ζ hζ n Sg r s w σ φ Df hpre
  have hne : ∀ c, mseg (fun v => algebraMap Ω Ω' (y v)) c ≠ 0 → mseg y c ≠ 0 :=
    fun c hc h0 => hc (by rw [mseg_map, h0, map_zero])
  obtain ⟨hp0, ⟨u, hu, hwu⟩, hpn⟩ := hpre.char
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp0' : (p : O') ≠ 0 := by
    intro h0
    have h1 : algebraMap Ω Ω' (p : Ω) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap O' Ω'), h0, map_zero]
    exact hpΩ ((map_eq_zero _).1 h1)
  have hpn' : ¬ IsUnit (p : O') := by
    intro h
    rw [← map_natCast (algebraMap O O')] at h
    exact hpn (isUnit_of_map_unit (algebraMap O O') _ h)

  have hex : ∀ τ, ∃ χ : F →*₀ O', ∀ a, IsLocalRing.residue O' (χ a) =
      ((IsLocalRing.ResidueField.map (algebraMap O O')).comp (σ τ)) a := fun τ =>
    (teichmuller_lift_of_embedding O' F p ζ hζ _).1.exists
  choose χ₀ hχ₀ using hex
  refine ⟨fun τ a => χ₀ τ a, fun c => (Df c).bc
    ((chartRing O' (mseg fun v => algebraMap Ω Ω' (y v)) c).restrictScalars O), ⟨?_, ?_, ?_, ?_, ?_⟩,
    fun c _ τ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact isLatFamily_span y _ (fun a v => bcMap_smul' a v) hpre.famM
  · intro τ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre.fam τ
    exact ⟨isLatFamily_span y _ (fun a v => bcMap_smul' a v) h1,
      isLatFamily_span y _ (fun a v => bcMap_smul' a v) h2,
      isLatFamily_span y _ (fun a v => bcMap_smul' a v) h3,
      isLatFamily_span y _ (fun a v => bcMap_smul' a v) h4,
      isLatFamily_span y _ (fun a v => Prod.ext (bcMap_smul' a v.1) (bcMap_smul' a v.2)) h5,
      isLatFamily_span y _ (fun a v => Prod.ext (bcMap_smul' a v.1) (bcMap_smul' a v.2)) h6,
      isLatFamily_span y _ (fun a v => Prod.ext (bcMap_smul' a v.1) (bcMap_smul' a v.2)) h7⟩
  · refine ⟨hp0', ⟨algebraMap O O' u, hu.map _, ?_⟩, hpn', zero_ne_one, fun τ => ⟨map_zero _, map_one _⟩⟩
    rw [← map_pow, hwu, map_mul, map_natCast]
  · intro c hc
    exact base_bc (Df c) _ _ (fun a ha => map_mem_chartRing y c ha) hp2 hpΩ w hu hwu (hpre.base c (hne c hc))
  · intro c hc
    exact test_bc (Df c) _ _ (fun a ha => map_mem_chartRing y c ha) hp0' hpn' σ χ₀ hχ₀ φ w
      (hpre.test c (hne c hc))

end GlobalTheory.CompanionTheory.Ar.Num.PreFamExt
