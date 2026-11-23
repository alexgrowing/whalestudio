import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticTorusFixedVerticesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsLatticeIffFixedPointQuadraticTorus

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.PS

open QuadraticAlgebra

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

theorem even_mul {x y : K} (hx : EvenVal O x) (hy : EvenVal O y) : EvenVal O (x * y) := by
  obtain ⟨u, s, hs, rfl⟩ := hx
  obtain ⟨v, r, hr, rfl⟩ := hy
  exact ⟨u * v, s * r, mul_ne_zero hs hr, by rw [Units.val_mul, map_mul]; ring⟩

theorem even_inv {x : K} (hx : EvenVal O x) : EvenVal O x⁻¹ := by
  obtain ⟨u, s, hs, rfl⟩ := hx
  exact ⟨u⁻¹, s⁻¹, inv_ne_zero hs, by rw [map_units_inv, mul_inv, inv_pow]⟩

theorem gs_ml (t : K) (a : (Etau K τ)ˣ) : Gs O τ t a = ml a '' Gs O τ (t * nU a) 1 := by
  ext S
  constructor
  · rintro ⟨h, c, hc, hg⟩
    refine ⟨ml a⁻¹ S, ⟨fix_ml _ ?_, c, hc, ?_⟩, by rw [← ml_mul, mul_inv_cancel, ml_one]⟩
    · rwa [mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, mul_one]
    · simpa using gen_ml hg a⁻¹
  · rintro ⟨S, ⟨h, c, hc, hg⟩, rfl⟩
    exact ⟨fix_ml _ h, c, hc, by simpa using gen_ml hg a⟩

theorem ml_inj (a : (Etau K τ)ˣ) : Function.Injective (ml a) := fun S S' h => by
  have := congrArg (ml a⁻¹) h
  rwa [← ml_mul, ← ml_mul, inv_mul_cancel, ml_one, ml_one] at this

theorem gs_ncard (t : K) (a : (Etau K τ)ˣ) : (Gs O τ t a).ncard = (Gs O τ (t * nU a) 1).ncard := by
  rw [gs_ml, Set.ncard_image_of_injective _ (ml_inj a)]

variable [IsDomain O] [IsDiscreteValuationRing O] {Δ : K}

theorem even_or_irr (L : IsLoc O Δ) {π : O} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    EvenVal O x ∨ EvenVal O (x / algebraMap O K π) := by
  haveI := L.frac
  have h0 : algebraMap O K π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · refine Or.inl ⟨u, algebraMap O K π ^ k, zpow_ne_zero _ h0, ?_⟩
    rw [Units.smul_def, Algebra.smul_def, mul_comm 2 k, zpow_mul, zpow_ofNat]
  · refine Or.inr ⟨u, algebraMap O K π ^ k, zpow_ne_zero _ h0, ?_⟩
    rw [Units.smul_def, Algebra.smul_def, mul_comm 2 k, zpow_add_one₀ h0, zpow_mul, zpow_ofNat]
    field_simp

theorem even_or (L : IsLoc O Δ) {x p : K} (hx : x ≠ 0) (hp : p ≠ 0) (h : ¬ EvenVal O p) :
    EvenVal O x ∨ EvenVal O (x / p) := by
  haveI := L.frac
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O K π ≠ 0 := by simpa using hπ.ne_zero
  refine (even_or_irr L hπ hx).imp_right fun h1 => ?_
  have := even_mul h1 (even_inv ((even_or_irr L hπ hp).resolve_left h))
  convert this using 1
  field_simp

theorem not_even_irr (L : IsLoc O Δ) {π : O} (hπ : Irreducible π) : ¬ EvenVal O (algebraMap O K π) := by
  haveI := L.frac
  rintro ⟨u, s, -, h⟩
  have h1 : IsIntegral O (s ^ 2) := by
    have : s ^ 2 = algebraMap O K ((u⁻¹ : Oˣ) * π) := by
      rw [map_mul, h, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow two_pos h1)
  rw [← map_pow, ← map_mul] at h
  have h2 : π = (u * r) * r := by rw [IsFractionRing.injective O K h]; ring
  have hr : IsUnit r := (hπ.isUnit_or_isUnit h2).elim isUnit_of_mul_isUnit_right id
  exact hπ.not_isUnit (h2 ▸ (u.isUnit.mul hr).mul hr)

theorem unit_of_sq (L : IsLoc O Δ) {s : Kˣ} {ε : Oˣ} (h : 1 = algebraMap O K ε * (s : K) ^ 2) :
    ∃ u : Oˣ, algebraMap O K u = s := by
  haveI := L.frac
  have h1 : IsIntegral O ((s : K) ^ 2) := by
    have : (s : K) ^ 2 = algebraMap O K (ε⁻¹ : Oˣ) := by
      rw [map_units_inv]; exact eq_inv_of_mul_eq_one_right h.symm
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow two_pos h1)
  have h2 : r * (ε * r) = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, map_mul, map_one, hr, h]; ring
  exact ⟨Units.mkOfMulEqOne _ _ h2, hr⟩

theorem cls_key (L : IsLoc O Δ) {t t' : Kˣ} {S S' : Set (Etau K τ)} (h : S ∈ Gs O τ t 1) (h' : S' ∈ Gs O τ t' 1)
    (e : cls τ S = cls τ S') : ∃ (s : Kˣ) (ε : Oˣ), S = ml (sc τ s) S' ∧ (t' : K) = algebraMap O K ε * (s : K) ^ 2 * t := by
  obtain ⟨s, hs⟩ := cls_eq e
  obtain ⟨h, c, -, hg⟩ := h
  have h1 : IsFixP O τ (t' / (s : K) ^ 2) S := by
    rw [hs]
    refine fix_ml _ ?_
    rw [nU_sc, Units.val_pow_eq_pow_val, div_mul_cancel₀ _ (pow_ne_zero _ s.ne_zero)]
    exact h'.1
  obtain ⟨ε, hε⟩ := fix_uniq L hg h h1 t.ne_zero (div_ne_zero t'.ne_zero (pow_ne_zero _ s.ne_zero))
  refine ⟨s, ε, hs, ?_⟩
  rw [div_eq_iff (pow_ne_zero _ s.ne_zero)] at hε
  rw [hε]; ring

theorem cls_injOn (L : IsLoc O Δ) (t : Kˣ) : Set.InjOn (cls τ) (Gs O τ t 1) := by
  intro S h S' h' e
  obtain ⟨s, ε, hs, hε⟩ := cls_key L h h' e
  obtain ⟨u, hu⟩ := unit_of_sq L (s := s) (ε := ε) (mul_right_cancel₀ t.ne_zero (by rw [one_mul]; exact hε))
  rw [hs, ml_unit h'.1.fg u s hu]

theorem cls_sub (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (t : K) : cls τ '' Gs O τ t 1 ⊆ Fv O τ := by
  rintro _ ⟨S, ⟨h, c, hc, hg⟩, rfl⟩
  exact ⟨S, (UpperTheory.isLattice_iff_fixedPoint_quadraticTorus O K Δ τ L hτ S).1 t h, h.stab, ⟨c, hc, by simpa using hg⟩, rfl⟩

theorem gs_fin (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (t : Kˣ) (a : (Etau K τ)ˣ) : (Gs O τ t a).Finite := by
  rw [gs_ml, ← Units.val_mul]
  exact (Set.Finite.of_finite_image ((UpperTheory.quadraticTorus_fixedVertices_finite O K Δ τ L hτ).subset (cls_sub L hτ _)) (cls_injOn L _)).image _

theorem fv_card (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (t p : Kˣ) (hp : ¬ EvenVal O (p : K)) :
    (Fv O τ).ncard = (Gs O τ t 1).ncard + (Gs O τ (t * p : Kˣ) 1).ncard := by
  have aux : ∀ (t : Kˣ) (t' : K) (S : Set (Etau K τ)), IsFixP O τ t' S → (∃ c ∈ Cint O τ, Gen O τ S c) →
      EvenVal O (t' / t) → cls τ S ∈ cls τ '' Gs O τ t 1 := by
    rintro t t' S h ⟨c, hc, hg⟩ ⟨ε, s, hs, e⟩
    refine ⟨ml (sc τ (Units.mk0 s hs)) S, ⟨fix_ml _ ?_, _, mul_mem (sc_mem _) hc, by rw [one_mul]; exact gen_ml hg _⟩,
      cls_sc _ _⟩
    convert fix_unit ε⁻¹ h using 1
    rw [div_eq_iff t.ne_zero] at e
    rw [e, nU_sc, Units.val_pow_eq_pow_val, Units.val_mk0, mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one]
    ring
  have hU : Fv O τ = cls τ '' Gs O τ t 1 ∪ cls τ '' Gs O τ (t * p : Kˣ) 1 := by
    refine Set.Subset.antisymm ?_ (Set.union_subset (cls_sub L hτ _) (cls_sub L hτ _))
    rintro _ ⟨S, hl, hs, hg, rfl⟩
    obtain ⟨t', h0, h⟩ := (UpperTheory.isLattice_iff_fixedPoint_quadraticTorus O K Δ τ L hτ S).2 hl hs
    rcases even_or L (div_ne_zero h0 t.ne_zero) p.ne_zero hp with e | e
    · exact Or.inl (aux _ _ _ h hg e)
    · exact Or.inr (aux _ _ _ h hg (by rwa [div_div, ← Units.val_mul] at e))
  rw [hU, Set.ncard_union_eq ?_ ((gs_fin L hτ _ _).image _) ((gs_fin L hτ _ _).image _),
    (cls_injOn L _).ncard_image, (cls_injOn L _).ncard_image]
  rw [Set.disjoint_left]
  rintro _ ⟨S, h, rfl⟩ ⟨S', h', e⟩
  obtain ⟨s, ε, -, hε⟩ := cls_key L h h' e.symm
  exact hp ⟨ε, s, s.ne_zero, mul_right_cancel₀ t.ne_zero (by rw [← hε, Units.val_mul, mul_comm])⟩

theorem vcount_eq (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) : vcount O τ ω = ((Fv O τ).ncard : ℂ) := by
  letI := mulAct τ
  let P : Set (Set (Set (Etau K τ))) := {X | ∃ S, IsLat O τ S ∧ (∀ y ∈ S, ω * y ∈ S) ∧ X = cls τ S}
  have hs : ∀ (z : (Etau K τ)ˣ) (S : Set (Etau K τ)), z • cls τ S = cls τ (ml z S) := fun z S => cls_ml z S
  rw [← wCard _ _ (Cint O τ) P (Fv O τ) ?_ ?_ (UpperTheory.quadraticTorus_fixedVertices_finite O K Δ τ L hτ) ?_ ?_ ?_]
  · unfold vcount
    congr 1
  · rintro z _ ⟨S, hl, hst, rfl⟩
    exact ⟨_, lat_ml hl z, stab_ml hst z, hs z S⟩
  · rintro _ ⟨S, hl, hst, -, rfl⟩
    exact ⟨S, hl, hst, rfl⟩
  · rintro z hz _ ⟨S, hl, hst, ⟨c, hc, hg⟩, rfl⟩
    exact ⟨_, lat_ml hl z, stab_ml hst z, ⟨_, mul_mem hz hc, gen_ml hg z⟩, hs z S⟩
  · rintro _ ⟨S, hl, hst, rfl⟩
    obtain ⟨y, hy⟩ := gen_ex L hτ hl
    exact ⟨y⁻¹, _, lat_ml hl _, stab_ml hst _, ⟨_, by simp, gen_ml hy _⟩, hs _ S⟩
  · rintro z _ ⟨S, -, -, ⟨c, hc, hg⟩, rfl⟩ ⟨S', -, -, ⟨c', hc', hg'⟩, e⟩
    refine ⟨z, ?_, rfl⟩
    rw [hs] at e
    obtain ⟨s, e⟩ := cls_eq e
    have h1 := gen_ml hg' (sc τ s)
    rw [← e] at h1
    have := mul_mem (mul_mem (mul_mem (sc_mem s) hc') (gen_uniq h1 (gen_ml hg z))) (inv_mem hc)
    rwa [mul_inv_cancel_left, mul_inv_cancel_right] at this

theorem pcount_eq (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (t : Kˣ) (a b : (Etau K τ)ˣ)
    (h1 : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = a * c * z ^ 2 ∨ y = b * c * z ^ 2)
    (h2 : ∀ z : (Etau K τ)ˣ, z ^ 2 * a * b⁻¹ ∈ Cint O τ → z ∈ Cint O τ) :
    pcount O τ t = ((Gs O τ t a ∪ Gs O τ t b).ncard : ℂ) := by
  letI := quoAct τ
  have hs : ∀ (z : (Etau K τ)ˣ) (S : Set (Etau K τ)), z • S = ml (qU z) S := fun z S => by
    rw [ml, qU_val]; rfl
  have hf : ∀ (z : (Etau K τ)ˣ) (S : Set (Etau K τ)), IsFixP O τ t S → IsFixP O τ t (z • S) := fun z S h => by
    rw [hs]; exact fix_ml _ (by simpa [nU_qU] using h)
  have hC : ∀ a, ∀ z ∈ Cint O τ, ∀ S ∈ Gs O τ t a, z • S ∈ Gs O τ t a := by
    rintro a z hz S ⟨h, c, hc, hg⟩
    refine ⟨hf z S h, _, mul_mem (qU_mem hz) hc, ?_⟩
    rw [hs, mul_left_comm]; exact gen_ml hg _
  have hE : ∀ a c z S, c ∈ Cint O τ → IsFixP O τ t S → Gen O τ S (a * c * z ^ 2) → z⁻¹ • S ∈ Gs O τ t a := by
    intro a c z S hc h hg
    refine ⟨hf _ S h, c * sc τ (nU z), mul_mem hc (sc_mem _), ?_⟩
    rw [hs]
    convert gen_ml hg (qU z⁻¹) using 1
    rw [qU, inv_inv]
    apply mul_left_cancel (a := z ^ 2)
    rw [← mul_assoc (z ^ 2) (_ * _) (_ * _ * _), ← mul_assoc (z ^ 2) (z⁻¹ ^ 2), ← mul_pow, mul_inv_cancel, one_pow, one_mul]
    ac_rfl
  have hU : ∀ a b z S, S ∈ Gs O τ t a → z • S ∈ Gs O τ t b → z ^ 2 * a * b⁻¹ ∈ Cint O τ := by
    rintro a b z S ⟨-, c, hc, hg⟩ ⟨-, c', hc', hg'⟩
    rw [hs] at hg'
    have := mul_mem (mul_mem (mul_mem hc' (gen_uniq hg' (gen_ml hg (qU z)))) (inv_mem hc)) (sc_mem (nU z))
    convert this using 1
    rw [qU, map_inv, map_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  rw [← wCard _ _ (Cint O τ) {S | IsFixP O τ t S} _ hf ?_ ((gs_fin L hτ t a).union (gs_fin L hτ t b)) ?_ ?_ ?_]
  · unfold pcount
    congr 1
  · rintro S (h | h) <;> exact h.1
  · rintro z hz S (h | h)
    · exact Or.inl (hC _ z hz S h)
    · exact Or.inr (hC _ z hz S h)
  · intro S h
    obtain ⟨y, hy⟩ := gen_ex L hτ ((UpperTheory.isLattice_iff_fixedPoint_quadraticTorus O K Δ τ L hτ S).1 t h)
    obtain ⟨z, c, hc, rfl | rfl⟩ := h1 y
    · exact ⟨_, Or.inl (hE _ _ _ _ hc h hy)⟩
    · exact ⟨_, Or.inr (hE _ _ _ _ hc h hy)⟩
  · intro z S h h'
    refine ⟨z, ?_, rfl⟩
    rcases h with h | h <;> rcases h' with h' | h'
    · exact mem_C_of_sq (by simpa using hU _ _ _ _ h h')
    · exact h2 z (hU _ _ _ _ h h')
    · refine inv_mem_iff.1 (h2 z⁻¹ ?_)
      convert inv_mem (hU _ _ _ _ h h') using 1
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    · exact mem_C_of_sq (by simpa using hU _ _ _ _ h h')

end UpperTheory.V.Z.Sym.Loc.PS
