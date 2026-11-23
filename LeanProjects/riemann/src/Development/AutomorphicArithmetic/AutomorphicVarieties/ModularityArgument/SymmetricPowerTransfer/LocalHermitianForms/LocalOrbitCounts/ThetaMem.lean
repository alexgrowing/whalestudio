import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.HermAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Fixg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (h2 : ∃ u : Oˣ, algebraMap O K u = 2 - τ)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S : Set (Sp Δ τ)} (hS : IsFix O c d m S) (x : Sp Δ τ) :
    x ∈ S ↔ (x.1, (0 : EL Δ τ)) ∈ S ∧ ((0 : Lsq K Δ), x.2) ∈ S := by
  obtain ⟨hadd, -, hfst, hsnd⟩ := UpperTheory.V.Z.Sym.Loc.One.splitS O K Δ τ hL hτ h2 c d m hD S hS
  constructor
  · intro hx
    refine ⟨hfst x hx, ?_⟩
    have h := hsnd x hx 1 ⟨1, by simp⟩ ⟨0, by simp⟩
    rwa [ofE_one, one_mul] at h
  · rintro ⟨h1, h3⟩
    have h := hadd _ h1 _ h3
    simpa using h

private theorem mem_iff_mk_ofE_mul_snd_mem_of_forall_inr_iff {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (h2 : ∃ u : Oˣ, algebraMap O K u = 2 - τ)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S₀ S₁ : Set (Sp Δ τ)} (h₀ : IsFix O c d m S₀)
    (h₁ : IsFix O c d m S₁) (s : K) (y₀ : (EL Δ τ)ˣ)
    (hy : ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ x : EL Δ τ, ((0 : Lsq K Δ), x) ∈ S ↔
      ∃ a b : Etau K τ, x = ↑y₀ * (ofE Δ a + ({ re := 0, im := s } : Lsq K Δ) • ofE Δ b) ∧
        ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S ∧ ((0 : Lsq K Δ), ↑y₀ * ofE Δ b) ∈ S)
    (q : (Etau K τ)ˣ)
    (hq : ∀ a : Etau K τ, ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S₀ ↔
      ((0 : Lsq K Δ), ↑y₀ * ofE Δ ((q : Etau K τ) * a)) ∈ S₁)
    (x : Sp Δ τ) : x ∈ S₀ ↔ (x.1, ofE Δ (q : Etau K τ) * x.2) ∈ S₁ := by
  rw [mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub hL hτ h2 hD h₀ x, mem_iff_fst_mem_and_snd_mem_of_isFix_of_isUnit_two_sub hL hτ h2 hD h₁ (x.1, ofE Δ (q : Etau K τ) * x.2)]
  dsimp only
  have hf : (x.1, (0 : EL Δ τ)) ∈ S₀ ↔ (x.1, (0 : EL Δ τ)) ∈ S₁ :=
    ⟨UpperTheory.V.Z.Sym.Loc.One.fst O K Δ τ hL hτ h2 c d m hD S₀ S₁ h₀ h₁ x.1,
      UpperTheory.V.Z.Sym.Loc.One.fst O K Δ τ hL hτ h2 c d m hD S₁ S₀ h₁ h₀ x.1⟩
  refine and_congr hf ?_
  rw [hy S₀ h₀, hy S₁ h₁]
  constructor
  · rintro ⟨a, b, hx, ha, hb⟩
    refine ⟨(q : Etau K τ) * a, (q : Etau K τ) * b, ?_, (hq a).1 ha, (hq b).1 hb⟩
    rw [hx, ofE_mul, ofE_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  · rintro ⟨a, b, hx, ha, hb⟩
    refine ⟨(↑q⁻¹ : Etau K τ) * a, (↑q⁻¹ : Etau K τ) * b, ?_, (hq _).2 (by rwa [Units.mul_inv_cancel_left]),
      (hq _).2 (by rwa [Units.mul_inv_cancel_left])⟩
    have hq1 : ofE Δ (↑q⁻¹ : Etau K τ) * ofE Δ (q : Etau K τ) = 1 := by
      rw [← ofE_mul, Units.inv_mul, ofE_one]
    calc x.2 = ofE Δ (↑q⁻¹ : Etau K τ) * (ofE Δ (q : Etau K τ) * x.2) := by
          rw [← mul_assoc, hq1, one_mul]
      _ = _ := by
        rw [hx, ofE_mul, ofE_mul, Algebra.smul_def, Algebra.smul_def]
        ring

private theorem mem_iff_tor_mem_of_isFix_of_isIntegral_quo {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ τ : K} (hL : IsLoc O Δ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4)
    {c : K} {d m : EL Δ τ} (hD : IsDat c d m) {S : Set (Sp Δ τ)} (hS : IsFix O c d m S)
    (z : (Etau K τ)ˣ) (hz1 : IsIntegral O (quo z)) (hz2 : IsIntegral O (quo z⁻¹)) (x : Sp Δ τ) :
    x ∈ S ↔ tor Δ z x ∈ S := by
  obtain ⟨hτ, h2, -, -⟩ := UpperTheory.V.Z.Sym.Loc.One.intE O K Δ τ hL hu
  obtain ⟨u, s, hs, hΔ⟩ := hL.even
  obtain ⟨y₀, hy⟩ := UpperTheory.V.Z.Sym.Loc.One.snd O K Δ τ hL hu c d m hD s⁻¹ u
    (by rw [hΔ, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), mul_one])
  have hω : ∀ x ∈ {a : Etau K τ | ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S},
      ω * x ∈ {a : Etau K τ | ((0 : Lsq K Δ), ↑y₀ * ofE Δ a) ∈ S} := by
    intro x hx
    have h := (UpperTheory.V.Z.Sym.Loc.One.splitS O K Δ τ hL hτ h2 c d m hD S hS).2.2.2 _ hx ω ⟨0, by simp⟩ ⟨1, by simp⟩
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [ofE_mul, mul_left_comm]
    exact h
  obtain ⟨u₀, hu₀⟩ := UpperTheory.V.Z.Sym.Loc.One.princ O K Δ τ hL hu _
    (UpperTheory.V.Z.Sym.Loc.One.lat O K Δ τ hL c d m S hS y₀) hω
  simp only [Set.mem_setOf_eq] at hu₀
  have hqq : quo z * quo z⁻¹ = 1 := by
    simp only [quo, inv_inv]
    have e1 : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := Units.mul_inv z
    have e2 : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
      rw [← star_mul, Units.mul_inv, star_one]
    linear_combination (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ)) * e1 + e2
  let q : (Etau K τ)ˣ := ⟨quo z, quo z⁻¹, hqq, by rw [mul_comm]; exact hqq⟩
  have H := mem_iff_mk_ofE_mul_snd_mem_of_forall_inr_iff hL hτ h2 hD hS hS s⁻¹ y₀ hy q (by
    intro a
    rw [hu₀, hu₀]
    show IsIntegral O ((↑u₀⁻¹ : Etau K τ) * a) ↔ IsIntegral O ((↑u₀⁻¹ : Etau K τ) * (quo z * a))
    constructor
    · intro h
      have h' := hz1.mul h
      have e : quo z * ((↑u₀⁻¹ : Etau K τ) * a) = (↑u₀⁻¹ : Etau K τ) * (quo z * a) := by ring
      rwa [e] at h'
    · intro h
      have h' := hz2.mul h
      have e : quo z⁻¹ * ((↑u₀⁻¹ : Etau K τ) * (quo z * a)) = (↑u₀⁻¹ : Etau K τ) * a := by
        linear_combination ((↑u₀⁻¹ : Etau K τ) * a) * hqq
      rwa [e] at h') x
  exact H

theorem UpperTheory.V.Z.Sym.Loc.oneU :
    UpperTheory.V.Z.Sym.Loc.OneU := by
  intro O K _ _ _ _ _ Δ τ hL c d m hD δ ι P hM hδ hu
  obtain ⟨u, s, hs, hΔ⟩ := hL.even
  have hstar : ∀ x : Lsq K Δ, IsInt O x → IsInt O (star x) := fun x =>
    ((UpperTheory.V.Z.Sym.Loc.descent O K Δ hL s⁻¹ u
      (by rw [hΔ, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs), mul_one])) x).2
  have kuOf : ∀ g : U3 Δ, (∀ v : Fin 3 → Lsq K Δ, (∀ i, IsInt O (v i)) →
      ∀ i, IsInt O (((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v) i)) → g ∈ KU O Δ := by
    intro g hg
    have hij : ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := by
      intro i j
      have h := hg (Pi.single j 1) (by
        intro k
        simp only [Pi.single_apply]
        split_ifs
        · exact isIntegral_one
        · exact isIntegral_zero) i
      simpa [Matrix.mulVec_single] using h
    show ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
    exact fun i j => ⟨hij i j, hstar _ (hij i j)⟩
  have h1fix := UpperTheory.V.Z.Sym.Loc.One.fixg O K Δ τ hL c d m δ ι P hM 1
    (by rw [inv_one, one_mul, map_one, mul_one]; exact hδ)
  have hmem1 : ∀ x : Sp Δ τ, x ∈ {x : Sp Δ τ | ∀ i, IsInt O
      (((((1 : U3 Δ)⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P x) i)} ↔ ∀ i, IsInt O (P x i) := by
    intro x
    simp
  have hθ : ∀ g : U3 Δ, ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := fun g => rfl
  have hstarmv : ∀ (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
      star (M *ᵥ v) = M.map star *ᵥ star v := by
    intro M v
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have hcomm : ∀ z : (Etau K τ)ˣ, (ι z)⁻¹ * δ * theta Δ (ι z) = δ := by
    intro z
    have hv : ∀ x : Sp Δ τ, ((δ * theta Δ (ι z) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) =
        ((ι z * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (P x) := by
      intro x
      have e1 : semi d (tor Δ z x) = tor Δ z (semi d x) := by
        simp only [semi, tor, sigL_mul, sigL_ofE]
        exact Prod.ext rfl (by dsimp only; ring)
      have e2 := congrArg P e1
      rw [hM.semi, hM.tor, hM.tor, hM.semi, hstarmv] at e2
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hθ]
      exact e2
    have hM' : ((δ * theta Δ (ι z) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
        ((ι z * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := by
      funext i j
      have h := congrFun (hv (P.symm (star (Pi.single j 1)))) i
      simpa [Matrix.mulVec_single] using h
    have hU : δ * theta Δ (ι z) = ι z * δ := Subtype.ext hM'
    rw [mul_assoc, hU, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨fun y => ⟨fun hy => ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · have hyfix := UpperTheory.V.Z.Sym.Loc.One.fixg O K Δ τ hL c d m δ ι P hM y hy
    obtain ⟨z, hz⟩ := UpperTheory.V.Z.Sym.Loc.One.uniq O K Δ τ hL hu c d m hD _ _ h1fix hyfix
    refine ⟨z, (ι z)⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
    apply kuOf
    intro v hv i
    have hx := (hz (P.symm ((((ι z)⁻¹ * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v))).2 (by
      show ∀ i, IsInt O ((((y⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ
        P (tor Δ z (P.symm ((((ι z)⁻¹ * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ v)))) i)
      rw [hM.tor, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Submonoid.coe_mul, ← Submonoid.coe_mul]
      have e : y⁻¹ * ι z * ((ι z)⁻¹ * y) = 1 := by group
      rw [e, Submonoid.coe_one, Matrix.one_mulVec]
      exact hv)
    rw [hmem1] at hx
    simpa using hx i
  · rintro ⟨z, k, hk, rfl⟩
    have hθk : theta Δ k ∈ KU O Δ := by
      have hk' : ∀ i j, IsInt O ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
          IsInt O (star ((k : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) := hk
      show ∀ i j, IsInt O (((theta Δ k : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
        IsInt O (star (((theta Δ k : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
      intro i j
      rw [hθ]
      simp only [Matrix.map_apply, star_star]
      exact ⟨(hk' i j).2, (hk' i j).1⟩
    have e : (ι z * k)⁻¹ * δ * theta Δ (ι z * k) = k⁻¹ * ((ι z)⁻¹ * δ * theta Δ (ι z)) * theta Δ k := by
      rw [map_mul, _root_.mul_inv_rev]
      simp only [mul_assoc]
    rw [e, hcomm z]
    exact mul_mem (mul_mem (inv_mem hk) hδ) hθk
  · intro z hz
    apply (UpperTheory.V.Z.Sym.Loc.stabU O K Δ τ hL c d m hD δ ι P hM 1).1
    show (MulAut.conj (1 : U3 Δ)⁻¹).toMonoidHom (ι z) ∈ KU O Δ
    simpa using hz
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    show ι z ∈ KU O Δ
    apply kuOf
    intro v hv i
    have hx := (mem_iff_tor_mem_of_isFix_of_isIntegral_quo hL hu hD h1fix z hz1 hz2 (P.symm v)).1 ((hmem1 _).2 (by simpa using hv))
    rw [hmem1, hM.tor] at hx
    simpa using hx i
