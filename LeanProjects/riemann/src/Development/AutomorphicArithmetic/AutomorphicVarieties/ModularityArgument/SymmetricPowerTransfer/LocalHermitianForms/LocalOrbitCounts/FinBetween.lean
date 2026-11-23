import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeProperties.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem fin_between {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
    (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (x : Etau K τ) (hx : x.im ≠ 0) :
    {S : Set (Etau K τ) | IsLat O τ S ∧ 1 ∈ S ∧ x ∈ S ∧ ∀ w ∈ S, IsIntegral O w}.Finite := by
  haveI := L.frac
  classical
  obtain ⟨N, hN, hden⟩ := int_denom L hτ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) ({-x.re / x.im, 1 / x.im} : Finset K)
  obtain ⟨p, hp⟩ := hr _ (Finset.mem_insert_self _ _)
  obtain ⟨q, hq⟩ := hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [Algebra.smul_def] at hp hq
  haveI := finite_quot_span L (mul_ne_zero hN (nonZeroDivisors.coe_ne_zero r))
  let M := integralClosure O (Etau K τ)
  haveI : Module.Finite O M := Module.Finite.iff_fg (N := Subalgebra.toSubmodule M).2 (intE_fg L hτ)
  let I : Submodule O M := Ideal.span {N * r} • ⊤
  haveI : Finite (M ⧸ I) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let f : Set (M ⧸ I) → Set (Etau K τ) := fun A => Subtype.val '' (I.mkQ ⁻¹' A)
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨⟨⟨g, rfl⟩, -⟩, h1, h2, h3⟩
  set T := Submodule.span O (g : Set (Etau K τ))
  refine ⟨I.mkQ '' (Subtype.val ⁻¹' (T : Set (Etau K τ))), ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
    have h4 : y - z ∈ (Ideal.span {N * r} • ⊤ : Submodule O M) := (Submodule.Quotient.eq _).1 e.symm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨m, -, hm⟩ := h4
    have hm' : (N * r) • (m : Etau K τ) = y - z := congrArg Subtype.val hm
    obtain ⟨a, b, ha, hb⟩ := hden _ m.2
    have e2 : (y : Etau K τ) = z + ((r * a + b * p) • (1 : Etau K τ) + (b * q) • x) := by
      rw [← sub_eq_iff_eq_add', ← hm', ← algebraMap_smul K (N * r), ← algebraMap_smul K (r * a + b * p), ← algebraMap_smul K (b * q)]
      simp only [map_mul, map_add, hp, hq, ← ha, ← hb]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, - algebraMap_smul] <;> field_simp <;> ring
    rw [e2]
    exact T.add_mem hz (T.add_mem (T.smul_mem _ h1) (T.smul_mem _ h2))
  · intro hw
    exact ⟨⟨w, h3 w hw⟩, ⟨⟨w, h3 w hw⟩, hw, rfl⟩, rfl⟩

open UpperTheory.V.Z.Sym.Loc.GL in
theorem UpperTheory.V.Z.Sym.Loc.finG : UpperTheory.V.Z.Sym.Loc.FinG := by
  intro O K _ _ _ _ _ Δ τ L hτ j hj z hz
  haveI := L.frac
  classical
  obtain ⟨g, hg⟩ := (gConj O K Δ τ L hτ (j0 τ) j leftMulMatrixEmbedding_omega_trace hj).1
  have det : ∀ (y : GL (Fin 2) K) (s : Kˣ) (k : GL (Fin 2) K), k ∈ KG O K → y⁻¹ * jU j z * y = sc s * k →
      ∃ e : Oˣ, QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K e * (s : K) ^ 2 := fun y s k hk e => by
    obtain ⟨u, hu⟩ := kg_det hk
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
    simp only [Units.val_mul] at this
    rw [Matrix.det_units_conj', Matrix.det_mul, hu, sc_val, Matrix.det_smul] at this
    exact ⟨u, by rw [← j_det j hj]; exact this.trans (by simp [mul_comm])⟩
  by_cases h0 : ∃ y₀ : GL (Fin 2) K, y₀⁻¹ * jU j z * y₀ ∈ ZK O K
  swap
  · exact ⟨∅, fun y hy => absurd ⟨y, hy⟩ h0⟩
  obtain ⟨y₀, hy₀⟩ := h0
  obtain ⟨s, k₀, hk₀, e₀⟩ := zk_iff.1 hy₀
  obtain ⟨ε, hε⟩ := det y₀ s k₀ hk₀ e₀
  let u : (Etau K τ)ˣ := su τ s⁻¹ * z
  have hun : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, Algebra.smul_def, map_mul, QuadraticAlgebra.norm_algebraMap, hε, Units.val_inv_eq_inv_val]
    field_simp
  have hui : (u : Etau K τ).im ≠ 0 := by
    rw [Units.val_mul, su_mul]
    simpa using hz
  have fin := fin_between L hτ u hui
  choose! rep hrep using fun S (h : IsLat O τ S) => isLat_lat h
  refine ⟨fin.toFinset.image fun S => g⁻¹ * rep S, fun y hy => ?_⟩
  have h1 : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) ∈ ZK O K := by
    have : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) = sc s⁻¹ * (y⁻¹ * jU j z * y) := by
      rw [map_mul, jU_su, hg, mul_assoc (sc s⁻¹), ← mul_assoc, ← sc_comm]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) hy
  have h2 := ent_of_zk ε (by
    rw [← mul_assoc, Units.val_mul, Units.val_mul, Matrix.det_units_conj', ← hun]; exact leftMulMatrixEmbedding_det_eq_norm _) h1
  have h3 := lat_le (τ := τ).2 h2
  rw [lat_mul] at h3
  obtain ⟨t, ht⟩ := PS.gen_ex L hτ (lat_isLat (O := O) (g * y))
  have hl := PS.lat_ml (lat_isLat (O := O) (τ := τ) (g * y)) t⁻¹
  have hm : PS.ml t⁻¹ (LL O τ (g * y)) ∈ fin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨hl, PS.mem_ml.2 (by simpa using ht.1), PS.mem_ml.2 ?_, ?_⟩
    · rw [inv_inv, mul_comm]; exact h3 ⟨_, ht.1, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ht.2 w hw
  refine ⟨t, _, Finset.mem_image_of_mem _ hm, (jU j t * (g⁻¹ * rep (PS.ml t⁻¹ (LL O τ (g * y)))))⁻¹ * y, ?_, by group⟩
  have : cls τ (LL O τ (jU (j0 τ) t * rep (PS.ml t⁻¹ (LL O τ (g * y))))) = cls τ (LL O τ (g * y)) := by
    rw [lat_mul, ← hrep _ hl]
    change cls τ (PS.ml _ _) = _
    rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  rw [cls_lat] at this
  rw [hg]
  simpa [mul_assoc] using this
