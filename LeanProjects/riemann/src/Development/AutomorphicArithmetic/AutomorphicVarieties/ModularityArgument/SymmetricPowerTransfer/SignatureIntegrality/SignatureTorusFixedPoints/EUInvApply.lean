import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ s : K}

private theorem neg_sq (hs : s * s = Δ) : (-s) * (-s) = Δ := by rw [neg_mul_neg, hs]

private theorem proj_apply (hs : s * s = Δ) (x : Lsq K Δ) : proj hs x = x.re + s * x.im := rfl

private theorem proj_star (hs : s * s = Δ) (x : Lsq K Δ) : proj hs (star x) = proj (neg_sq hs) x := by
  simp [proj_apply]

private theorem proj_alg (hs : s * s = Δ) (a : K) : proj hs (algebraMap K (Lsq K Δ) a) = a := by
  simp [proj_apply]

private theorem proj_ext (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) {x y : Lsq K Δ}
    (e1 : proj hs x = proj hs y) (e2 : proj (neg_sq hs) x = proj (neg_sq hs) y) : x = y := by
  rw [proj_apply, proj_apply] at e1 e2
  have a : 2 * x.re = 2 * y.re := by linear_combination e1 + e2
  have b : (2 * s) * x.im = (2 * s) * y.im := by linear_combination e1 - e2
  ext
  · exact mul_left_cancel₀ h2 a
  · exact mul_left_cancel₀ (mul_ne_zero h2 h0) b

private def lft (s a b : K) : Lsq K Δ := ⟨(a + b) / 2, (a - b) / (2 * s)⟩

private theorem proj_lft (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (a b : K) :
    proj hs (lft s a b) = a := by
  rw [proj_apply]
  show (a + b) / 2 + s * ((a - b) / (2 * s)) = a
  field_simp
  ring

private theorem proj_lft' (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (a b : K) :
    proj (neg_sq hs) (lft s a b) = b := by
  rw [proj_apply]
  show (a + b) / 2 + -s * ((a - b) / (2 * s)) = b
  field_simp
  ring

private theorem eU_val (hs : s * s = Δ) (g : U3 Δ) :
    ((eU hs g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj hs) := rfl

private theorem eU_inv_apply (hs : s * s = Δ) (g : U3 Δ) (i j : Fin 3) :
    (((eU hs g)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      proj (neg_sq hs) ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) j i) := by
  rw [← map_inv, eU_val, Matrix.map_apply, ← proj_star]
  rfl

private theorem theta_val (g : U3 Δ) :
    ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star := rfl

private theorem eU_theta (hs : s * s = Δ) (g : U3 Δ) : eU hs (theta Δ g) = th K 3 (eU hs g) := by
  ext i j
  rw [eU_val, theta_val]
  show _ = ((eU hs g)⁻¹ : GL (Fin 3) K) j i
  rw [eU_inv_apply, Matrix.map_apply, Matrix.map_apply, proj_star]

end Alg

section Alg2

variable {K : Type} [Field K] {Δ s : K}

private theorem proj_star' (hs : s * s = Δ) (x : Lsq K Δ) : proj (neg_sq hs) (star x) = proj hs x := by
  simp [proj_apply]

private theorem eU_inj (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) : Function.Injective (eU hs) := by
  intro g g' h
  refine Subtype.ext (Matrix.ext fun i j => proj_ext h2 h0 hs ?_ ?_)
  · have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j) h
    simpa only [eU_val, Matrix.map_apply] using this
  · have := congrArg (fun x : GL (Fin 3) K => ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j i) h
    simpa only [eU_inv_apply] using this

private theorem eU_surj (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) : Function.Surjective (eU hs) := by
  intro A
  set B : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hB
  let M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
    Matrix.of fun i j => lft s ((A : Matrix (Fin 3) (Fin 3) K) i j) (B j i)
  have p1 : M.map (proj hs) = (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    exact proj_lft h2 h0 hs _ _
  have p2 : M.map (proj (neg_sq hs)) = Bᵀ := by
    ext i j
    exact proj_lft' h2 h0 hs _ _
  have q1 : (star M).map (proj hs) = B := by
    ext i j
    rw [Matrix.map_apply, Matrix.star_apply, proj_star]
    have e := congrFun (congrFun p2 j) i
    simpa only [Matrix.map_apply, Matrix.transpose_apply] using e
  have q2 : (star M).map (proj (neg_sq hs)) = (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by
    ext i j
    rw [Matrix.map_apply, Matrix.star_apply, proj_star']
    have e := congrFun (congrFun p1 j) i
    simpa only [Matrix.map_apply, Matrix.transpose_apply] using e
  have hBA : B * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hB]
    exact A.inv_mul
  have e1 : (star M * M).map (proj hs) = (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj hs) := by
    rw [Matrix.map_mul, q1, p1, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (star M * M).map (proj (neg_sq hs)) =
      (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (proj (neg_sq hs)) := by
    rw [Matrix.map_mul, q2, p2, ← Matrix.transpose_mul, hBA, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : star M * M = 1 := by
    refine Matrix.ext fun i j => ?_
    apply proj_ext h2 h0 hs
    · have e := congrFun (congrFun e1 i) j
      simpa only [Matrix.map_apply] using e
    · have e := congrFun (congrFun e2 i) j
      simpa only [Matrix.map_apply] using e
  refine ⟨⟨M, (Matrix.mem_unitaryGroup_iff').2 hu⟩, ?_⟩
  apply Units.ext
  rw [eU_val]
  exact p1

private theorem hasTau_iff (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) (δ : U3 Δ) (τ : K) :
    HasTau δ τ ↔ ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly =
      (X - 1) * (X ^ 2 - C τ * X + 1) := by
  set N : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) with hN
  set Q : K[X] := (X - 1) * (X ^ 2 - C τ * X + 1) with hQ
  have hQ' : ((X - 1) * (X ^ 2 - C (algebraMap K (Lsq K Δ) τ) * X + 1) : (Lsq K Δ)[X]) =
      Q.map (algebraMap K (Lsq K Δ)) := by
    simp [hQ]
  have hA : ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = N.map (proj hs) := by
    rw [← eU_theta, ← map_mul, eU_val]
  have htt : theta Δ (theta Δ δ) = δ := by
    apply Subtype.ext
    rw [theta_val, theta_val]
    refine Matrix.ext fun i j => ?_
    show star (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) = _
    exact star_star _
  have hθ : (theta Δ δ * δ : U3 Δ) = theta Δ (δ * theta Δ δ) := by
    rw [map_mul, htt]
  have hB : N.map (proj (neg_sq hs)) =
      ((eU hs (theta Δ δ) * eU hs δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← map_mul, eU_val, hθ, theta_val]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, proj_star]
  have h1 : N.charpoly.map (proj hs) =
      ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly := by
    rw [hA, Matrix.charpoly_map]
  have h2' : N.charpoly.map (proj (neg_sq hs)) =
      ((eU hs δ * th K 3 (eU hs δ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).charpoly := by
    rw [← Matrix.charpoly_map, hB, ← eU_theta, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm]
  show N.charpoly = _ ↔ _
  rw [hQ']
  constructor
  · intro h
    rw [← h1, h, Polynomial.map_map]
    have hc : (proj hs).comp (algebraMap K (Lsq K Δ)) = RingHom.id K := RingHom.ext (proj_alg hs)
    rw [hc, Polynomial.map_id]
  · intro h
    refine Polynomial.ext fun n => ?_
    rw [Polynomial.coeff_map]
    apply proj_ext h2 h0 hs
    · rw [proj_alg, ← Polynomial.coeff_map, h1, h]
    · rw [proj_alg, ← Polynomial.coeff_map, h2', h]

end Alg2

section Int

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {O : Type} [CommRing O] [Algebra O k] {Δ s : k}

private theorem val_of_int (hO : IsInts k O) {a : k} (h : IsIntegral O a) : valuation k a ≤ 1 := by
  have hv : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩
  exact hv.mem_of_integral h

private theorem proj_algO (hs : s * s = Δ) (r : O) : proj hs (algebraMap O (Lsq k Δ) r) = algebraMap O k r := by
  rw [IsScalarTower.algebraMap_apply O k (Lsq k Δ), proj_alg]

private theorem int_proj (hs : s * s = Δ) {x : Lsq k Δ} (h : IsIntegral O x) : IsIntegral O (proj hs x) := by
  have hc : (algebraMap O k).comp (RingHom.id O) = (proj hs).comp (algebraMap O (Lsq k Δ)) :=
    RingHom.ext fun r => (proj_algO hs r).symm
  exact IsIntegral.map_of_comp_eq (RingHom.id O) (proj hs) hc h

private theorem int_of_val (hO : IsInts k O) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) {x : Lsq k Δ}
    (e1 : valuation k (proj hs x) ≤ 1) (e2 : valuation k (proj (neg_sq hs) x) ≤ 1) : IsIntegral O x := by
  have hsum : valuation k (proj hs x + proj (neg_sq hs) x) ≤ 1 := (valuation k).map_add_le e1 e2
  have hprod : valuation k (proj hs x * proj (neg_sq hs) x) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' e1 e2
  obtain ⟨p, hp⟩ := RingHom.mem_range.1 ((hO.range _).2 hsum)
  obtain ⟨q, hq⟩ := RingHom.mem_range.1 ((hO.range _).2 hprod)
  refine ⟨X ^ 2 - C p * X + C q, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [IsScalarTower.algebraMap_apply O k (Lsq k Δ) p, IsScalarTower.algebraMap_apply O k (Lsq k Δ) q, hp, hq]
  apply proj_ext h2 h0 hs
  · simp only [map_add, map_sub, map_mul, map_pow, proj_alg, map_zero]
    ring
  · simp only [map_add, map_sub, map_mul, map_pow, proj_alg, map_zero]
    ring

private theorem comap_KO (hO : IsInts k O) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) (hs : s * s = Δ) :
    (KO k (Fin 3)).comap (eU hs) = KU O Δ := by
  ext g
  rw [Subgroup.mem_comap, GlAx.mem_KO, GlAx.bd_zero, GlAx.bd_zero]
  constructor
  · rintro ⟨hA, hB⟩
    have a1 : ∀ i j, valuation k (proj hs ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) ≤ 1 := fun i j => by
      have e := hA i j
      rw [eU_val, Matrix.map_apply, Valuation.mem_integer_iff] at e
      exact e
    have a2 : ∀ i j, valuation k (proj (neg_sq hs) ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) ≤ 1 := fun i j => by
      have e := hB j i
      rw [eU_inv_apply, Valuation.mem_integer_iff] at e
      exact e
    show ∀ i j, _ ∧ _
    refine fun i j => ⟨int_of_val hO h2 h0 hs (a1 i j) (a2 i j), int_of_val hO h2 h0 hs ?_ ?_⟩
    · rw [proj_star]
      exact a2 i j
    · rw [proj_star']
      exact a1 i j
  · intro hg
    have hg' : ∀ i j, IsIntegral O ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j) ∧
        IsIntegral O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq k Δ)) i j)) := hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [eU_val, Matrix.map_apply, Valuation.mem_integer_iff]
      exact val_of_int hO (int_proj hs (hg' i j).1)
    · rw [eU_inv_apply, ← proj_star hs, Valuation.mem_integer_iff]
      exact val_of_int hO (int_proj hs (hg' j i).2)

end Int

theorem eU_facts : EU := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs h0
  exact ⟨⟨eU_inj h2 h0 hs, eU_surj h2 h0 hs⟩, eU_theta hs, comap_KO hO h2 h0 hs, hasTau_iff h2 h0 hs⟩

end UpperTheory.V.Z.Sym.Sig

end
