import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem comm_of_sep {K V : Type} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g h : Module.End K V) (hs : f.charpoly.Separable)
    (hg : Commute f g) (hh : Commute f h) : g * h = h * g := by
  classical
  have key : ∀ μ : K, ∀ x ∈ f.maxGenEigenspace μ, (g * h) x = (h * g) x := by
    intro μ x hx
    have hd : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hd
    have hgW := Module.End.mapsTo_maxGenEigenspace_of_comm hg μ
    have hhW := Module.End.mapsTo_maxGenEigenspace_of_comm hh μ
    obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hv ⟨g (v : V), hgW v.2⟩
    obtain ⟨c, hc⟩ := hv ⟨h (v : V), hhW v.2⟩
    have ha' : a • (v : V) = x := congrArg Subtype.val ha
    have hb' : b • (v : V) = g v := congrArg Subtype.val hb
    have hc' : c • (v : V) = h v := congrArg Subtype.val hc
    rw [← ha', Module.End.mul_apply, Module.End.mul_apply, map_smul, map_smul, map_smul, map_smul,
      ← hb', ← hc', map_smul, map_smul, ← hb', ← hc', smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hker : ∀ μ, f.maxGenEigenspace μ ≤ LinearMap.ker (g * h - h * g) := by
    intro μ x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact key μ x hx
  have htop : LinearMap.ker (g * h - h * g) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)

private theorem mat_comm_of_sep {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (P Z E : Matrix (Fin n) (Fin n) K) (hs : P.charpoly.Separable)
    (hg : P * Z = Z * P) (hh : P * E = E * P) : Z * E = E * Z := by
  let φ := (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))
  have hc : (φ P).charpoly = P.charpoly := Matrix.charpoly_toLin' P
  have e := comm_of_sep (φ P) (φ Z) (φ E) (by rw [hc]; exact hs)
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hg])
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hh])
  apply φ.injective
  rw [map_mul, map_mul]
  exact e

theorem UpperTheory.V.Pa.od_comm :
    ∀ (A : Type) [CommRing A] [IsDomain A] (n a : ℕ) (P Z : Matrix (Fin n) (Fin n) A) (al : Fin n → A), P ∈ Ev A A n a → Z ∈ Od A A n a → Function.Injective al → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → P * Z = Z * P → Z = 0 := by
  intro A _ _ n a P Z al hP hZ hal hchar hPZ
  classical
  have hP' : ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → P i j = 0 := by
    intro i j h
    have := (hP i j).2 h
    simpa using this
  have hZ' : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
    intro i j h
    have := (hZ i j).1 h
    simpa using this
  let e : Fin n → A := fun i => if (i : ℕ) < a then 1 else 0
  have hPE : P * Matrix.diagonal e = Matrix.diagonal e * P := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · simp [e, hi, hj]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj]
  let K := AlgebraicClosure (FractionRing A)
  let ι : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hs : (P.map ι).charpoly.Separable := by
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (hι.comp hal)
  have h1 : P.map ι * Z.map ι = Z.map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPZ]
  have h2 : P.map ι * (Matrix.diagonal e).map ι = (Matrix.diagonal e).map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPE]
  have h3 := mat_comm_of_sep (P.map ι) (Z.map ι) ((Matrix.diagonal e).map ι) hs h1 h2
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h3
  have h4 : Z * Matrix.diagonal e = Matrix.diagonal e * Z := Matrix.map_injective hι h3
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h5
  rw [Matrix.zero_apply]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · exact hZ' i j (by simp [hi, hj])
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5.symm
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5
  · exact hZ' i j (by simp [hi, hj])
