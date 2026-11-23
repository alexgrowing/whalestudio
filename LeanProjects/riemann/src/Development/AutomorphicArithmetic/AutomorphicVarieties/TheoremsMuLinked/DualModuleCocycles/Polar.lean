import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (t : MonoidAlgebra R F.G₀ →ₗ[R] R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X), ((P : Matrix (Fin n) (Fin n) O)ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) O)ᵀ = -P) → F.IsForm O n ρ P → (∀ g, t (F.star O R n (MonoidAlgebra.single g 1)) = t (MonoidAlgebra.single g 1)) → IsLift x δ (repR x (mat ρ)) t c d → ∃ d' : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x (mat ρ)) t (2 * c) d' ∧ ∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d' (F.star O R n a) = (d' a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P t c d hP hF ht hd
  obtain ⟨hsm, hsa, hsr, hss, -, hsρ⟩ := starFacts F (O := O) (R := R) (n := n)
  have hρs := hsρ x ρ P hF
  obtain ⟨ε, hεε, hPt⟩ : ∃ ε : O, ε * ε = 1 ∧
      (P : Matrix (Fin n) (Fin n) O)ᵀ = ε • (P : Matrix (Fin n) (Fin n) O) := by
    rcases hP with h | h
    · exact ⟨1, one_mul 1, by rw [h, one_smul]⟩
    · exact ⟨-1, by ring, by rw [h, neg_one_smul]⟩
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B :=
    fun A B => Matrix.map_mul
  set Pb := bar X (P : Matrix (Fin n) (Fin n) O) with hPb
  set Q := bar X ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hQ
  set e : X := algebraMap O X ε with he
  have hQP : Q * Pb = 1 := by
    rw [hQ, hPb, ← hmap, Units.inv_mul]
    simp [bar]
  have hPQ : Pb * Q = 1 := by
    rw [hQ, hPb, ← hmap, Units.mul_inv]
    simp [bar]
  have hQP' : ∀ M, Q * (Pb * M) = M := fun M => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPQ' : ∀ M, Pb * (Q * M) = M := fun M => by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hee : e * e = 1 := by rw [he, ← map_mul, hεε, map_one]
  have hPbt : Pbᵀ = e • Pb := by
    ext i j
    have h := congrFun (congrFun hPt i) j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp [hPb, bar, Matrix.transpose_apply, h, map_mul, he]
  have hQt : Qᵀ = e • Q := by
    have h0 : e • (Pb * Qᵀ) = 1 := by
      rw [← Matrix.smul_mul, ← hPbt, ← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h1 : Pb * Qᵀ = e • 1 := by
      calc Pb * Qᵀ = (e * e) • (Pb * Qᵀ) := by rw [hee, one_smul]
        _ = e • 1 := by rw [mul_smul, h0]
    calc Qᵀ = Q * (Pb * Qᵀ) := by rw [hQP']
      _ = e • Q := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hρ : ∀ a, bar X (repR x (mat ρ) (F.star O R n a)) =
      Q * (bar X (repR x (mat ρ) a))ᵀ * Pb := by
    intro a
    rw [hρs, hmap, hmap]
    rfl
  have hρT : ∀ a, (bar X (repR x (mat ρ) (F.star O R n a)))ᵀ =
      Pb * bar X (repR x (mat ρ) a) * Q := by
    intro a
    rw [hρ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hPbt, hQt]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc]
  let eD : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X :=
    AddMonoidHom.mk' (fun a => Q * (d (F.star O R n a))ᵀ * Pb) (by
      intro a b
      simp only [hsa, map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul])
  have heD : ∀ a, eD a = Q * (d (F.star O R n a))ᵀ * Pb := fun a => rfl
  have h0 : F.star O R n 0 = 0 := by simpa using hsr 0 0
  have htS : ∀ a, t (F.star O R n a) = t a := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [h0]
    | add a b ha hb => rw [hsa, map_add, map_add, ha, hb]
    | single g r =>
      have hs : (MonoidAlgebra.single g r : MonoidAlgebra R F.G₀) = r • MonoidAlgebra.single g 1 := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [hs, hsr, map_smul, map_smul, ht]
  refine ⟨d + eD, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    simp only [AddMonoidHom.add_apply, heD, hd.mul, hsm, Matrix.transpose_add, Matrix.transpose_mul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQP', hQP, Matrix.mul_one]
    abel
  · intro r a
    simp only [AddMonoidHom.add_apply, heD, hd.smul, hsr, Matrix.transpose_add, Matrix.transpose_smul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hQP',
      hQP, Matrix.mul_one, smul_add, two_mul, add_smul]
    abel
  · intro a
    rw [AddMonoidHom.add_apply, Matrix.trace_add, hd.tr, heD, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hPQ, Matrix.one_mul, Matrix.trace_transpose, hd.tr, htS, two_mul, add_smul]
  · intro a
    simp only [AddMonoidHom.add_apply, heD, hss, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPbt, hQt, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc, hPQ', hPQ, hQP, hQP', Matrix.mul_one]
    abel
