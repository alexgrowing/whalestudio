import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SignLemma

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_rep_conj_chi_smul_and_q_twisted {K : Type} [Field K] {n : ℕ} (u v r ri r' ri' : Matrix (Fin n) (Fin n) K) (e : K)
    (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1) (hr' : r' * ri' = 1)
    (hA : rᵀ * u * r' = e • u) (X : Matrix (Fin n) (Fin n) K) :
    -(v * (r * X * ri)ᵀ * u) = r' * -(v * Xᵀ * u) * ri' := by
  have hrT : riᵀ * rᵀ = 1 := by rw [← Matrix.transpose_mul, hr, Matrix.transpose_one]
  have h1 : u * r' = e • (riᵀ * u) := by
    calc u * r' = riᵀ * (rᵀ * u * r') := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrT, Matrix.one_mul]
      _ = e • (riᵀ * u) := by rw [hA, Matrix.mul_smul]
  have h2 : ∀ Z, r' * (v * Z) = e • (v * (riᵀ * Z)) := by
    intro Z
    calc r' * (v * Z) = v * (u * r') * (v * Z) := by
          rw [← Matrix.mul_assoc v u r', hvu, Matrix.one_mul]
      _ = e • (v * (riᵀ * Z)) := by
          rw [h1]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc u v Z, huv, Matrix.one_mul]
  have hA' : rᵀ * (u * r') = e • u := by rw [← Matrix.mul_assoc]; exact hA
  have h3 : -(v * (r * X * ri)ᵀ * u) * r' = r' * -(v * Xᵀ * u) := by
    simp only [Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hA', h2,
      Matrix.mul_smul]
  calc -(v * (r * X * ri)ᵀ * u) = -(v * (r * X * ri)ᵀ * u) * (r' * ri') := by
        rw [hr', Matrix.mul_one]
    _ = r' * -(v * Xᵀ * u) * ri' := by rw [← Matrix.mul_assoc, h3]

private theorem u_mul_ri_mul_v_eq_transpose_of_eigen {K : Type} [Field K] {n : ℕ} (u v A r ri : Matrix (Fin n) (Fin n) K) (e : K)
    (he : e ≠ 0) (huv : u * v = 1) (hvu : v * u = 1) (hr : r * ri = 1)
    (h1 : A * u * r = e • u) (h2 : A * uᵀ * r = e • uᵀ) : u * ri * v = uᵀ * ri * vᵀ := by
  have huvT : uᵀ * vᵀ = 1 := by rw [← Matrix.transpose_mul, hvu, Matrix.transpose_one]
  have hA1 : A = e • (u * ri * v) := by
    calc A = A * u * r * ri * v := by
          rw [Matrix.mul_assoc (A * u) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A u v, huv,
            Matrix.mul_one]
      _ = e • (u * ri * v) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  have hA2 : A = e • (uᵀ * ri * vᵀ) := by
    calc A = A * uᵀ * r * ri * vᵀ := by
          rw [Matrix.mul_assoc (A * uᵀ) r ri, hr, Matrix.mul_one, Matrix.mul_assoc A uᵀ vᵀ, huvT,
            Matrix.mul_one]
      _ = e • (uᵀ * ri * vᵀ) := by rw [h2, Matrix.smul_mul, Matrix.smul_mul]
  exact smul_right_injective _ he (hA1.symm.trans hA2)

private theorem neg_conj_neg_transpose_eq_self_of_symm {K : Type} [Field K] {n : ℕ} (u v X : Matrix (Fin n) (Fin n) K)
    (hvu : v * u = 1) (hS : u * X * v = uᵀ * X * vᵀ) : -(v * (-(v * Xᵀ * u))ᵀ * u) = X := by
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc uᵀ X vᵀ, ← hS, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  simp only [Matrix.mul_assoc]
  rw [hvu, Matrix.mul_one, ← Matrix.mul_assoc, hvu, Matrix.one_mul]

theorem UpperTheory.V.Ws.Eb.adExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K), Full ρ → F.IsForm O n ρ P →
        ∃ R : Representation K F.Γ (Matrix (Fin n) (Fin n) K), IsAdExt F ρ P R := by
  intro l _ F O _ _ K _ _ n ρ P hFull hForm
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hconjv : ∀ g : F.G₀, ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c := by
    intro g
    show F.c * ↑g * F.c⁻¹ = _
    rw [hci]
  have hconj2 : ∀ g : F.G₀, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    rw [hconjv, hconjv]
    simp only [mul_assoc, hcc, mul_one, hcc']
  have heps : ∀ g : F.G₀, F.eps O K (F.conj g) = F.eps O K g := by
    intro g
    simp [W.GFrame.eps, W.GFrame.conj, W.pushCh]
  have hF : ∀ g : F.G₀, (↑(ρ g) : Matrix (Fin n) (Fin n) K)ᵀ * (↑P : Matrix (Fin n) (Fin n) K) *
      (↑(ρ (F.conj g)) : Matrix (Fin n) (Fin n) K) =
      ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (↑P : Matrix (Fin n) (Fin n) K) := hForm
  have huv : (↑P : Matrix (Fin n) (Fin n) K) * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv P
  have hvu : (↑P⁻¹ : Matrix (Fin n) (Fin n) K) * (↑P : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul P
  have hS : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑P : Matrix (Fin n) (Fin n) K) * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) =
      (↑P : Matrix (Fin n) (Fin n) K)ᵀ * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ := by
    intro X
    have hX : X ∈ Submodule.span K (Set.range (W.mat ρ)) := by
      have h : Submodule.span K (Set.range (W.mat ρ)) = ⊤ := hFull
      rw [h]
      exact Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e1 := hF (F.conj h⁻¹)
      rw [hconj2] at e1
      have e2 := congrArg Matrix.transpose (hF h⁻¹)
      rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc, ← heps h⁻¹] at e2
      refine u_mul_ri_mul_v_eq_transpose_of_eigen _ _ ((↑(ρ (F.conj h⁻¹)) : Matrix (Fin n) (Fin n) K)ᵀ) (↑(ρ h⁻¹)) _ _
        (Units.ne_zero _) huv hvu ?_ e1 e2
      show (↑(ρ h⁻¹) : Matrix (Fin n) (Fin n) K) * (↑(ρ h) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => simp only [Matrix.mul_smul, Matrix.smul_mul, hx]
  let θ : Module.End K (Matrix (Fin n) (Fin n) K) :=
    { toFun := fun X => -((↑P⁻¹ : Matrix (Fin n) (Fin n) K) * Xᵀ * (↑P : Matrix (Fin n) (Fin n) K))
      map_add' := fun X Y => by
        simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
      map_smul' := fun a X => by
        simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
          RingHom.id_apply] }
  have hkey : ∀ g : F.G₀, θ * Loc.adGL ρ g = Loc.adGL ρ (F.conj g) * θ := by
    intro g
    apply LinearMap.ext
    intro X
    exact exists_rep_conj_chi_smul_and_q_twisted _ _ _ _ _ _ _ huv hvu (Units.mul_inv _) (Units.mul_inv _) (hF g) X
  have hθθ : θ * θ = 1 := by
    apply LinearMap.ext
    intro X
    exact neg_conj_neg_transpose_eq_self_of_symm _ _ X hvu (hS X)
  have hker : ∀ γ : F.Γ, F.η γ ≠ 1 → γ * F.c ∈ F.η.ker := by
    intro γ h
    rw [MonoidHom.mem_ker, map_mul, F.η_c]
    rcases Int.units_eq_one_or (F.η γ) with h' | h'
    · exact absurd h' h
    · rw [h']
      exact Int.units_mul_self _
  have hAd : ∀ x y : F.G₀, (x : F.Γ) = y → Loc.adGL ρ x = Loc.adGL ρ y := by
    intro x y hxy
    rw [Subtype.ext hxy]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  let f : F.Γ → Module.End K (Matrix (Fin n) (Fin n) K) := fun γ =>
    if h : F.η γ = 1 then Loc.adGL ρ ⟨γ, h⟩ else Loc.adGL ρ ⟨γ * F.c, hker γ h⟩ * θ
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ⟨?_, ?_⟩⟩
  · show f 1 = 1
    simp only [f, dif_pos (map_one F.η)]
    exact map_one (Loc.adGL ρ)
  · intro a b
    show f (a * b) = f a * f b
    have hab : F.η (a * b) = F.η a * F.η b := map_mul _ _ _
    rcases Int.units_eq_one_or (F.η a) with ha | ha <;>
      rcases Int.units_eq_one_or (F.η b) with hb | hb
    · have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb, one_mul]
      simp only [f, dif_pos ha, dif_pos hb, dif_pos h1]
      rw [← map_mul (Loc.adGL ρ)]
      exact hAd _ _ rfl
    · have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, one_mul]; exact hne
      simp only [f, dif_pos ha, dif_neg hb', dif_neg h1]
      rw [← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [mul_assoc])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have h1 : F.η (a * b) ≠ 1 := by rw [hab, ha, hb, mul_one]; exact hne
      simp only [f, dif_neg ha', dif_pos hb, dif_neg h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, hkey, ← mul_assoc, ← map_mul (Loc.adGL ρ)]
      congr 1
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc'])
    · have ha' : F.η a ≠ 1 := by rw [ha]; exact hne
      have hb' : F.η b ≠ 1 := by rw [hb]; exact hne
      have h1 : F.η (a * b) = 1 := by rw [hab, ha, hb]; exact Int.units_mul_self _
      simp only [f, dif_neg ha', dif_neg hb', dif_pos h1]
      rw [mul_assoc (Loc.adGL ρ _) θ, ← mul_assoc θ, hkey, mul_assoc (Loc.adGL ρ _) θ θ, hθθ,
        mul_one, ← map_mul (Loc.adGL ρ)]
      exact hAd _ _ (by simp [hconjv, mul_assoc, hcc, hcc'])
  · intro g X
    show f ↑g X = _
    simp only [f, dif_pos (MonoidHom.mem_ker.mp g.2)]
  · intro X
    show f F.c X = _
    have hn : ¬ F.η F.c = 1 := by rw [F.η_c]; exact hne
    simp only [f, dif_neg hn]
    rw [Module.End.mul_apply]
    have h1 : ∀ p, (⟨F.c * F.c, p⟩ : F.G₀) = 1 := fun p => Subtype.ext hcc
    rw [h1, map_one]
    rfl
