import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SqBasis
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section
variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem nu_mul (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by simp [nu]
private theorem nu_one : nu ι 1 = 1 := by simp [nu]
private theorem nu_zero : nu ι 0 = 0 := by simp [nu]
private theorem nu_nonneg (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _
private theorem nu_pos {x : ℂ} (hx : x ≠ 0) : 0 < nu ι x := by
  simpa [nu] using hx
private theorem nu_neg (x : ℂ) : nu ι (-x) = nu ι x := by simp [nu]
private theorem nu_add_le (x y : ℂ) : nu ι (x + y) ≤ max (nu ι x) (nu ι y) := by
  simpa [nu] using IsUltrametricDist.norm_add_le_max (ι.symm x) (ι.symm y)
private theorem nu_sum_le {α : Type} (s : Finset α) (f : α → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, nu ι (f i) ≤ C) : nu ι (∑ i ∈ s, f i) ≤ C := by
  unfold nu
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h
private theorem nu_zpow (x : ℂ) (k : ℤ) : nu ι (x ^ k) = nu ι x ^ k := by
  simp [nu, map_zpow₀, norm_zpow]
private theorem nu_prod {α : Type} (s : Finset α) (f : α → ℂ) :
    nu ι (∏ i ∈ s, f i) = ∏ i ∈ s, nu ι (f i) := by
  simp [nu, map_prod, norm_prod]

private def ball : Subring ℂ where
  carrier := {x | nu ι x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [nu_mul]; exact mul_le_one₀ ha (nu_nonneg ι _) hb
  one_mem' := (nu_one ι).le
  add_mem' {a b} ha hb := (nu_add_le ι a b).trans (max_le ha hb)
  zero_mem' := by simp [nu_zero]
  neg_mem' {a} ha := by simpa [nu_neg] using ha

private theorem prod_zpow_sum {α : Type} {p : ℝ} (hp : p ≠ 0) (s : Finset α) (f : α → ℤ) :
    ∏ i ∈ s, p ^ f i = p ^ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hp]

private theorem mat_bound {κ : Type} [Fintype κ] [DecidableEq κ] (A B : Matrix κ κ ℂ) (c : κ → ℂ) {X : ℝ}
    (hX : 0 ≤ X) (hA : ∀ i j, nu ι (A i j) ≤ 1) (hB : ∀ i j, nu ι (B i j) ≤ 1)
    (hc : ∀ m, nu ι (c m) ≤ X) (i j : κ) : nu ι ((A * diagonal c * B) i j) ≤ X := by
  rw [Matrix.mul_apply]
  refine nu_sum_le ι _ _ hX fun m _ => ?_
  rw [Matrix.mul_diagonal, nu_mul, nu_mul]
  calc _ ≤ 1 * X * 1 :=
        mul_le_mul (mul_le_mul (hA _ _) (hc _) (nu_nonneg ι _) zero_le_one) (hB _ _) (nu_nonneg ι _)
          (by simpa using hX)
    _ = X := by ring

private theorem mat_bound' {κ δ : Type} [Fintype κ] (P : Matrix δ κ ℂ) (M : Matrix κ κ ℂ) (Q : Matrix κ δ ℂ)
    {c Y : ℝ} (hc : 0 ≤ c) (hY : 0 ≤ Y) (hP : ∀ i j, nu ι (P i j) ≤ c) (hQ : ∀ i j, nu ι (Q i j) ≤ c)
    (hM : ∀ i j, nu ι (M i j) ≤ Y) (i j : δ) : nu ι ((P * M * Q) i j) ≤ c * c * Y := by
  have h0 : 0 ≤ c * c * Y := by positivity
  rw [Matrix.mul_apply]
  refine nu_sum_le ι _ _ h0 fun y _ => ?_
  rw [nu_mul, Matrix.mul_apply]
  have h1 : nu ι (∑ x, P i x * M x y) ≤ c * Y :=
    nu_sum_le ι _ _ (by positivity) fun x _ => by
      rw [nu_mul]; exact mul_le_mul (hP _ _) (hM _ _) (nu_nonneg ι _) hc
  calc _ ≤ (c * Y) * c := mul_le_mul h1 (hQ _ _) (nu_nonneg ι _) (by positivity)
    _ = c * c * Y := by ring

private theorem entries_le_one {n : ℕ} (lam : DomWeight n) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℂ (nablaSq ℂ n lam))
    (hb : ∀ c : ball ι, c ≠ 0 → ∀ g : GL (Fin n) (ball ι), (∀ i j, c ∣ (g.val - 1) i j) → ∀ i j, ∃ x,
      b.repr (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map (algebraMap (ball ι) ℂ) g) (b j)) i =
        (if i = j then 1 else 0) + algebraMap (ball ι) ℂ (c * x))
    (h : GL (Fin n) ℂ) (h1 : ∀ i j, h.val i j ∈ ball ι) (h2 : ∀ i j, (h⁻¹).val i j ∈ ball ι) (i j : κ) :
    nu ι (LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam h) i j) ≤ 1 := by
  obtain ⟨k, rfl⟩ := Formalism.UG.P.cartan_mem_of_entries (ball ι) h h1 h2
  obtain ⟨x, hx⟩ := hb 1 one_ne_zero k (fun _ _ => one_dvd _) i j
  rw [LinearMap.toMatrix_apply]
  have e : Formalism.UG.bc (n := Fin n) (ball ι).subtype k = GeneralLinearGroup.map (algebraMap (ball ι) ℂ) k := by
    ext; rfl
  rw [e, hx]
  have m1 : ((if i = j then 1 else 0 : ℂ)) ∈ ball ι := by
    split_ifs
    exacts [(ball ι).one_mem, (ball ι).zero_mem]
  exact (ball ι).add_mem m1 (SetLike.coe_mem (1 * x))

end

section
variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]
  {u : HeightOneSpectrum (𝓞 E)} (ψ : u.adicCompletion E →+* ℂ)

private noncomputable def dg {n : ℕ} (ϖ : (u.adicCompletion E)ˣ) (a : Fin n → ℤ) : GL (Fin n) (u.adicCompletion E) :=
  diagGL _ n fun i => ϖ ^ a i

private theorem dg_inv {n : ℕ} (ϖ : (u.adicCompletion E)ˣ) (a : Fin n → ℤ) : (dg ϖ a)⁻¹ = dg ϖ (-a) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change diagonal _ * diagonal _ = (1 : Matrix _ _ _)
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  change ((ϖ ^ a i * ϖ ^ (-a i) : (u.adicCompletion E)ˣ) : u.adicCompletion E) = 1
  rw [← _root_.zpow_add]
  simp

private theorem nu_unit (hψ : ∀ x, Valued.v x ≤ 1 → nu ι (ψ x) ≤ 1) {x : u.adicCompletion E}
    (hx : Valued.v x = 1) : nu ι (ψ x) = 1 := by
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 := hψ x hx.le
  have h2 := hψ x⁻¹ (by rw [map_inv₀, hx, inv_one])
  have h3 : nu ι (ψ x) * nu ι (ψ x⁻¹) = 1 := by
    rw [← nu_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, nu_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ nu ι (ψ x) * 1 := mul_le_mul_of_nonneg_left h2 (nu_nonneg ι _)
    _ = _ := mul_one _

private theorem side {n : ℕ} (lam : DomWeight n) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℂ (nablaSq ℂ n lam)) (μ : κ → Fin n → ℤ)
    (hK : ∀ h : GL (Fin n) ℂ, (∀ i j, h.val i j ∈ ball ι) → (∀ i j, (h⁻¹).val i j ∈ ball ι) → ∀ i j,
      nu ι (LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam h) i j) ≤ 1)
    (hD : ∀ (g : GL (Fin n) ℂ) (t : Fin n → ℂ), g.val = diagonal t → ∀ j,
      GlobalTheory.Branching.sqRep ℂ n lam g (b j) = (∏ i, t i ^ μ j i) • b j)
    (hψ : ∀ x, Valued.v x ≤ 1 → nu ι (ψ x) ≤ 1) (ϖ : (u.adicCompletion E)ˣ) (a : Fin n → ℤ)
    {k₁ k₂ : GL (Fin n) (u.adicCompletion E)} (h₁ : k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u))
    (h₂ : k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u)) {X : ℝ} (hX : 0 ≤ X)
    (hc : ∀ m, nu ι (ψ ϖ) ^ (∑ i, a i * μ m i) ≤ X) (i j : κ) :
    nu ι (LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam
      (GeneralLinearGroup.map ψ (k₁ * dg ϖ a * k₂))) i j) ≤ X := by
  have hKm : ∀ k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u), ∀ i j,
      nu ι (LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ k)) i j) ≤ 1 := by
    intro k hk
    refine hK _ (fun i j => hψ _ (Formalism.UG.P.cartan_entries_of_mem _ k hk i j)) fun i j => ?_
    rw [← map_inv]
    exact hψ _ (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk) i j)
  have hp : nu ι (ψ ϖ) ≠ 0 := (nu_pos ι ((map_ne_zero ψ).2 ϖ.ne_zero)).ne'
  let c : κ → ℂ := fun m => ∏ i, ψ ((ϖ ^ a i : (u.adicCompletion E)ˣ) : u.adicCompletion E) ^ μ m i
  have hDm : LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ (dg ϖ a))) =
      diagonal c := by
    ext p q
    rw [LinearMap.toMatrix_apply, hD _ (fun i => ψ ((ϖ ^ a i : (u.adicCompletion E)ˣ) : u.adicCompletion E)) ?_ q]
    · rw [map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases h : p = q
      · subst h
        simp [c]
      · simp [h, Ne.symm h]
    · ext r s
      simp [dg, diagGL, diagonal_apply, apply_ite ψ]
  have hT : ∀ x y : GL (Fin n) ℂ, LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam (x * y)) =
      LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam x) * LinearMap.toMatrix b b (GlobalTheory.Branching.sqRep ℂ n lam y) :=
    fun x y => by rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b]
  rw [(GeneralLinearGroup.map ψ).map_mul, (GeneralLinearGroup.map ψ).map_mul, hT, hT, hDm]
  refine mat_bound ι _ _ c hX (hKm k₁ h₁) (hKm k₂ h₂) (fun m => ?_) i j
  have e : ∀ i, nu ι (ψ ((ϖ ^ a i : (u.adicCompletion E)ˣ) : u.adicCompletion E) ^ μ m i) =
      nu ι (ψ ϖ) ^ (a i * μ m i) := fun i => by
    rw [nu_zpow, Units.val_zpow_eq_zpow_val, map_zpow₀, nu_zpow, _root_.zpow_mul]
  simp only [c, nu_prod, e, prod_zpow_sum hp]
  exact hc m

private theorem decomp (hψ : ∀ x, Valued.v x ≤ 1 → nu ι (ψ x) ≤ 1) {n : ℕ} (ϖ : (u.adicCompletion E)ˣ)
    (hϖ : Formalism.UG.IsUnifV E u ϖ) (g : GL (Fin n) (u.adicCompletion E)) (hg : ∀ i j, Valued.v (g.val i j) ≤ 1) :
    ∃ a : Fin n → ℤ, Antitone a ∧ (∀ i, 0 ≤ a i) ∧ nu ι (ψ g.val.det) = nu ι (ψ ϖ) ^ ∑ i, a i ∧
      (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u),
        g = k₁ * dg ϖ a * k₂) ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u),
        g = k₁ * dg ϖ (a ∘ Fin.rev) * k₂ := by
  have hlt : Valued.v (ϖ : u.adicCompletion E) < 1 := Formalism.UG.P.cartan_unif_lt_one E u _ hϖ
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E u n ϖ hlt.le hϖ g
  have e' : g = k₁ * dg ϖ a * k₂ := Units.ext (by
    rw [e]
    simp only [Units.val_mul]
    congr 2
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    exact (Units.val_zpow_eq_zpow_val _ _).symm)
  have hdet : ∀ k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E u), nu ι (ψ k.val.det) = 1 := fun k hk =>
    nu_unit ι ψ hψ (Formalism.UG.P.cartan_val_det _ Valued.v (Formalism.UG.P.cartan_mem_Ov E u) k hk)
  have hp : nu ι (ψ ϖ) ≠ 0 := (nu_pos ι ((map_ne_zero ψ).2 ϖ.ne_zero)).ne'
  refine ⟨a, ha, fun i => ?_, ?_, ⟨k₁, hk₁, k₂, hk₂, e'⟩, ?_⟩
  · have h1 : k₁⁻¹ * g * k₂⁻¹ = dg ϖ a := by rw [e']; group
    have h2 : ((k₁⁻¹ * g * k₂⁻¹).val i i) ∈ Formalism.UG.Ov E u := by
      simp only [Units.val_mul, Matrix.mul_apply]
      refine Subring.sum_mem _ fun y _ => Subring.mul_mem _ (Subring.sum_mem _ fun x _ =>
        Subring.mul_mem _ (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁) _ _) (hg _ _))
        (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂) _ _)
    rw [h1] at h2
    have h3 : Valued.v ((ϖ : u.adicCompletion E) ^ a i) ≤ 1 := by
      have : (dg ϖ a).val i i = (ϖ : u.adicCompletion E) ^ a i := by
        simp [dg, diagGL, Units.val_zpow_eq_zpow_val]
      rw [← this]
      exact h2
    rw [map_zpow₀] at h3
    exact (zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)) hlt).1 h3
  · have h1 : g.val.det = k₁.val.det * (∏ i, ((ϖ ^ a i : (u.adicCompletion E)ˣ) : u.adicCompletion E)) * k₂.val.det := by
      rw [e']
      simp only [Units.val_mul, Matrix.det_mul]
      congr 2
      exact det_diagonal
    rw [h1, map_mul, map_mul, nu_mul, nu_mul, hdet k₁ hk₁, hdet k₂ hk₂, one_mul, mul_one, map_prod, nu_prod,
      ← prod_zpow_sum hp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, nu_zpow]
  · obtain ⟨S₁, h₁, e₁⟩ := Formalism.UG.P.cartan_perm_glint (Formalism.UG.Ov E u) (Fin.revPerm (n := n)).symm
    obtain ⟨S₂, h₂, e₂⟩ := Formalism.UG.P.cartan_perm_glint (Formalism.UG.Ov E u) (Fin.revPerm (n := n))
    have h3 : dg ϖ a = S₁ * dg ϖ (a ∘ Fin.rev) * S₂ := Units.ext (by
      simp only [Units.val_mul]
      rw [e₁, e₂]
      exact Formalism.UG.P.cartan_diag_perm (fun i => ((ϖ ^ a i : (u.adicCompletion E)ˣ) : u.adicCompletion E)) Fin.revPerm)
    refine ⟨k₁ * S₁, mul_mem hk₁ h₁, S₂ * k₂, mul_mem h₂ hk₂, ?_⟩
    rw [e', h3]
    group

end

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.repBound :
    UpperTheory.V.Z.Int.RepBound := by
  intro l _ ι E _ _ u ψ hψ n lam d e
  obtain ⟨κ, _, _, k0, b, μ, h1, -, h3, h4, h5, -⟩ :=
    UpperTheory.V.Hi.sqBasis (ball ι) ℂ Subtype.val_injective n lam
  have hK := entries_le_one ι lam b h1
  let P := e.toMatrix b
  let Q := b.toMatrix e
  obtain ⟨c, hc, hP, hQ⟩ : ∃ c : ℝ, 0 ≤ c ∧ (∀ i j, nu ι (P i j) ≤ c) ∧ ∀ i j, nu ι (Q i j) ≤ c := by
    have s1 : 0 ≤ ∑ i, ∑ j, nu ι (P i j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nu_nonneg ι _
    have s2 : 0 ≤ ∑ i, ∑ j, nu ι (Q i j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nu_nonneg ι _
    refine ⟨(∑ i, ∑ j, nu ι (P i j)) + ∑ i, ∑ j, nu ι (Q i j), add_nonneg s1 s2, fun i j => ?_, fun i j => ?_⟩
    · have t1 : nu ι (P i j) ≤ ∑ j, nu ι (P i j) :=
        Finset.single_le_sum (f := fun j => nu ι (P i j)) (fun _ _ => nu_nonneg ι _) (Finset.mem_univ j)
      have t2 : ∑ j, nu ι (P i j) ≤ ∑ i, ∑ j, nu ι (P i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, nu ι (P i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => nu_nonneg ι _) (Finset.mem_univ i)
      linarith
    · have t1 : nu ι (Q i j) ≤ ∑ j, nu ι (Q i j) :=
        Finset.single_le_sum (f := fun j => nu ι (Q i j)) (fun _ _ => nu_nonneg ι _) (Finset.mem_univ j)
      have t2 : ∑ j, nu ι (Q i j) ≤ ∑ i, ∑ j, nu ι (Q i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, nu ι (Q i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => nu_nonneg ι _) (Finset.mem_univ i)
      linarith
  have hM : ∀ f : nablaSq ℂ n lam →ₗ[ℂ] nablaSq ℂ n lam,
      LinearMap.toMatrix e e f = P * LinearMap.toMatrix b b f * Q := fun f =>
    (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f).symm
  refine ⟨c * c, by positivity, fun lo hi hlh g hg i j => ?_⟩
  obtain ⟨ϖ0, hϖ0⟩ : ∃ p, Formalism.UG.IsUnifV E u p := u.valuedAdicCompletion_surjective E _
  let ϖ : (u.adicCompletion E)ˣ := Units.mk0 ϖ0 (Formalism.UG.P.cartan_unif_ne_zero E u ϖ0 hϖ0)
  obtain ⟨a, ha, ha0, hdet, ⟨k₁, hk₁, k₂, hk₂, e₁⟩, ⟨k₃, hk₃, k₄, hk₄, e₂⟩⟩ := decomp ι ψ hψ ϖ hϖ0 g hg
  have hp0 : 0 < nu ι (ψ ϖ) := nu_pos ι ((map_ne_zero ψ).2 ϖ.ne_zero)
  have hp1 : nu ι (ψ ϖ) ≤ 1 := hψ _ (Formalism.UG.P.cartan_unif_lt_one E u _ hϖ0).le
  have hmono : ∀ x y : ℤ, x ≤ y → nu ι (ψ ϖ) ^ y ≤ nu ι (ψ ϖ) ^ x := fun x y h =>
    zpow_le_zpow_right_of_le_one₀ hp0 hp1 h
  rw [hdet, ← _root_.zpow_mul, ← _root_.zpow_mul]
  constructor
  · have B := side ι ψ lam b μ hK h3 hψ ϖ a hk₁ hk₂ (X := nu ι (ψ ϖ) ^ ((∑ i, a i) * lo))
      (zpow_nonneg hp0.le _) (fun m => hmono _ _ (by
        refine le_trans ?_ (h5 m a ha)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [h4]
        exact mul_le_mul_of_nonneg_left (hlh _).1 (ha0 r)))
    rw [← e₁] at B
    rw [hM]
    exact mat_bound' ι P _ Q hc (zpow_nonneg hp0.le _) hP hQ B i j
  · have hinv : g⁻¹ = k₄⁻¹ * dg ϖ (-(a ∘ Fin.rev)) * k₃⁻¹ := by
      rw [e₂, ← dg_inv]
      group
    have hanti : Antitone (-(a ∘ Fin.rev)) := fun r s hrs =>
      neg_le_neg (ha (Fin.rev_le_rev.mpr hrs))
    have B := side ι ψ lam b μ hK h3 hψ ϖ (-(a ∘ Fin.rev)) (inv_mem hk₄) (inv_mem hk₃)
      (X := nu ι (ψ ϖ) ^ ((∑ i, a i) * -hi)) (zpow_nonneg hp0.le _) (fun m => hmono _ _ (by
        refine le_trans ?_ (h5 m _ hanti)
        rw [← Equiv.sum_comp Fin.revPerm a, Finset.sum_mul]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [h4]
        have := mul_le_mul_of_nonneg_left (hlh r.rev).2 (ha0 r.rev)
        simp only [Fin.revPerm_apply, Pi.neg_apply, Function.comp_apply]
        linarith))
    rw [← hinv] at B
    rw [hM]
    exact mat_bound' ι P _ Q hc (zpow_nonneg hp0.le _) hP hQ B i j
