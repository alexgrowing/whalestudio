import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj {K : Type} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * Mᵀ * Jmat K n) i j = M j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat]
  simp [Fin.rev_eq_iff]
  simp [eq_comm (a := j), Fin.rev_eq_iff]

private theorem ord3 {K : Type} [CommRing K] (α β γ p₀ q₀ p₁ q₁ p₂ q₂ : K) :
    (!![p₀, 0, 0; (p₀ - 1) * α, 1, 0; (p₀ - q₀) * γ - (1 - q₀) * (α * β), (1 - q₀) * β, q₀] -
        p₀ • (1 : Matrix (Fin 3) (Fin 3) K)) *
      ((!![p₁, 0, 0; (p₁ - 1) * α, 1, 0; (p₁ - q₁) * γ - (1 - q₁) * (α * β), (1 - q₁) * β, q₁] -
        (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (!![p₂, 0, 0; (p₂ - 1) * α, 1, 0; (p₂ - q₂) * γ - (1 - q₂) * (α * β), (1 - q₂) * β, q₂] -
        q₂ • (1 : Matrix (Fin 3) (Fin 3) K))) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

private theorem low_pol {K : Type} [CommRing K] (p q y z a : K) :
    !![q, 0, 0; z, 1, 0; a, y, p] = Jmat K 3 * (!![p, 0, 0; y, 1, 0; a, z, q])ᵀ * Jmat K 3 := by
  ext i j
  rw [jconj]
  fin_cases i <;> fin_cases j <;> rfl

private theorem low_mul {K : Type} [CommRing K] (p q y z a p' q' y' z' a' : K) :
    !![p * p', 0, 0; y * p' + y', 1, 0; a * p' + z * y' + q * a', z + q * z', q * q'] =
      !![p, 0, 0; y, 1, 0; a, z, q] * !![p', 0, 0; y', 1, 0; a', z', q'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem low_diag {K : Type} [CommRing K] (p q p' q' y a : K) (i j : Fin 3) (h : i ≠ j) :
    (!![p, 0, 0; y, 1, 0; a, y, q] - !![p', 0, 0; y, 1, 0; a, y, q'] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_up {K : Type} [CommRing K] (p q y z a : K) (i j : Fin 3) (h : i < j) :
    (!![p, 0, 0; y, 1, 0; a, z, q] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

theorem UpperTheory.lowerTriangular_conj_antidiag :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (y a : F.G0 → Q), F.Low Q y a → ∃ ρ : NRep F 3 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧ (∀ g, ρ.r g 1 0 = y g) ∧ ∀ g, ρ.r g 2 0 = a g := by
  intro l _ k _ _ F C₀ hF Q _ _ y a h
  obtain ⟨s1, s2, s3, s4, -⟩ := UpperTheory.V.Fr.star hF
  have y1 : y 1 = 0 := by
    have := h.muly 1 1
    simpa using this
  have st1 : F.star 1 = 1 := by simp [Frame.star]
  have a1 : a 1 = 0 := by
    have := h.mula 1 1
    simpa [y1] using this
  let p : F.G0 → Q := fun g => algebraMap k Q (F.Ψ g : k)
  let q : F.G0 → Q := fun g => algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k)
  have pm : ∀ g g', p (g * g') = p g * p g' := fun g g' => by simp [p]
  have qm : ∀ g g', q (g * g') = q g * q g' := fun g g' => by simp [q, mul_comm]
  have ps : ∀ g, p (F.star g) = q g := fun g => by simp only [p, q, s3]
  have qs : ∀ g, q (F.star g) = p g := fun g => by simp only [p, q, s3, inv_inv]
  have ym : ∀ g g', y (g * g') = y g * p g' + y g' := fun g g' => by
    rw [h.muly, Algebra.smul_def, mul_comm]
  have am : ∀ g g', a (g * g') = a g * p g' + y (F.star g) * y g' + q g * a g' := fun g g' => by
    rw [h.mula, Algebra.smul_def, Algebra.smul_def, mul_comm _ (a g)]
  have zm : ∀ g g', y (F.star (g * g')) = y (F.star g) + q g * y (F.star g') := fun g g' => by
    rw [s2, ym, ps]; ring
  let r : F.G0 →* Matrix (Fin 3) (Fin 3) Q :=
    { toFun := fun g => !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [p, q, y1, a1, st1]
      map_mul' := fun g g' => by
        rw [zm, pm, qm, ym, am, low_mul] }
  have hr : ∀ g, r g = !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g] := fun _ => rfl
  have w0 : w 3 0 = 1 := rfl
  have w1 : w 3 1 = 0 := rfl
  have w2 : w 3 2 = -1 := rfl
  let ψ : ∀ v, Fin 3 → F.Gv v →* Qˣ := fun v i =>
    (Units.map (algebraMap k Q).toMonoidHom).comp ((zpowGroupHom (w 3 i)).comp (F.Ψ.comp (F.loc v)))
  have hψ : ∀ v i g, (ψ v i g : Q) = algebraMap k Q ((F.Ψ (F.loc v g) ^ w 3 i : kˣ) : k) := fun _ _ _ => rfl
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have hc : Continuous fun x : F.G0 => (g : F.Γ)⁻¹ * (x : F.Γ) := by fun_prop
    have : ∀ᶠ x : F.G0 in nhds g, (g : F.Γ)⁻¹ * (x : F.Γ) ∈ (F.Ψ.ker : Set F.Γ) :=
      (hF.Ψ_open.preimage hc).mem_nhds (by simp)
    refine this.mono fun x hx => ?_
    have hx' : F.Ψ ((g : F.Γ)⁻¹ * (x : F.Γ)) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    exact hx'.symm
  have lp : IsLocallyConstant p := hΨ.comp fun u : kˣ => algebraMap k Q (u : k)
  have lq : IsLocallyConstant q := hΨ.comp fun u : kˣ => algebraMap k Q ((u⁻¹ : kˣ) : k)
  have lz : IsLocallyConstant fun g => y (F.star g) := h.lcy.comp_continuous s4
  refine ⟨⟨r, ψ, fun g => ?_, fun i j hij => ?_, fun v g => ?_⟩, ⟨fun g i => ?_, hψ⟩, ?_, fun i j => ?_,
    fun g => rfl, fun g => rfl⟩
  · rw [hr, hr, ps, qs, s1, h.pol, ← low_pol]
  · rw [hr, hr, s1, h.pol, ← h.nor]
    exact low_diag _ _ _ _ _ _ i j hij
  · obtain ⟨α, β, γ, H⟩ := h.loc v
    have e : ∀ s, r (F.loc0 v s) = !![p (F.loc0 v s), 0, 0; (p (F.loc0 v s) - 1) * α, 1, 0;
        (p (F.loc0 v s) - q (F.loc0 v s)) * γ - (1 - q (F.loc0 v s)) * (α * β), (1 - q (F.loc0 v s)) * β,
        q (F.loc0 v s)] := fun s => by
      obtain ⟨h1, h2, h3⟩ := H s
      rw [hr, h1, h2, h3]
      simp only [Algebra.smul_def, map_sub, map_one]
      rfl
    have e0 : ∀ s, (ψ v 0 s : Q) = p (F.loc0 v s) := fun s => by rw [hψ, w0, zpow_one]; rfl
    have e1 : ∀ s, (ψ v 1 s : Q) = 1 := fun s => by rw [hψ, w1, zpow_zero]; simp
    have e2 : ∀ s, (ψ v 2 s : Q) = q (F.loc0 v s) := fun s => by rw [hψ, w2, _root_.zpow_neg_one]; rfl
    have := ord3 α β γ (p (F.loc0 v (g 0))) (q (F.loc0 v (g 0))) (p (F.loc0 v (g 1))) (q (F.loc0 v (g 1)))
      (p (F.loc0 v (g 2))) (q (F.loc0 v (g 2)))
    rw [← e, ← e, ← e] at this
    rw [ordProd, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_cons, List.prod_nil, mul_one]
    show (r _ - (ψ v 0 (g 0) : Q) • 1) * ((r _ - (ψ v 1 (g 1) : Q) • 1) * (r _ - (ψ v 2 (g 2) : Q) • 1)) = 0
    rw [e0, e1, e2]
    exact this
  · show r g i i = _
    rw [hr]
    fin_cases i
    · simp [w0, p]
    · simp [w1]
    · simp [w2, q]
  · refine Ideal.span_eq_bot.2 ?_
    rintro x ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    exact low_up _ _ _ _ _ i j hij
  · show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    exacts [lp, IsLocallyConstant.const 0, IsLocallyConstant.const 0, h.lcy, IsLocallyConstant.const 1,
      IsLocallyConstant.const 0, h.lca, lz, lq]
