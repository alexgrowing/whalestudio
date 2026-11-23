import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.cocLift (hP : LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B]
    [IsTopologicalRing B]
    {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B']
    [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B']
    (p : B →ₐ[ℚ_[l]] B') (hp : Function.Surjective p) (χ : G →* B) (hχ : Continuous χ)
    (h0 : ∃ g, IsUnit (χ g - algebraMap ℚ_[l] B ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])))
    (f : G → G → B) (hf : Continuous fun q : G × G => f q.1 q.2)
    (hc : ∀ g h k, f g h + f (g * h) k = χ g * f h k + f g (h * k))
    (x' : G → B') (hx' : Continuous x') (hx : ∀ g h, x' (g * h) = x' g + p (χ g) * x' h + p (f g h)) :
    ∃ x : G → B, Continuous x ∧ (∀ g h, x (g * h) = x g + χ g * x h + f g h) ∧ ∀ g, p (x g) = x' g := by
  let J : Submodule ℚ_[l] B := LinearMap.ker p.toLinearMap
  have hJ : ∀ a, a ∈ J ↔ p a = 0 := fun _ => Iff.rfl
  letI : TopologicalSpace J := moduleTopology ℚ_[l] J
  haveI : IsModuleTopology ℚ_[l] J := ⟨rfl⟩
  haveI : ContinuousAdd J := IsModuleTopology.toContinuousAdd ℚ_[l] J
  haveI : IsTopologicalAddGroup J := IsModuleTopology.topologicalAddGroup ℚ_[l] J
  haveI : ContinuousSMul ℚ_[l] J := IsModuleTopology.toContinuousSMul ℚ_[l] J
  have hι : Continuous (fun a : J => (a : B)) := IsModuleTopology.continuous_of_linearMap J.subtype
  obtain ⟨π, hπ⟩ := J.subtype.exists_leftInverse_of_injective J.ker_subtype
  have hπc : Continuous π := IsModuleTopology.continuous_of_linearMap π
  have hπ' : ∀ a : J, π a = a := fun a => LinearMap.congr_fun hπ a
  obtain ⟨s, hs⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  have hsc : Continuous s := IsModuleTopology.continuous_of_linearMap s
  have hs' : ∀ a, p (s a) = a := fun a => LinearMap.congr_fun hs a
  let ρ : Representation ℚ_[l] G J :=
    { toFun := fun g => (LinearMap.mulLeft ℚ_[l] (χ g)).restrict fun a ha => by
        rw [hJ] at ha ⊢
        simp [ha]
      map_one' := by ext a; simp
      map_mul' := fun g h => by ext a; simp [mul_assoc] }
  have hρ : ∀ g (a : J), (ρ g a : B) = χ g * a := fun _ _ => rfl
  have hρc : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    have : (fun q : G × J => ρ q.1 q.2) = fun q => π (χ q.1 * q.2) := funext fun q => by rw [← hρ, hπ']
    rw [this]
    exact hπc.comp ((hχ.comp continuous_fst).mul (hι.comp continuous_snd))
  obtain ⟨-, hfin, -, hd⟩ := tateRat hP (l := l) φ hφ (E := ℚ_[l]) ρ hρc
  have hbot : H0dual ((cycA v l ℚ_[l]).comp φ) ρ = ⊥ := by
    refine eq_bot_iff.2 fun F hF => ?_
    obtain ⟨g, u, hu⟩ := h0
    refine LinearMap.ext fun a => ?_
    let b : J := ⟨(u⁻¹ : Bˣ) * (a : B), by rw [hJ, map_mul, (hJ _).1 a.2, mul_zero]⟩
    have e : a = ρ g b - (((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) • b := by
      apply Subtype.ext
      rw [Submodule.coe_sub, hρ, Submodule.coe_smul, Algebra.smul_def, ← sub_mul, ← hu]
      exact (Units.mul_inv_cancel_left u _).symm
    rw [e, map_sub, hF g b, map_smul]
    exact sub_self _
  rw [hbot, finrank_bot] at hd
  haveI : Subsingleton (H2 ρ) := finrank_zero_iff.1 hd
  let z : G × G → B := fun q => s (x' (q.1 * q.2)) - s (x' q.1) - χ q.1 * s (x' q.2) - f q.1 q.2
  have hzJ : ∀ q, z q ∈ J := fun q => by
    rw [hJ]
    simp only [z, map_sub, map_mul, hs', hx]
    ring
  have hzc : Continuous z := by
    have := hsc.comp hx'
    exact (((this.comp continuous_mul).sub (this.comp continuous_fst)).sub
      ((hχ.comp continuous_fst).mul (this.comp continuous_snd))).sub hf
  let Z : Z2 ρ := ⟨fun q => ⟨z q, hzJ q⟩, by
    have : (fun q => (⟨z q, hzJ q⟩ : J)) = fun q => π (z q) := funext fun q => (hπ' ⟨z q, hzJ q⟩).symm
    rw [this]
    exact hπc.comp hzc, fun g h k => by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, hρ, z, map_mul, mul_assoc, Submodule.coe_zero]
    linear_combination hc g h k⟩
  have hZ : (Submodule.Quotient.mk Z : H2 ρ) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy, hyZ⟩ := (separated_dvr_second_cohomology_mem ρ _).1 (Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 hZ))
  refine ⟨fun g => s (x' g) + y g, (hsc.comp hx').add (hι.comp hy), fun g h => ?_, fun g => ?_⟩
  · have e : χ g * y h - y (g * h) + y g = z (g, h) := congrArg Subtype.val (congrFun hyZ (g, h))
    simp only [z] at e
    linear_combination -e
  · rw [map_add, hs', (hJ _).1 (y g).2, add_zero]

namespace UpperTheory.V.Loc.SpBor

open UpperTheory.V.GradeZeroInterpolatingElement Matrix

variable {B B' : Type} [CommRing B] [CommRing B']

private def bor (α β u a b c d : B) : M4 B :=
  !![α * α * β * u, a * (α * β * u), c * (α * u), d * u;
     0, α * β * u, b * (α * u), (c - a * b) * u;
     0, 0, α * u, -a * u;
     0, 0, 0, u]

private theorem bor_mul (α β u a b c d α' β' u' a' b' c' d' : B) :
    bor α β u a b c d * bor α' β' u' a' b' c' d' =
      bor (α * α') (β * β') (u * u') (a + α * a') (b + β * b') (c + α * β * c' + a * β * b')
        (d + α * α * β * d' + (a * α * β * (c' - a' * b') - c * α * a')) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bor, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem bor_one : bor (1 : B) 1 1 0 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bor]

private theorem bor_gsp (α β u a b c d : B) : IsGSp (α * α * β * u * u) (bor α β u a b c d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bor, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] <;> ring

private theorem bor_map (p : B →+* B') (α β u a b c d : B) :
    (bor α β u a b c d).map p = bor (p α) (p β) (p u) (p a) (p b) (p c) (p d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bor]

private theorem bor_inj {α β u a b c d a' b' c' d' : B} (hα : IsUnit α) (hβ : IsUnit β) (hu : IsUnit u)
    (h : bor α β u a b c d = bor α β u a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  ⟨((hα.mul hβ).mul hu).mul_right_cancel (congrFun (congrFun h 0) 1),
    (hα.mul hu).mul_right_cancel (congrFun (congrFun h 1) 2),
    (hα.mul hu).mul_right_cancel (congrFun (congrFun h 0) 2), hu.mul_right_cancel (congrFun (congrFun h 0) 3)⟩

private theorem bor_of {α β u α' β' u' ν : B} (hα : α * α' = 1) (hβ : β * β' = 1) (hu : u * u' = 1) (T : M4 B)
    (hl : ∀ i j, j < i → T i j = 0) (h0 : T 0 0 = α * α * β * u) (h1 : T 1 1 = α * β * u) (h2 : T 2 2 = α * u)
    (h3 : T 3 3 = u) (hT : IsGSp ν T) :
    T = bor α β u (T 0 1 * (α' * β' * u')) (T 1 2 * (α' * u')) (T 0 2 * (α' * u')) (T 0 3 * u') := by
  have e1 := congrFun (congrFun hT 0) 1
  have e2 := congrFun (congrFun hT 0) 2
  have l10 := hl 1 0 (by decide)
  have l20 := hl 2 0 (by decide)
  have l30 := hl 3 0 (by decide)
  have l21 := hl 2 1 (by decide)
  have l31 := hl 3 1 (by decide)
  have l32 := hl 3 2 (by decide)
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, l21, l31, l32, h1, h2, h3] at e1 e2
  have k1 : α' * β' * u' * (α * β * u) = 1 := by linear_combination (β * β' * u * u') * hα + (u * u') * hβ + hu
  have k2 : α' * u' * (α * u) = 1 := by linear_combination (u * u') * hα + hu
  have f1 : T 2 3 = -(T 0 1 * (α' * β' * u')) * u := by
    linear_combination (α' * β' * u') * e1 - T 2 3 * k1
  have f2 : T 1 3 = (T 0 2 * (α' * u') - T 0 1 * (α' * β' * u') * (T 1 2 * (α' * u'))) * u := by
    rw [f1] at e2
    linear_combination (-(α' * u')) * e2 - T 1 3 * k2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bor, l10, l20, l30, l21, l31, l32, h0, h1, h2, h3, f1, f2]
  · rw [mul_assoc, k1, mul_one]
  · rw [mul_assoc, k2, mul_one]
  · rw [mul_assoc, mul_comm u', hu, mul_one]
  · rw [mul_assoc, k2, mul_one]

private theorem bor_cont {X : Type} [TopologicalSpace X] [TopologicalSpace B] [IsTopologicalRing B]
    {α β u a b c d : X → B} (hα : Continuous α) (hβ : Continuous β) (hu : Continuous u) (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) (i j : Fin 4) :
    Continuous fun x => bor (α x) (β x) (u x) (a x) (b x) (c x) (d x) i j := by
  fin_cases i <;> fin_cases j <;> simp [bor] <;> fun_prop

end UpperTheory.V.Loc.SpBor

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Loc.SpBor in

theorem UpperTheory.V.Loc.borLift (hP : LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B]
    [IsTopologicalRing B]
    {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B']
    [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B']
    (p : B →ₐ[ℚ_[l]] B') (hp : Function.Surjective p) (α β u : G →* B) (hα : Continuous α) (hβ : Continuous β)
    (hu : Continuous u)
    (h0 : ∀ χ ∈ [α, β, α * β, α * α * β], ∃ g, IsUnit (χ g - algebraMap ℚ_[l] B ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])))
    (T' : G →* M4 B') (hT : ∀ i j, Continuous fun g => T' g i j) (hl : ∀ g i j, j < i → T' g i j = 0)
    (hd : ∀ g i, T' g i i = p (![α g * α g * β g * u g, α g * β g * u g, α g * u g, u g] i))
    (hG : ∀ g, ∃ ν, IsGSp ν (T' g)) :
    ∃ T : G →* M4 B, (∀ i j, Continuous fun g => T g i j) ∧ (∀ g i j, j < i → T g i j = 0) ∧
      (∀ g i, T g i i = ![α g * α g * β g * u g, α g * β g * u g, α g * u g, u g] i) ∧
      (∀ g, IsGSp (α g * α g * β g * u g * u g) (T g)) ∧ ∀ g, (T g).map p = T' g := by
  have hpc : Continuous p := IsModuleTopology.continuous_of_linearMap p.toLinearMap
  have hi : ∀ (χ : G →* B) g, p (χ g) * p (χ g⁻¹) = 1 := fun χ g => by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hun : ∀ (χ : G →* B) g, IsUnit (p (χ g)) := fun χ g => IsUnit.of_mul_eq_one _ (hi χ g)
  obtain ⟨a', b', c', d', ha', hb', hc', hd', hT'⟩ : ∃ a' b' c' d' : G → B', Continuous a' ∧ Continuous b' ∧
      Continuous c' ∧ Continuous d' ∧ ∀ g, T' g = bor (p (α g)) (p (β g)) (p (u g)) (a' g) (b' g) (c' g) (d' g) := by
    have c1 : Continuous fun g => p (α g⁻¹) := hpc.comp (hα.comp continuous_inv)
    have c2 : Continuous fun g => p (β g⁻¹) := hpc.comp (hβ.comp continuous_inv)
    have c3 : Continuous fun g => p (u g⁻¹) := hpc.comp (hu.comp continuous_inv)
    refine ⟨_, _, _, _, (hT 0 1).mul ((c1.mul c2).mul c3), (hT 1 2).mul (c1.mul c3), (hT 0 2).mul (c1.mul c3),
      (hT 0 3).mul c3, fun g => ?_⟩
    obtain ⟨ν, hν⟩ := hG g
    exact bor_of (hi α g) (hi β g) (hi u g) (T' g) (hl g) (by simpa using hd g 0) (by simpa using hd g 1)
      (by simpa using hd g 2) (by simpa using hd g 3) hν
  have key := fun g h => by
    have e := (hT' (g * h)).symm
    rw [map_mul T', hT' g, hT' h, bor_mul, ← map_mul p, ← map_mul p, ← map_mul p, ← map_mul α, ← map_mul β,
      ← map_mul u] at e
    exact bor_inj (hun α (g * h)) (hun β (g * h)) (hun u (g * h)) e
  obtain ⟨a, ha, ea, pa⟩ := cocLift hP φ hφ p hp α hα (h0 _ (by simp)) (fun _ _ => 0) continuous_const (by simp)
    a' ha' fun g h => by rw [(key g h).1, map_zero, add_zero]
  obtain ⟨b, hb, eb, pb⟩ := cocLift hP φ hφ p hp β hβ (h0 _ (by simp)) (fun _ _ => 0) continuous_const (by simp)
    b' hb' fun g h => by rw [(key g h).2.1, map_zero, add_zero]
  obtain ⟨c, hc, ec, pc⟩ := cocLift hP φ hφ p hp (α * β) (hα.mul hβ) (h0 _ (by simp)) (fun g h => a g * β g * b h)
    (by fun_prop) (fun g h k => by simp only [ea, eb, map_mul, MonoidHom.mul_apply]; ring)
    c' hc' fun g h => by simp only [(key g h).2.2.1, map_mul, MonoidHom.mul_apply, pa, pb]
  obtain ⟨d, hd, ed, pd⟩ := cocLift hP φ hφ p hp (α * α * β) ((hα.mul hα).mul hβ) (h0 _ (by simp))
    (fun g h => a g * α g * β g * (c h - a h * b h) - c g * α g * a h)
    (by fun_prop) (fun g h k => by simp only [ea, eb, ec, map_mul, MonoidHom.mul_apply]; ring)
    d' hd' fun g h => by simp only [(key g h).2.2.2, map_mul, map_sub, MonoidHom.mul_apply, pa, pb, pc]
  have a1 : a 1 = 0 := by simpa using ea 1 1
  have b1 : b 1 = 0 := by simpa using eb 1 1
  have c1 : c 1 = 0 := by simpa [a1] using ec 1 1
  have d1 : d 1 = 0 := by simpa [a1, c1] using ed 1 1
  refine ⟨{ toFun := fun g => bor (α g) (β g) (u g) (a g) (b g) (c g) (d g)
            map_one' := by rw [a1, b1, c1, d1, map_one, map_one, map_one, bor_one]
            map_mul' := fun g h => by
              simp only [bor_mul, ea, eb, ec, ed, map_mul, MonoidHom.mul_apply, add_zero] },
    bor_cont hα hβ hu ha hb hc hd, fun g i j h => ?_, fun g i => ?_, fun g => bor_gsp _ _ _ _ _ _ _, fun g => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  · fin_cases i <;> rfl
  · rw [hT', ← pa, ← pb, ← pc, ← pd]
    exact bor_map (p : B →+* B') _ _ _ _ _ _ _
