import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpTanL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFinrankTwoCocyclesCharRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSp4RootVectorUniqueOnWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedHomOfFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Core

variable {H E : Type} [Group H] [Field E]

private theorem mem_sp4_iff {X : M4 E} : X ∈ sp4 E ↔ ∀ a b, (sgn a * sgn b) • X b.rev a.rev = -X a b := by
  show adj X = -X ↔ _
  rw [← Matrix.ext_iff]
  rfl

private theorem hom_iff (χ : Fin 4 → H →* Eˣ) (γ : H → M4 E) :
    (∃ r : H →* M4 (DualNumber E), ∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) ↔
      ∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b := by
  have key : ∀ (r : H → M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → ∀ g h a b,
      (r (g * h) a b = (r g * r h) a b ↔ γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b) := by
    intro r hr g h a b
    have hf : ∀ g a b, (r g a b).fst = if a = b then (χ a g : E) else 0 := fun g a b => by rw [hr]; rfl
    have hs : ∀ g a b, (r g a b).snd = γ g a b * χ b g := fun g a b => by rw [hr]; rfl
    have u1 := Units.ne_zero (χ b g)
    have u2 := Units.ne_zero (χ b h)
    rw [TrivSqZeroExt.ext_iff, Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.fst_sum]
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hf, hs, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, Units.val_mul]
    rw [and_iff_right (by split_ifs with h <;> simp [h])]
    constructor
    · intro e
      field_simp
      apply mul_right_cancel₀ u2
      linear_combination e
    · intro e
      rw [e]
      field_simp
      ring
  refine ⟨fun ⟨r, hr⟩ g h a b => (key r hr g h a b).1 (by rw [map_mul]), fun hz => ?_⟩
  let r : H → M4 (DualNumber E) := fun g => Matrix.of fun a b => ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩
  refine ⟨⟨⟨r, ?_⟩, fun g h => Matrix.ext fun a b => (key r (fun _ _ _ => rfl) g h a b).2 (hz g h a b)⟩,
    fun _ _ _ => rfl⟩
  refine Matrix.ext fun a b => ?_
  have h1 : γ 1 a b = 0 := by simpa using hz 1 1 a b
  refine TrivSqZeroExt.ext ?_ ?_
  · show (if a = b then (χ a 1 : E) else 0) = _
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  · show γ 1 a b * χ b 1 = _
    by_cases h : a = b
    · subst h; simp [h1]
    · simp [h, h1]

private theorem wt_fib : ∀ a b a' b' : Fin 4, a ≠ b → wt a' b' = wt a b →
    (a' = a ∧ b' = b) ∨ (a' = b.rev ∧ b' = a.rev) := by decide

private theorem wt_cases : ∀ j ∈ wts, j = 0 ∨ (∃ a b : Fin 4, a < b ∧ wt a b = j ∧ dimsL j = 2) ∨
    ∃ a b : Fin 4, b < a ∧ wt a b = j ∧ dimsL j = 1 := by decide

private theorem wt_pos_ne : ∀ a b a' b' : Fin 4, a < b → b' ≤ a' → wt a' b' ≠ wt a b := by decide

private theorem dimsL_out (j : ℤ × ℤ) (h : j ∉ wts) : dimsL j = 0 := by
  rw [dimsL, if_neg h, if_neg]
  rintro (rfl | rfl | rfl | rfl | rfl) <;> exact h (by decide)

private theorem sgn_rev : ∀ a b : Fin 4, sgn b.rev * sgn a.rev = sgn a * sgn b := by decide

private theorem sgn_sq : ∀ a b : Fin 4, sgn a * sgn b * (sgn a * sgn b) = 1 := by decide

private theorem ex_root [CharZero E] (a b : Fin 4) :
    ∃ X ∈ sp4 E, X a b ≠ 0 ∧ ∀ a' b', wt a' b' ≠ wt a b → X a' b' = 0 := by
  refine ⟨Matrix.single a b 1 - adj (Matrix.single a b 1), mem_sp4_iff.2 fun i j => ?_, ?_, fun i j h => ?_⟩
  · simp only [Matrix.sub_apply, adj_apply, Fin.rev_rev, sgn_rev, smul_sub, smul_smul, sgn_sq, one_smul, neg_sub]
  · fin_cases a <;> fin_cases b <;> simp [adj_apply, sgn, Fin.rev, Matrix.single_apply] <;> norm_num
  · rw [Matrix.sub_apply, adj_apply, Matrix.single_apply_of_ne, Matrix.single_apply_of_ne, smul_zero, sub_zero]
    · rintro ⟨rfl, rfl⟩
      exact h (wt_rev _ _).symm
    · rintro ⟨rfl, rfl⟩
      exact h rfl

variable [TopologicalSpace H] [TopologicalSpace E] [IsTopologicalRing E]

private def Q (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (j : ℤ × ℤ) (γ : H → M4 E) : Prop :=
  (∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b) ∧ (∀ g, γ g ∈ sp4 E) ∧
    (∃ X ∈ sp4 E, ∀ g a b, b < a → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧ (∀ s, I s → ∀ a, γ s a a = 0) ∧
      (∀ a b, Continuous fun g => γ g a b) ∧ ∀ g a b, wt a b ≠ j → γ g a b = 0

private theorem dim_root [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a b, Continuous fun g => (χ a g : E) / χ b g)
    (a b : Fin 4) (hba : b < a) (g0 : H) (h0 : χ a g0 ≠ χ b g0) (S : Submodule E (H → M4 E))
    (hS : ∀ γ, γ ∈ S ↔ Q χ I (wt a b) γ) : finrank E S = 1 := by
  have hab : a ≠ b := hba.ne'
  have hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g := fun g a b => by
    rw [div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]
  have hw : ∀ a', wt a' a' ≠ wt a b := fun a' h => hab ((wt_eq_zero a b).1 (h.symm.trans ((wt_eq_zero _ _).2 rfl)))
  obtain ⟨X, hX, hX0, hXw⟩ := ex_root (E := E) a b
  let v : H → M4 E := fun g => Matrix.of fun a b => (1 - (χ a g : E) / χ b g) * X a b
  have hv : ∀ g a b, v g a b = (1 - (χ a g : E) / χ b g) * X a b := fun _ _ _ => rfl
  have hvS : v ∈ S := by
    refine (hS v).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_, ⟨X, hX, fun g a b _ => rfl⟩,
      fun s _ a' => ?_, fun a b => ?_, fun g a' b' h => ?_⟩
    · have u1 := Units.ne_zero (χ b g)
      have u2 := Units.ne_zero (χ b h)
      simp only [hv, map_mul, Units.val_mul]
      field_simp
      ring
    · rw [hv, hv, hr, ← mul_smul_comm, mem_sp4_iff.1 hX, mul_neg]
    · rw [hv, hXw _ _ (hw a'), mul_zero]
    · exact (continuous_const.sub (hc a b)).mul continuous_const
    · rw [hv, hXw _ _ h, mul_zero]
  have hk : 1 - (χ a g0 : E) / χ b g0 ≠ 0 := fun h =>
    h0 (Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 (sub_eq_zero.1 h).symm))
  refine (finrank_eq_one_iff_of_nonzero' (⟨v, hvS⟩ : S) fun h => ?_).2 fun ⟨γ, hγ⟩ => ?_
  · have := congrFun (congrFun (congrFun (congrArg Subtype.val h) g0) a) b
    exact mul_ne_zero hk hX0 this
  · obtain ⟨-, h1, ⟨Y, hY, h2⟩, -, -, h3⟩ := (hS γ).1 hγ
    refine ⟨Y a b / X a b, Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)⟩
    show Y a b / X a b * v g a' b' = γ g a' b'
    have e : Y a b / X a b * v g a b = γ g a b := by
      rw [hv, h2 g a b hba]
      field_simp
    by_cases h : wt a' b' = wt a b
    · rcases wt_fib a b a' b' hab h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact e
      · have e1 := mem_sp4_iff.1 (h1 g) b.rev a.rev
        have e2 := mem_sp4_iff.1 (((hS v).1 hvS).2.1 g) b.rev a.rev
        rw [Fin.rev_rev, Fin.rev_rev] at e1 e2
        rw [← neg_inj, ← e1, ← mul_neg, ← e2, ← e, mul_smul_comm]
    · rw [h3 g a' b' h, hv, hXw _ _ h, mul_zero, mul_zero]

private theorem dim_pos [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (a b : Fin 4) (hab : a < b) (T : Submodule E (H → E))
    (hT : ∀ z, z ∈ T ↔ Continuous z ∧ ∀ g h, z (g * h) = z g + (χ a g : E) / χ b g * z h)
    (S : Submodule E (H → M4 E)) (hS : ∀ γ, γ ∈ S ↔ Q χ I (wt a b) γ) : finrank E S = finrank E T := by
  have hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g := fun g a b => by
    rw [div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]
  obtain ⟨X, hX, hX1, hXw, hY⟩ := UpperTheory.exists_sp4_root_vector_unique_on_weight E a b hab.ne
  let f : S →ₗ[E] T :=
    { toFun := fun γ => ⟨fun g => γ.1 g a b, (hT _).2
        ⟨((hS _).1 γ.2).2.2.2.2.1 a b, fun g h => ((hS _).1 γ.2).1 g h a b⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨z, hz⟩ => ?_⟩
    · obtain ⟨-, h2, -, -, -, h5⟩ := (hS γ).1 hγ
      refine Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)
      show γ g a' b' = 0
      have h0 : γ g a b = 0 := congrFun (congrArg Subtype.val h) g
      by_cases e : wt a' b' = wt a b
      · rw [hY _ (h2 g) a' b' e, h0, zero_mul]
      · exact h5 g a' b' e
    · obtain ⟨z1, z2⟩ := (hT z).1 hz
      let γ : H → M4 E := fun g => z g • X
      have hγ : ∀ g a b, γ g a b = z g * X a b := fun _ _ _ => rfl
      refine ⟨⟨γ, (hS γ).2 ⟨fun g h a' b' => ?_, fun g => Submodule.smul_mem _ _ hX,
        ⟨0, zero_mem _, fun g a' b' h => ?_⟩, fun s _ a' => ?_, fun a' b' => z1.mul continuous_const,
        fun g a' b' h => ?_⟩⟩, ?_⟩
      · simp only [hγ]
        by_cases e : wt a' b' = wt a b
        · rcases wt_fib a b a' b' hab.ne e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [z2]; ring
          · rw [z2, hr]; ring
        · simp [hXw _ _ e]
      · rw [hγ, hXw _ _ (wt_pos_ne a b a' b' hab h.le), mul_zero, Matrix.zero_apply, mul_zero]
      · rw [hγ, hXw _ _ (wt_pos_ne a b a' a' hab le_rfl), mul_zero]
      · rw [hγ, hXw _ _ h, mul_zero]
      · exact Subtype.ext (funext fun g => (hγ g a b).trans (by rw [hX1, mul_one]))
  exact (LinearEquiv.ofBijective f hf).finrank_eq

private theorem dim_zero (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (σ : H)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (S : Submodule E (H → M4 E)) (hS : ∀ γ, γ ∈ S ↔ Q χ I 0 γ) : finrank E S = 2 := by
  let f : S →ₗ[E] E × E :=
    { toFun := fun γ => (γ.1 σ 0 0, γ.1 σ 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨x, y⟩ => ?_⟩
    · obtain ⟨h1, h2, -, h3, h4, h5⟩ := (hS γ).1 hγ
      have hd : ∀ a, γ σ a a = 0 → ∀ g, γ g a a = 0 := fun a ha g =>
        congrFun (hun (fun g => γ g a a) (h4 a a) (fun g h => by simpa using h1 g h a a) (fun g hg => h3 g hg a) ha) g
      have d0 := hd 0 (congrArg Prod.fst h)
      have d1 := hd 1 (congrArg Prod.snd h)
      refine Subtype.ext (funext fun g => Matrix.ext fun a b => ?_)
      show γ g a b = 0
      by_cases hab : a = b
      · subst hab
        have e := mem_sp4_iff.1 (h2 g) a a
        fin_cases a
        · exact d0 g
        · exact d1 g
        · exact neg_eq_zero.1 (e.symm.trans ((congrArg _ (d1 g)).trans (smul_zero _)))
        · exact neg_eq_zero.1 (e.symm.trans ((congrArg _ (d0 g)).trans (smul_zero _)))
      · exact h5 g a b fun e => hab ((wt_eq_zero a b).1 e)
    · obtain ⟨u, u1, u2, u3, u4⟩ := hex x
      obtain ⟨w, w1, w2, w3, w4⟩ := hex y
      let γ : H → M4 E := fun g => Matrix.diagonal ![u g, w g, -w g, -u g]
      refine ⟨⟨γ, (hS γ).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_,
        ⟨0, zero_mem _, fun g a b h => by simp [γ, h.ne']⟩, fun s hs a => ?_, fun a b => ?_, fun g a b h => ?_⟩⟩, ?_⟩
      · by_cases hab : a = b
        · subst hab
          fin_cases a <;> simp [γ, u2, w2, add_comm]
        · simp [γ, hab]
      · fin_cases a <;> fin_cases b <;> simp [γ, sgn, Fin.rev, Matrix.diagonal_apply]
      · fin_cases a <;> simp [γ, u3 s hs, w3 s hs]
      · by_cases hab : a = b
        · subst hab
          fin_cases a
          exacts [u1, w1, w1.neg, u1.neg]
        · simp [γ, hab, continuous_const]
      · exact Matrix.diagonal_apply_ne _ fun e => h ((wt_eq_zero a b).2 e)
      · exact Prod.ext u4 w4
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

private theorem dim_core [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E) (σ : H)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a, Continuous fun g => (χ a g : E))
    (hci : ∀ a, Continuous fun g => (χ a g : E)⁻¹) (hne : ∀ a b, a ≠ b → ∃ g, χ a g ≠ χ b g)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (hpos : ∀ a b, a < b → ∃ T : Submodule E (H → E),
      (∀ z, z ∈ T ↔ Continuous z ∧ ∀ g h, z (g * h) = z g + (χ a g : E) / χ b g * z h) ∧ finrank E T = 2)
    (P : (H →* M4 (DualNumber E)) → Prop)
    (hP : ∀ (γ : H → M4 E) (r : H →* M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → (∀ a b, Continuous fun g => γ g a b) →
      (P r ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, b < a → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧
        ∀ s, I s → ∀ a, γ s a a = 0))
    (j : ℤ × ℤ) (S : Submodule E (H → M4 E))
    (hS : ∀ s, s ∈ S ↔ (∃ r : H →* M4 (DualNumber E),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, s g a b⟩) ∧ P r) ∧
        (∀ a b, Continuous fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) : finrank E S = dimsL j := by
  let m : (H → M4 E) ≃ₗ[E] (H → M4 E) :=
    { toFun := fun γ g => Matrix.of fun a b => γ g a b * χ b g
      invFun := fun γ g => Matrix.of fun a b => γ g a b * (χ b g : E)⁻¹
      map_add' := fun x y => funext fun g => Matrix.ext fun a b => add_mul _ _ _
      map_smul' := fun x y => funext fun g => Matrix.ext fun a b => mul_assoc _ _ _
      left_inv := fun x => funext fun g => Matrix.ext fun a b => mul_inv_cancel_right₀ (Units.ne_zero _) _
      right_inv := fun x => funext fun g => Matrix.ext fun a b => inv_mul_cancel_right₀ (Units.ne_zero _) _ }
  have hm : ∀ γ g a b, m γ g a b = γ g a b * χ b g := fun _ _ _ _ => rfl
  have hQ : ∀ γ, γ ∈ S.comap (m : (H → M4 E) →ₗ[E] (H → M4 E)) ↔ Q χ I j γ := fun γ => by
    show m γ ∈ S ↔ _
    rw [hS]
    simp only [hm]
    constructor
    · rintro ⟨⟨r, h1, h2⟩, h3, h4⟩
      have h5 : ∀ a b, Continuous fun g => γ g a b := fun a b =>
        ((h3 a b).mul (hci b)).congr fun g => mul_inv_cancel_right₀ (Units.ne_zero _) _
      obtain ⟨h6, h7, h8⟩ := (hP γ r h1 h5).1 h2
      exact ⟨(hom_iff χ γ).1 ⟨r, h1⟩, h6, h7, h8, h5, fun g a b h =>
        (mul_eq_zero.1 (h4 g a b h)).resolve_right (Units.ne_zero _)⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      obtain ⟨r, hr⟩ := (hom_iff χ γ).2 h1
      exact ⟨⟨r, hr, (hP γ r hr h5).2 ⟨h2, h3, h4⟩⟩, fun a b => (h5 a b).mul (hc b),
        fun g a b h => by rw [h6 g a b h, zero_mul]⟩
  rw [← (m.ofSubmodule' S).finrank_eq]
  by_cases h1 : j ∈ wts
  · rcases wt_cases j h1 with rfl | ⟨a, b, hab, rfl, e⟩ | ⟨a, b, hab, rfl, e⟩
    · exact dim_zero χ I σ hex hun _ hQ
    · obtain ⟨T, hT, h2⟩ := hpos a b hab
      rw [e, ← h2]
      exact dim_pos χ I θ hθ a b hab T hT _ hQ
    · obtain ⟨g, hg⟩ := hne a b hab.ne'
      rw [e]
      exact dim_root χ I θ hθ (fun a b => ((hc a).mul (hci b)).congr fun g => (div_eq_mul_inv _ _).symm)
        a b hab g hg _ hQ
  · rw [dimsL_out j h1]
    refine (congrArg (fun T : Submodule E (H → M4 E) => finrank E T) (eq_bot_iff.2 fun γ hγ => ?_)).trans (finrank_bot _ _)
    exact funext fun g => Matrix.ext fun a b => ((hQ γ).1 hγ).2.2.2.2.2 g a b fun h => h1 (h ▸ wt_mem a b)

end Core

private theorem cont_of_open {H O E : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group O]
    [TopologicalSpace E] (φ : H →* O) (h : IsOpen (φ.ker : Set H)) (f : O → E) : Continuous fun g => f (φ g) := by
  have : IsLocallyConstant φ := (IsLocallyConstant.iff_exists_open _).2 fun x =>
    ⟨(fun y => x⁻¹ * y) ⁻¹' φ.ker, h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => by
      have := MonoidHom.mem_ker.1 hy
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm⟩
  exact (this.comp f).continuous

theorem UpperTheory.tangent_space_deformation_at_l :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (j : ℤ × ℤ) (S : Submodule E (D.Gp l → M4 E)), (∀ s, s ∈ S ↔ (∃ r' : D.Gp l →* M4 (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At l g a b), s g a b⟩) ∧ EqL D r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) → finrank E ↥S = dimsL j := by
  intro hL Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ j S hS
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  haveI : IsGalois ℚ Ω := {}
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  obtain ⟨-, f2, -, -, -, f4, f3, -, -, -, -, -, f5, -⟩ := facts D hD
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hp : l.Prime := Fact.out
  let ι : c.Oˣ →* Eˣ := Units.map (algebraMap c.O E).toMonoidHom
  have hι : Function.Injective ι := Units.map_injective (IsFractionRing.injective c.O E)
  have hdiv : ∀ (x y : c.Oˣ), algebraMap c.O E ((x * y⁻¹ : c.Oˣ) : c.O) = algebraMap c.O E x / algebraMap c.O E y :=
    fun x y => by simp [div_eq_mul_inv]
  let χ : Fin 4 → D.Gp l →* Eˣ := fun a => ι.comp ((D.ps a).comp (D.Gp l).subtype)
  have hχ' : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.Oˣ) := fun _ _ => rfl
  have hr0 : ∀ (g : D.Gp l) a b, algebraMap c.O E (D.r0At l g a b) = if a = b then (χ a g : E) else 0 :=
    fun g a b => by
      show algebraMap c.O E (Matrix.diagonal (fun a => ((D.ps a g : c.Oˣ) : c.O)) a b) = _
      rw [Matrix.diagonal_apply, hχ']
      split_ifs <;> simp
  have hcy : Continuous fun g => algebraMap c.O E (chiO ℚ Ω l c.O g : c.Oˣ) := by
    have h1 : Continuous (algebraMap ℚ_[l] E) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)
    have h2 : Continuous fun g : G ℚ Ω => ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
    refine (h1.comp (continuous_subtype_val.comp h2)).congr fun g => ?_
    show algebraMap ℚ_[l] E (algebraMap ℤ_[l] ℚ_[l] _) = algebraMap c.O E (algebraMap ℤ_[l] c.O _)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hal : Continuous fun g => algebraMap c.O E (D.al g : c.Oˣ) :=
    ((hcy.mul (cont_of_open D.om f5 fun u => algebraMap c.O E (u⁻¹ : c.Oˣ))).mul
      (cont_of_open D.ξ hD.xi_open fun u => algebraMap c.O E u)).congr fun g => by
        simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Pi.mul_apply]
  have hPs : Continuous fun g => algebraMap c.O E (D.Psi g : c.Oˣ) :=
    ((hcy.pow D.e).mul (cont_of_open D.ψ hD.psi_open fun u => algebraMap c.O E u)).congr fun g => by
      simp only [Raw.Psi, UpperTheory.V.Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, map_mul,
        Units.val_pow_eq_pow_val, map_pow, Pi.mul_apply, Pi.pow_apply]
  have hps : ∀ a, Continuous fun g => algebraMap c.O E (D.ps a g : c.Oˣ) := fun a => by
    fin_cases a
    · exact (hal.mul hPs).congr fun g => (map_mul _ _ _).symm
    · exact hPs
    · exact hal
    · exact continuous_const (y := algebraMap c.O E 1)
  have hc : ∀ a, Continuous fun g => (χ a g : E) := fun a => (hps a).comp continuous_subtype_val
  obtain ⟨hex, hun⟩ := UpperTheory.exists_unique_unramified_hom_of_frobenius_value l l hp (D.pl l) (hD.pl_over l hp) ⟨D.sg l, (f2 l hT).1⟩ (hD.sg_frob l hT) E
  refine dim_core χ (fun g => (g : G ℚ Ω) ∈ D.Ip l) (fun g => algebraMap c.O E (D.th g)) ⟨D.sg l, (f2 l hT).1⟩
    (fun g a => ?_) hc (fun a => ?_) (fun a b hab => ?_) hex hun (fun a b hab => ?_) (EqL D)
    (fun γ r hr hγ => ?_) j S
    (fun s => by simpa only [hr0, QCont] using hS s)
  · rw [hχ', hχ', ← map_mul, ← Units.val_mul, mul_comm, ← MonoidHom.mul_apply, f4]
  · exact ((hc a).comp continuous_inv).congr fun g => by simp
  · exact ⟨D.s0, fun e => hab (f3 (congrArg Units.val (hι e)))⟩
  · have key := UpperTheory.exists_finrank_two_cocycles_char_ratio hL D hD E a b hab
    simp only [hdiv] at key
    exact key
  · have key := spTanL D hD E γ r (fun g a b => ?_) hγ
    · simp only [hdiv] at key
      exact key
    · rw [hr, hr0]
      congr 1
      show _ = (γ g * (Matrix.diagonal fun a => ((D.ps a g : c.Oˣ) : c.O)).map (algebraMap c.O E)) a b
      rw [Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, hχ']
