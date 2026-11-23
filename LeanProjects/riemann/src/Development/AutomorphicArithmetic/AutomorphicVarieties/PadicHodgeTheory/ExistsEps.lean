import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdDual
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial
open UpperTheory.V.Loc.OrdinaryDeformation TrivSqZeroExt

section Fibre

variable {E B : Type} [Field E] [CommRing B] [Algebra E B] (π : B →ₐ[E] E)

private noncomputable def fib : Subalgebra E (B × DualNumber E) :=
  AlgHom.equalizer (π.comp (AlgHom.fst E B _)) ((fstHom E E E).comp (AlgHom.snd E B _))

private noncomputable def p1 : fib π →ₐ[E] B := (AlgHom.fst E B _).comp (fib π).val

private noncomputable def p2 : fib π →ₐ[E] DualNumber E := (AlgHom.snd E B _).comp (fib π).val

private noncomputable def p3 (ε : B) (h0 : π ε = 0) (hε : ∀ b, b * ε = π b • ε) : fib π →ₐ[E] B where
  toFun c := c.1.1 + c.1.2.snd • ε
  map_one' := by simp
  map_zero' := by simp
  map_add' c c' := by
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add, snd_add, add_smul]
    abel
  map_mul' c c' := by
    have h : π c.1.1 = c.1.2.fst := c.2
    have h' : π c'.1.1 = c'.1.2.fst := c'.2
    simp only [Subalgebra.coe_mul, Prod.fst_mul, Prod.snd_mul, DualNumber.snd_mul, add_mul, mul_add, mul_smul_comm,
      smul_mul_assoc, mul_comm ε c'.1.1, hε, h, h', h0, smul_smul, add_smul, mul_zero, zero_smul, add_zero]
    rw [map_add, map_smul, h0, smul_zero, add_zero, h, mul_comm c'.1.2.snd, mul_comm c.1.2.snd]
    abel
  commutes' a := by simp [algebraMap_eq_inl]

private theorem exists_eps [IsNoetherianRing B] (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : B) (hx : π x = 0)
    (hx0 : x ≠ 0) : ∃ ε : B, ε ≠ 0 ∧ π ε = 0 ∧ ∀ b, b * ε = π b • ε := by
  classical
  have hn : ∃ k, RingHom.ker π ^ (k + 1) = ⊥ := by
    obtain ⟨k, hk⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (RingHom.ker π))).2
      fun a ha => hπ a ha
    exact ⟨k, by rw [pow_succ, hk]; simp⟩
  have h1 := Nat.find_spec hn
  have h2 : Nat.find hn ≠ 0 := fun h => by
    rw [h, zero_add, pow_one] at h1
    exact hx0 (Ideal.mem_bot.1 (h1 ▸ (hx : x ∈ RingHom.ker π)))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h2
  obtain ⟨ε, h3, h4⟩ := (Submodule.ne_bot_iff _).1 (Nat.find_min hn (hk ▸ Nat.lt_succ_self k))
  refine ⟨ε, h4, Ideal.pow_le_self k.succ_ne_zero h3, fun b => ?_⟩
  have h5 : ε * (b - algebraMap E B (π b)) ∈ RingHom.ker π ^ (k + 1 + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul h3 (by simp [RingHom.mem_ker])
  rw [hk] at h1
  rw [h1, Ideal.mem_bot] at h5
  rw [Algebra.smul_def]
  linear_combination h5

end Fibre

theorem UpperTheory.V.Loc.ordEq :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG 3 B), D.InDcr (π : B →+* E) r ↔ D.InDord (π : B →+* E) r := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r
  refine ⟨fun hr => ?_, dcr_of_dord⟩
  induction hn : finrank ℚ_[l] B using Nat.strong_induction_on generalizing B with
  | _ N ih =>
  by_cases hinj : ∀ x, π x = 0 → x = 0
  · refine ⟨r, 1, ⟨hr, fun g a b h => hinj _ ?_⟩, (congOne_iff _ _).2 (map_one _), fun a b _ => by simp,
      (conjBy_one r).symm⟩
    have hab : a ≠ b := by
      rintro rfl
      simp [wt] at h
    change (((GG.map (π : B →+* E)).comp r) g).mat a b = 0
    rw [hr.red, rz_eq, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab]
  push Not at hinj
  obtain ⟨x, hx, hx0⟩ := hinj
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite ℚ_[l] B
  obtain ⟨ε, hε0, h0, hε⟩ := exists_eps π hπ x hx hx0
  let I : Ideal B := Ideal.span {ε}
  let q : B →ₐ[E] B ⧸ I := Ideal.Quotient.mkₐ E I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective E I
  let π' : (B ⧸ I) →ₐ[E] E := Ideal.Quotient.liftₐ I π fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  have hπq : π'.comp q = π := AlgHom.ext fun _ => rfl
  have hπ' : ∀ a, π' a = 0 → IsNilpotent a := fun a ha => by
    obtain ⟨b, rfl⟩ := hq a
    exact (hπ b ha).map q
  have hlt : finrank ℚ_[l] (B ⧸ I) < N := by
    rw [← hn, ← (q.restrictScalars ℚ_[l]).toLinearMap.finrank_range_add_finrank_ker,
      LinearMap.range_eq_top.2 hq, finrank_top]
    refine Nat.lt_add_of_pos_right (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨ε, ?_⟩, fun h => hε0 (congrArg Subtype.val h)⟩)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hr' := dcr_map (q.restrictScalars ℚ_[l]) hq (π' := (π' : (B ⧸ I) →+* E)) (RingHom.ext fun _ => rfl) hr
  obtain ⟨u', n', hu', hn1', hn2', e'⟩ := ih _ hlt (B ⧸ I) π' hπ' _ hr' rfl
  obtain ⟨u₁, hu₁, rfl⟩ := triLift hP D E B π hπ (B ⧸ I) π' hπ' q hq hπq u' hu'
  obtain ⟨n₁, hn₁, rfl⟩ := lift_lower (q : B →+* B ⧸ I) hq n' hn2'
  have hc₁ : Matrix.GeneralLinearGroup.map (π : B →+* E) n₁ = 1 := ((congOne_iff _ _).1 hn1' :)
  have hr₁ := dcr_conj hu₁.toInDcrAt n₁ hc₁
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  haveI : Module.Finite ℚ_[l] (fib π) :=
    Module.Finite.of_injective ((fib π).val.restrictScalars ℚ_[l]).toLinearMap Subtype.val_injective
  let f₁ : fib π →ₐ[ℚ_[l]] B := (p1 π).restrictScalars ℚ_[l]
  let f₂ : fib π →ₐ[ℚ_[l]] DualNumber E := (p2 π).restrictScalars ℚ_[l]
  let f₃ : fib π →ₐ[ℚ_[l]] B := (p3 π ε h0 hε).restrictScalars ℚ_[l]
  have i12 : ∀ c c', f₁ c = f₁ c' → f₂ c = f₂ c' → c = c' := fun c c' h h' => Subtype.ext (Prod.ext h h')
  have i13 : ∀ c c', f₁ c = f₁ c' → f₃ c = f₃ c' → c = c' := fun c c' h h' => by
    have h1 : c.1.1 = c'.1.1 := h
    have h2 : c.1.1 + c.1.2.snd • ε = c'.1.1 + c'.1.2.snd • ε := h'
    have h3 : π c.1.1 = c.1.2.fst := c.2
    have h4 : π c'.1.1 = c'.1.2.fst := c'.2
    rw [h1, add_right_inj] at h2
    exact i12 c c' h (TrivSqZeroExt.ext (by rw [h1, h4] at h3; exact h3.symm) (smul_left_injective E hε0 h2))
  have g12 : ∀ (s : B) (t : DualNumber E), π s = t.fst → ∃ c, f₁ c = s ∧ f₂ c = t := fun s t h => ⟨⟨(s, t), h⟩, rfl, rfl⟩
  have g13 : ∀ s t : B, q s = q t → ∃ c, f₁ c = s ∧ f₃ c = t := fun s t h => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h.symm)
    refine ⟨⟨(s, (π s, π c)), rfl⟩, rfl, ?_⟩
    change s + π c • ε = t
    rw [← hε, hc, add_sub_cancel]
  have s2 : Function.Surjective f₂ := fun t => (g12 (algebraMap E B t.fst) t (π.commutes _)).imp fun _ h => h.2
  have s3 : Function.Surjective f₃ := fun t => (g13 t t rfl).imp fun _ h => h.2
  have k2 : (fstHom E E E : DualNumber E →+* E).comp (f₂ : fib π →+* DualNumber E) =
      (π : B →+* E).comp (f₁ : fib π →+* B) := RingHom.ext fun c => Eq.symm c.2
  have k3 : (π : B →+* E).comp (f₃ : fib π →+* B) = (π : B →+* E).comp (f₁ : fib π →+* B) := RingHom.ext fun c => by
    change π (c.1.1 + c.1.2.snd • ε) = π c.1.1
    rw [map_add, map_smul, h0, smul_zero, add_zero]
  obtain ⟨R, hR1, hR3⟩ := glue_hom (f₁ : fib π →+* B) (f₃ : fib π →+* B) (q : B →+* B ⧸ I) (q : B →+* B ⧸ I) i13 g13
    (conjBy n₁ u₁) r ((map_conjBy _ _ _).trans e'.symm)
  have hR := dcr_pair f₁ f₃ i13 (hR1 ▸ hr₁) (hR3 ▸ hr)
  obtain ⟨u₂, n₂, hu₂, hn₂, hn₂', e₂⟩ := dual_ord hP D E _ (dcr_map f₂ s2 k2 hR)
  obtain ⟨u, hu1, hu2⟩ := glue_hom (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) (π : B →+* E)
    (fstHom E E E : DualNumber E →+* E) i12 g12 u₁ u₂ (hu₁.red.trans hu₂.red.symm)
  obtain ⟨n, hn1, hn2⟩ := glue_GL (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) (π : B →+* E)
    (fstHom E E E : DualNumber E →+* E) i12 g12 n₁ n₂ (hc₁.trans ((congOne_iff _ _).1 hn₂).symm)
  subst hu1 hu2 hn1 hn2
  rw [← hR3]
  refine dord_map f₃ s3 k3 ⟨u, n, ⟨dcr_pair f₁ f₂ i12 hu₁.toInDcrAt hu₂.toInDcrAt, fun g a b h => ?_⟩,
    (congOne_iff _ _).2 hc₁, fun a b h => ?_, MonoidHom.ext fun g => ?_⟩
  · exact i12 _ _ ((hu₁.tri g a b h).trans (map_zero _).symm) ((hu₂.tri g a b h).trans (map_zero _).symm)
  · exact i12 _ _ (((map_sub_one _ n a b).symm.trans (hn₁ a b h)).trans (map_zero _).symm)
      (((map_sub_one _ n a b).symm.trans (hn₂' a b h)).trans (map_zero _).symm)
  · exact gg_ext (f₁ : fib π →+* B) (f₂ : fib π →+* DualNumber E) i12
      (DFunLike.congr_fun (hR1.trans (map_conjBy _ n u).symm) g) (DFunLike.congr_fun (e₂.trans (map_conjBy _ n u).symm) g)
