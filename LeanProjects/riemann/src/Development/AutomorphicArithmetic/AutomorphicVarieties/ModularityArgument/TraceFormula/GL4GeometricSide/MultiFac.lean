import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrred

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.MF

variable {F : Type} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]

private def Faith (A : Subalgebra ℂ (Module.End ℂ F)) : Prop :=
  ∀ W : Submodule ℂ F, W ≠ ⊥ → (∀ a ∈ A, ∀ x ∈ W, a x ∈ W) → ∀ a ∈ A, (∀ x ∈ W, a x = 0) → a = 0

private def Simp (A : Subalgebra ℂ (Module.End ℂ F)) (W : Submodule ℂ F) : Prop :=
  W ≠ ⊥ ∧ (∀ a ∈ A, ∀ x ∈ W, a x ∈ W) ∧ ∀ W' ≤ W, (∀ a ∈ A, ∀ x ∈ W', a x ∈ W') → W' = ⊥ ∨ W' = W

private theorem exists_simp (A : Subalgebra ℂ (Module.End ℂ F)) (G : Submodule ℂ F) (h0 : G ≠ ⊥)
    (hG : ∀ a ∈ A, ∀ x ∈ G, a x ∈ G) : ∃ W ≤ G, Simp A W := by
  obtain ⟨W, ⟨h1, h2, h3⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ F)).has_min
    {W | W ≤ G ∧ W ≠ ⊥ ∧ ∀ a ∈ A, ∀ x ∈ W, a x ∈ W} ⟨G, le_rfl, h0, hG⟩
  refine ⟨W, h1, h2, h3, fun W' hle hst => ?_⟩
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  · exact Or.inr (by_contra fun hne => hmin W' ⟨hle.trans h1, hb, hst⟩ (lt_of_le_of_ne hle hne))

private theorem exists_equiv {A : Subalgebra ℂ (Module.End ℂ F)} (hA : Faith A) {W : Submodule ℂ F} (hW : Simp A W) :
    ∃ ρ : A ≃ₐ[ℂ] Module.End ℂ W, ∀ a : A, ρ a = a.1.restrict (hW.2.1 a.1 a.2) := by
  let φ : A →ₐ[ℂ] Module.End ℂ W :=
    { toFun := fun a => a.1.restrict (hW.2.1 a.1 a.2)
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun a b => by ext; rfl
      commutes' := fun c => by ext; rfl }
  have hs : Function.Surjective φ := by
    refine GlobalTheory.CompanionTheory.BurnsideU.burnside_surj_of_irred φ fun N hN => ?_
    rcases hW.2.2 (N.map W.subtype) (Submodule.map_subtype_le _ _) (by
      rintro a ha _ ⟨y, hy, rfl⟩
      exact ⟨_, hN ⟨a, ha⟩ y hy, rfl⟩) with h | h
    · left
      exact Submodule.map_injective_of_injective W.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective W.injective_subtype (by rw [h, Submodule.map_subtype_top])
  have hi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine Subtype.ext (hA W hW.1 hW.2.1 a.1 a.2 fun x hx => ?_)
    exact congrArg Subtype.val (LinearMap.congr_fun ha ⟨x, hx⟩)
  exact ⟨AlgEquiv.ofBijective φ ⟨hi, hs⟩, fun a => rfl⟩

private theorem inner_invol {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : Module.End ℂ W ≃ₐ[ℂ] Module.End ℂ W) (hf : ∀ x, f (f x) = x) :
    ∃ t : Module.End ℂ W, t * t = 1 ∧ ∀ x, f x = t * x * t := by
  obtain ⟨T, hT⟩ := f.eq_linearEquivConjAlgEquiv
  have h1 : ∀ x, f x * T.toLinearMap = T.toLinearMap * x := fun x => by
    rw [hT]; ext; simp
  have hc : T.toLinearMap * T.toLinearMap ∈ Subalgebra.center ℂ (Module.End ℂ W) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    conv_lhs => rw [← hf b]
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hc
  obtain ⟨c, hc⟩ := hc
  rw [Algebra.algebraMap_eq_smul_one] at hc
  by_cases hW : Subsingleton W
  · exact ⟨1, Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine hW ⟨fun x y => T.injective (T.injective ?_)⟩
    have h2 := fun z => LinearMap.congr_fun hc z
    simp only [zero_smul, LinearMap.zero_apply, Module.End.mul_apply, LinearEquiv.coe_coe] at h2
    rw [← h2, ← h2]
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self c⁻¹
  have h3 : (d • T.toLinearMap) * (d • T.toLinearMap) = 1 := by
    rw [smul_mul_smul_comm, ← hc, ← hd, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨d • T.toLinearMap, h3, fun x => ?_⟩
  rw [smul_mul_assoc d _ x, ← h1, ← smul_mul_assoc, smul_mul_assoc d, ← mul_smul_comm, mul_assoc, h3, mul_one]

private theorem trace_form {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] :
    ∃ e : Module.End ℂ W, e * e = e ∧ (∀ a, ∃ c : ℂ, e * a * e = c • e) ∧
      ∀ φ : Module.End ℂ W →ₗ[ℂ] ℂ, (∀ a b, φ (a * b) = φ (b * a)) → ∀ a, φ a = LinearMap.trace ℂ W a * φ e := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  refine ⟨l.smulRight v, by ext; simp [hl], fun a => ⟨l (a v), by ext; simp [smul_smul, mul_comm]⟩, fun φ hφ a => ?_⟩
  have h1 : ∀ (f : W →ₗ[ℂ] ℂ) (w : W), φ (f.smulRight w) = LinearMap.trace ℂ W (f.smulRight w) * φ (l.smulRight v) := by
    intro f w
    have e1 : f.smulRight w = l.smulRight w * f.smulRight v := by ext; simp [hl]
    have e2 : f.smulRight v * l.smulRight w = f w • l.smulRight v := by ext; simp [smul_smul, mul_comm]
    rw [LinearMap.trace_smulRight]
    rw [e1, hφ, e2, map_smul, smul_eq_mul]
  let b := Module.finBasis ℂ W
  have h2 : a = ∑ i, (b.coord i).smulRight (a (b i)) := by
    refine b.ext fun j => ?_
    simp [Finsupp.single_apply]
  rw [h2, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => h1 _ _

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {A : Subalgebra ℂ (Module.End ℂ F)} [Nontrivial F] (hA : Faith A) {Θ : Module.End ℂ F}
    (hΘ : Θ * Θ = 1) (hn : ∀ a ∈ A, Θ * a * Θ ∈ A) : ∃ t : A, t * t = 1 ∧ ∀ a : A, Θ * a.1 * Θ = t.1 * a.1 * t.1 := by
  obtain ⟨W, -, hW⟩ := exists_simp A ⊤ top_ne_bot fun _ _ _ _ => trivial
  obtain ⟨ρ, -⟩ := exists_equiv hA hW
  have hΘ' : ∀ z, Θ * (Θ * z) = z := fun z => by rw [← mul_assoc, hΘ, one_mul]
  let φ : A →ₐ[ℂ] A :=
    { toFun := fun a => ⟨Θ * a.1 * Θ, hn _ a.2⟩
      map_one' := Subtype.ext (by simp [hΘ])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc, hΘ'])
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp [mul_add, add_mul])
      commutes' := fun c => Subtype.ext (by simp [Algebra.algebraMap_eq_smul_one, hΘ]) }
  have hφ : ∀ a, φ (φ a) = a := fun a => Subtype.ext (by
    change Θ * (Θ * a.1 * Θ) * Θ = a.1
    simp [mul_assoc, hΘ', hΘ])
  let ψ : A ≃ₐ[ℂ] A := AlgEquiv.ofBijective φ (Function.Involutive.bijective hφ)
  obtain ⟨t, ht, hx⟩ := inner_invol ((ρ.symm.trans ψ).trans ρ) fun x => by
    simp [ψ, hφ]
  refine ⟨ρ.symm t, by rw [← map_mul, ht, map_one], fun a => ?_⟩
  have h1 : φ a = ρ.symm t * a * ρ.symm t := ρ.injective (by simpa [ψ] using hx (ρ a))
  exact congrArg Subtype.val h1

private theorem exists_eig [Nontrivial F] {u : Module.End ℂ F} (hu : u * u = 1) :
    ∃ ε : ℂ, ε * ε = 1 ∧ LinearMap.ker (u - ε • 1) ≠ ⊥ := by
  obtain ⟨ε, hε⟩ := Module.End.exists_eigenvalue u
  obtain ⟨v, hv⟩ := hε.exists_hasEigenvector
  have h1 := hv.apply_eq_smul
  refine ⟨ε, ?_, (Submodule.ne_bot_iff _).2 ⟨v, by simp [h1], hv.2⟩⟩
  have h2 := LinearMap.congr_fun hu v
  rw [Module.End.mul_apply, h1, map_smul, h1, smul_smul, Module.End.one_apply] at h2
  exact smul_left_injective ℂ hv.2 (by simpa using h2)

private theorem loc {A : Subalgebra ℂ (Module.End ℂ F)} [Nontrivial F] (hA : Faith A) {Θ : Module.End ℂ F}
    (hΘ : Θ * Θ = 1) (hn : ∀ a ∈ A, Θ * a * Θ ∈ A) :
    ∃ (W : Submodule ℂ F) (ε : ℂ) (t e : A), Simp A W ∧ ε * ε = 1 ∧ t * t = 1 ∧ (∀ a : A, Θ * a.1 * Θ = t.1 * a.1 * t.1) ∧
      (∀ x ∈ W, Θ x = ε • t.1 x) ∧ e ≠ 0 ∧ e * e = e ∧ (∀ a, ∃ c : ℂ, e * a * e = c • e) ∧
      ∀ c : Module.End ℂ F, (∀ a : A, Commute a.1 c) → ∀ a : A,
        LinearMap.trace ℂ F (a.1 * c) = trOn W a.1 * LinearMap.trace ℂ F (e.1 * c) := by
  obtain ⟨t, ht, hx⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hA hΘ hn
  have ht' : t.1 * t.1 = 1 := congrArg Subtype.val ht
  have hc : ∀ a : A, t.1 * Θ * a.1 = a.1 * (t.1 * Θ) := fun a => by
    calc t.1 * Θ * a.1 = t.1 * (Θ * a.1 * Θ) * Θ := by simp only [mul_assoc, hΘ, mul_one]
      _ = (t.1 * t.1) * a.1 * (t.1 * Θ) := by rw [hx]; simp only [mul_assoc]
      _ = _ := by rw [ht', one_mul]
  have hu : t.1 * Θ * (t.1 * Θ) = 1 := by
    rw [← mul_assoc, hc t, ← mul_assoc, ht', one_mul, hΘ]
  obtain ⟨ε, hε, hk⟩ := exists_eig hu
  have hm : ∀ x, x ∈ LinearMap.ker (t.1 * Θ - ε • 1) ↔ (t.1 * Θ) x = ε • x := fun x => by
    simp [sub_eq_zero]
  obtain ⟨W, hle, hW⟩ := exists_simp A _ hk fun a ha x hx' => by
    rw [hm] at hx' ⊢
    rw [← Module.End.mul_apply, hc ⟨a, ha⟩, Module.End.mul_apply, hx', map_smul]
  obtain ⟨ρ, hρ⟩ := exists_equiv hA hW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW.1
  obtain ⟨e, he, hcor, htr⟩ := trace_form (W := W)
  refine ⟨W, ε, t, ρ.symm e, hW, hε, ht, hx, fun x hx' => ?_, fun h0 => ?_, by rw [← map_mul, he], fun a => ?_,
    fun c hc a => ?_⟩
  · rw [← map_smul, ← (hm x).1 (hle hx'), ← Module.End.mul_apply, ← mul_assoc, ht', one_mul]
  · have h1 := htr (LinearMap.trace ℂ W) (LinearMap.trace_mul_comm ℂ) 1
    rw [(map_eq_zero_iff _ ρ.symm.injective).1 h0, map_zero, mul_zero, LinearMap.trace_one, Nat.cast_eq_zero] at h1
    exact Module.finrank_pos.ne' h1
  · obtain ⟨c, hc⟩ := hcor (ρ a)
    exact ⟨c, ρ.injective (by simpa using hc)⟩
  · have h1 := htr (LinearMap.trace ℂ F ∘ₗ LinearMap.mulRight ℂ c ∘ₗ A.val.toLinearMap ∘ₗ ρ.symm.toLinearMap)
      (fun x y => by
        change LinearMap.trace ℂ F ((ρ.symm (x * y)).1 * c) = LinearMap.trace ℂ F ((ρ.symm (y * x)).1 * c)
        rw [map_mul ρ.symm, map_mul ρ.symm, MulMemClass.coe_mul, MulMemClass.coe_mul, mul_assoc, LinearMap.trace_mul_comm,
          mul_assoc, ← (hc _).eq, mul_assoc]) (ρ a)
    change LinearMap.trace ℂ F ((ρ.symm (ρ a)).1 * c) = _ * LinearMap.trace ℂ F ((ρ.symm e).1 * c) at h1
    rw [AlgEquiv.symm_apply_apply] at h1
    rw [h1, trOn, dif_pos (hW.2.1 a.1 a.2), hρ]

private theorem prod_step {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid X] [Module ℂ X] {N : ι → Type}
    (Φ : (∀ i, N i) → X) (l : ∀ i, N i → ℂ) (e : ∀ i, N i)
    (h : ∀ a i, Φ a = l i (a i) • Φ (Function.update a i (e i))) (a : ∀ i, N i) : Φ a = (∏ i, l i (a i)) • Φ e := by
  have key : ∀ s : Finset ι, Φ a = (∏ i ∈ s, l i (a i)) • Φ (s.piecewise e a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [ih, h _ i, Finset.prod_insert hi, Finset.piecewise_insert, Finset.piecewise_eq_of_notMem _ _ _ hi, smul_smul,
        mul_comm]
  simpa using key Finset.univ

section Glob

variable {ι : Type} [Fintype ι] [DecidableEq ι] {𝔞 : ι → Subalgebra ℂ (Module.End ℂ F)}
  (P : (∀ i, 𝔞 i) →* Module.End ℂ F) (hP : ∀ i (y : 𝔞 i), P (Pi.mulSingle i y) = y.1)

include hP

omit [FiniteDimensional ℂ F] [Fintype ι] in
private theorem P_upd (a : ∀ i, 𝔞 i) (i : ι) (y : 𝔞 i) : P (Function.update a i y) = y.1 * P (Function.update a i 1) := by
  rw [← hP, ← map_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [FiniteDimensional ℂ F] [Fintype ι] in
private theorem P_comm (a : ∀ i, 𝔞 i) (i : ι) (y : 𝔞 i) : Commute y.1 (P (Function.update a i 1)) := by
  rw [← hP]
  refine Commute.map ?_ P
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

private theorem untw [Nontrivial F]
    (hs : ∀ W : Submodule ℂ F, (∀ i, ∀ a ∈ 𝔞 i, ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = ⊤)
    (l : ∀ i, 𝔞 i → ℂ) (e : ∀ i, 𝔞 i) (he : ∀ i, e i * e i = e i) (hcor : ∀ i a, ∃ c : ℂ, e i * a * e i = c • e i)
    (htr : ∀ i (c : Module.End ℂ F), (∀ a : 𝔞 i, Commute a.1 c) → ∀ a : 𝔞 i,
      LinearMap.trace ℂ F (a.1 * c) = l i a * LinearMap.trace ℂ F ((e i).1 * c)) (a : ∀ i, 𝔞 i) :
    LinearMap.trace ℂ F (P a) = ∏ i, l i (a i) := by
  have h1 : ∀ a, LinearMap.trace ℂ F (P a) = (∏ i, l i (a i)) • LinearMap.trace ℂ F (P e) :=
    prod_step (fun a => LinearMap.trace ℂ F (P a)) l e fun a i => by
      rw [P_upd P hP a i (e i), smul_eq_mul, ← htr i _ (P_comm P hP a i), ← P_upd P hP, Function.update_eq_self]
  have hee : e * e = e := funext he
  have hE : P e * P e = P e := by rw [← map_mul, hee]
  have h2 : ∀ a, ∃ c : ℂ, P e * P a * P e = c • P e := fun a => by
    choose c hc using hcor
    refine ⟨∏ i, c i (a i), ?_⟩
    have h3 := prod_step (fun a => P (e * a * e)) c e (fun a i => by
      have e1 : e * a * e = Function.update (e * a * e) i (c i (a i) • e i) := by
        rw [← hc]; exact (Function.update_eq_self i _).symm
      have e2 : e * Function.update a i (e i) * e = Function.update (e * a * e) i (e i) := by
        funext j
        by_cases h : j = i
        · subst h; simp [he]
        · simp [h]
      rw [e2, P_upd P hP _ i (e i), ← smul_mul_assoc, ← Subalgebra.coe_smul, ← P_upd P hP, ← e1]) a
    simpa only [hee, map_mul, hE] using h3
  have h0 : P e ≠ 0 := fun h => by
    have h4 := h1 1
    rw [h, map_zero, smul_zero, map_one, LinearMap.trace_one, Nat.cast_eq_zero] at h4
    exact Module.finrank_pos.ne' h4
  obtain ⟨x, hx⟩ : ∃ x, P e x ≠ 0 := by
    by_contra hcon
    exact h0 (LinearMap.ext fun x => by_contra fun h => hcon ⟨x, h⟩)
  have hspan : Submodule.span ℂ (Set.range fun a => P a (P e x)) = ⊤ := by
    refine (hs _ fun i b hb y hy => ?_).resolve_left fun h => hx ?_
    · refine (Submodule.map_span_le b _ _).2 ?_ ⟨y, hy, rfl⟩
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Pi.mulSingle i ⟨b, hb⟩ * a, by simp [hP]⟩
    · rw [← Submodule.mem_bot ℂ, ← h]
      exact Submodule.subset_span ⟨1, by simp⟩
  have hr : LinearMap.range (P e) = Submodule.span ℂ {P e x} := by
    refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨x, rfl⟩)
    rw [← Submodule.map_top, ← hspan, Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := h2 a
    exact Submodule.mem_span_singleton.2 ⟨c, (LinearMap.congr_fun hc x).symm⟩
  have h5 : LinearMap.trace ℂ F (P e) = 1 := by
    rw [(LinearMap.IsIdempotentElem.isProj_range (P e) hE).trace, hr, finrank_span_singleton hx, Nat.cast_one]
  rw [h1, h5, smul_eq_mul, mul_one]

end Glob

end UpperTheory.V.Z.GSp4Splitting.MF

open UpperTheory.V.Z.GSp4Splitting.MF in
theorem UpperTheory.V.Z.GSp4Splitting.multiFac :
    MultiFac := by
  intro ι _ F _ _ _ _ 𝔞 Θ hc hs hΘ hn
  classical
  have hF : ∀ i, Faith (𝔞 i) := by
    intro i W h0 hW a ha hz
    let K : Submodule ℂ F := ⨅ b : {b // b ∈ 𝔞 i ∧ ∀ x ∈ W, b x = 0}, LinearMap.ker b.1
    have hK : ∀ x, x ∈ K ↔ ∀ b ∈ 𝔞 i, (∀ x ∈ W, b x = 0) → b x = 0 := fun x => by
      simp [K, Submodule.mem_iInf]
    have hT : K = ⊤ := by
      refine (hs K fun j b hb x hx => ?_).resolve_left fun h => h0 (le_bot_iff.1 ?_)
      · rw [hK] at hx ⊢
        intro d hd hdz
        by_cases h : i = j
        · subst h
          exact hx (d * b) (mul_mem hd hb) fun y hy => hdz _ (hW b hb y hy)
        · rw [← Module.End.mul_apply, (hc i j h d hd b hb).eq, Module.End.mul_apply, hx d hd hdz, map_zero]
      · rw [← h]
        exact fun x hx => (hK x).2 fun b _ hb => hb x hx
    exact LinearMap.ext fun x => (hK x).1 (hT ▸ Submodule.mem_top) a ha hz
  choose W ε t e hW hε ht hx hΘW he0 he hcor htr using fun i => loc (hF i) hΘ (hn i)
  let ϕ : ∀ i, 𝔞 i →* Module.End ℂ F := fun i => (𝔞 i).val
  have hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) := fun i j h x y => hc i j h _ x.2 _ y.2
  let P := MonoidHom.noncommPiCoprod ϕ hcomm
  have hP : ∀ i (y : 𝔞 i), P (Pi.mulSingle i y) = y.1 := fun i y => MonoidHom.noncommPiCoprod_mulSingle ϕ i y
  have hL : ∀ a : ∀ i, 𝔞 i, ((Finset.univ : Finset ι).toList.map fun i => (a i).1).prod = P a := fun a => by
    rw [← Finset.noncommProd_toFinset _ _ (fun i _ j _ h => hc i j h _ (a i).2 _ (a j).2) (Finset.nodup_toList _)]
    simp only [P, MonoidHom.noncommPiCoprod_apply, Finset.toList_toFinset]
    rfl
  have hun := untw P hP hs (fun i a => trOn (W i) a.1) e he hcor htr
  have htt : P t * P t = 1 := by rw [← map_mul, show t * t = 1 from funext ht, map_one]
  have hu : ∀ i (b : 𝔞 i), Θ * P t * b.1 = b.1 * (Θ * P t) := fun i b => by
    have h1 : t * Pi.mulSingle i b = Pi.mulSingle i (t i * b * t i) * t := by
      funext j
      by_cases h : j = i
      · subst h; simp [mul_assoc, ht]
      · simp [h]
    calc Θ * P t * b.1 = Θ * P (t * Pi.mulSingle i b) := by rw [map_mul, hP, mul_assoc]
      _ = Θ * (Θ * b.1 * Θ * P t) := by rw [h1, map_mul, hP, hx]; rfl
      _ = _ := by simp only [← mul_assoc, hΘ, one_mul]
  have hΘt : Commute Θ (P t) := by
    have h2 : ∀ i, Commute Θ (t i).1 := fun i => by
      have h3 : (t i).1 * (t i).1 = 1 := congrArg Subtype.val (ht i)
      have h4 := hx i (t i)
      rw [h3, one_mul] at h4
      change Θ * _ = _ * Θ
      conv_rhs => rw [← h4]
      rw [mul_assoc, hΘ, mul_one]
    simp only [P, MonoidHom.noncommPiCoprod_apply]
    exact Finset.noncommProd_commute _ _ _ _ fun i _ => h2 i
  have hsq : Θ * P t * (Θ * P t) = 1 := by
    rw [mul_assoc, ← mul_assoc (P t), ← hΘt.eq, mul_assoc, htt, mul_one, hΘ]
  obtain ⟨s, hs2, hk⟩ := exists_eig hsq
  have hm : ∀ x, x ∈ LinearMap.ker (Θ * P t - s • 1) ↔ (Θ * P t) x = s • x := fun x => by
    simp [sub_eq_zero]
  have hT := (hs _ fun i b hb x hx' => by
    rw [hm] at hx' ⊢
    rw [← Module.End.mul_apply, hu i ⟨b, hb⟩, Module.End.mul_apply, hx', map_smul]).resolve_left hk
  have hΘeq : Θ = s • P t := by
    rw [LinearMap.ker_eq_top, sub_eq_zero] at hT
    rw [← mul_one Θ, ← htt, ← mul_assoc, hT, smul_mul_assoc, one_mul]
  have hst : ∀ i, ∀ x ∈ W i, Θ x ∈ W i := fun i x hx' => by
    rw [hΘW i x hx']
    exact Submodule.smul_mem _ _ ((hW i).2.1 _ (t i).2 x hx')
  refine ⟨W, s * ∏ i, ε i, ?_, fun i => ⟨(hW i).1, (hW i).2.1, hst i, (hW i).2.2⟩, fun a ha => ?_⟩
  · rw [← mul_self_eq_one_iff, mul_mul_mul_comm, hs2, ← Finset.prod_mul_distrib]
    simp [hε]
  · have h1 : ∀ i, trOn (W i) (a i * (t i).1) = ε i * trOn (W i) (a i * Θ) := fun i => by
      have p1 : ∀ x ∈ W i, (a i * (t i).1) x ∈ W i := (hW i).2.1 _ (mul_mem (ha i) (t i).2)
      have p2 : ∀ x ∈ W i, (a i * Θ) x ∈ W i := fun x hx' => (hW i).2.1 _ (ha i) _ (hst i x hx')
      rw [trOn, trOn, dif_pos p1, dif_pos p2, ← smul_eq_mul (ε i), ← map_smul]
      congr 1
      ext x
      simp [hΘW i x.1 x.2, smul_smul, hε]
    rw [hL fun i => ⟨a i, ha i⟩]
    conv_lhs => rw [hΘeq, mul_smul_comm, ← map_mul, map_smul, hun]
    rw [smul_eq_mul, mul_assoc, ← Finset.prod_mul_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => h1 i)
