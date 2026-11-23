import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_of_univ {R F W : Type} [AddCommGroup R] [Field F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (π : R →+ W) (T : Submodule F (R →+ F))
    (h1 : ∀ φ : Module.Dual F W, φ.toAddMonoidHom.comp π ∈ T)
    (h2 : ∀ α ∈ T, ∃ φ : Module.Dual F W, φ.toAddMonoidHom.comp π = α) :
    Module.Finite F T ∧ (∀ b, (∀ α ∈ T, α b = 0) → π b = 0) ∧
      ∀ ξ : Module.Dual F T, ∃ w : W, ∀ b, π b = w → ∀ α : T, (α : R →+ F) b = ξ α := by
  let Φ : Module.Dual F W →ₗ[F] T :=
    { toFun := fun φ => ⟨φ.toAddMonoidHom.comp π, h1 φ⟩
      map_add' := fun _ _ => Subtype.ext (by ext; simp)
      map_smul' := fun _ _ => Subtype.ext (by ext; simp) }
  have hΦ : Function.Surjective Φ := fun α => by
    obtain ⟨φ, e⟩ := h2 α.1 α.2
    exact ⟨φ, Subtype.ext e⟩
  refine ⟨Module.Finite.of_surjective Φ hΦ, fun b hb => ?_, fun ξ => ?_⟩
  · exact (Module.forall_dual_apply_eq_zero_iff F (π b)).1 fun φ => hb _ (h1 φ)
  · obtain ⟨w, hw⟩ := (Module.evalEquiv F W).surjective (ξ.comp Φ)
    refine ⟨w, fun b hb α => ?_⟩
    obtain ⟨φ, rfl⟩ := hΦ α
    have := LinearMap.congr_fun hw φ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    rw [← this, ← hb]
    rfl

private theorem tp_abs {O R F : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field F] [Algebra O R] [IsLocalHom (algebraMap O R)] (r : R →+* F) (hk : RingHom.ker r = maximalIdeal R)
    (hs : Function.Surjective (r.comp (algebraMap O R))) (I J : Ideal R)
    (hJ : J = (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ⊔ I) (hI : I ≤ maximalIdeal R)
    (hJm : J ≤ maximalIdeal R) (T : Submodule F (R →+ F))
    (hT : ∀ α, α ∈ T ↔ (∀ b b', α (b * b') = r b * α b' + r b' * α b) ∧ (∀ o, α (algebraMap O R o) = 0) ∧
      ∀ b ∈ I, α b = 0) :
    Module.Finite F T ∧ (∀ b ∈ maximalIdeal R, (∀ α ∈ T, α b = 0) → b ∈ J) ∧
      ∀ ξ : Module.Dual F T, ∃ b ∈ maximalIdeal R, ∀ α : T, (α : R →+ F) b = ξ α := by
  have hm : ∀ b, b ∈ maximalIdeal R ↔ r b = 0 := fun b => by rw [← hk, RingHom.mem_ker]
  have hO : ∀ o : O, algebraMap O R o ∈ maximalIdeal R → algebraMap O R o ∈ J := fun o ho => by
    rw [hJ]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_))
    exact fun hu => ho (hu.map _)
  have hsq : ∀ x ∈ maximalIdeal R, ∀ y ∈ maximalIdeal R, x * y ∈ J := fun x hx y hy => by
    rw [hJ, pow_two]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mul_mem_mul hx hy))
  have hdec : ∀ b : R, ∃ o : O, ∃ x ∈ maximalIdeal R, b = algebraMap O R o + x := fun b => by
    obtain ⟨o, ho⟩ := hs (r b)
    refine ⟨o, b - algebraMap O R o, (hm _).2 ?_, by ring⟩
    rw [map_sub, ← ho]; simp
  let N : Submodule O R := J.restrictScalars O ⊔ 1
  have hNJ : ∀ b ∈ J, N.mkQ b = 0 := fun b hb =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left hb)
  have hNO : ∀ o : O, N.mkQ (algebraMap O R o) = 0 := fun o =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right (Submodule.mem_one.2 ⟨o, rfl⟩))
  have hkill : ∀ o : O, r (algebraMap O R o) = 0 → ∀ w : R ⧸ N, o • w = 0 := fun o ho w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [← map_smul, Algebra.smul_def]
    exact hNJ _ (J.mul_mem_right _ (hO o ((hm _).2 ho)))
  letI : SMul F (R ⧸ N) := ⟨fun c w => Function.surjInv hs c • w⟩
  have hsm : ∀ (o : O) (w : R ⧸ N), (r.comp (algebraMap O R)) o • w = o • w := fun o w => by
    show Function.surjInv hs _ • w = o • w
    rw [← sub_eq_zero, ← sub_smul]
    refine hkill _ ?_ w
    have := Function.surjInv_eq hs ((r.comp (algebraMap O R)) o)
    rw [map_sub, map_sub, sub_eq_zero]
    exact this
  letI : Module F (R ⧸ N) := Function.Surjective.moduleLeft (r.comp (algebraMap O R)) hs hsm
  have hder : ∀ b b' : R, N.mkQ (b * b') = r b • N.mkQ b' + r b' • N.mkQ b := fun b b' => by
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    obtain ⟨o', x', hx', rfl⟩ := hdec b'
    have e : (algebraMap O R o + x) * (algebraMap O R o' + x') =
        algebraMap O R (o * o') + (o • x' + o' • x) + x * x' := by
      simp only [Algebra.smul_def, map_mul]; ring
    have e1 : r (algebraMap O R o + x) = (r.comp (algebraMap O R)) o := by
      rw [map_add, (hm x).1 hx, add_zero]; rfl
    have e2 : r (algebraMap O R o' + x') = (r.comp (algebraMap O R)) o' := by
      rw [map_add, (hm x').1 hx', add_zero]; rfl
    rw [e, e1, e2, hsm, hsm]
    simp only [map_add, hNO, hNJ _ (hsq x hx x' hx'), map_smul, zero_add, add_zero]
  have hsurj : ∀ w : R ⧸ N, ∃ b ∈ maximalIdeal R, N.mkQ b = w := fun w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    exact ⟨x, hx, by rw [map_add, hNO, zero_add]⟩
  haveI : Module.Finite F (R ⧸ N) := by
    obtain ⟨s, hs'⟩ := IsNoetherian.noetherian (maximalIdeal R)
    refine ⟨Submodule.fg_def.2 ⟨N.mkQ '' s, s.finite_toSet.image _, eq_top_iff.2 fun w _ => ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := hsurj w
    rw [← hs'] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | smul c x hx ih =>
      rw [hs'] at hx
      rw [smul_eq_mul, hder, (hm x).1 hx, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (ih trivial)
  obtain ⟨f1, f2, f3⟩ := dual_of_univ (F := F) N.mkQ.toAddMonoidHom T (fun φ => (hT _).2 ⟨fun b b' => by
      show φ (N.mkQ (b * b')) = r b * φ (N.mkQ b') + r b' * φ (N.mkQ b)
      rw [hder, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul], fun o => by
      show φ (N.mkQ _) = 0
      rw [hNO, map_zero], fun b hb => by
      show φ (N.mkQ _) = 0
      rw [hNJ b (by rw [hJ]; exact Ideal.mem_sup_right hb), map_zero]⟩) (fun α hα => by
    obtain ⟨a1, a2, a3⟩ := (hT α).1 hα
    let K : Ideal R :=
      { carrier := {b | r b = 0 ∧ α b = 0}
        add_mem' := fun {x y} hx hy => ⟨by rw [map_add, hx.1, hy.1, add_zero], by rw [map_add, hx.2, hy.2, add_zero]⟩
        zero_mem' := ⟨map_zero _, map_zero _⟩
        smul_mem' := fun c x hx => ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero],
          by rw [smul_eq_mul, a1, hx.1, hx.2]; ring⟩ }
    have hK : J ≤ K := by
      rw [hJ]
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 fun o ho => ⟨(hm _).1 (hJm ?_), a2 o⟩) ?_)
        fun b hb => ⟨(hm _).1 (hI hb), a3 b hb⟩
      · rw [hJ]; exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))
      · rw [pow_two]
        refine Ideal.mul_le.2 fun x hx y hy => ⟨?_, ?_⟩
        · rw [map_mul, (hm x).1 hx, zero_mul]
        · rw [a1, (hm x).1 hx, (hm y).1 hy]; ring
    have hN : ∀ b ∈ N.toAddSubgroup, α b = 0 := fun b hb => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from hb)
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
      rw [map_add, a2, (hK hy).2, add_zero]
    let ψ : (R ⧸ N) →+ F := QuotientAddGroup.lift N.toAddSubgroup α hN
    have hψ : ∀ b, ψ (N.mkQ b) = α b := fun _ => rfl
    refine ⟨{ toFun := ψ, map_add' := ψ.map_add, map_smul' := fun c w => ?_ }, AddMonoidHom.ext hψ⟩
    obtain ⟨o, rfl⟩ := hs c
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [hsm, ← map_smul, hψ, hψ, Algebra.smul_def, a1, a2]
    simp)
  refine ⟨f1, fun b hb h => ?_, fun ξ => ?_⟩
  · have h0 : b ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (f2 b h)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from h0)
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
    refine J.add_mem hy (hO o ?_)
    have := (maximalIdeal R).sub_mem hb (hJm hy)
    rwa [add_sub_cancel_left] at this
  · obtain ⟨w, hw⟩ := f3 ξ
    obtain ⟨b, hb, e⟩ := hsurj w
    exact ⟨b, hb, hw b e⟩

theorem UpperTheory.V.Pa.tpDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.Tp ∧ (∀ b ∈ maximalIdeal S.Bh, (∀ α ∈ S.Tp, α b = 0) → b ∈ S.J2) ∧ ∀ ξ : Module.Dual S.F S.Tp, ∃ b ∈ maximalIdeal S.Bh, ∀ α : S.Tp, (α : S.Bh →+ S.F) b = ξ α := by
  intro l _ S
  haveI : IsNoetherianRing S.Bh := { noetherian := S.d6.noetherian }
  obtain ⟨-, -, -, -, -, hI, hJ⟩ := prAdd l S
  exact tp_abs S.rF S.rF_ker S.oo_surj (ired S.U.N) S.J2 rfl hI hJ S.Tp fun _ => Iff.rfl
