import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pull_zero (d : DeltaDat Xo c 0) : Pull d 0 0 := fun _ _ _ _ _ _ y₂ y _ =>
  (evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm

theorem pull_one (d : DeltaDat Xo c 0) : Pull d 1 1 := fun k _ _ _ _ _ y₂ y _ =>
  (GlobalTheory.RawSpan.evR_one_field k y₂).trans (GlobalTheory.RawSpan.evR_one_field k y).symm

theorem pull_add {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g) (h' : Pull d f' g') :
    Pull d (f + f') (g + g') := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_add _ _ g g' y₂).trans ((congrArg₂ (· + ·) (h k hk y₂ y ho) (h' k hk y₂ y ho)).trans (evalAt_add _ _ f f' y).symm)

theorem pull_mul {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g) (h' : Pull d f' g') :
    Pull d (f * f') (g * g') := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_mul _ _ g g' y₂).trans ((congrArg₂ (· * ·) (h k hk y₂ y ho) (h' k hk y₂ y ho)).trans (evalAt_mul _ _ f f' y).symm)

theorem pull_smul {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) (a : c.F) :
    Pull d (a • f) (d.eF a • g) := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_smul _ _ (d.eF a) g y₂).trans
    ((congrArg₂ (· * ·) (hk a) (h k hk y₂ y ho)).trans (evalAt_smul _ _ a f y).symm)

theorem pull_inj {d : DeltaDat Xo c 0} (hd : d.IsLev) {f f' : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g)
    (h' : Pull d f' g) (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k) :
    evR Xo c f y = evR Xo c f' y := by
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
    congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  exact (h k hk y₂ y hy).symm.trans (h' k hk y₂ y hy)

theorem not_pull_zero_one {d : DeltaDat Xo c 0} (hd : d.IsLev) (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k]
    (y : FrPt Xo c k) : ¬ Pull d 0 1 := fun h => by
  have e := pull_inj hd h (pull_one d) k y
  rw [GlobalTheory.RawSpan.evR_one_field k y] at e
  exact zero_ne_one ((evalAt_zero _ _ y).symm.trans e)

theorem pull_id (nab : NabV Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    Pull (GlobalTheory.RawSpan.idCover nab 0) f f := by
  intro k _ _ i₁ i₂ hk y₂ y ho
  have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
  subst e
  have hb := @GlobalTheory.FrameLift.frBor_lift E _ _ _ H Dw l Xo k _ c 0 (GlobalTheory.RawSpan.idCover nab 0) GlobalTheory.firstFiveLaws.1.globalFns
    i₂ i₂ 1 y y y y₂ (@GlobalTheory.RawSpan.frOver_self E _ _ _ H Dw l Xo c nab 0 k _ i₂ y) ho
    ((CategoryTheory.Category.comp_id _).symm.trans ho.1) (@GlobalTheory.ShFam.Descent.frBor_one E _ _ _ H Dw l Xo c k _ i₂ y)
  have := @GlobalTheory.ThetaSumDescent.evR_frBor E _ _ _ H Dw l Xo c n a f hf k _ i₂ 1 y y₂ hb
  refine this.trans ?_
  simp [wchar]

theorem exists_pull_of_moveInv (d : DeltaDat Xo c 0) (hd : d.IsLev) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (g : Rul d.Xo₂ d.c₂) (hg : g ∈ sec d.Xo₂ d.c₂ a n) (hi : GlobalTheory.ThetaSumDescent.MoveInv d g) :
    ∃ f ∈ sec Xo c a n, Pull d f g := by
  obtain ⟨f, hf, h⟩ := GlobalTheory.ThetaSumDescent.exists_sec_of_moveInv d hd g hg hi
  exact ⟨f, hf, fun k _ _ _ _ hk y₂ y ho => (h k hk y y₂ ho).symm⟩

theorem fibConst_of_moveInv (d : DeltaDat Xo c 0) (hd : d.IsLev) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (g : Rul d.Xo₂ d.c₂) (hg : g ∈ sec d.Xo₂ d.c₂ a n) (hi : GlobalTheory.ThetaSumDescent.MoveInv d g) : FibConst d g := by
  obtain ⟨f, -, h⟩ := exists_pull_of_moveInv d hd g hg hi
  exact h.fibConst

theorem intAt_zero : IntAt Xo c 0 := by
  rintro la _ ⟨y, rfl⟩
  rw [vAtV_zero]; exact le_top

theorem intAt_add {f g : Rul Xo c} (hf : IntAt Xo c f) (hg : IntAt Xo c g) : IntAt Xo c (f + g) := by
  rintro la _ ⟨y, rfl⟩
  exact (le_min (hf la _ ⟨y, rfl⟩) (hg la _ ⟨y, rfl⟩)).trans (vAtV_add y f g)

theorem intAt_mul {f g : Rul Xo c} (hf : IntAt Xo c f) (hg : IntAt Xo c g) : IntAt Xo c (f * g) := by
  rintro la _ ⟨y, rfl⟩
  rw [vAtV_mul]
  exact add_nonneg (hf la _ ⟨y, rfl⟩) (hg la _ ⟨y, rfl⟩)

theorem laQ_eq : LaQ Dw l = LevQ Dw l := rfl

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem congMod_iff (h h' : Dw.La →ₗ[𝓞 E] Dw.La) :
    CongMod l.Mb h h' ↔ ∀ a, (Submodule.Quotient.mk (h a) : LaQ Dw l) = Submodule.Quotient.mk (h' a) :=
  forall_congr' fun _ => (Submodule.Quotient.eq _).symm

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

theorem lift_unique {lift lift' : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (h' : IsLift lift') (γ : Gam Dw l) :
    CongMod l.Mb (lift γ) (lift' γ) := (congMod_iff _ _).2 fun a => (lift_mk h γ a).trans (lift_mk h' γ a).symm

theorem lift_mul {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ γ' : Gam Dw l) :
    CongMod l.Mb (lift (γ * γ')) (lift γ ∘ₗ lift γ') := (congMod_iff _ _).2 fun a => by
  rw [lift_mk h, LinearMap.comp_apply, lift_mk h, lift_mk h]; rfl

theorem eq_of_congMod {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) {γ γ' : Gam Dw l}
    (e : CongMod l.Mb (lift γ) (lift γ')) : γ = γ' := by
  ext q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (lift_mk h γ a).symm.trans (((congMod_iff _ _).1 e a).trans (lift_mk h γ' a))

theorem mb_ne_bot : l.Mb ≠ ⊥ := fun h => by
  have e := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at e
  have := l.three_le
  omega

theorem finite_laQ : Finite (LaQ Dw l) := by
  have := Dw.fin
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ mb_ne_bot
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LaQ Dw l) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem finite_gam : Finite (Gam Dw l) := by
  have := finite_laQ (Dw := Dw) (l := l)
  exact Finite.of_injective (fun γ : Gam Dw l => (γ : LaQ Dw l → LaQ Dw l)) DFunLike.coe_injective

theorem mb_ne_top : l.Mb ≠ ⊤ := fun h => by
  have e := l.prod
  rw [h, Ideal.map_top, Ideal.top_mul, eq_comm, Ideal.span_singleton_eq_top] at e
  have h1 := (e.map (Algebra.norm ℤ))
  have h2 : Algebra.norm ℤ ((l.M : 𝓞 E)) = (l.M : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 E) (l.M : ℤ)]; simp
  rw [h2, isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne', Int.isUnit_iff] at h1
  have := l.three_le
  omega

theorem nontrivial_laQ (hr : 1 ≤ Dw.p + Dw.q) : Nontrivial (LaQ Dw l) := by
  have := Dw.fin
  have := Dw.proj
  rw [Submodule.Quotient.nontrivial_iff]
  intro h
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul l.Mb (⊤ : Submodule (𝓞 E) Dw.La)
    Module.Finite.fg_top h.ge
  have hne : r ≠ 0 := by
    rintro rfl
    exact mb_ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using l.Mb.neg_mem hr1))
  have : Nontrivial Dw.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Dw.rank]; omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : Dw.La)
  exact hx ((smul_eq_zero.1 (hr0 x trivial)).resolve_left hne)

theorem nontrivial_gam (hr : 1 ≤ Dw.p + Dw.q) : Nontrivial (Gam Dw l) := by
  have := nontrivial_laQ (l := l) hr
  refine ⟨LinearEquiv.neg _, 1, fun h => ?_⟩
  obtain ⟨q, hq⟩ := exists_ne (0 : LaQ Dw l)
  have h2 : -q = q := LinearEquiv.congr_fun h q
  have hM : (l.M : 𝓞 E) • q = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.smul_mem_smul ?_ trivial
    have e : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left e
  obtain ⟨m, hm⟩ := l.odd
  have h3 : (2 : 𝓞 E) • q = 0 := by rw [two_smul]; nth_rewrite 1 [← h2]; exact neg_add_cancel q
  rw [hm] at hM
  push_cast at hM
  rw [add_smul, one_smul, mul_comm, mul_smul, h3, smul_zero, zero_add] at hM
  exact hq hM

end GlobalTheory.LevPullModel
