import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CardKerMatrixFiniteField

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization

namespace GlobalTheory.SW.HeckeId

section Abstract

theorem card_proj_mem (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {p : ℙ F V // p.rep ∈ K} * (Nat.card F - 1) + 1 = Nat.card K := by
  rw [← card_lines_le_submodule F V K]
  congr 2
  refine Nat.card_congr (((Projectivization.equivSubmodule F V).subtypeEquiv
    (q := fun l => l.1 ≤ K) fun p => ?_).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ (· ≤ K)))
  change _ ↔ p.submodule ≤ K
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

theorem card_ker_dual (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F V] [FiniteDimensional F W] (g : V →ₗ[F] W) :
    Nat.card (LinearMap.ker g) * Nat.card F ^ Module.finrank F W =
      Nat.card (LinearMap.ker g.dualMap) * Nat.card F ^ Module.finrank F V := by
  have h1 := g.finrank_range_add_finrank_ker
  have h2 := g.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h2
  rw [Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker g),
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker g.dualMap), ← pow_add, ← pow_add]
  congr 1
  omega

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]

def Hyp (P : Ideal O) (M : Type) [AddCommGroup M] [Module O M] : Set (Submodule O M) :=
  {N | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}

theorem Hyp.smul_mem {P : Ideal O} {N : Submodule O M} (h : N ∈ Hyp P M) {c : O} (hc : c ∈ P)
    (x : M) : c • x ∈ N := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, Algebra.smul_def]
  have : algebraMap O (O ⧸ P) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [this, zero_mul]

theorem Hyp.exists_not_mem {P : Ideal O} {N : Submodule O M} (h : N ∈ Hyp P M) : ∃ v, v ∉ N := by
  obtain ⟨f, hf, rfl⟩ := h
  by_contra h
  push Not at h
  exact hf (LinearMap.ext h)

theorem Hyp.gen {P : Ideal O} [hP : P.IsMaximal] {N : Submodule O M} (h : N ∈ Hyp P M) {v : M}
    (hv : v ∉ N) (x : M) : ∃ r : O, x - r • v ∈ N := by
  obtain ⟨f, -, rfl⟩ := h
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (show f v ≠ 0 from hv)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (f x * b)
  refine ⟨c, ?_⟩
  have : algebraMap O (O ⧸ P) c = f x * b := hc
  rw [LinearMap.mem_ker, map_sub, map_smul, Algebra.smul_def, this, mul_assoc, mul_comm b, hb,
    mul_one, sub_self]

theorem Hyp.eq_of_le {P : Ideal O} [hP : P.IsMaximal] {N N' : Submodule O M} (h : N ∈ Hyp P M)
    (hle : N ≤ N') (hne : ¬ ∀ x, x ∈ N') : N = N' := by
  refine le_antisymm hle fun v hv => by_contra fun hv' => hne fun x => ?_
  obtain ⟨r, hr⟩ := Hyp.gen h hv' x
  simpa using N'.add_mem (hle hr) (N'.smul_mem r hv)

attribute [local instance] Ideal.Quotient.field

theorem card_hyp_le (P : Ideal O) [hP : P.IsMaximal] [Finite (M →ₗ[O] O ⧸ P)]
    (K : Submodule (O ⧸ P) (M →ₗ[O] O ⧸ P)) (U : Submodule O M)
    (hK : ∀ f, f ∈ K ↔ U ≤ LinearMap.ker f) :
    {N ∈ Hyp P M | U ≤ N}.ncard * (Nat.card (O ⧸ P) - 1) + 1 = Nat.card K := by
  rw [← card_proj_mem _ _ K]
  congr 2
  symm
  refine Nat.card_eq_of_bijective
    (fun p => ⟨LinearMap.ker p.1.rep, ⟨_, p.1.rep_nonzero, rfl⟩, (hK _).1 p.2⟩) ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have h : LinearMap.ker p.rep = LinearMap.ker p'.rep := congrArg Subtype.val h
    refine Subtype.ext ?_
    change p = p'
    rw [← p.mk_rep, ← p'.mk_rep, Projectivization.mk_eq_mk_iff']
    obtain ⟨v, hv⟩ := Hyper.surj_of_ne P _ p'.rep_nonzero
    refine ⟨p.rep v, LinearMap.ext fun x => ?_⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (p'.rep x)
    have h1 : x - c • v ∈ LinearMap.ker p'.rep := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, ← hc, Algebra.smul_def, mul_one]
      exact sub_self _
    rw [← h, LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
    rw [h1, LinearMap.smul_apply, ← hc, Algebra.smul_def c, smul_eq_mul, mul_comm]; rfl
  · rintro ⟨_, ⟨f, hf, rfl⟩, hU⟩
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (O ⧸ P) f hf
    refine ⟨⟨Projectivization.mk _ f hf, ha ▸ K.smul_mem (a : O ⧸ P) ((hK f).2 hU)⟩, Subtype.ext ?_⟩
    ext x
    simp only [← ha, LinearMap.mem_ker]
    simp [Units.smul_def]

theorem one_tmul_eq_zero (P : Ideal O) (x : M) :
    (1 : O ⧸ P) ⊗ₜ[O] x = 0 ↔ x ∈ (P • ⊤ : Submodule O M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M P).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_lines [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] : ∃ (A : ℕ) (e : Fin A → M),
    A * (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 ∧
    (∀ i, e i ∉ (P • ⊤ : Submodule O M)) ∧
    ∀ (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L]
      (u : M →ₗ[O] L),
      (Nat.card {i // u (e i) ∈ (P • ⊤ : Submodule O L)} * (Nat.card (O ⧸ P) - 1) + 1) *
          Nat.card (O ⧸ P) ^ Module.finrank O L =
        ({N ∈ Hyp P L | LinearMap.range u ≤ N}.ncard * (Nat.card (O ⧸ P) - 1) + 1) *
          Nat.card (O ⧸ P) ^ Module.finrank O M := by
  have : Finite ((O ⧸ P) ⊗[O] M) := Module.finite_of_finite (O ⧸ P)
  have hs : ∀ v : (O ⧸ P) ⊗[O] M, ∃ x : M, (1 : O ⧸ P) ⊗ₜ[O] x = v :=
    TensorProduct.mk_surjective O M (O ⧸ P) Ideal.Quotient.mk_surjective
  choose l hl using hs
  let ε := Finite.equivFin (ℙ (O ⧸ P) ((O ⧸ P) ⊗[O] M))
  refine ⟨_, fun i => l (ε.symm i).rep, ?_, fun i => ?_, fun L _ _ _ _ u => ?_⟩
  · rw [← Projectivization.card, ← Hyper.finrank_fibre O M (O ⧸ P),
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
  · rw [← one_tmul_eq_zero, hl]
    exact Projectivization.rep_nonzero _
  · let e := LinearMap.liftBaseChangeEquiv (R := O) (M := L) (N := O ⧸ P) (O ⧸ P)
    have : Module.Finite (O ⧸ P) (L →ₗ[O] O ⧸ P) := Module.Finite.equiv e.symm
    have : Finite (L →ₗ[O] O ⧸ P) := Module.finite_of_finite (O ⧸ P)
    let g := u.baseChange (O ⧸ P)
    rw [card_hyp_le P ((LinearMap.ker g.dualMap).comap e.toLinearMap), ← Hyper.finrank_fibre O M (O ⧸ P),
      ← Hyper.finrank_fibre O L (O ⧸ P),
      Nat.card_congr (e.ofSubmodule' (LinearMap.ker g.dualMap)).toEquiv, ← card_ker_dual,
      ← card_proj_mem]
    · congr 3
      refine Nat.card_congr (ε.symm.subtypeEquiv fun i => ?_)
      rw [← one_tmul_eq_zero, LinearMap.mem_ker]
      conv_rhs => rw [← hl (ε.symm i).rep]
      rfl
    · intro f
      rw [LinearMap.range_le_ker_iff]
      change (e f) ∘ₗ g = 0 ↔ _
      constructor
      · intro h
        ext x
        simpa [e, g] using LinearMap.congr_fun h (1 ⊗ₜ x)
      · intro h
        refine LinearMap.ext fun v => ?_
        rw [← hl v]
        simpa [e, g] using LinearMap.congr_fun h (l v)

theorem exists_reps [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] {B : ℕ}
    (hB : Nat.card (O ⧸ P) ^ Module.finrank O M = B) : ∃ ξ : Fin B → M, ∀ χ : AddChar M ℂ,
    (∀ c ∈ P, ∀ x, χ (c • x) = 1) → ∑ j, χ (ξ j) = if ∀ x, χ x = 1 then (B : ℂ) else 0 := by
  have : Finite ((O ⧸ P) ⊗[O] M) := Module.finite_of_finite (O ⧸ P)
  have hs : ∀ v : (O ⧸ P) ⊗[O] M, ∃ x : M, (1 : O ⧸ P) ⊗ₜ[O] x = v :=
    TensorProduct.mk_surjective O M (O ⧸ P) Ideal.Quotient.mk_surjective
  choose l hl using hs
  have hc : Nat.card ((O ⧸ P) ⊗[O] M) = B := by
    rw [← hB, ← Hyper.finrank_fibre O M (O ⧸ P), Module.natCard_eq_pow_finrank (K := O ⧸ P)]
  let ε := Finite.equivFinOfCardEq hc
  refine ⟨fun j => l (ε.symm j), fun χ hχ => ?_⟩
  have h0 : ∀ x ∈ (P • ⊤ : Submodule O M), χ x = 1 := fun x hx =>
    Submodule.smul_induction_on hx (fun c hc x _ => hχ c hc x) fun x y hx hy => by
      rw [AddChar.map_add_eq_mul, hx, hy, mul_one]
  have h1 : ∀ x y : M, (1 : O ⧸ P) ⊗ₜ[O] x = (1 : O ⧸ P) ⊗ₜ[O] y → χ x = χ y := fun x y h => by
    have := h0 (x - y) (by rw [← one_tmul_eq_zero, TensorProduct.tmul_sub, h, sub_self])
    rw [← sub_add_cancel x y, AddChar.map_add_eq_mul, this, one_mul]
  let ψ : AddChar ((O ⧸ P) ⊗[O] M) ℂ :=
    ⟨fun v => χ (l v), by rw [h1 _ 0 (by rw [hl]; simp), AddChar.map_zero_eq_one], fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact h1 _ _ (by rw [TensorProduct.tmul_add, hl, hl, hl])⟩
  haveI := Fintype.ofFinite ((O ⧸ P) ⊗[O] M)
  change ∑ j, ψ (ε.symm j) = _
  rw [ε.symm.sum_comp (fun v => ψ v), AddChar.sum_eq_ite, ← Nat.card_eq_fintype_card, hc]
  refine if_congr ⟨fun h x => ?_, fun h => ?_⟩ rfl rfl
  · rw [← h1 _ _ (hl (1 ⊗ₜ x))]
    exact DFunLike.congr_fun h _
  · ext v
    exact h _

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

open Nbr

omit [IsCMField E] in
theorem finrank_of_agree {m : ℕ} {X : Lt E N} (h : Agree m X (stdL E N)) :
    Module.finrank (𝓞 E) X = N := by
  have : IsLocalizedModule (𝓞 E)⁰ X.subtype := by
    obtain ⟨s, hs, -, -, h2⟩ := h
    have := isLocalizedModule_id (𝓞 E)⁰ (Fin N → E) E
    refine ⟨IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := Fin N → E)), fun y => ?_,
      fun {x₁ x₂} h => ⟨1, by rw [Subtype.ext h]⟩⟩
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ y
    choose c hc using hd
    have h1 : (d : 𝓞 E) • y ∈ stdL E N := by
      have : (d : 𝓞 E) • y = ∑ i, c i • (Pi.single i 1 : Fin N → E) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply, ← hc j, Algebra.smul_def]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : (s : 𝓞 E) ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hs.ne')
    exact ⟨(⟨_, h2 _ h1⟩, ⟨s, hs'⟩ * d), mul_smul _ _ _⟩
  rw [← IsLocalizedModule.finrank_eq (𝓞 E)⁰ X.subtype le_rfl,
    ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]
  simp

omit [IsCMField E] in
theorem gidx_of_le {m q : ℕ} {X Y : Lt E N} (hX : Agree m X (stdL E N)) (hle : X ≤ Y)
    (hi : X.toAddSubgroup.relIndex Y.toAddSubgroup = q) : gidx Y = q * gidx X := by
  obtain ⟨t, ht, -, -, h2⟩ := hX
  have h0 := TwistAdm.relIndex_ne_zero _ _ TwistAdm.std_fg ht h2
  unfold gidx
  have hle' : X.toAddSubgroup ≤ Y.toAddSubgroup := hle
  generalize X.toAddSubgroup = X at *
  generalize Y.toAddSubgroup = Y at *
  generalize (stdL E N).toAddSubgroup = S at *
  have a1 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) X Y inf_le_right hle'
  have a2 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) (S ⊓ Y) Y (inf_le_inf_left _ hle') inf_le_right
  have a3 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) (S ⊓ Y) S (inf_le_inf_left _ hle') inf_le_left
  rw [AddSubgroup.inf_relIndex_right] at a1 a2
  rw [AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_left] at a3
  rw [← a3] at h0
  have b1 : (((S ⊓ X).relIndex (S ⊓ Y) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul h0)
  have b2 : ((Y.relIndex S : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul h0)
  have b3 := congrArg (Nat.cast : ℕ → ℝ) (a1.trans a2.symm)
  rw [← a3, ← hi]
  push_cast at b3 ⊢
  field_simp
  linear_combination -b3

omit [IsCMField E] in
theorem exists_pole (P : Ideal (𝓞 E)) [hP : P.IsMaximal] (hP0 : P ≠ ⊥) :
    ∃ t : E, (∀ c ∈ P, IsIntegral ℤ ((c : E) * t)) ∧ ∃ d ∈ P, ∃ r ∉ P, ((r : 𝓞 E) : E) = (d : E) * t := by
  obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top
  have htP : ∀ c ∈ P, IsIntegral ℤ ((c : E) * t) := fun c hc => by
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hP0)).1 ht _
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hb : (b : E) = t * (c : E) := hb
    rw [mul_comm, ← hb]; exact b.2
  exact ⟨t, htP, exists_not_mem hP0 (fun h => ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, h⟩, rfl⟩)) htP⟩

omit [IsCMField E] in
theorem pole_smul_mem {P : Ideal (𝓞 E)} [hP : P.IsMaximal] {t : E}
    (ht : ∀ c ∈ P, IsIntegral ℤ ((c : E) * t)) {d r : 𝓞 E} (hd : d ∈ P) (hr : r ∉ P)
    (e : (r : E) = (d : E) * t) (L : Lt E n) (v : L) :
    t • (v : Fin n → E) ∈ L ↔ v ∈ (P • ⊤ : Submodule (𝓞 E) L) := by
  rw [Submodule.mem_smul_top_iff]
  constructor
  · intro h
    obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hr
    have h1 : (v : Fin n → E) = u • (d • (t • (v : Fin n → E))) + c • (v : Fin n → E) := by
      rw [osmul d, smul_smul, ← e, ← osmul, smul_smul, ← add_smul, huc, one_smul]
    rw [h1]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.smul_mem_smul hd h))
      (Submodule.smul_mem_smul hc v.2)
  · intro h
    refine Submodule.smul_induction_on (p := fun w => t • w ∈ L) h (fun c hc x hx => ?_)
      fun x y hx hy => by rw [smul_add]; exact add_mem hx hy
    rw [osmul, smul_smul, mul_comm]
    exact L.smul_mem (⟨_, ht c hc⟩ : 𝓞 E) hx

noncomputable def eT (w : E) : ℂ := cexp (2 * Real.pi * I * ((Algebra.trace ℚ E w : ℚ) : ℂ))

omit [IsCMField E] in
theorem eT_add (w w' : E) : eT (w + w') = eT w * eT w' := by
  simp [eT, mul_add, Complex.exp_add]

omit [IsCMField E] in
theorem eT_eq_one_iff (w : E) : eT w = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ E w = k := by
  rw [eT, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ?_
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl

omit [IsCMField E] in
theorem eT_int {w : E} (h : IsIntegral ℤ w) : eT w = 1 := by
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) h)
  exact (eT_eq_one_iff w).2 ⟨k, hk.symm⟩

omit [IsCMField E] in
theorem int_of_eT {q : ℕ} (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ 2 * NumberField.discr E) {w : E}
    (h1 : IsIntegral ℤ ((q : E) * w)) (h2 : ∀ c : 𝓞 E, eT ((c : E) * w) = 1) : IsIntegral ℤ w := by
  have h3 : IsIntegral ℤ ((NumberField.discr E : E) * w) := by
    have hw : w ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
      intro a ha
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨k, hk⟩ := (eT_eq_one_iff _).1 (h2 c)
      exact ⟨k, by rw [Algebra.traceForm_apply, mul_comm]; exact hk.symm⟩
    have h4 := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰
      (NumberField.discr_mem_differentIdeal E (𝓞 E))
    rw [coeIdeal_differentIdeal ℤ ℚ] at h4
    have h5 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))).1 h4 w hw
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h5
    have hb : (b : E) = (NumberField.discr E : E) * w := by simpa using hb
    rw [← hb]; exact b.2
  have h6 : IsCoprime (q : ℤ) (NumberField.discr E) :=
    ((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 fun h => hd (h.mul_left 2)
  obtain ⟨a, b, hab⟩ := h6
  have h7 : (a : E) * q + b * (NumberField.discr E : E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → E) hab
  have : w = a • ((q : E) * w) + b • ((NumberField.discr E : E) * w) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-w) * h7
  rw [this]
  exact (h1.smul a).add (h3.smul b)

theorem sum_add_cc {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (w : E) :
    ∑ τ : Ψ, τ.1 (w + cc w) = ((Algebra.trace ℚ E w : ℚ) : ℂ) := by
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := w)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom _ _) _ _ fun _ => rfl).symm
  have h4 : ∑ σ ∈ Ψᶜ, σ w = ∑ σ ∈ Ψ, σ (cc w) := by
    refine Finset.sum_bij' (fun σ _ => ComplexEmbedding.conjugate σ)
      (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      by_contra h
      exact (Finset.mem_compl.1 hσ) ((hΨ σ).2 h)
    · intro σ hσ
      exact Finset.mem_compl.2 ((hΨ σ).1 hσ)
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _
      rw [Base.map_cc]
      simp
  rw [h3, ← Finset.sum_add_sum_compl Ψ, h4] at h2
  rw [Finset.sum_coe_sort Ψ (fun τ => τ (w + cc w))]
  simp only [map_add, Finset.sum_add_distrib]
  exact h2.symm

noncomputable def sym (a b : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  vecMulVec a (fun i => cc (b i)) + vecMulVec b fun i => cc (a i)

theorem ccT_sym (a b : Fin N → E) : ccT (sym a b) = sym a b := by
  ext i j
  simp [ccT, sym, vecMulVec_apply, cc, mul_comm, add_comm]

theorem chiH_sym {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (a b : Fin N → E)
    (x : Matrix (Fin n) (Fin N) E) : chiH Ψ (sym a b) x = eT (herm 1 (x *ᵥ a) (x *ᵥ b)) := by
  have h : ∀ a b : Fin N → E,
      (x * vecMulVec a (fun i => cc (b i)) * ccT x).trace = herm 1 (x *ᵥ a) (x *ᵥ b) := by
    intro a b
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Nbr.herm_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ccT, cc, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [chiH, eT, ← sum_add_cc hΨ, herm_symm, sym, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, h, h]

theorem herm_ar (x y y' : Fin n → E) : herm 1 x (y + y') = herm 1 x y + herm 1 x y' := by
  simp [Nbr.herm_one, cc, mul_add, Finset.sum_add_distrib]

theorem inf_mem_hyp {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h' : Λ' ∈ Nb M P Λ) : Λ'.comap Λ.subtype ∈ Hyp P Λ :=
  (index_iff hP.1 hP.2.2.1 _).1
    ⟨fun c hc x => smul_le_iff.1 h'.2.1 c hc x x.2, h'.2.2.trans hP.2.2.1⟩

def perp (Λ : Lt E n) (y : Fin n → E) : Submodule (𝓞 E) Λ :=
  Submodule.comap Λ.subtype
    { carrier := {x : Fin n → E | Int' x y}
      add_mem' := fun ha hb => Int'.add ha hb
      zero_mem' := int_zero y
      smul_mem' := fun c _ hx => Int'.smul c hx }

theorem nb_unique {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' Λ'' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) (h'' : Λ'' ∈ Nb M P Λ) {y : Fin n → E} (hy : y ∉ Λ)
    (hy' : y ∈ Λ') (hy'' : y ∈ Λ'') : Λ' = Λ'' := by
  have := max_of_norm hP.1 hP.2.2.1
  have hS : SD Λ := h.2.1
  have key : ∀ L ∈ Nb M P Λ, y ∈ L → L.comap Λ.subtype = perp Λ y := fun L hL hyL =>
    Hyp.eq_of_le (inf_mem_hyp hP hL) (fun x hx => (hL.1.2.1 _).1 hx y hyL)
      fun H => hy ((hS y).2 fun z hz => Int'.symm (H ⟨z, hz⟩))
  have e' := congrArg (Submodule.map Λ.subtype) ((key _ h' hy').trans (key _ h'' hy'').symm)
  simp only [Submodule.map_comap_subtype] at e'
  exact (eq_nbOf hP h h').trans (e' ▸ (eq_nbOf hP h h'').symm)

theorem perp_mem_hyp {P : Ideal (𝓞 E)} [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {Λ : Lt E n} (hS : SD Λ)
    {y : Fin n → E} (hy : y ∉ Λ) (hQ : ∀ c ∈ conjI P, c • y ∈ Λ) : perp Λ y ∈ Hyp P Λ := by
  obtain ⟨t, ht, d, hd, r, hr, e⟩ := exists_pole P hP0
  have hint : ∀ c ∈ P, ∀ x : Λ, IsIntegral ℤ ((c : E) * herm 1 (x : Fin n → E) y) := fun c hc x => by
    have h1 : co c ∈ conjI P := mem_conjI.2 (by rwa [co_co])
    have h2 := (int_move c (x : Fin n → E) y).2 ((hS _).1 x.2 _ (hQ _ h1))
    unfold Int' at h2
    rwa [osmul, herm_sl] at h2
  let g : Λ →ₗ[𝓞 E] 𝓞 E :=
    { toFun := fun x => ⟨_, hint d hd x⟩
      map_add' := fun x x' => RingOfIntegers.ext (by
        change (d : E) * herm 1 ((x : Fin n → E) + (x' : Fin n → E)) y = (d : E) * _ + (d : E) * _
        rw [herm_al, mul_add])
      map_smul' := fun c x => RingOfIntegers.ext (by
        change (d : E) * herm 1 ((c : E) • (x : Fin n → E)) y = (c : E) * ((d : E) * _)
        rw [herm_sl, mul_left_comm]) }
  have hk : LinearMap.ker (P.mkQ ∘ₗ g) = perp Λ y := by
    ext x
    refine (Submodule.Quotient.mk_eq_zero P).trans ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hr
      have h3 : (u : E) * (r : E) + (c : E) = 1 := by
        exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
      have h4 : IsIntegral ℤ ((d : E) * herm 1 (x : Fin n → E) y * t) := ht _ hx
      have h5 : herm 1 (x : Fin n → E) y = (u : E) * ((d : E) * herm 1 (x : Fin n → E) y * t) +
          (c : E) * herm 1 (x : Fin n → E) y := by
        linear_combination (-herm 1 (x : Fin n → E) y) * h3 + (u : E) * herm 1 (x : Fin n → E) y * e
      change IsIntegral ℤ (herm 1 (x : Fin n → E) y)
      rw [h5]
      exact (IsIntegral.mul u.2 h4).add (hint c hc x)
    · have hx : IsIntegral ℤ (herm 1 (x : Fin n → E) y) := hx
      let w : 𝓞 E := ⟨_, hx⟩
      have h1 : g x = w * d := RingOfIntegers.ext (mul_comm (d : E) (w : E))
      rw [h1]
      exact P.mul_mem_left _ hd
  refine ⟨_, fun h0 => hy ((hS y).2 fun z hz => Int'.symm ?_), hk⟩
  have : (⟨z, hz⟩ : Λ) ∈ perp Λ y := by rw [← hk, h0]; trivial
  exact this

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem comap_mem_hyp {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ¬ ∀ ξ, u ξ ∈ Λ)
    (hu' : ∀ ξ, u ξ ∈ Λ') : Λ.comap u ∈ Hyp (conjI P) X := by
  obtain ⟨f, -, hf⟩ := inf_mem_hyp (good_conj hP) (nb_symm hP h h')
  have hk : LinearMap.ker (f ∘ₗ u.codRestrict Λ' hu') = Λ.comap u := by
    rw [LinearMap.ker_comp, hf]; rfl
  refine ⟨_, fun h0 => hu fun ξ => ?_, hk⟩
  have : ξ ∈ Λ.comap u := by rw [← hk, h0]; trivial
  exact this

theorem exists_nb {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) {a b : 𝓞 E} (ha : a ∈ P) (hab : a + b = 1)
    (u : X →ₗ[𝓞 E] (Fin n → E)) (hH : Λ.comap u ∈ Hyp (conjI P) X) {η : X} (hη : u η ∉ Λ)
    (hI : ∀ ξ, Int' (u η) (u (b • ξ))) : ∃ Λ' ∈ Nb M P Λ, ∀ ξ, u ξ ∈ Λ' := by
  have := max_of_norm hP.1 hP.2.2.1
  have := max_of_norm (good_conj hP).1 (good_conj hP).2.2.1
  have hS : SD Λ := h.2.1
  have hQ : ∀ c ∈ conjI P, ∀ ξ, c • u ξ ∈ Λ := fun c hc ξ => by
    rw [← map_smul]; exact Hyp.smul_mem hH hc ξ
  obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 _).2
    (perp_mem_hyp (ne_bot_of_norm hP.1 hP.2.2.1) hS hη fun c hc => hQ c hc η)
  have h5 : ((perp Λ (u η)).map Λ.subtype).comap Λ.subtype = perp Λ (u η) :=
    Submodule.comap_map_eq_of_injective Λ.injective_subtype _
  have h6 : P • Λ ≤ (perp Λ (u η)).map Λ.subtype :=
    smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
  have h7 : ((perp Λ (u η)).map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
    rw [relIndex_eq, h5, h4]
  refine ⟨_, nbOf_mem hP h h6 (Λ.map_subtype_le _) h7, fun ξ => ⟨?_, fun c hc => ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨r, hr⟩ := Hyp.gen hH (v := η) hη ξ
    have hr : u (ξ - r • η) ∈ Λ := hr
    have := Int'.add ((hS _).1 hr z z.2) ((Int'.symm hz).smul r)
    rwa [← map_smul, ← map_add, sub_add_cancel] at this
  · refine ⟨⟨_, hQ c hc ξ⟩, ?_, rfl⟩
    have h8 : Int' (a • c • u ξ) (u η) := h3 a ha ⟨_, hQ c hc ξ⟩
    have := h8.add (hI (c • ξ)).symm
    rwa [map_smul, map_smul, ← add_smul, hab, one_smul] at this

theorem count_pole {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) {a b : 𝓞 E} (ha : a ∈ P) (hab : a + b = 1)
    (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ¬ ∀ ξ, u ξ ∈ Λ) {A : ℕ} (B : Fin A → Submodule (𝓞 E) X)
    (hB : ∀ i, B i ∈ Hyp (conjI P) X) (hB1 : Function.Injective B)
    (hB2 : ∀ K ∈ Hyp (conjI P) X, ∃ i, B i = K) (η : Fin A → X) (hη : ∀ i, η i ∉ B i) :
    {i | (∀ ξ ∈ B i, u ξ ∈ Λ) ∧ ∀ ξ, Int' (u (η i)) (u (b • ξ))}.ncard =
      {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'}.ncard := by
  have := max_of_norm (good_conj hP).1 (good_conj hP).2.2.1
  have k1 : ∀ i, (∀ ξ ∈ B i, u ξ ∈ Λ) → B i = Λ.comap u := fun i hi => Hyp.eq_of_le (hB i) hi hu
  by_cases hex : ∃ Λ' ∈ Nb M P Λ, ∀ ξ, u ξ ∈ Λ'
  · obtain ⟨Λ', h', hu'⟩ := hex
    obtain ⟨i, hi⟩ := hB2 _ (comap_mem_hyp hP h h' u hu hu')
    obtain ⟨y, hy⟩ := not_forall.1 hu
    rw [Set.ncard_eq_one.2 ⟨i, ?_⟩, Set.ncard_eq_one.2 ⟨Λ', ?_⟩]
    · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨h', hu'⟩, fun L hL =>
        nb_unique hP h hL.1 h' hy (hL.2 y) (hu' y)⟩
    · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨fun ξ hξ => by rwa [hi] at hξ,
        fun ξ => (h'.1.2.1 _).1 (hu' _) _ (hu' _)⟩, fun j hj => hB1 ((k1 j hj.1).trans hi.symm)⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'})
      fun L hL => hex ⟨L, hL⟩, Set.ncard_empty,
      Set.eq_empty_of_forall_notMem (s := {i | (∀ ξ ∈ B i, u ξ ∈ Λ) ∧ _}), Set.ncard_empty]
    rintro i ⟨hi, hI⟩
    exact hex (exists_nb hP h ha hab u (k1 i hi ▸ hB i) (fun H => hη i (k1 i hi ▸ H)) hI)

theorem count_int {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ∀ ξ, u ξ ∈ Λ) :
    {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'}.ncard =
      {K ∈ Hyp P Λ | LinearMap.range (u.codRestrict Λ hu) ≤ K}.ncard := by
  refine Set.BijOn.ncard_eq (f := fun Λ' : Lt E n => Λ'.comap Λ.subtype)
    ⟨fun Λ' h' => ⟨inf_mem_hyp hP h'.1, ?_⟩, fun Λ' h' Λ'' h'' e => ?_, fun K hK => ?_⟩
  · rintro _ ⟨ξ, rfl⟩
    exact h'.2 ξ
  · have e' := congrArg (Submodule.map Λ.subtype) e
    simp only [Submodule.map_comap_subtype] at e'
    exact (eq_nbOf hP h h'.1).trans (e' ▸ (eq_nbOf hP h h''.1).symm)
  · obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 K).2 hK.1
    have h5 : (K.map Λ.subtype).comap Λ.subtype = K :=
      Submodule.comap_map_eq_of_injective Λ.injective_subtype K
    have h6 : P • Λ ≤ K.map Λ.subtype :=
      smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
    have h7 : (K.map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
      rw [relIndex_eq, h5, h4]
    have h8 := (nbOf_spec hP h h6 (Λ.map_subtype_le K) h7).2
    refine ⟨_, ⟨nbOf_mem hP h h6 (Λ.map_subtype_le K) h7,
      fun ξ => (h8.ge ⟨_, hK.2 ⟨ξ, rfl⟩, rfl⟩).2⟩, Eq.trans ?_ h5⟩
    ext x
    exact ⟨fun hx => h8.le ⟨x.2, hx⟩, fun hx => (h8.ge hx).2⟩

noncomputable def pairChar (u : X →ₗ[𝓞 E] (Fin n → E)) (b : 𝓞 E) (η : X) : AddChar X ℂ where
  toFun := fun ξ => eT (herm 1 (u η) (u (b • ξ)))
  map_zero_eq_one' := eT_int (Int'.symm (by rw [smul_zero, map_zero]; exact int_zero _))
  map_add_eq_mul' := fun ξ ξ' => by rw [smul_add, map_add, herm_ar, eT_add]

theorem pairChar_spec {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (hS : SD Λ) {b : 𝓞 E} (hb : b ∈ conjI P) (u : X →ₗ[𝓞 E] (Fin n → E))
    (hQ : ∀ c ∈ conjI P, ∀ ξ, u (c • ξ) ∈ Λ) (η : X) :
    (∀ c ∈ P, ∀ ξ, pairChar u b η (c • ξ) = 1) ∧
      ((∀ ξ, pairChar u b η ξ = 1) ↔ ∀ ξ, Int' (u η) (u (b • ξ))) := by
  have k : ∀ c ∈ conjI P, ∀ ξ, Int' (c • u η) (u (b • ξ)) := fun c hc ξ => by
    rw [← map_smul]; exact (hS _).1 (hQ c hc η) _ (hQ b hb ξ)
  refine ⟨fun c hc ξ => eT_int ?_, fun H ξ => int_of_eT hP.1 hP.2.2.2.2 ?_ fun c => ?_,
    fun H ξ => eT_int (H ξ)⟩
  · have := (int_move _ _ _).1 (k (co c) (mem_conjI.2 (by rwa [co_co])) ξ)
    rwa [co_co, ← map_smul, smul_comm] at this
  · have := k (q : ℕ) ((good_conj hP).2.2.1 ▸ Ideal.absNorm_mem _) ξ
    unfold Int' at this
    rw [osmul, herm_sl] at this
    exact this
  · have : eT (herm 1 (u η) (u (b • co c • ξ))) = 1 := H (co c • ξ)
    rwa [smul_comm, map_smul, osmul, herm_sr, coe_co, cc_cc] at this

theorem finsum_ite {ι : Type} {S : Set ι} (hS : S.Finite) (p : ι → Prop) [DecidablePred p] (c : ℂ) (f : ι → ℂ)
    (hf : ∀ i ∈ S, f i = if p i then c else 0) :
    ∑ᶠ i ∈ S, f i = ({i ∈ S | p i}.ncard : ℂ) * c := by
  rw [finsum_mem_congr rfl hf, finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset]
  congr 3
  ext i
  simp

theorem sum_ite' {A : ℕ} (p : Fin A → Prop) [DecidablePred p] (c : ℂ) (f : Fin A → ℂ)
    (hf : ∀ i, f i = if p i then c else 0) : ∑ i, f i = ({i | p i}.ncard : ℂ) * c := by
  have := finsum_ite Set.finite_univ p c f fun i _ => hf i
  rw [finsum_mem_univ, finsum_eq_sum_of_fintype] at this
  simpa using this

omit [IsCMField E] in
theorem exists_mult' {M R q : ℕ} (hR : 0 < R) (hq : q.Coprime (R * M)) {𝔛 : Lt E N}
    (h : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, (s : E) • v = (q : E) • ξ := by
  obtain ⟨s, hs, h1⟩ := TwistAdm.exists_mult hR h
  have hc' : q.Coprime (R ^ 2) := (Nat.Coprime.coprime_mul_right_right hq).pow_right 2
  refine ⟨q ^ (R ^ 2).totient * s, by simpa using (Nat.ModEq.pow_totient hc').mul hs,
    fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.totient_pos.2 (pow_pos hR 2)).ne'
  refine ⟨_, TwistAdm.nat_smul_mem _ (q ^ k) (h1 v hv), ?_⟩
  rw [hk, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [pow_succ]
  ring

theorem twist_ite {M R s : ℕ} {φ : Fam E n N} {Y : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) Y (stdL E N)) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M)
    (x : Matrix (Fin n) (Fin N) E) (hs : s ≡ 1 [MOD R ^ 2])
    (h : ∀ v ∈ stdL E N, (s : E) • v ∈ Y) : twist R Y φ Λ x =
      if ∀ ξ ∈ Y, (R : E) • (x *ᵥ ξ) ∈ Λ then φ Λ ((s : E) • x) else 0 := by
  split_ifs with h1
  · exact TwistAdm.twist_val hφ hA hΛ x s hs h1 (TwistAdm.cols_of_cond h h1)
  · rw [TwistAdm.twist_eq φ (TwistAdm.exists_mult hφ.pos.2 hA), if_neg h1]

end GlobalTheory.SW.HeckeId

open GlobalTheory.SW.HeckeId GlobalTheory.SW.Nbr in

theorem GlobalTheory.SW.hecke_relation_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (M R q : ℕ) (P : Ideal (𝓞 E)) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → GoodPrime (R * M) q P → ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E), A * (q - 1) = q ^ N - 1 ∧ (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧ (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧ ∀ j, ccT (β i j) = β i j) ∧ ∀ Λ ∈ Vset E n M, ∀ x, ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, twist R (XA i) φ Λ x + ∑ i, ∑ j, chiH Ψ (β i j) x * twist R (XB i) φ Λ x) = ((q : ℂ) - 1) * (q : ℂ) ^ N * (∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) + ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) * twist R 𝔛 φ Λ x := by
  intro E _ _ _ Ψ hΨ n N M R q P φ 𝔛 hφ hfg hA hP'
  have hP : GoodPrime M q P := ⟨hP'.1, Nat.Coprime.coprime_mul_left_right hP'.2.1, hP'.2.2⟩
  have hQ := good_conj hP
  have hq := hP.1
  have mP := max_of_norm hq hP.2.2.1
  have mQ := max_of_norm hq hQ.2.2.1
  have cP : Nat.card (𝓞 E ⧸ P) = q := hP.2.2.1
  have cQ : Nat.card (𝓞 E ⧸ conjI P) = q := hQ.2.2.1
  have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (cP ▸ hq.ne_zero)
  have : Finite (𝓞 E ⧸ conjI P) := Nat.finite_of_card_ne_zero (cQ ▸ hq.ne_zero)
  have qP : ((q : ℕ) : 𝓞 E) ∈ P := hP.2.2.1 ▸ Ideal.absNorm_mem P
  have qQ : ((q : ℕ) : 𝓞 E) ∈ conjI P := hQ.2.2.1 ▸ Ideal.absNorm_mem _
  have := proj hfg
  have : Module.Finite (𝓞 E) 𝔛 := Module.Finite.iff_fg.mpr hfg
  have hrk := finrank_of_agree hA
  obtain ⟨A, e, hA1, he, hcount⟩ := exists_lines (M := 𝔛) P
  rw [cP, hrk] at hA1 hcount
  obtain ⟨-, hH⟩ := Hyper.count (M := 𝔛) (conjI P)
  rw [cQ, hrk, ← hA1] at hH
  have hH' : Nat.card (Hyp (conjI P) 𝔛) = A :=
    Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq.one_lt) hH
  have : Finite (Hyp (conjI P) 𝔛) := (Hyper.count (M := 𝔛) (conjI P)).1
  let ε := Finite.equivFinOfCardEq hH'
  obtain ⟨B, hB, hB1, hB2⟩ : ∃ B : Fin A → Submodule (𝓞 E) 𝔛, (∀ i, B i ∈ Hyp (conjI P) 𝔛) ∧
      Function.Injective B ∧ ∀ K ∈ Hyp (conjI P) 𝔛, ∃ i, B i = K :=
    ⟨fun i => (ε.symm i).1, fun i => (ε.symm i).2, Subtype.val_injective.comp ε.symm.injective,
      fun K hK => ⟨ε ⟨K, hK⟩, by simp⟩⟩
  choose η hη using fun i => Hyp.exists_not_mem (hB i)
  obtain ⟨ξ, hξ⟩ := exists_reps (M := 𝔛) P (B := q ^ N) (by rw [cP, hrk])
  obtain ⟨t, ht, d, hd, r, hr, edr⟩ := exists_pole P (ne_bot_of_norm hq hP.2.2.1)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hP.2.2.2.1
  obtain ⟨s, hs, hs1⟩ := exists_mult' hφ.pos.2 hP'.2.1 hA
  let XA : Fin A → Lt E N := fun i => 𝔛 ⊔ Submodule.span (𝓞 E) {t • (e i : Fin N → E)}
  let XB : Fin A → Lt E N := fun i => (B i).map 𝔛.subtype
  have mA : ∀ i v, v ∈ XA i ↔ ∃ y ∈ 𝔛, ∃ c : 𝓞 E, y + c • t • (e i : Fin N → E) = v := by
    intro i v
    simp only [XA, Submodule.mem_sup, Submodule.mem_span_singleton]
    exact ⟨fun ⟨y, hy, _, ⟨c, rfl⟩, h⟩ => ⟨y, hy, c, h⟩, fun ⟨y, hy, c, h⟩ => ⟨y, hy, _, ⟨c, rfl⟩, h⟩⟩
  have pA : ∀ i, ∀ c ∈ P, c • t • (e i : Fin N → E) ∈ 𝔛 := fun i c hc => by
    rw [osmul, smul_smul]
    exact 𝔛.smul_mem (⟨_, ht c hc⟩ : 𝓞 E) (e i).2
  have qB : ∀ i, ∀ v ∈ 𝔛, (q : E) • v ∈ XB i := fun i v hv =>
    ⟨_, Hyp.smul_mem (hB i) qQ ⟨v, hv⟩, rfl⟩
  have aA : ∀ i, Agree (R * M) 𝔛 (XA i) := fun i =>
    ⟨q, hq.pos, hP'.2.1, fun v hv => Submodule.mem_sup_left (Base.nat_smul_mem _ _ hv), fun v hv => by
      obtain ⟨y, hy, c, rfl⟩ := (mA i v).1 hv
      rw [smul_add, smul_comm (q : E) c]
      exact add_mem (Base.nat_smul_mem _ _ hy) (𝔛.smul_mem c (pA i _ qP))⟩
  have aB : ∀ i, Agree (R * M) 𝔛 (XB i) := fun i =>
    ⟨q, hq.pos, hP'.2.1, qB i, fun v hv => Base.nat_smul_mem _ _ (𝔛.map_subtype_le _ hv)⟩
  have aA' := fun i => agree_trans (agree_symm (aA i)) hA
  have aB' := fun i => agree_trans (agree_symm (aB i)) hA
  refine ⟨A, XA, XB, fun i j => sym ((R : E) • (η i : Fin N → E)) ((R : E) • ((b • ξ j : 𝔛) : Fin N → E)),
    hA1, fun i => ⟨fg_of_agree hfg (aA i), aA' i, gidx_of_le hA le_sup_left ?_,
      fg_of_agree hfg (aB i), aB' i, (gidx_of_le (aB' i) (𝔛.map_subtype_le _) ?_).symm,
      fun j => ccT_sym _ _⟩, fun Λ hΛ x => ?_⟩
  · rw [relIndex_eq]
    refine ((index_iff hq hP.2.2.1 _).2 (Hyper.exists_fun P _
      ⟨t • (e i : Fin N → E), Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
      (fun h => he i ((pole_smul_mem ht hd hr edr 𝔛 (e i)).1 h)) (pA i) fun v => ?_)).2
    obtain ⟨y, hy, c, h⟩ := (mA i v).1 v.2
    refine ⟨c, ?_⟩
    change (v : Fin N → E) - c • t • (e i : Fin N → E) ∈ 𝔛
    rwa [← h, add_sub_cancel_right]
  · rw [relIndex_eq, Submodule.comap_map_eq_of_injective 𝔛.injective_subtype]
    exact ((index_iff hq hQ.2.2.1 _).2 (hB i)).2
  have hS : SD Λ := hΛ.2.1
  obtain ⟨u, hu⟩ : ∃ u : 𝔛 →ₗ[𝓞 E] (Fin n → E), ∀ v, u v = (R : E) • (x *ᵥ v) :=
    ⟨(((R : E) • x).mulVecLin.restrictScalars (𝓞 E)) ∘ₗ 𝔛.subtype, fun v =>
      Matrix.smul_mulVec (R : E) x (v : Fin N → E)⟩
  have cX : ∀ L : Lt E n, (∀ v ∈ 𝔛, (R : E) • (x *ᵥ v) ∈ L) ↔ ∀ v, u v ∈ L := fun L => by
    simp only [hu, Subtype.forall]
  have sX : ∀ v ∈ stdL E N, (s : E) • v ∈ 𝔛 := fun v hv => by
    obtain ⟨w, hw, h⟩ := hs1 v hv
    rw [h]; exact Base.nat_smul_mem _ _ hw
  set c := φ Λ ((s : E) • x) with hc
  have e1 : ∑ i, twist R (XA i) φ Λ x = ({i | (∀ v, u v ∈ Λ) ∧ t • u (e i) ∈ Λ}.ncard : ℂ) * c := by
    refine sum_ite' _ _ _ fun i => ?_
    rw [twist_ite hφ (aA' i) hΛ x hs fun v hv => Submodule.mem_sup_left (sX v hv)]
    refine if_congr ⟨fun h => ⟨(cX Λ).1 fun v hv => h v (Submodule.mem_sup_left hv), ?_⟩,
      fun h v hv => ?_⟩ rfl rfl
    · have := h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rwa [Matrix.mulVec_smul, smul_comm, ← hu] at this
    · obtain ⟨y, hy, c, rfl⟩ := (mA i v).1 hv
      rw [Matrix.mulVec_add, smul_add, osmul, Matrix.mulVec_smul, Matrix.mulVec_smul,
        smul_comm (R : E) (c : E), smul_comm (R : E) t, ← hu]
      exact add_mem ((cX Λ).2 h.1 y hy) (Λ.smul_mem c h.2)
  have e2 : ∑ i, ∑ j, chiH Ψ (sym ((R : E) • (η i : Fin N → E))
      ((R : E) • ((b • ξ j : 𝔛) : Fin N → E))) x * twist R (XB i) φ Λ x =
      ({i | (∀ v ∈ B i, u v ∈ Λ) ∧ ∀ v, Int' (u (η i)) (u (b • v))}.ncard : ℂ) * (q ^ N * c) := by
    refine sum_ite' _ _ _ fun i => ?_
    rw [← Finset.sum_mul, twist_ite hφ (aB' i) hΛ x hs fun v hv => by
      obtain ⟨w, hw, h⟩ := hs1 v hv
      rw [h]; exact qB i w hw]
    have k : (∀ v ∈ XB i, (R : E) • (x *ᵥ v) ∈ Λ) ↔ ∀ v ∈ B i, u v ∈ Λ :=
      ⟨fun h v hv => hu v ▸ h _ ⟨v, hv, rfl⟩, fun h _ ⟨v, hv, e⟩ => e ▸ hu v ▸ h v hv⟩
    by_cases h : ∀ v ∈ B i, u v ∈ Λ
    · obtain ⟨k1, k2⟩ := pairChar_spec hP hS hb u (fun c hc v => h _ (Hyp.smul_mem (hB i) hc v)) (η i)
      have k3 : ∀ j, chiH Ψ (sym ((R : E) • (η i : Fin N → E))
          ((R : E) • ((b • ξ j : 𝔛) : Fin N → E))) x = pairChar u b (η i) (ξ j) := fun j => by
        rw [chiH_sym hΨ, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hu, ← hu]; rfl
      rw [if_pos (k.2 h), Finset.sum_congr rfl fun j _ => k3 j, hξ _ k1]
      by_cases h2 : ∀ v, Int' (u (η i)) (u (b • v))
      · rw [if_pos (k2.2 h2), if_pos ⟨h, h2⟩, Nat.cast_pow]
      · rw [if_neg (fun H => h2 (k2.1 H)), if_neg (fun H => h2 H.2), zero_mul]
    · rw [if_neg (fun H => h (k.1 H)), if_neg (fun H => h H.1), mul_zero]
  have e3 : ∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x =
      ({Λ' ∈ Nb M P Λ | ∀ v, u v ∈ Λ'}.ncard : ℂ) * c := by
    refine finsum_ite (nb_count hP hΛ).1 _ _ _ fun Λ' h' => ?_
    rw [twist_ite hφ hA h'.1 x hs sX]
    refine if_ctx_congr (cX Λ') (fun h => (hφ.loc Λ hΛ Λ' h'.1
      (agree_of_le hP hP'.2.1 hS h'.1.2.1 h'.2.1) _ (fun k => ?_)
      (TwistAdm.cols_of_cond sX ((cX Λ').2 h))).symm) fun _ => rfl
    obtain ⟨w, hw, h1⟩ := hs1 _ (TwistAdm.single_mem_std k)
    rw [TwistAdm.col_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h1,
      Matrix.mulVec_smul, smul_comm]
    exact smul_le_iff.1 (conj_le hS h'.1.2.1 h'.2.1) _ qQ _ ((cX Λ').2 h w hw)
  rw [e1, e2, e3, twist_ite hφ hA hΛ x hs sX]
  by_cases h : ∀ v, u v ∈ Λ
  · have := proj hΛ.1
    have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.1
    have k1 := hcount Λ (u.codRestrict Λ h)
    rw [finrank_eq hΛ, ← count_int hP hΛ u h] at k1
    have k2 : Nat.card {i // u.codRestrict Λ h (e i) ∈ (P • ⊤ : Submodule (𝓞 E) Λ)} =
        {i | (∀ v, u v ∈ Λ) ∧ t • u (e i) ∈ Λ}.ncard :=
      Nat.card_congr (Equiv.subtypeEquivRight fun i =>
        (pole_smul_mem ht hd hr edr Λ _).symm.trans (and_iff_right h).symm)
    have k3 : {i | (∀ v ∈ B i, u v ∈ Λ) ∧ ∀ v, Int' (u (η i)) (u (b • v))}.ncard = A := by
      rw [Set.eq_univ_of_forall (s := {i | (∀ v ∈ B i, u v ∈ Λ) ∧ _})
        fun i => ⟨fun v _ => h v, fun v => (hS _).1 (h _) _ (h _)⟩]
      simp [Set.ncard_univ]
    rw [k2] at k1
    rw [k3, if_pos ((cX Λ).2 h), ← hc]
    have k4 := congrArg (Nat.cast : ℕ → ℂ) k1
    have k5 := congrArg (Nat.cast : ℕ → ℂ) hA1
    push_cast [Nat.cast_sub hq.one_le, Nat.cast_sub (Nat.one_le_pow N q hq.pos)] at k4 k5
    linear_combination c * k4 + (q : ℂ) ^ N * c * k5
  · rw [count_pole hP hΛ ha hab u h B hB hB1 hB2 η hη, if_neg fun H => h ((cX Λ).1 H),
      Set.eq_empty_of_forall_notMem (s := {i | (∀ v, u v ∈ Λ) ∧ _}) fun i H => h H.1]
    simp only [Set.ncard_empty, Nat.cast_zero]
    ring
