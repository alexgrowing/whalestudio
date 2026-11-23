import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowersStatement

noncomputable section

open Formalism.MainNotions.DIV.Cons (intO)
open TensorProduct Coalgebra WithConv

namespace GlobalTheory.GroupLikeDerivation

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {M : Type} [AddCommGroup M] [Module ↥(intO C) M]

theorem norm_smul_le (o : ↥(intO C)) (x : C) : ‖o • x‖ ≤ ‖x‖ := by
  have ho : ‖(o : C)‖ ≤ 1 := o.2
  change ‖(o : C) * x‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ho

theorem norm_le_of_mem_span (f : M →ₗ[↥(intO C)] C) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span ↥(intO C) s) : ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx => rw [map_smul]; exact (norm_smul_le _ _).trans hx

theorem bddAbove_norm [Module.Finite ↥(intO C) M] (f : M →ₗ[↥(intO C)] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ↥(intO C)) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supNorm (f : WithConv (M →ₗ[↥(intO C)] C)) : ℝ := ⨆ m, ‖f.ofConv m‖

theorem le_supNorm [Module.Finite ↥(intO C) M] (f : WithConv (M →ₗ[↥(intO C)] C)) (m : M) :
    ‖f.ofConv m‖ ≤ supNorm f := le_ciSup (bddAbove_norm f.ofConv) m

theorem supNorm_le {f : WithConv (M →ₗ[↥(intO C)] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supNorm f ≤ r := ciSup_le h

theorem supNorm_nonneg (f : WithConv (M →ₗ[↥(intO C)] C)) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem supNorm_smul (c : C) (f : WithConv (M →ₗ[↥(intO C)] C)) :
    supNorm (c • f) = ‖c‖ * supNorm f := by
  rw [supNorm, supNorm, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl

theorem supNorm_add_le [Module.Finite ↥(intO C) M] (f g : WithConv (M →ₗ[↥(intO C)] C)) :
    supNorm (f + g) ≤ max (supNorm f) (supNorm g) :=
  supNorm_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supNorm f m) (le_supNorm g m))

theorem supNorm_mul_le [Module.Finite ↥(intO C) M] [Coalgebra ↥(intO C) M]
    (f g : WithConv (M →ₗ[↥(intO C)] C)) : supNorm (f * g) ≤ supNorm f * supNorm g := by
  refine supNorm_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary ↥(intO C) m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supNorm f _) (le_supNorm g _) (norm_nonneg _) (supNorm_nonneg _)

theorem supNorm_le_of_tmul {f : WithConv (M ⊗[↥(intO C)] M →ₗ[↥(intO C)] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supNorm f ≤ r := by
  refine supNorm_le fun t => ?_
  induction t with
  | zero => simpa using hr
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem supNorm_eq_mul [Module.Finite ↥(intO C) M] (f g : WithConv (M →ₗ[↥(intO C)] C))
    (h : WithConv (M ⊗[↥(intO C)] M →ₗ[↥(intO C)] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supNorm h = supNorm f * supNorm g := by
  apply le_antisymm
  · refine supNorm_le_of_tmul (mul_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supNorm f _) (le_supNorm g _) (norm_nonneg _) (supNorm_nonneg _)
  · rw [supNorm.eq_1 f, Real.iSup_mul_of_nonneg (supNorm_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supNorm.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supNorm h _

theorem exists_supNorm_pow_le [Module.Finite ↥(intO C) M] [Coalgebra ↥(intO C) M]
    [IsCocomm ↥(intO C) M] {y : WithConv (M →ₗ[↥(intO C)] C)} (hy : IsIntegral ↥(intO C) y) :
    ∃ K : ℝ, ∀ k : ℕ, supNorm (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supNorm f, fun k => supNorm_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span ↥(intO C) (s : Set (WithConv (M →ₗ[↥(intO C)] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[↥(intO C)] C) →ₗ[↥(intO C)] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span ev (Finset.sum_nonneg fun _ _ => supNorm_nonneg _)
    (fun f hf => (le_supNorm f m).trans
      (Finset.single_le_sum (f := fun f => supNorm f) (fun _ _ => supNorm_nonneg _) hf)) hk

end Norm

section Conv

variable {R C A : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing A] [Bialgebra R A]

def extProd (f g : WithConv (A →ₗ[R] C)) : WithConv (A ⊗[R] A →ₗ[R] C) :=
  toConv ((Algebra.TensorProduct.lmul' R (S := C)).toLinearMap ∘ₗ TensorProduct.map f.ofConv g.ofConv)

@[simp] theorem extProd_tmul (f g : WithConv (A →ₗ[R] C)) (a b : A) :
    (extProd f g).ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b := by
  simp [extProd]

theorem extProd_mul (f g h k : WithConv (A →ₗ[R] C)) :
    extProd f g * extProd h k = extProd (f * h) (g * k) := by
  have h1 := TensorProduct.map_convMul_map (f := f) (h := h) (g := g) (k := k)
  have h2 := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R (S := C))
    (toConv (TensorProduct.map f.ofConv g.ofConv)) (toConv (TensorProduct.map h.ofConv k.ofConv))
  rw [h1] at h2
  exact (congrArg toConv h2).symm

theorem tensor_ext {f g : WithConv (A ⊗[R] A →ₗ[R] C)}
    (h : ∀ a b, f.ofConv (a ⊗ₜ b) = g.ofConv (a ⊗ₜ b)) : f = g :=
  WithConv.ext (TensorProduct.ext' h)

theorem extProd_one : extProd (1 : WithConv (A →ₗ[R] C)) 1 = 1 :=
  tensor_ext fun a b => by simp [mul_comm]

variable (R C A) in

def inlHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd f 1
      map_add' := fun f g => tensor_ext fun a b => by simp [add_mul]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_assoc] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in

def inrHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd 1 f
      map_add' := fun f g => tensor_ext fun a b => by simp [mul_add]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_left_comm] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in

def mulHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv (f.ofConv ∘ₗ (Bialgebra.mulCoalgHom R A).toLinearMap)
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
    (tensor_ext fun a b => by simp [mul_comm])
    fun f g => congrArg toConv (LinearMap.convMul_comp_coalgHom_distrib f g _)

variable (R C A) in

def extendHom : WithConv (A →ₗ[R] R) →ₐ[R] WithConv (A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv ((Algebra.ofId R C).toLinearMap ∘ₗ f.ofConv)
      map_add' := fun f g => WithConv.ext (LinearMap.ext fun a => by simp)
      map_smul' := fun c f => WithConv.ext (LinearMap.ext fun a =>
        map_smul (Algebra.ofId R C).toLinearMap c (f.ofConv a)) }
    (WithConv.ext (LinearMap.ext fun a => by simp))
    fun f g => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ f g)

theorem inlHom_mul_inrHom (f g : WithConv (A →ₗ[R] C)) :
    inlHom R C A f * inrHom R C A g = extProd f g := by
  change extProd f 1 * extProd 1 g = _
  rw [extProd_mul, mul_one, one_mul]

end Conv

theorem exists_isGroupLikeElem {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] (χ : CartierDual R A →ₐ[R] R) :
    ∃ u : A, IsGroupLikeElem R u ∧ ∀ φ : CartierDual R A, φ.ofConv u = χ φ := by
  have h : ∀ φ : CartierDual R A,
      φ.ofConv ((CartierDual.bidual R A).symm (toConv χ.toLinearMap)) = χ φ :=
    fun φ => CartierDual.apply_bidual_symm _ φ
  refine ⟨_, (CartierDual.isGroupLikeElem_iff_mul _).2 ⟨?_, fun φ ψ => ?_⟩, h⟩
  · rw [h]; exact map_one χ
  · rw [h, h, h]; exact map_mul χ φ ψ

theorem dvd_iff_norm {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {q : ↥(intO C)} (hq : q ≠ 0) (x : ↥(intO C)) : q ∣ x ↔ ‖(q : C)⁻¹ * (x : C)‖ ≤ 1 := by
  have hq' : (q : C) ≠ 0 := fun h => hq (Subtype.ext h)
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subring.coe_mul, inv_mul_cancel_left₀ hq']
    exact z.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul]
    exact (mul_inv_cancel_left₀ hq' _).symm

theorem dvd_mul_of_groupLike (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A]
    [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)) (hq : q ≠ 0)
    (D : A →ₗ[↥(intO C)] ↥(intO C))
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b -
      Coalgebra.counit (R := ↥(intO C)) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u)
    (c : ↥(intO C)) (hc : ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  set y : WithConv (A →ₗ[↥(intO C)] C) := (q : C)⁻¹ • extendHom ↥(intO C) C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (q : C)⁻¹ * (D a : C) := fun _ => rfl
  have hint : IsIntegral ↥(intO C) y :=
    GlobalTheory.T.isIntegral_of_divisible_characters C (CartierDual ↥(intO C) A) _ (extendHom ↥(intO C) C A) (toConv D) q hq
      fun χ => by
        obtain ⟨u, h1, h2⟩ := exists_isGroupLikeElem χ
        rw [← h2]
        exact hu u h1
  have key := GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers C p hp _ _ supNorm supNorm (mulHom ↥(intO C) C A)
    (inlHom ↥(intO C) C A) (inrHom ↥(intO C) C A) supNorm_smul supNorm_smul supNorm_nonneg
    supNorm_nonneg supNorm_add_le supNorm_mul_le
    (fun f => supNorm_le fun t => le_supNorm f _)
    (fun f g => supNorm_eq_mul f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supNorm_pow_le hint)
    (supNorm_le_of_tmul zero_le_one fun a b => by
      have h := (dvd_iff_norm hq _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      change _ - _ * ((counit (R := ↥(intO C)) b : ↥(intO C)) : C) -
        ((counit (R := ↥(intO C)) a : ↥(intO C)) : C) * _ = _
      push_cast
      ring)
    c hc
  rw [dvd_iff_norm hq]
  have h : (q : C)⁻¹ * ((c * D a : ↥(intO C)) : C) = ((c : C) • y).ofConv a := by
    change _ = (c : C) * y.ofConv a
    rw [hya]
    push_cast
    ring
  rw [h]
  exact (le_supNorm _ a).trans key

end GlobalTheory.GroupLikeDerivation
