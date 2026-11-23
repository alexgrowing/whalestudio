import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZDerivJac

namespace GlobalTheory.RgGu.Nup2

theorem exists_injective_of_tensor {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (i : α)
    (hi : (ρ i).IsIrreducible) {D : Type} [AddCommGroup D] [Module ℂ D] (R : Representation ℂ (Γ i) D)
    (φ : PiTensorProduct ℂ X →ₗ[ℂ] D) (hφ : ∀ g x, φ (piTensor ρ (Pi.mulSingle i g) x) = R g (φ x)) (hne : φ ≠ 0) :
    ∃ f : (ρ i).IntertwiningMap R, Function.Injective f := by
  have hx : ∃ x : ∀ a, X a, φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using h x))
  obtain ⟨x, hx⟩ := hx
  let ℓ : X i →ₗ[ℂ] D := φ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
  have hℓ : ∀ w, ℓ w = φ (PiTensorProduct.tprod ℂ (Function.update x i w)) := fun w => rfl
  let f : (ρ i).IntertwiningMap R := ⟨ℓ, fun g => LinearMap.ext fun w => by
    show ℓ (ρ i g w) = R g (ℓ w)
    rw [hℓ, hℓ, ← hφ, piTensor_tprod]
    congr 2
    funext a
    by_cases h : a = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]⟩
  refine ⟨f, ?_⟩
  haveI := hi
  rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · exfalso
    apply hx
    have e := congrArg (fun F : (ρ i).IntertwiningMap R => F (x i)) h
    have e2 : f (x i) = φ (PiTensorProduct.tprod ℂ x) := by
      show ℓ (x i) = _
      rw [hℓ, Function.update_eq_self]
    rw [← e2]
    exact e

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem exists_irr_sub_of_quot (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n t : ℕ} {X D : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup D] [Module ℂ D] (T : Representation ℂ (Levi k fun a => Fin (dd n t a)) X)
    (hs : IsSmooth T) (hT : HasFiniteLength T) (R : Representation ℂ (GL (Fin n) k) D) (L : X →ₗ[ℂ] D)
    (hL : ∀ g x, L ((T.comp (iota n t) : Representation ℂ (GL (Fin n) k) X) g x) = R g (L x)) (hne : L ≠ 0) :
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap R), Function.Injective f := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded T).1 hT
  let P : Set (Subrepresentation T) := {B | ∃ x ∈ B, L x ≠ 0}
  have hP : P.Nonempty := by
    by_contra h
    apply hne
    ext x
    by_contra hx
    exact h ⟨⊤, x, trivial, hx⟩
  obtain ⟨B, ⟨x0, hx0B, hx0⟩, hBmin⟩ := wellFounded_lt.has_min P hP
  have hbot : ⊥ < B := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    subst h
    have : x0 = 0 := (Submodule.mem_bot ℂ).1 hx0B
    exact hx0 (by rw [this, map_zero])
  obtain ⟨C, hCB, hCmax⟩ := wellFounded_gt.has_min {C : Subrepresentation T | C < B} ⟨⊥, hbot⟩
  have hcov : C ⋖ B := ⟨hCB, fun E hCE hEB => hCmax E hEB hCE⟩
  have hCker : ∀ x ∈ C, L x = 0 := by
    intro x hx
    by_contra h
    exact hBmin C ⟨x, hx, h⟩ hCB
  let K := C.toSubmodule.comap B.toSubmodule.subtype
  let φ : (B.toSubmodule ⧸ K) →ₗ[ℂ] D := K.liftQ (L ∘ₗ B.toSubmodule.subtype) (fun y hy => hCker y.1 hy)
  have hφ : ∀ y : B.toSubmodule, φ (Submodule.Quotient.mk y) = L y.1 := fun y => rfl
  have hZi : (subQuot B C).IsIrreducible := isIrreducible_subQuot hcov
  have hZsq : IsSubquotient (subQuot B C) T :=
    ⟨B, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  have hZs : IsSmooth (subQuot B C) := hZsq.isSmooth hs
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (dd n t) (⟨_, subQuot B C, hZs, hZi⟩ : IrrRep _)
  let φ' := φ ∘ₗ E.symm.toIntertwiningMap.toLinearMap
  have hq : ∀ (g : GL (Fin (dd n t 0)) k) z, φ (subQuot B C (Pi.mulSingle 0 g) z) = R g (φ z) := by
    intro g z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact hL g y.1
  have hφ'rel : ∀ (g : GL (Fin (dd n t 0)) k) x,
      φ' ((piTensor fun a => (σ a).rep.ρ) (Pi.mulSingle 0 g) x) = R g (φ' x) := by
    intro g x
    have hE := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' (Pi.mulSingle 0 g)) x
    exact (congrArg φ hE).trans (hq g _)
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    apply hx0
    have e := LinearMap.congr_fun h0 (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩))
    have e2 : E.symm.toIntertwiningMap (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) =
        Submodule.Quotient.mk ⟨x0, hx0B⟩ := E.toLinearEquiv.symm_apply_apply _
    have e3 : φ' (E.toIntertwiningMap (Submodule.Quotient.mk ⟨x0, hx0B⟩)) = L x0 := by
      show φ (E.symm.toIntertwiningMap _) = _
      rw [e2]
      rfl
    rw [← e3]
    exact e
  obtain ⟨f, hf⟩ := exists_injective_of_tensor (fun a => (σ a).rep.ρ) (0 : Fin 2) (σ 0).rep.irr
    (R := R) φ' hφ'rel hφ'ne
  refine ⟨(σ 0).rep, f, hf⟩

set_option maxHeartbeats 1000000 in

theorem jac_deriv_rel (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    ∃ L : Jacquet π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) →ₗ[ℂ]
        TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1,
      Function.Surjective L ∧ ∀ g x,
        L (((jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) :
          Representation ℂ (GL (Fin n) k) _) g x) =
        twist (GlobalTheory.BZMir.deriv k ψ j π) (detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))) g (L x) := by
  obtain ⟨L, hL, hLe⟩ := exists_jac_deriv ψ n j π
  refine ⟨L, hL, fun g x => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [twist_apply]
  have h1 := congrArg (fun c : ℂˣ => (c : ℂ) • GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v)))
    (delta_mulSingle n j g)
  refine Eq.trans ?_ h1
  have h2 := hLe g v
  have h3 : (jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) g (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun a => Fin (dd n (j + 1) a))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ : ℂˣ) : ℂ) •
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v) :=
    jac_mk _ π _ v
  rw [h3, map_smul, h2]

set_option maxHeartbeats 1000000 in

theorem derivSub (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : GlobalTheory.BZSeg.DerivSub k := by
  intro ψ n j V _ _ π hs hf hnt
  have hχ : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2)))) :=
    (isSmoothChar_absPow _).detChar
  have hχi : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹ := by
    unfold IsSmoothChar at hχ ⊢
    convert hχ using 2
    ext g
    simp [MonoidHom.mem_ker]
  obtain ⟨L, hL, hLe⟩ := jac_deriv_rel ψ (n + 1) j π
  have hne : L ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1)
    obtain ⟨x, rfl⟩ := hL y
    exact hy (by rw [h0, LinearMap.zero_apply])
  obtain ⟨S0, f, hf'⟩ := exists_irr_sub_of_quot hA _ (isSmooth_jac _ hs)
    (GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ _ V π hs hf) _ L hLe hne
  refine ⟨⟨S0.V, twist S0.ρ (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))⁻¹,
    isSmooth_twist S0.smooth hχi, isIrreducible_twist S0.irr _⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf'⟩
  ext w
  have e := LinearMap.congr_fun (f.isIntertwining' g) w
  simp only [LinearMap.coe_comp, Function.comp_apply, twist_apply] at e ⊢
  rw [map_smul, e, smul_smul]
  simp

theorem derivSub_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivSub k :=
  fun _ _ _ _ _ hA => derivSub hA

end GlobalTheory.RgGu.Nup2

end
