import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem detjac_tprod_ne_zero {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (y : ∀ a, X a) (hy : ∀ a, y a ≠ 0) : PiTensorProduct.tprod ℂ y ≠ 0 := by
  have hφ : ∀ b, ∃ φ : X b →ₗ[ℂ] ℂ, φ (y b) ≠ 0 := fun b => by
    by_contra! h
    exact hy b ((Module.forall_dual_apply_eq_zero_iff ℂ (y b)).1 h)
  choose φ hφ using hφ
  intro h
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap φ)) h
  rw [PiTensorProduct.lift.tprod, map_zero] at h1
  exact Finset.prod_ne_zero_iff.2 (fun b _ => hφ b) (by simpa using h1)

private theorem detjac_scalar_factor {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hX : ∀ a, Nontrivial (X a)) (j : α) (g : Γ j) (c : ℂ)
    (h : ∀ w, piTensor ρ (Pi.mulSingle j g) w = c • w) (v : X j) : ρ j g v = c • v := by
  choose x hx using fun a => exists_ne (0 : X a)
  have h1 := h (PiTensorProduct.tprod ℂ (Function.update x j v))
  have h2 : (fun a => ρ a ((Pi.mulSingle j g : ∀ a, Γ a) a) (Function.update x j v a)) =
      Function.update x j (ρ j g v) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · simp [Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha]
  rw [piTensor_tprod, h2, ← MultilinearMap.map_update_smul, ← sub_eq_zero, ← MultilinearMap.map_update_sub] at h1
  by_contra hne
  refine detjac_tprod_ne_zero _ (fun a => ?_) h1
  by_cases ha : a = j
  · subst ha; simpa [sub_eq_zero] using hne
  · simpa [Function.update_of_ne ha] using hx a

private theorem detjac_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : jhMult σ ρ ≠ 0) :
    IsSubquotient σ ρ := by
  by_contra hn
  refine h ?_
  simp only [jhMult, ENat.iSup_eq_zero]
  rintro r ⟨S, T, -, -, h3⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rfl
  obtain ⟨φ⟩ := h3 ⟨0, hr⟩
  refine absurd ?_ hn
  refine (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans ?_
  exact ⟨S ⟨0, hr⟩, ⟨Submodule.mkQ _, fun g => rfl⟩, Submodule.mkQ_surjective _⟩

private theorem detjac_equiv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    (hi : π.IsIrreducible) (ψ : G →* ℂˣ) (h : ∀ g v, π g v = (ψ g : ℂ) • v) : Nonempty ((ofChar ψ).Equiv π) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let f : (ofChar ψ).IntertwiningMap π := ⟨LinearMap.toSpanSingleton ℂ V x, fun g => LinearMap.ext fun c => by
    simp [h, smul_smul]⟩
  have hinj : Function.Injective f := smul_left_injective ℂ hx
  refine ⟨equivOfBijective f ⟨hinj, ?_⟩⟩
  rcases eq_bot_or_eq_top f.range with h0 | h0
  · have : x ∈ f.range := ⟨1, one_smul _ _⟩
    rw [h0] at this
    exact absurd this hx
  · intro v
    have : v ∈ f.range := by rw [h0]; trivial
    exact this

theorem UpperTheory.Lit.Mix.detjac :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = t), 0 < (q 0).1 → jm q hq (detRep (Fin t) χ) ≠ 0 → ∃ A : Multiset (IrrGL k), HasSupport (q 0).rep A ∧ (IrrGL.ofChar χ hχ).nu (-((t : ℂ) - 1) / 2) ∈ A := by
  intro k _ _ _ _ t χ hχ q hq hpos hj
  have hsub := detjac_isSubquotient hj
  have hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  have hm : modExp (fun i : Fin 2 => Fin (q i).1) 0 = (q 1).1 := by
    have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
    simp [modExp, h1]
  have hc : χ * absPow k (-(modExp (fun i : Fin 2 => Fin (q i).1) 0 : ℂ) / 2) =
      (χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2) := by
    rw [mul_assoc, ← absPow_add, hm, ← hq, Fin.sum_univ_two]
    congr 2
    push_cast
    ring
  have hact : ∀ g v, (q 0).rep g v = ((detChar (Fin (q 0).1)
      ((χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2))) g : ℂ) • v := by
    intro g v
    refine detjac_scalar_factor (fun a => (q a).rep)
      (fun a => Model.nontrivial_of_isIrreducible (q a).2.rep.irr) 0 g _ (fun w => ?_) v
    rw [Model.scalar_of_isSubquotient hsub (Model.jac_detRep _ χ _) w, detLevi_apply, Fin.prod_univ_two,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), map_one, map_one, mul_one, hc, detChar_apply]
  obtain ⟨φ⟩ := detjac_equiv (q 0).2.rep.irr _ hact
  refine ⟨_, (hasSupport_detRep hχ' hpos).of_equiv φ, ?_⟩
  refine Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, hpos, ?_⟩)
  rw [Nat.cast_zero, IrrGL.nu_zero, IrrGL.nu, IrrGL.tw_ofChar]
  rfl
