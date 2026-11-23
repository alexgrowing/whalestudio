import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationCentralCharacterIsolateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetMirabolicInductionCharacterStatement
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.LeftEndJacquet

theorem scalar_comm {k : Type} [Field k] (ϖ : kˣ) (g : GL (Fin 1) k) :
    g * GeneralLinearGroup.scalar (Fin 1) ϖ = GeneralLinearGroup.scalar (Fin 1) ϖ * g := by
  ext i j
  simp [Matrix.mul_apply, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, mul_comm]

theorem ext_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π' : Representation ℂ (GL m k) V) (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (y : ℂ ⊗[ℂ] V) :
    extTensor (detRep (Fin 1) ξ) π' (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) y = (ξ ϖ : ℂ) • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul c v =>
    rw [extTensor_tmul]
    simp [detRep, detChar, TensorProduct.smul_tmul']

theorem isIrreducible_of_injective : ∀ {K V W : Type} [Group K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ K V) (π₂ : Representation ℂ K W) [Nontrivial V], π₂.IsIrreducible →
    ∀ (φ : π₁.IntertwiningMap π₂), Function.Injective φ → π₁.IsIrreducible := by
  intro K V W _ _ _ _ _ π₁ π₂ _ h φ hφ
  haveI : IsSimpleOrder (Subrepresentation π₂) := h
  have hbt : (⊥ : Subrepresentation π₁) ≠ ⊤ := by
    intro hb
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation π₁).toSubmodule := Submodule.mem_top
    rw [← hb] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun U => ?_ }
  let I : Subrepresentation π₂ := ⟨U.toSubmodule.map φ.toLinearMap, by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨π₁ g u, U.apply_mem_toSubmodule g hu, by simp [φ.isIntertwining]⟩⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)
    have : φ u ∈ I.toSubmodule := ⟨u, hu, rfl⟩
    rw [hI] at this
    have h0 : φ u = 0 := (Submodule.mem_bot ℂ).1 this
    exact (Submodule.mem_bot ℂ).2 (hφ (h0.trans (map_zero φ).symm))
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
    have : φ v ∈ I.toSubmodule := by rw [hI]; exact Submodule.mem_top
    obtain ⟨u, hu, huv⟩ := this
    have := hφ huv
    rw [← this]
    exact hu

theorem aeval_jac₂_eq_zero_of_surjective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m a b : Type} [Fintype m] [DecidableEq m] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (π' : Representation ℂ (GL m k) V) (τ : Representation ℂ (GL m k) Y) (f : π'.IntertwiningMap τ),
    Function.Surjective f → ∀ (e' : a ⊕ b ≃ m) (g : GL a k × GL b k) (q : Polynomial ℂ),
    Polynomial.aeval (jac₂ e' π' g) q = 0 → Polynomial.aeval (jac₂ e' τ g) q = 0 := by
  intro k _ _ _ _ m a b _ _ _ _ _ _ V Y _ _ _ _ π' τ f hf e' g q hq
  let J := jacMap (two e') f
  have hJ : ∀ x, J (jac₂ e' π' g x) = jac₂ e' τ g (J x) := fun x => LinearMap.congr_fun (J.isIntertwining' _) x
  have hpow : ∀ (i : ℕ) x, J (((jac₂ e' π' g) ^ i) x) = ((jac₂ e' τ g) ^ i) (J x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hJ]
  have hcomm : ∀ (r : Polynomial ℂ) x, J (Polynomial.aeval (jac₂ e' π' g) r x) = Polynomial.aeval (jac₂ e' τ g) r (J x) := by
    intro r x
    induction r using Polynomial.induction_on' with
    | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
    | monomial i c =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow]
  refine LinearMap.ext fun y => ?_
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  have h1 : (Submodule.Quotient.mk (f v) : Jacquet τ (unipRad k (two e'))) = J (Submodule.Quotient.mk v) := rfl
  rw [h1, ← hcomm, hq]
  simp

theorem exists_injective_of_extTensor : ∀ {H K V W : Type} [Group H] [Group K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ψ : Representation ℂ H ℂ) (π₁ : Representation ℂ K V) (π₂ : Representation ℂ K W)
    (φ : (extTensor ψ π₁).IntertwiningMap (extTensor ψ π₂)), Function.Injective φ →
    ∃ φ' : π₁.IntertwiningMap π₂, Function.Injective φ' := by
  intro H K V W _ _ _ _ _ _ ψ π₁ π₂ φ hφ
  let L1 := TensorProduct.lid ℂ V
  let L2 := TensorProduct.lid ℂ W
  let f : V →ₗ[ℂ] W := L2.toLinearMap ∘ₗ φ.toLinearMap ∘ₗ L1.symm.toLinearMap
  have key2 : ∀ (g : K) (y : ℂ ⊗[ℂ] W), L2 (extTensor ψ π₂ (1, g) y) = π₂ g (L2 y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul c w => simp [extTensor_tmul, L2]
  have key1 : ∀ (g : K) (v : V), extTensor ψ π₁ (1, g) (L1.symm v) = L1.symm (π₁ g v) := by
    intro g v
    simp [extTensor_tmul, L1]
  refine ⟨⟨f, fun g => LinearMap.ext fun v => ?_⟩, ?_⟩
  · show L2 (φ (L1.symm (π₁ g v))) = π₂ g (L2 (φ (L1.symm v)))
    rw [← key1, ← key2]
    congr 1
    exact LinearMap.congr_fun (φ.isIntertwining' (1, g)) (L1.symm v)
  · exact L2.injective.comp (hφ.comp L1.symm.injective)

theorem exists_injective_of_eigen : ∀ {G V V₂ X X₂ : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X₂] [Module ℂ X₂]
    (ρ : Representation ℂ G V) (ρ₂ : Representation ℂ G V₂) (σ : Representation ℂ G X)
    (σ₂ : Representation ℂ G X₂) (z : G), (∀ g, g * z = z * g) → ∀ (a : ℂ) (p : ρ.IntertwiningMap σ),
    (∀ y, ∃ v, ρ z v = a • v ∧ p v = y) → (∀ v, ρ z v = a • v → p v = 0 → v = 0) →
    ∀ (ι : ρ.IntertwiningMap ρ₂), Function.Injective ι → ∀ (p₂ : ρ₂.IntertwiningMap σ₂),
    (∀ v, ρ₂ z v = a • v → p₂ v = 0 → v = 0) → ∃ φ : σ.IntertwiningMap σ₂, Function.Injective φ := by
  intro G V V₂ X X₂ _ _ _ _ _ _ _ _ _ ρ ρ₂ σ σ₂ z hz a p hp hpi ι hι p₂ hp₂
  have pint : ∀ g v, p (ρ g v) = σ g (p v) := fun g v => LinearMap.congr_fun (p.isIntertwining' g) v
  have iint : ∀ g v, ι (ρ g v) = ρ₂ g (ι v) := fun g v => LinearMap.congr_fun (ι.isIntertwining' g) v
  have p2int : ∀ g v, p₂ (ρ₂ g v) = σ₂ g (p₂ v) := fun g v => LinearMap.congr_fun (p₂.isIntertwining' g) v
  let s : X → V := fun y => Classical.choose (hp y)
  have hs1 : ∀ y, ρ z (s y) = a • s y := fun y => (Classical.choose_spec (hp y)).1
  have hs2 : ∀ y, p (s y) = y := fun y => (Classical.choose_spec (hp y)).2
  have uniq : ∀ y v, ρ z v = a • v → p v = y → s y = v := by
    intro y v hv hpv
    have h := hpi (s y - v) (by rw [map_sub, hs1, hv, smul_sub]) (by rw [map_sub, hs2, hpv, sub_self])
    exact sub_eq_zero.1 h
  let sL : X →ₗ[ℂ] V :=
    { toFun := s
      map_add' := fun x y => (uniq (x + y) (s x + s y) (by rw [map_add, hs1, hs1, smul_add])
        (by rw [map_add, hs2, hs2])).trans rfl
      map_smul' := fun c x => uniq (c • x) (c • s x) (by rw [map_smul, hs1, smul_comm])
        (by rw [map_smul, hs2]) }
  have sint : ∀ g y, s (σ g y) = ρ g (s y) := by
    intro g y
    refine uniq _ _ ?_ (by rw [pint, hs2])
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hs1, map_smul]
  let F : X →ₗ[ℂ] X₂ := p₂.toLinearMap ∘ₗ ι.toLinearMap ∘ₗ sL
  refine ⟨⟨F, fun g => LinearMap.ext fun y => ?_⟩, fun y y' hyy => ?_⟩
  · show p₂ (ι (s (σ g y))) = σ₂ g (p₂ (ι (s y)))
    rw [sint, iint, p2int]
  · have hF : ∀ y, F y = p₂ (ι (s y)) := fun y => rfl
    have h0 : F (y - y') = 0 := by rw [map_sub, sub_eq_zero]; exact hyy
    have he : ρ₂ z (ι (s (y - y'))) = a • ι (s (y - y')) := by rw [← iint, hs1, map_smul]
    have h1 := hp₂ _ he (by rw [← hF]; exact h0)
    have h2 : s (y - y') = 0 := hι (h1.trans (map_zero ι).symm)
    have h3 : y - y' = 0 := by rw [← hs2 (y - y'), h2, map_zero]
    exact sub_eq_zero.1 h3

theorem exists_injective_ind₂ : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ⊕ b ≃ n) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL a k × GL b k) W), IsSmooth π → π.IsIrreducible →
    ∀ (p : (jac₂ e π).IntertwiningMap σ), (∃ v, p v ≠ 0) →
    ∃ φ : π.IntertwiningMap (ind₂ e σ), Function.Injective φ := by
  intro k _ _ _ _ n a b _ _ _ _ _ _ e V W _ _ _ _ π σ hπ hirr p hp
  let σ' := σ.comp (leviTwo k a b).symm.toMonoidHom
  let p' : (jac (two e) π).IntertwiningMap σ' :=
    ⟨p.toLinearMap, fun h => by
      have := p.isIntertwining' ((leviTwo k a b).symm h)
      simpa [jac₂, σ'] using this⟩
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective (two e) hπ σ').2 p'
  haveI := hirr
  refine ⟨f, (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 => ?_⟩
  obtain ⟨v, hv⟩ := hp
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  apply hv
  have h1 : p (Submodule.Quotient.mk w) = (Model.evalOne (two e) f) (Submodule.Quotient.mk w) := by
    rw [hf]; rfl
  rw [h1, h0]
  rfl

theorem isIrreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : Fin 1 ⊕ m ≃ n) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Nontrivial V'] (π : Representation ℂ (GL n k) V) (π' : Representation ℂ (GL m k) V') (hπ : IsSmooth π) (hirr : π.IsIrreducible) (hπ' : IsSmooth π') (hfl : HasFiniteLength π') (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (ϖ : kˣ) (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e π)) (hS : Monotone S) (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N) (φ : (subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) ξ) π')) (hother : ∀ t, t ≠ t₀ → ∃ c : ℂ, c ≠ (ξ ϖ : ℂ) ∧ ∀ w ∈ (S t.succ).toSubmodule, jac₂ e π (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) w - c • w ∈ (S t.castSucc).toSubmodule) (hii : ∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' π' (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0), π'.IsIrreducible := by
  intro k _ _ _ _ hG n m _ _ _ _ e V V' _ _ _ _ _ π π' hπ hirr hπ' hfl ξ hξ ϖ N S hS h0 hN t₀ φ hother hii
  have hzc : ∀ g : GL (Fin 1) k × GL m k,
      g * (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) = (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) * g :=
    fun g => Prod.ext (scalar_comm ϖ g.1) (by simp)
  have hoth : ∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ ∀ w ∈ (S t.succ).toSubmodule,
      Polynomial.aeval (jac₂ e π (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q w ∈
        (S t.castSucc).toSubmodule := by
    intro t ht
    obtain ⟨c, hc, hw⟩ := hother t ht
    refine ⟨Polynomial.X - Polynomial.C c, by simpa [sub_eq_zero] using hc.symm, fun w hw' => ?_⟩
    simpa [Module.algebraMap_end_apply] using hw w hw'
  obtain ⟨p, hpsurj, hpinj⟩ := GlobalTheory.T.filtration_central_character_isolate (jac₂ e π) (extTensor (detRep (Fin 1) ξ) π') N S hS h0 hN
    _ hzc t₀ (ξ ϖ) ⟨φ⟩ (ext_scalar π' ξ ϖ) hoth
  obtain ⟨Y, _, _, τ, hτs, hτirr, qτ, hqτ⟩ :=
    IrrQuot.exists_irreducible_smooth_quotient π' hπ' hfl inferInstance
  haveI : Nontrivial Y := Model.nontrivial_of_isIrreducible hτirr
  let T : (extTensor (detRep (Fin 1) ξ) π').IntertwiningMap (extTensor (detRep (Fin 1) ξ) τ) :=
    ⟨TensorProduct.map LinearMap.id qτ.toLinearMap, fun g => by
      apply TensorProduct.ext'
      intro x y
      simp [extTensor_tmul, qτ.isIntertwining]⟩
  have hT : Function.Surjective T := TensorProduct.map_surjective Function.surjective_id hqτ
  obtain ⟨y, hy⟩ := exists_ne (0 : ℂ ⊗[ℂ] Y)
  obtain ⟨x, rfl⟩ := hT y
  obtain ⟨v, -, rfl⟩ := hpsurj x
  obtain ⟨ι₀, hι₀⟩ := exists_injective_ind₂ e π (extTensor (detRep (Fin 1) ξ) τ) hπ hirr (T.comp p) ⟨v, hy⟩
  let ι : (jac₂ e π).IntertwiningMap (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ))) :=
    ⟨(jacMap (two e) ι₀).toLinearMap, fun g => (jacMap (two e) ι₀).isIntertwining' _⟩
  have hι : Function.Injective ι :=
    JacInj.jacMap_injective k Bool n _ (two e) V _ π _ ι₀ (isSmooth_parInd _ _) hι₀
  have hkill : ∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ,
      q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' τ (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0 := by
    intro m' _ _ e'
    obtain ⟨q, hq, hq0⟩ := hii m' e'
    exact ⟨q, hq, aeval_jac₂_eq_zero_of_surjective π' τ qτ hqτ e' _ q hq0⟩
  obtain ⟨N₂, S₂, hS₂, h0₂, hN₂, t₂, ⟨φ₂⟩, hoth₂⟩ := GlobalTheory.T.jacquet_mirabolic_induction_character hG e τ hτs ξ hξ ϖ hkill
  obtain ⟨p₂, -, hp₂⟩ := GlobalTheory.T.filtration_central_character_isolate _ (extTensor (detRep (Fin 1) ξ) τ) N₂ S₂ hS₂ h0₂ hN₂
    _ hzc t₂ (ξ ϖ) ⟨φ₂⟩ (ext_scalar τ ξ ϖ) hoth₂
  obtain ⟨ψ, hψ⟩ := exists_injective_of_eigen _ _ _ _ _ hzc (ξ ϖ) p hpsurj hpinj ι hι p₂ hp₂
  obtain ⟨ψ', hψ'⟩ := exists_injective_of_extTensor _ π' τ ψ hψ
  exact isIrreducible_of_injective π' τ hτirr ψ' hψ'

end GlobalTheory.LeftEndJacquet
