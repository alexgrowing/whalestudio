import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil Matrix
open scoped TensorProduct

namespace GlobalTheory.SuppStage

section Abstract

variable {G G' X X' A : Type} [Group G] [Group G'] [AddCommGroup X] [Module ℂ X] [AddCommGroup X']
  [Module ℂ X']

def Flag (π : Representation ℂ G X) (L N : Set G) (ι : A → G) (χ : A → ℂ) : Prop :=
  ∃ S T : Submodule ℂ X, ¬ S ≤ T ∧ (∀ g ∈ L, ∀ x ∈ S, π g x ∈ S) ∧ (∀ g ∈ L, ∀ x ∈ T, π g x ∈ T) ∧
    (∀ u ∈ N, ∀ x, π u x - x ∈ T) ∧ ∀ z, ∀ x ∈ S, π (ι z) x - χ z • x ∈ T

theorem Flag.comap {π : Representation ℂ G X} {π' : Representation ℂ G' X'} {L N : Set G}
    {L' N' : Set G'} {ι : A → G} {ι' : A → G'} {χ : A → ℂ} (h : Flag π L N ι χ) (φ : X' →ₗ[ℂ] X)
    (hφ : Function.Surjective φ) (δ : A → ℂ)
    (hL : ∀ g' ∈ L', ∃ g ∈ L, ∃ c : ℂ, ∀ x, φ (π' g' x) = c • π g (φ x))
    (hN : ∀ u' ∈ N', ∃ u ∈ N, ∀ x, φ (π' u' x) = π u (φ x))
    (hι : ∀ z x, φ (π' (ι' z) x) = δ z • π (ι z) (φ x)) :
    Flag π' L' N' ι' fun z => δ z * χ z := by
  obtain ⟨S, T, h1, h2, h3, h4, h5⟩ := h
  refine ⟨S.comap φ, T.comap φ, fun h => h1 fun x hx => ?_, fun g' hg x hx => ?_, fun g' hg x hx => ?_,
    fun u' hu x => ?_, fun z x hx => ?_⟩
  · obtain ⟨y, rfl⟩ := hφ x
    exact h hx
  · obtain ⟨g, hg, c, hc⟩ := hL g' hg
    rw [Submodule.mem_comap, hc]
    exact S.smul_mem c (h2 g hg _ hx)
  · obtain ⟨g, hg, c, hc⟩ := hL g' hg
    rw [Submodule.mem_comap, hc]
    exact T.smul_mem c (h3 g hg _ hx)
  · obtain ⟨u, hu, hc⟩ := hN u' hu
    rw [Submodule.mem_comap, map_sub, hc]
    exact h4 u hu _
  · rw [Submodule.mem_comap, map_sub, hι, map_smul, mul_smul, ← smul_sub]
    exact T.smul_mem _ (h5 z _ hx)

theorem Flag.map {π : Representation ℂ G X} {π' : Representation ℂ G X'} {L : Set G} {Γ : Type} [Group Γ]
    (s : Γ →* G) (H : Subgroup Γ) {ι : A → G} {χ : A → ℂ} (h : Flag π L (s '' H) ι χ)
    (φ : π.IntertwiningMap π') (hφ : Function.Injective φ)
    (hL : ∀ g ∈ L, ∀ u ∈ H, ∃ u' ∈ H, g * s u = s u' * g)
    (hex : ∀ x, φ x ∈ twKer (π'.comp s) H 1 → x ∈ twKer (π.comp s) H 1) :
    Flag π' L (s '' H) ι χ := by
  obtain ⟨S, T, h1, h2, h3, h4, h5⟩ := h
  have hT : twKer (π.comp s) H 1 ≤ T := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    simpa using h4 _ ⟨u, u.2, rfl⟩ v)
  have hK : ∀ u ∈ H, ∀ x, π' (s u) x - x ∈ twKer (π'.comp s) H 1 := fun u hu x =>
    Submodule.subset_span ⟨⟨u, hu⟩, x, by simp⟩
  have hI : ∀ g x, φ.toLinearMap (π g x) = π' g (φ.toLinearMap x) := fun g x => φ.isIntertwining _ _ g x
  refine ⟨S.map φ.toLinearMap, T.map φ.toLinearMap ⊔ twKer (π'.comp s) H 1, fun h => h1 fun x hx => ?_,
    ?_, fun g hg => ?_, ?_, ?_⟩
  · obtain ⟨_, ⟨y, hy, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h ⟨x, hx, rfl⟩)
    have : φ (x - y) ∈ twKer (π'.comp s) H 1 := by
      have e' : φ x = φ y + w := e.symm
      rwa [map_sub, e', add_sub_cancel_left]
    simpa using add_mem (hT (hex _ this)) hy
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨_, h2 g hg x hx, hI g x⟩
  · show T.map φ.toLinearMap ⊔ twKer (π'.comp s) H 1 ≤
      Submodule.comap (π' g) (T.map φ.toLinearMap ⊔ twKer (π'.comp s) H 1)
    refine sup_le ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.mem_sup_left ⟨_, h3 g hg x hx, hI g x⟩
    · rintro _ ⟨u, v, rfl⟩
      obtain ⟨u', hu', e⟩ := hL g hg u u.2
      refine Submodule.mem_sup_right ?_
      have := hK u' hu' (π' g v)
      rw [← Module.End.mul_apply, ← map_mul, ← e, map_mul] at this
      simpa using this
  · rintro _ ⟨u, hu, rfl⟩ x
    exact Submodule.mem_sup_right (hK u hu x)
  · rintro z _ ⟨x, hx, rfl⟩
    exact Submodule.mem_sup_left ⟨_, h5 z x hx, by rw [map_sub, map_smul, hI]⟩

theorem Flag.piTensor {α : Type} [Fintype α] [DecidableEq α] {Γ Y : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (Y a))
    (hY : ∀ a, Nontrivial (Y a)) (a : α) {L N : Set (Γ a)} {ι : A → Γ a} {χ : A → ℂ}
    (h : Flag (ρ a) L N ι χ) :
    Flag (SmGL.piTensor ρ) {g | g a ∈ L} (MonoidHom.mulSingle Γ a '' N)
      (fun z => Pi.mulSingle a (ι z)) χ := by
  obtain ⟨S, T, h1, h2, h3, h4, h5⟩ := h
  let U : Submodule ℂ (Y a) → Submodule ℂ (⨂[ℂ] a, Y a) := fun S =>
    Submodule.span ℂ {y | ∃ x : ∀ b, Y b, x a ∈ S ∧ y = PiTensorProduct.tprod ℂ x}
  have hU : ∀ S : Submodule ℂ (Y a), (∀ g ∈ L, ∀ x ∈ S, ρ a g x ∈ S) →
      ∀ g ∈ {g : ∀ a, Γ a | g a ∈ L}, ∀ y ∈ U S, SmGL.piTensor ρ g y ∈ U S := by
    intro S hS g hg
    show U S ≤ Submodule.comap (SmGL.piTensor ρ g) (U S)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨_, hS _ hg _ hx, piTensor_tprod ρ g x⟩
  have key : ∀ (g : Γ a) (c : ℂ) (x : ∀ b, Y b), ρ a g (x a) - c • x a ∈ T →
      SmGL.piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) -
        c • PiTensorProduct.tprod ℂ x ∈ U T := by
    intro g c x hx
    refine Submodule.subset_span ⟨Function.update x a (ρ a g (x a) - c • x a), by simpa using hx, ?_⟩
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (ρ a g (x a)) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [piTensor_tprod, h1, MultilinearMap.map_update_sub, MultilinearMap.map_update_smul,
      Function.update_eq_self]
  refine ⟨U S, U T, fun h => h1 fun x₀ hx₀ => by_contra fun hT => ?_, hU S h2, hU T h3, ?_, fun z => ?_⟩
  · have h1 : ∀ a, ∃ (x : Y a) (l : Module.Dual ℂ (Y a)), l x = 1 := fun a => by
      obtain ⟨x, hx⟩ := exists_ne (0 : Y a)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
      exact ⟨x, l, hl⟩
    choose x l hl using h1
    obtain ⟨l₀, h0, h0'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hT inferInstance
    let F := PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap (Function.update l a l₀))
    have hF : U T ≤ LinearMap.ker F := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      have : l₀ (y a) = 0 := (Submodule.eq_bot_iff _).1 h0' _ ⟨_, hy, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, F, PiTensorProduct.lift.tprod,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simpa using this))
    have := hF (h (Submodule.subset_span ⟨Function.update x a x₀, by simpa using hx₀, rfl⟩))
    simp only [LinearMap.mem_ker, F, PiTensorProduct.lift.tprod,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at this
    obtain ⟨b, -, hb⟩ := Finset.prod_eq_zero_iff.1 this
    by_cases hba : b = a
    · subst hba
      exact h0 (by simpa using hb)
    · simp [Function.update_of_ne hba, hl] at hb
  · rintro _ ⟨u, hu, rfl⟩ y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, add_sub_add_comm]; exact add_mem hx hy
    | smul_tprod r x =>
      rw [map_smul, ← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      simpa using key u 1 x (by simpa using h4 u hu _)
  · show U S ≤ Submodule.comap (SmGL.piTensor ρ (Pi.mulSingle a (ι z)) - χ z • LinearMap.id) (U T)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact key _ _ x (h5 z _ hx)

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n V : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]

def blockScalar (e : (Σ a, m a) ≃ n) (a : α) (z : kˣ) : GL n k :=
  leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (m a) z))

theorem deltaHalf_mulSingle (a : α) (g : GL (m a) k) :
    deltaHalf k m (Pi.mulSingle a g) = absPow k ((modExp m a : ℂ) / 2) (GeneralLinearGroup.det g) := by
  rw [deltaHalf_apply, Finset.prod_eq_single a, Pi.mulSingle_eq_same]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  · simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_leviEmb_mulSingle (e : (Σ a, m a) ≃ n) (a : α) (g : GL (m a) k) :
    GeneralLinearGroup.det (leviEmb k e (Pi.mulSingle a g)) = GeneralLinearGroup.det g := by
  rw [det_leviEmb, Finset.prod_eq_single a, Pi.mulSingle_eq_same]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, map_one]
  · simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_blockScalar (e : (Σ a, m a) ≃ n) (a : α) (z : kˣ) :
    (blockScalar e a z : Matrix n n k) = diagonal fun i => if blk e i = a then (z : k) else 1 := by
  ext i j
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
  by_cases h : b = b'
  · subst h
    rw [blockScalar, leviEmb_apply_same]
    by_cases hb : b = a
    · subst hb
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · simp [Pi.mulSingle_eq_of_ne hb, diagonal_apply, hb, one_apply]
  · rw [blockScalar, leviEmb_apply_ne k e _ h, diagonal_apply_ne]
    intro h'
    exact h (congrArg Sigma.fst (e.injective h'))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_range_leviEmb {e : (Σ a, m a) ≃ n} {g : GL n k} :
    g ∈ Set.range (leviEmb k e) ↔ ∀ i j, blk e i ≠ blk e j → (g : Matrix n n k) i j = 0 := by
  constructor
  · rintro ⟨l, rfl⟩ i j h
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    exact leviEmb_apply_ne k e _ (by simpa using h) _ _
  · intro h
    refine ⟨leviProj k e ⟨g, mem_parab.2 fun i j hij => h i j hij.ne'⟩, ?_⟩
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      rfl
    · rw [leviEmb_apply_ne k e _ hb, h _ _ (by simpa using hb)]

theorem inSupport_iff {π : Representation ℂ (GL n k) V} {ψ : kˣ →* ℂˣ} :
    InSupport π ψ ↔ ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n) (a : Fin s), d a = 1 ∧
      Flag π (Set.range (leviEmb k e)) (unipRad k e) (blockScalar e a)
        fun z => (absPow k ((modExp (fun a => Fin (d a)) a : ℂ) / 2) z : ℂ) * ψ z := by
  refine exists₄_congr fun s d e a => and_congr_right fun ha => ⟨?_, ?_⟩
  · rintro ⟨Y, _, _, σ, hσ, ⟨S, φ, hφ⟩, hact⟩
    have h0 : Flag (jac e π) Set.univ {1}
        (fun z => Pi.mulSingle a (GeneralLinearGroup.scalar (Fin (d a)) z)) fun z => ψ z := by
      refine ⟨S.toSubmodule, (LinearMap.ker φ.toLinearMap).map S.toSubmodule.subtype, fun h => ?_,
        fun g _ x hx => S.apply_mem_toSubmodule g hx, ?_, ?_, fun z x hx => ?_⟩
      · have := Model.nontrivial_of_isIrreducible hσ
        obtain ⟨y, hy⟩ := exists_ne (0 : Y)
        obtain ⟨x, rfl⟩ := hφ y
        obtain ⟨x', hx', e'⟩ := h x.2
        obtain rfl : x' = x := Subtype.ext e'
        exact hy hx'
      · rintro g - _ ⟨x, hx, rfl⟩
        refine ⟨S.toRepresentation g x, ?_, rfl⟩
        have hx' : φ x = 0 := hx
        show φ _ = 0
        rw [φ.isIntertwining, hx', map_zero]
      · rintro _ rfl x
        simp
      · refine ⟨S.toRepresentation _ ⟨x, hx⟩ - (ψ z : ℂ) • ⟨x, hx⟩, ?_, rfl⟩
        show φ _ = 0
        rw [map_sub, map_smul, φ.isIntertwining, hact, ProdSupport.det_scalar_one ha, sub_self]
    refine h0.comap (Submodule.mkQ _) (Submodule.mkQ_surjective _) _ ?_ ?_ fun z x => ?_
    · rintro _ ⟨l, rfl⟩
      refine ⟨l, trivial, deltaHalf k _ l, fun x => ?_⟩
      simp only [Submodule.mkQ_apply]
      rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
    · intro u hu
      refine ⟨1, rfl, fun x => ?_⟩
      rw [map_one, Module.End.one_apply]
      exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu x)
    · simp only [Submodule.mkQ_apply]
      rw [jac_mk, smul_smul, deltaHalf_mulSingle, ProdSupport.det_scalar_one ha, Units.mul_inv, one_smul]
      rfl
  · rintro ⟨S, T, h1, h2, h3, h4, h5⟩
    have hT : twKer π (unipRad k e) 1 ≤ T := Submodule.span_le.2 (by
      rintro _ ⟨u, v, rfl⟩
      simpa using h4 _ u.2 v)
    let U : ∀ S : Submodule ℂ V, (∀ g ∈ Set.range (leviEmb k e), ∀ x ∈ S, π g x ∈ S) →
        Subrepresentation (jac e π) := fun S hS => ⟨S.map (Submodule.mkQ _), by
      rintro g _ ⟨x, hx, rfl⟩
      exact Submodule.smul_mem _ _ ⟨_, hS _ ⟨g, rfl⟩ x hx, rfl⟩⟩
    have hne : Nontrivial ((U S h2).toSubmodule ⧸
        (U T h3).toSubmodule.comap (U S h2).toSubmodule.subtype) := by
      refine Submodule.Quotient.nontrivial_iff.2 fun h => h1 fun x hx => ?_
      obtain ⟨y, hy, e'⟩ : (⟨_, x, hx, rfl⟩ : (U S h2).toSubmodule) ∈
        (U T h3).toSubmodule.comap (U S h2).toSubmodule.subtype := by rw [h]; trivial
      simpa using sub_mem hy (hT ((Submodule.Quotient.eq _).1 e'))
    obtain ⟨Y, _, _, σ, hσ, hsub⟩ :=
      IrrSubquot.exists_irreducible_subquotient _ _ (subQuot (U S h2) (U T h3)) hne
    refine ⟨Y, _, _, σ, hσ, hsub.trans ⟨U S h2, ⟨Submodule.mkQ _, fun _ => rfl⟩,
      Submodule.Quotient.mk_surjective _⟩, fun g => Model.scalar_of_isSubquotient hsub fun y => ?_⟩
    obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (Submodule.Quotient.eq _).2 ⟨_, T.smul_mem
      ((deltaHalf k _ (Pi.mulSingle (M := fun a => GL (Fin (d a)) k) a g))⁻¹ : ℂˣ)
      (h5 (GeneralLinearGroup.det g) x hx), ?_⟩
    show _ = jac e π _ (Submodule.Quotient.mk x) - _ • Submodule.Quotient.mk x
    rw [jac_mk, blockScalar, ← ProdSupport.eq_scalar_det ha, smul_sub, smul_smul, deltaHalf_mulSingle,
      Units.inv_mul_cancel_left, map_sub, map_smul, map_smul]
    rfl

end Local

section Refine

theorem exists_blk_eq {n : Type} [Fintype n] {S : ℕ} (w : n → Fin S) :
    ∃ (D : Fin S → ℕ) (E : (Σ a, Fin (D a)) ≃ n), ∀ i, blk E i = w i :=
  ⟨fun a => Fintype.card {i // w i = a},
    (Equiv.sigmaCongrRight fun _ => (Fintype.equivFin _).symm).trans (Equiv.sigmaFiberEquiv w),
    fun _ => rfl⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β n V : Type} {c : β → Type} [Fintype β] [LinearOrder β] [∀ a, Fintype (c a)]
  [∀ a, DecidableEq (c a)] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]

theorem inSupport_of_flag_jac (π : Representation ℂ (GL n k) V) (f : (Σ j, c j) ≃ n) (j₀ : β) {s : ℕ}
    {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ c j₀) (a : Fin s) (ha : d a = 1) (ψ : kˣ →* ℂˣ)
    (h : Flag (jac f π) {g | g j₀ ∈ Set.range (leviEmb k e)}
      (MonoidHom.mulSingle (fun j => GL (c j) k) j₀ '' unipRad k e)
      (fun z => Pi.mulSingle j₀ (blockScalar e a z))
      fun z => (absPow k ((modExp (fun a => Fin (d a)) a : ℂ) / 2) z : ℂ) * ψ z) : InSupport π ψ := by
  obtain ⟨t, ht0, ht⟩ : ∃ t : ∀ j, c j → Fin s, t j₀ = blk e ∧ ∀ j, j ≠ j₀ → ∀ x, t j x = a :=
    ⟨Function.update (fun _ _ => a) j₀ (blk e), by simp, fun j hj x => by simp [hj]⟩
  obtain ⟨S, o, hlt, heq⟩ : ∃ (S : ℕ) (o : β → Fin s → Fin S),
      (∀ j b j' b', o j b < o j' b' ↔ j < j' ∨ j = j' ∧ b < b') ∧
        ∀ j b j' b', o j b = o j' b' ↔ j = j' ∧ b = b' :=
    ⟨_, fun j b => (monoEquivOfFin (β ×ₗ Fin s) rfl).symm (toLex (j, b)),
      fun j b j' b' => (OrderIso.lt_iff_lt _).trans Prod.Lex.toLex_lt_toLex,
      fun j b j' b' => (EmbeddingLike.apply_eq_iff_eq _).trans (toLex_inj.trans Prod.ext_iff)⟩
  obtain ⟨D, E, hE⟩ := exists_blk_eq fun i => o (f.symm i).1 (t _ (f.symm i).2)
  replace hE : ∀ j x, blk E (f ⟨j, x⟩) = o j (t j x) := fun j x => by
    rw [hE, f.symm_apply_apply]
  have count : ∀ (P : Fin _ → Prop) [DecidablePred P] (Q : β → Prop) [DecidablePred Q]
      (R : Fin s → Prop) [DecidablePred R], ¬ Q j₀ →
      (∀ j b, j ≠ j₀ → (P (o j b) ↔ Q j)) → (∀ b, P (o j₀ b) ↔ R b) →
      ∑ b with P b, (Fintype.card (Fin (D b)) : ℤ) =
        ∑ j with Q j, (Fintype.card (c j) : ℤ) + ∑ b with R b, (Fintype.card (Fin (d b)) : ℤ) := by
    intro P _ Q _ R _ h0 h1 h2
    rw [EmptyBlocks.sum_card_blocks E, EmptyBlocks.sum_card_blocks e, Finset.sum_filter,
      Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀), ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀),
      if_neg h0, add_zero]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hE, h1 j _ (Finset.ne_of_mem_erase hj)]
      split_ifs <;> simp
    · simp only [hE, h2, ht0]
  have hD : D (o j₀ a) = 1 := by
    have := count (· = o j₀ a) (fun _ => False) (· = a) not_false
      (fun j b hj => by simp [heq, hj]) (fun b => by simp [heq])
    rw [Finset.filter_eq', if_pos (Finset.mem_univ _)] at this
    simpa [Finset.filter_eq', ha] using this
  have hmod : modExp (fun b => Fin (D b)) (o j₀ a) =
      modExp c j₀ + modExp (fun a => Fin (d a)) a := by
    unfold modExp
    rw [count _ (j₀ < ·) (a < ·) (lt_irrefl _)
        (fun j b hj => by simp [hlt, hj.symm])
        (fun b => by simp [hlt]),
      count _ (· < j₀) (· < a) (lt_irrefl _)
        (fun j b hj => by simp [hlt, hj])
        (fun b => by simp [hlt])]
    ring
  have hjac : ∀ g x, Submodule.mkQ _ (π (leviEmb k f g) x) =
      (deltaHalf k c g : ℂ) • jac f π g (Submodule.mkQ _ x) := fun g x => by
    simp only [Submodule.mkQ_apply]
    rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
  refine inSupport_iff.2 ⟨_, D, E, o j₀ a, hD, ?_⟩
  have h1 := h.comap (π' := π) (L' := Set.range (leviEmb k E)) (N' := unipRad k E)
    (ι' := blockScalar E (o j₀ a)) (Submodule.mkQ _) (Submodule.mkQ_surjective _)
    (fun z => absPow k ((modExp c j₀ : ℂ) / 2) z) ?_ ?_ ?_
  · convert h1 using 2 with z
    rw [hmod, Int.cast_add, add_div, absPow_add, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  · intro g hg
    rw [mem_range_leviEmb] at hg
    obtain ⟨l, rfl⟩ : g ∈ Set.range (leviEmb k f) := mem_range_leviEmb.2 fun i j hij => hg i j (by
      obtain ⟨⟨b, y⟩, rfl⟩ := f.surjective i
      obtain ⟨⟨b', y'⟩, rfl⟩ := f.surjective j
      have : b ≠ b' := by simpa using hij
      simp [hE, heq, this])
    refine ⟨l, mem_range_leviEmb.2 fun x y hxy => ?_, _, hjac l⟩
    rw [← leviEmb_apply_same k f]
    exact hg _ _ (by simp [hE, heq, ht0, hxy])
  · intro u hu
    replace hu := CuspMax.mem_unipRad_iff_entries.1 hu
    have hp : u ∈ parab k f := mem_parab_iff.2 fun b b' y y' hb => by
      rw [hu _ _ (by simp [hE, hlt, hb.le, hb.ne']), one_apply_ne]
      intro h'
      exact hb.ne' (congrArg Sigma.fst (f.injective h'))
    obtain ⟨v, hv, hdec⟩ := exists_levi_mul_unip k f ⟨u, hp⟩
    have hdec' : u = leviEmb k f (leviProj k f ⟨u, hp⟩) * v := hdec
    have h0 : leviProj k f ⟨u, hp⟩ j₀ ∈ unipRad k e :=
      CuspMax.mem_unipRad_iff_entries.2 fun x y hxy => by
        rw [leviProj_apply, hu _ _ (by simpa [hE, hlt, ht0] using hxy)]
        simp [one_apply]
    have h1 : leviProj k f ⟨u, hp⟩ = Pi.mulSingle j₀ (leviProj k f ⟨u, hp⟩ j₀) := by
      funext j
      by_cases hj : j = j₀
      · subst hj
        simp
      · rw [Pi.mulSingle_eq_of_ne hj]
        ext x y
        rw [leviProj_apply, hu _ _ (by simp [hE, hlt, ht j hj])]
        simp [one_apply]
    refine ⟨_, ⟨_, h0, rfl⟩, fun x => ?_⟩
    have h2 : Submodule.mkQ (twKer π (unipRad k f) 1) (π v x) = Submodule.mkQ _ x :=
      (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hv x)
    conv_lhs => rw [hdec', map_mul, Module.End.mul_apply, hjac, h2, h1, deltaHalf_mulSingle,
      det_eq_one_of_mem_unipRad k h0, map_one, Units.val_one, one_smul]
    rfl
  · intro z x
    have h1 : blockScalar E (o j₀ a) z = leviEmb k f (Pi.mulSingle j₀ (blockScalar e a z)) := by
      ext i j
      obtain ⟨⟨b, y⟩, rfl⟩ := f.surjective i
      obtain ⟨⟨b', y'⟩, rfl⟩ := f.surjective j
      rw [val_blockScalar]
      by_cases hb : b = b'
      · subst hb
        rw [leviEmb_apply_same]
        by_cases hj : b = j₀
        · subst hj
          simp [val_blockScalar, diagonal_apply, hE, heq, ht0]
        · simp [Pi.mulSingle_eq_of_ne hj, diagonal_apply, hE, heq, hj, one_apply]
      · rw [leviEmb_apply_ne k f _ hb, diagonal_apply_ne]
        intro h'
        exact hb (congrArg Sigma.fst (f.injective h'))
    rw [h1, hjac, deltaHalf_mulSingle, blockScalar, det_leviEmb_mulSingle, ProdSupport.det_scalar_one ha]

theorem inSupport_of_factor {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (f : (Σ j, c j) ≃ n)
    {Y : β → Type} [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)]
    (σ : ∀ j, Representation ℂ (GL (c j) k) (Y j)) (hY : ∀ j, Nontrivial (Y j))
    (hsub : IsSubquotient (piTensor σ) (jac f π)) (j₀ : β) {ψ : kˣ →* ℂˣ} (h : InSupport (σ j₀) ψ) :
    InSupport π ψ := by
  obtain ⟨s, d, e, a, ha, h⟩ := inSupport_iff.1 h
  obtain ⟨S, φ, hφ⟩ := hsub
  have h1 := (h.piTensor σ hY j₀).comap (π' := S.toRepresentation) φ.toLinearMap hφ (fun _ => 1)
    (fun g hg => ⟨g, hg, 1, fun x => (φ.isIntertwining _ _ g x).trans (one_smul _ _).symm⟩)
    (fun g hg => ⟨g, hg, fun x => φ.isIntertwining _ _ g x⟩)
    (fun z x => (φ.isIntertwining _ _ _ x).trans (one_smul _ _).symm)
  simp only [one_mul] at h1
  let ι : S.toRepresentation.IntertwiningMap (jac f π) := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine inSupport_of_flag_jac π f j₀ e a ha ψ
    (h1.map (MonoidHom.mulSingle (fun j => GL (c j) k) j₀) (unipRad k e) ι Subtype.val_injective ?_ ?_)
  · rintro g ⟨l, hl⟩ u hu
    refine ⟨g j₀ * u * (g j₀)⁻¹,
      hl ▸ (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e l) u).1 hu, funext fun j => ?_⟩
    by_cases hj : j = j₀
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  · intro x hx
    have hinj := JacInj.jacMap_injective k _ _ _ e _ _ _ _
      (compMap ι (MonoidHom.mulSingle (fun j => GL (c j) k) j₀))
      (isSmooth_comp (isSmooth_jac f hπ) _
        (continuous_mulSingle (A := fun j => GL (c j) k) j₀)) Subtype.val_injective
    exact (Submodule.Quotient.mk_eq_zero _).1 ((injective_iff_map_eq_zero _).1 hinj
      (Submodule.Quotient.mk x) ((Submodule.Quotient.mk_eq_zero _).2 hx))

end Refine

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ)
      (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) k) V) (β : Type)
      [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r)
      (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (j₀ : β) (ψ : kˣ →* ℂˣ), IsSmooth ρ →
      IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ) → InSupport (s j₀).ρ ψ → InSupport ρ ψ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f s j₀ _ hρ hsub h =>
    inSupport_of_factor hρ f (fun j => (s j).ρ) (fun j => Model.nontrivial_of_isIrreducible (s j).irr)
      hsub j₀ h

end GlobalTheory.SuppStage
