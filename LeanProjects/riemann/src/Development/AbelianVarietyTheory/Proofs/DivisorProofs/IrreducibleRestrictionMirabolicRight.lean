import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.RightEnd

open Polynomial

section Abstract

variable {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem map_aeval (f : V →ₗ[ℂ] Y) (z : Module.End ℂ V) (z' : Module.End ℂ Y)
    (h : ∀ v, f (z v) = z' (f v)) (q : ℂ[X]) (v : V) : f (aeval z q v) = aeval z' q (f v) := by
  induction q using Polynomial.induction_on generalizing v with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval z'), Module.End.mul_apply,
      Module.End.mul_apply, ih, aeval_X, aeval_X, h]

theorem aeval_eigen (z : Module.End ℂ V) (c : ℂ) (v : V) (h : z v = c • v) (q : ℂ[X]) :
    aeval z q v = q.eval c • v :=
  Module.End.aeval_apply_of_mem_apply_eq_smul h

theorem chain (z : Module.End ℂ V) (c : ℂ) (N : ℕ) (S : Fin (N + 1) → Submodule ℂ V) (i : ℕ) :
    ∀ (d : ℕ) (h : i + d < N + 1), (∀ t : Fin N, i ≤ t → t < i + d →
      ∃ q : ℂ[X], q.eval c ≠ 0 ∧ ∀ w ∈ S t.succ, aeval z q w ∈ S t.castSucc) →
      ∃ q : ℂ[X], q.eval c ≠ 0 ∧ ∀ w ∈ S ⟨i + d, h⟩, aeval z q w ∈ S ⟨i, by omega⟩ := by
  intro d
  induction d with
  | zero => exact fun h _ => ⟨1, by simp, fun w hw => by simpa using hw⟩
  | succ d ih =>
    intro h H
    obtain ⟨q, hq, hq'⟩ := ih (by omega) fun t h1 h2 => H t h1 (by omega)
    obtain ⟨p, hp, hp'⟩ := H ⟨i + d, by omega⟩ (by simp) (by simp)
    refine ⟨q * p, by simp [hq, hp], fun w hw => ?_⟩
    rw [map_mul, Module.End.mul_apply]
    exact hq' _ (hp' w hw)

theorem chain_ends (z : Module.End ℂ V) (c : ℂ) (N : ℕ) (S : Fin (N + 1) → Submodule ℂ V)
    (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N)
    (H : ∀ t, t ≠ t₀ → ∃ q : ℂ[X], q.eval c ≠ 0 ∧ ∀ w ∈ S t.succ, aeval z q w ∈ S t.castSucc) :
    (∃ q : ℂ[X], q.eval c ≠ 0 ∧ ∀ w ∈ S t₀.castSucc, aeval z q w = 0) ∧
      ∃ q : ℂ[X], q.eval c ≠ 0 ∧ ∀ w, aeval z q w ∈ S t₀.succ := by
  have := t₀.2
  constructor
  · obtain ⟨q, hq, hq'⟩ := chain z c N S 0 t₀ (by omega) fun t _ h2 =>
      H t (by rintro rfl; omega)
    refine ⟨q, hq, fun w hw => ?_⟩
    have h1 := hq' w (by convert hw using 2; ext; simp)
    have h2 : aeval z q w ∈ S 0 := h1
    rwa [h0] at h2
  · obtain ⟨q, hq, hq'⟩ := chain z c N S (t₀ + 1) (N - (t₀ + 1)) (by omega) fun t h1 _ =>
      H t (by rintro rfl; omega)
    refine ⟨q, hq, fun w => hq' w ?_⟩
    have : (⟨t₀ + 1 + (N - (t₀ + 1)), by omega⟩ : Fin (N + 1)) = Fin.last N := by
      ext; simp
    rw [this, hN]; trivial

theorem split_step {ρ : Representation ℂ G V} {σ : Representation ℂ G Y} (B A : Subrepresentation ρ)
    (φ : (subQuot B A).Equiv σ) (z : G) (hz : ∀ g, g * z = z * g) (c : ℂ) (hσ : ∀ y, σ z y = c • y)
    (q₁ q₂ : ℂ[X]) (h₁ : q₁.eval c ≠ 0) (h₂ : q₂.eval c ≠ 0)
    (k₁ : ∀ w ∈ A.toSubmodule, aeval (ρ z) q₁ w = 0) (k₂ : ∀ w, aeval (ρ z) q₂ w ∈ B.toSubmodule) :
    (∃ p : V →ₗ[ℂ] Y, (∀ g v, p (ρ g v) = σ g (p v)) ∧ Function.Surjective p) ∧
      ∃ s : Y →ₗ[ℂ] V, (∀ g y, s (σ g y) = ρ g (s y)) ∧ Function.Injective s := by
  let r : B.toSubmodule →ₗ[ℂ] Y := φ.toLinearEquiv.toLinearMap ∘ₗ Submodule.mkQ _
  have hr : ∀ g b, r (B.toRepresentation g b) = σ g (r b) := fun g b =>
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (Submodule.Quotient.mk b)
  have hrs : Function.Surjective r := φ.toLinearEquiv.surjective.comp (Submodule.mkQ_surjective _)
  have hr0 : ∀ b, r b = 0 → (b : V) ∈ A.toSubmodule := fun b hb =>
    (Submodule.Quotient.mk_eq_zero (A.toSubmodule.comap B.toSubmodule.subtype)).1
      ((map_eq_zero_iff _ φ.toLinearEquiv.injective).1 hb)
  clear_value r
  have hval : ∀ q (b : B.toSubmodule), ((aeval (B.toRepresentation z) q b : B.toSubmodule) : V) =
      aeval (ρ z) q b := fun q b => map_aeval B.toSubmodule.subtype _ _ (fun _ => rfl) q b
  have hra : ∀ q b, r (aeval (B.toRepresentation z) q b) = q.eval c • r b := fun q b => by
    rw [map_aeval r _ _ (hr z), aeval_eigen _ c _ (hσ _)]
  have hcomm : ∀ g q v, ρ g (aeval (ρ z) q v) = aeval (ρ z) q (ρ g v) := fun g q v =>
    map_aeval (ρ g) _ _ (fun v => by
      rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]) q v
  constructor
  · refine ⟨r ∘ₗ LinearMap.codRestrict _ (aeval (ρ z) q₂) k₂, fun g v => ?_, fun y => ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hr]
      congr 1
      exact Subtype.ext (hcomm g q₂ v).symm
    · obtain ⟨b, hb⟩ := hrs ((q₂.eval c)⁻¹ • y)
      refine ⟨b, ?_⟩
      have : LinearMap.codRestrict _ (aeval (ρ z) q₂) k₂ b = aeval (B.toRepresentation z) q₂ b :=
        Subtype.ext (hval q₂ b).symm
      rw [LinearMap.comp_apply, this, hra, hb, smul_inv_smul₀ h₂]
  · obtain ⟨r', hr'⟩ := r.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hrs)
    have hr'' : ∀ y, r (r' y) = y := fun y => LinearMap.congr_fun hr' y
    let s : Y →ₗ[ℂ] V := aeval (ρ z) q₁ ∘ₗ B.toSubmodule.subtype ∘ₗ r'
    have hs : ∀ b, s (r b) = aeval (ρ z) q₁ b := fun b => by
      have := k₁ _ (hr0 (r' (r b) - b) (by rw [map_sub, hr'', sub_self]))
      rw [Submodule.coe_sub, map_sub, sub_eq_zero] at this
      exact this
    refine ⟨s, fun g y => ?_, (injective_iff_map_eq_zero _).2 fun y hy => ?_⟩
    · obtain ⟨b, rfl⟩ := hrs y
      rw [← hr, hs, hs, hcomm]
      rfl
    · obtain ⟨b, rfl⟩ := hrs y
      rw [hs, ← hval] at hy
      have h3 := hra q₁ b
      rw [show aeval (B.toRepresentation z) q₁ b = 0 from Subtype.ext hy, map_zero] at h3
      exact (smul_eq_zero.1 h3.symm).resolve_left h₁

theorem step_killed {ρ : Representation ℂ G V} {σ : Representation ℂ G Y} (B A : Subrepresentation ρ)
    (φ : (subQuot B A).Equiv σ) (z : G) (q : ℂ[X]) (h : aeval (σ z) q = 0) :
    ∀ w ∈ B.toSubmodule, aeval (ρ z) q w ∈ A.toSubmodule := by
  intro w hw
  have h4 := map_aeval (φ.toLinearEquiv.toLinearMap ∘ₗ Submodule.mkQ _) (B.toRepresentation z) _
    (fun v => Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap _
      (Submodule.Quotient.mk v)) q ⟨w, hw⟩
  rw [h, LinearMap.zero_apply] at h4
  have h5 := (Submodule.Quotient.mk_eq_zero (A.toSubmodule.comap B.toSubmodule.subtype)).1
    ((map_eq_zero_iff _ φ.toLinearEquiv.injective).1 h4)
  have h6 := map_aeval B.toSubmodule.subtype (B.toRepresentation z) (ρ z) (fun _ => rfl) q ⟨w, hw⟩
  rw [Submodule.mem_comap, h6] at h5
  exact h5

theorem aeval_smInd [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (σ : Representation ℂ P V)
    (z : P) (hz : ∀ y : G, y * z = z * y) (q : ℂ[X]) (h : aeval (σ z) q = 0) :
    aeval (smInd P σ z) q = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (Subtype.ext (funext fun l => ?_))
  let ev : smoothPart (ind P σ) →ₗ[ℂ] V :=
    { toFun := fun x => x.1.1 l
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have := map_aeval ev (smInd P σ z) (σ z) (fun y => by
    show y.1.1 (l * z) = _
    rw [hz]
    exact y.1.2 z l) q x
  rw [h] at this
  exact this

theorem embed_of_equiv {U : Type} [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G Y} {τ : Representation ℂ G U} (φ : ρ.Equiv σ)
    (h : ∃ E : Y →ₗ[ℂ] U, Function.Injective E ∧ ∀ l x, E (σ l x) = τ l (E x)) :
    ∃ E : V →ₗ[ℂ] U, Function.Injective E ∧ ∀ l x, E (ρ l x) = τ l (E x) := by
  obtain ⟨E, hE, hE'⟩ := h
  refine ⟨E ∘ₗ φ.toLinearEquiv.toLinearMap, hE.comp φ.toLinearEquiv.injective, fun l x => ?_⟩
  show E (φ.toIntertwiningMap (ρ l x)) = τ l (E (φ.toIntertwiningMap x))
  rw [Representation.IntertwiningMap.isIntertwining, hE']

theorem embed_step {ρ : Representation ℂ G V} (B A : Subrepresentation ρ)
    (z : G) (c : ℂ) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j) (hz : ∀ y, ρ z (j y) = c • j y)
    (q₁ q₂ : ℂ[X]) (h₁ : q₁.eval c ≠ 0) (h₂ : q₂.eval c ≠ 0)
    (k₁ : ∀ w ∈ A.toSubmodule, aeval (ρ z) q₁ w = 0) (k₂ : ∀ w, aeval (ρ z) q₂ w ∈ B.toSubmodule) :
    ∃ j' : Y →ₗ[ℂ] (B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype),
      Function.Injective j' ∧ ∀ g y y', j y' = ρ g (j y) → j' y' = subQuot B A g (j' y) := by
  have hB : ∀ y, j y ∈ B.toSubmodule := fun y => by
    have := k₂ (j y)
    rw [aeval_eigen _ c _ (hz y)] at this
    exact (B.toSubmodule.smul_mem_iff h₂).1 this
  refine ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ j hB,
    (injective_iff_map_eq_zero _).2 fun y hy => ?_, fun g y y' h => ?_⟩
  · have h3 := k₁ (j y)
      ((Submodule.Quotient.mk_eq_zero (A.toSubmodule.comap B.toSubmodule.subtype)).1 hy)
    rw [aeval_eigen _ c _ (hz y)] at h3
    exact (map_eq_zero_iff _ hj).1 ((smul_eq_zero.1 h3).resolve_left h₁)
  · exact congrArg Submodule.Quotient.mk (Subtype.ext h)

theorem isIrreducible_of_embed {ρ : Representation ℂ G V} (M : Subrepresentation ρ) (hM : IsCoatom M)
    (F : V →ₗ[ℂ] V ⧸ M.toSubmodule) (hF : Function.Injective F)
    (hi : ∀ g v, F (ρ g v) = ρ.quotient M.toSubmodule (fun g _ hv => M.apply_mem_toSubmodule g hv) g (F v)) :
    ρ.IsIrreducible := by
  have : Nontrivial (Subrepresentation ρ) := ⟨M, ⊤, hM.1⟩
  refine ⟨fun U => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  let T : Subrepresentation ρ := ⟨(U.toSubmodule.map F).comap M.toSubmodule.mkQ, by
    rintro g v ⟨u, hu, h⟩
    refine ⟨ρ g u, U.apply_mem_toSubmodule g hu, ?_⟩
    rw [hi, h]
    rfl⟩
  have hMT : M < T := by
    refine lt_of_le_of_ne (fun v hv => ?_) fun h => hU ?_
    · have hv' : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
      show M.toSubmodule.mkQ v ∈ U.toSubmodule.map F
      rw [hv']; exact zero_mem _
    · refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)
      obtain ⟨v, hv⟩ := M.toSubmodule.mkQ_surjective (F u)
      have h1 : v ∈ T.toSubmodule := ⟨u, hu, hv.symm⟩
      rw [← h] at h1
      have hv' : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
      exact (map_eq_zero_iff _ hF).1 (hv.symm.trans hv')
  have hT := hM.2 T hMT
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨w, hw⟩ := M.toSubmodule.mkQ_surjective (F v)
  have h1 : w ∈ T.toSubmodule := by rw [hT]; trivial
  obtain ⟨u, hu, h⟩ := h1
  rw [hF (hw.symm.trans h.symm)]
  exact hu

theorem exists_coatom {ρ : Representation ℂ G V} [Nontrivial V] (h : HasFiniteLength ρ) :
    ∃ M : Subrepresentation ρ, IsCoatom M := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have hN := (isFiniteLength_iff_isNoetherian_isArtinian.1 h).1
  have : IsCoatomic (Subrepresentation ρ) := φ.isCoatomic_iff.2 inferInstance
  refine ((eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left fun hb => ?_).imp
    fun _ h => h.1
  exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule hb)

end Abstract

section Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {X X' : β → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, Fintype (X' j)] [∀ j, DecidableEq (X' j)]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem deltaHalf_single (a₀ : β) (h0 : ∀ j, j ≠ a₀ → IsEmpty (X j)) (g : Levi k X) :
    deltaHalf k X g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha
    have hs : ∀ s : Finset β, a ∉ s → ∑ b ∈ s, (Fintype.card (X b) : ℤ) = 0 := fun s hs =>
      Finset.sum_eq_zero fun b hb => by
        have := h0 b fun e => hs (e ▸ hb)
        simp
    have hm : modExp X a = 0 := by
      unfold modExp
      rw [hs _ (by simp), hs _ (by simp), sub_zero]
    rw [hm]
    simp
  · haveI := h0 a ha
    rw [Subsingleton.elim (g a) 1, map_one, map_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β]
  [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in

theorem mem_parab_single (e : (Σ j, X j) ≃ n) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → IsEmpty (X j))
    (x : GL n k) : x ∈ parab k e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · exact (h0 b fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab).elim j
  · exact (h0 a ha).elim i

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem eq_one_single (e : (Σ j, X j) ≃ n) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → IsEmpty (X j))
    {g : GL n k} (hg : g ∈ unipRad k e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact (h0 b hb).elim j
  · exact (h0 a ha).elim i

def sigmaSingle {β : Type} [DecidableEq β] {X : β → Type} (a₀ : β) (h0 : ∀ j, j ≠ a₀ → IsEmpty (X j)) :
    (Σ j, X j) ≃ X a₀ :=
  (Equiv.ofBijective (Sigma.mk a₀) ⟨sigma_mk_injective, by
    rintro ⟨a, i⟩
    by_cases ha : a = a₀
    · subst ha; exact ⟨i, rfl⟩
    · exact (h0 a ha).elim i⟩).symm

theorem sigmaSingle_mk {β : Type} [DecidableEq β] {X : β → Type} (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → IsEmpty (X j)) (i : X a₀) : sigmaSingle a₀ h0 ⟨a₀, i⟩ = i :=
  (sigmaSingle a₀ h0).apply_symm_apply i

def scalars (X : β → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (s : β → kˣ) : Levi k X :=
  fun j => GeneralLinearGroup.scalar (X j) (s j)

theorem aeval_jac_eq_zero (e : (Σ j, X j) ≃ n) (f : (Σ j, X' j) ≃ n) (κ : ∀ j, X j ≃ X' j)
    (h : ∀ a i, e ⟨a, i⟩ = f ⟨a, κ a i⟩) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (p : V →ₗ[ℂ] W) (hp : ∀ g v, p (π g v) = τ g (p v))
    (hs : Function.Surjective p) (s : β → kˣ) (q : ℂ[X])
    (hq : aeval (jac e π (scalars X s)) q = 0) : aeval (jac f τ (scalars X' s)) q = 0 := by
  have hu : unipRad k e ≤ unipRad k f := fun u hu => by
    obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j hab => ?_, fun a i j => ?_⟩
    · obtain ⟨i, rfl⟩ := (κ a).surjective i
      obtain ⟨j, rfl⟩ := (κ b).surjective j
      rw [← h, ← h]
      exact mem_parab_iff.1 h1 a b i j hab
    · obtain ⟨i, rfl⟩ := (κ a).surjective i
      obtain ⟨j, rfl⟩ := (κ a).surjective j
      rw [← h, ← h, h2]
      simp [Matrix.one_apply]
  have hl : leviEmb k e (scalars X s) = leviEmb k f (scalars X' s) := by
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, h, h, leviEmb_apply_same]
      simp [scalars, GeneralLinearGroup.scalar, Matrix.diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hab, h, h, leviEmb_apply_ne _ _ _ hab]
  have hd : deltaHalf k X (scalars X s) = deltaHalf k X' (scalars X' s) := by
    rw [deltaHalf_apply, deltaHalf_apply]
    refine Finset.prod_congr rfl fun a _ => ?_
    have h1 : modExp X a = modExp X' a := by
      simp only [modExp, fun b => Fintype.card_congr (κ b)]
    have h2 : GeneralLinearGroup.det (scalars X s a) = GeneralLinearGroup.det (scalars X' s a) := by
      ext; simp [scalars, GeneralLinearGroup.scalar, Fintype.card_congr (κ a)]
    rw [h1, h2]
  let Θ : Jacquet π (unipRad k e) →ₗ[ℂ] Jacquet τ (unipRad k f) :=
    Submodule.mapQ _ _ p (Submodule.span_le.2 (by
      rintro _ ⟨u, v, rfl⟩
      exact Submodule.subset_span ⟨⟨u, hu u.2⟩, p v, by simp [hp]⟩))
  have hΘ : ∀ v, Θ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (p v) := fun _ => rfl
  refine LinearMap.ext fun x => ?_
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := hs w
  rw [← hΘ, ← map_aeval Θ (jac e π (scalars X s)) _ ?_, hq]
  · simp
  · intro y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [jac_mk, map_smul, hΘ, hΘ, jac_mk, hp, hl, hd]

end Blocks

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {M : Bool → Type} [∀ j, Fintype (M j)] [∀ j, DecidableEq (M j)]
  {c : Bool → Bool → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem diag_cell (f : ∀ i, (Σ j, c i j) ≃ M i) (g : ∀ j, (Σ i, c i j) ≃ M j)
    (h0 : ∀ i j, i ≠ j → IsEmpty (c i j)) (hfg : ∀ i t, f i ⟨i, t⟩ = g i ⟨i, t⟩)
    (ρ : Representation ℂ (Levi k M) W) :
    ∃ E : smoothPart (ind (relParab k (c := fun j i => c i j) g)
        ((twist ((relJac f ρ).comp (swapBlocks k c)) (relDeltaHalf k fun j i => c i j)).comp
          (relProj k (c := fun j i => c i j) g))) →ₗ[ℂ] W,
      Function.Injective E ∧ ∀ l x, E (cellFunctor f g ρ l x) = ρ l (E x) := by
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k M) = 1 := funext fun i =>
      eq_one_single (f i) i (fun j hj => h0 i j hj.symm) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k c z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ => deltaHalf_single i (fun j hj => h0 i j hj.symm) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => c i j) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ => deltaHalf_single j (fun i hi => h0 i j hi) (z j)
  have hP : ∀ x, x ∈ relParab k (c := fun j i => c i j) g := fun x j _ =>
    mem_parab_single (g j) j (fun i hi => h0 i j hi) (x j)
  have hγ : ∀ (p : relParab k (c := fun j i => c i j) g),
      relEmb k f (swapBlocks k c (relProj k (c := fun j i => c i j) g p)) = (p : Levi k M) := by
    intro p
    funext j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f j).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f j).surjective y
    obtain rfl : j = a := by
      by_contra hne
      exact (h0 _ _ hne).elim t
    obtain rfl : j = a' := by
      by_contra hne
      exact (h0 _ _ hne).elim s
    rw [leviEmb_apply_same, hfg, hfg]
    rfl
  let Ψ : Jacquet ρ (relUnip k f) ≃ₗ[ℂ] W := Submodule.quotEquivOfEqBot _ hbot
  have law : ∀ (p : relParab k (c := fun j i => c i j) g) u,
      Ψ (((twist ((relJac f ρ).comp (swapBlocks k c)) (relDeltaHalf k fun j i => c i j)).comp
          (relProj k (c := fun j i => c i j) g)) p u) = ρ p (Ψ u) := by
    intro p u
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hδ, hδ', hγ]
    simp only [inv_one, Units.val_one, one_smul]
    rfl
  have key : ∀ (x : smoothPart (ind (relParab k (c := fun j i => c i j) g)
        ((twist ((relJac f ρ).comp (swapBlocks k c)) (relDeltaHalf k fun j i => c i j)).comp
          (relProj k (c := fun j i => c i j) g)))) (l : Levi k M),
      Ψ (x.1.1 l) = ρ l (Ψ (x.1.1 1)) := fun x l => by
    refine Eq.trans ?_ (law ⟨l, hP l⟩ _)
    exact congrArg Ψ ((congrArg x.1.1 (mul_one l).symm).trans (x.1.2 ⟨l, hP l⟩ 1))
  refine ⟨{ toFun := fun x => Ψ (x.1.1 1)
            map_add' := fun x y => map_add Ψ _ _
            map_smul' := fun a x => map_smul Ψ _ _ }, fun x y h => ?_, fun l x => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun l => Ψ.injective ?_))
    have h' : Ψ (x.1.1 1) = Ψ (y.1.1 1) := h
    rw [key, key y, h']
  · show Ψ (x.1.1 (1 * l)) = ρ l (Ψ (x.1.1 1))
    rw [one_mul, key]

def lineRep (τ : Representation ℂ (GL (M false) k) W) (ψ : GL (M true) k →* ℂˣ) :
    Representation ℂ (Levi k M) W :=
  twist (τ.comp (Pi.evalMonoidHom (fun j => GL (M j) k) false))
    (ψ.comp (Pi.evalMonoidHom (fun j => GL (M j) k) true))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem lineRep_apply (τ : Representation ℂ (GL (M false) k) W) (ψ : GL (M true) k →* ℂˣ)
    (l : Levi k M) (v : W) : lineRep τ ψ l v = (ψ (l true) : ℂ) • τ (l false) v := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem scalars_comm {β : Type} {X : β → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (s : β → kˣ) (y : Levi k X) : y * scalars X s = scalars X s * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply]
  ext1
  simp only [scalars, Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

theorem other_cell (f : ∀ i, (Σ j, c i j) ≃ M i) (g : ∀ j, (Σ i, c i j) ≃ M j)
    (h0 : IsEmpty (c true true)) (τ : Representation ℂ (GL (M false) k) W) (ψ : GL (M true) k →* ℂˣ)
    (s : Bool → kˣ) (hs : s false = 1) (q : ℂ[X])
    (hq : aeval (jac (f false) τ (scalars (c false) s)) q = 0) :
    aeval (cellFunctor f g (lineRep τ ψ) (scalars M s)) q = 0 := by
  have hP : scalars M s ∈ relParab k (c := fun j i => c i j) g := fun j _ =>
    mem_parab.2 fun a b hab => by
      have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
      simp [scalars, Matrix.GeneralLinearGroup.scalar, hne]
  have hproj : relProj k (c := fun j i => c i j) g ⟨_, hP⟩ =
      fun j i => GeneralLinearGroup.scalar (c i j) (s j) := by
    funext j i
    refine Units.ext (Matrix.ext fun x y => ?_)
    refine (leviProj_apply k (g j) ⟨scalars M s j, hP j trivial⟩ i x y).trans ?_
    simp [scalars, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hsw : swapBlocks k c (relProj k (c := fun j i => c i j) g ⟨_, hP⟩) =
      fun i => scalars (c i) s := by
    rw [hproj]; rfl
  have h1 : scalars (c true) s = 1 := by
    funext j
    cases j
    · exact (congrArg (GeneralLinearGroup.scalar _) hs).trans (map_one _)
    · exact Subsingleton.elim _ _
  have hδ' : relDeltaHalf k (fun j i => c i j) (relProj k (c := fun j i => c i j) g ⟨_, hP⟩) = 1 := by
    rw [relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_single (X := fun i => c i true) false
      (by rintro (_ | _) h; exacts [absurd rfl h, h0]), one_mul, hproj]
    refine Eq.trans (congrArg _ ?_) (map_one _)
    funext i
    exact (congrArg (GeneralLinearGroup.scalar _) hs).trans (map_one _)
  let T := ((twist ((relJac f (lineRep τ ψ)).comp (swapBlocks k c))
    (relDeltaHalf k fun j i => c i j)).comp (relProj k (c := fun j i => c i j) g)) ⟨_, hP⟩
  let Θ : Jacquet τ (unipRad k (f false)) →ₗ[ℂ] Jacquet (lineRep τ ψ) (relUnip k f) :=
    Submodule.mapQ _ _ LinearMap.id (Submodule.span_le.2 (by
      rintro _ ⟨u, v, rfl⟩
      refine Submodule.subset_span ⟨⟨Pi.mulSingle false u.1, ?_⟩, v, ?_⟩
      · rintro (_ | _) -
        · simpa using u.2
        · simpa using one_mem _
      · simp [lineRep_apply]))
  have hΘ : ∀ v, Θ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  have hT : aeval T q = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← hΘ, ← map_aeval Θ (jac (f false) τ (scalars (c false) s)) _ ?_, hq]
    · simp
    · intro y
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [jac_mk, map_smul, hΘ, hΘ]
      simp only [T]
      rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hδ', hsw,
        relDeltaHalf_apply, Fintype.prod_bool, lineRep_apply, relEmb_apply, relEmb_apply, h1]
      simp
  exact aeval_smInd _ _ ⟨_, hP⟩ (scalars_comm s) q hT

end Cells

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem embed_of_cells {m : Type}
    [Fintype m] [DecidableEq m] {W Y J : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup J] [Module ℂ J]
    [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GL m k) W) (ψ : GL (Fin 1) k →* ℂˣ)
    (ρ : Representation ℂ (Levi k (Two m (Fin 1))) J) (N : ℕ)
    (b : Fin N ≃ SizeMatrix (Two m (Fin 1)) (Two m (Fin 1))) (S : Fin (N + 1) → Subrepresentation ρ)
    (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤)
    (hS : ∀ (t : Fin N) (f : ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ Two m (Fin 1) i)
      (g : ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ Two m (Fin 1) j),
      Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (cellFunctor f g (lineRep (M := Two m (Fin 1)) τ ψ))))
    (s : Bool → kˣ) (hs₀ : s false = 1) (c : ℂ)
    (hq : ∀ (d : Bool → ℕ) (f : (Σ j, Fin (d j)) ≃ m), d true = 1 → ∃ q : ℂ[X], q.eval c ≠ 0 ∧
      aeval (jac f τ (scalars (fun j => Fin (d j)) s)) q = 0)
    (j : Y →ₗ[ℂ] J)
    (hj : Function.Injective j)
    (A : Representation ℂ (GL m k × GL (Fin 1) k) Y)
    (hA : ∀ g y, j (A g y) = ρ (leviTwo k m (Fin 1) g) (j y)) (z : GL m k × GL (Fin 1) k)
    (hzs : leviTwo k m (Fin 1) z = scalars (Two m (Fin 1)) s) (hAz : ∀ y, A z y = c • y) :
    ∃ F : Y →ₗ[ℂ] W, Function.Injective F ∧ ∀ g y,
      F (A g y) = lineRep (M := Two m (Fin 1)) τ ψ (leviTwo k m (Fin 1) g) (F y) := by
  have hz : ∀ y, ρ (scalars (Two m (Fin 1)) s) (j y) = c • j y := fun y => by
    rw [← hzs, ← hA, hAz, map_smul]
  have hc : ∀ i, Fintype.card (Two m (Fin 1) i) = cond i 1 (Fintype.card m) := by
    rintro (_ | _) <;> simp
  let b₀ : SizeMatrix (Two m (Fin 1)) (Two m (Fin 1)) :=
    ⟨fun i j => if i = j then Fintype.card (Two m (Fin 1) i) else 0,
      fun i => by simp, fun j => by simp⟩
  obtain ⟨t₀, ht₀⟩ := b.surjective b₀
  obtain ⟨⟨q₁, h₁, k₁⟩, q₂, h₂, k₂⟩ := chain_ends
    (ρ
      (scalars (Two m (Fin 1)) s)) c N (fun t => (S t).toSubmodule)
    (congrArg Subrepresentation.toSubmodule h0) (congrArg Subrepresentation.toSubmodule hN) t₀
    fun t ht => by
      have r0 := (b t).2.1 false
      have r1 := (b t).2.1 true
      have c0 := (b t).2.2 false
      have c1 := (b t).2.2 true
      simp only [Fintype.sum_bool, hc, cond] at r0 r1 c0 c1
      have h11 : (b t).1 true true = 0 := by
        by_contra hne
        refine ht (b.injective (Subtype.ext ?_))
        rw [ht₀]
        funext i j
        cases i <;> cases j <;> simp [b₀, hc] <;> omega
      have f := (b t).nonempty_rows.some
      have g := (b t).nonempty_cols.some
      have φ := (hS t f g).some
      refine (hq _ (f false) (by omega)).imp fun q ⟨hq1, hq2⟩ => ?_
      have h3 := other_cell (c := fun i j => Fin ((b t).1 i j)) f g
        ⟨fun x => by have := x.2; omega⟩ τ ψ s hs₀ q hq2
      exact ⟨hq1, step_killed _ _ φ _ q h3⟩
  obtain ⟨j', hj', hj''⟩ := embed_step (S t₀.succ) (S t₀.castSucc) _ c j hj hz q₁ q₂ h₁ h₂ k₁ k₂
  have he : ∀ i j, i ≠ j → IsEmpty (Fin ((b t₀).1 i j)) := fun i j h => by
    rw [ht₀]
    exact ⟨fun x => by have := x.2; simp [b₀, h] at this⟩
  let κ : ∀ i, Fin ((b t₀).1 i i) ≃ Two m (Fin 1) i := fun i =>
    Fintype.equivOfCardEq (by rw [ht₀]; simp [b₀])
  let f : ∀ i, (Σ j, Fin ((b t₀).1 i j)) ≃ Two m (Fin 1) i := fun i =>
    (sigmaSingle (X := fun j => Fin ((b t₀).1 i j)) i fun j h => he i j h.symm).trans (κ i)
  let g : ∀ j, (Σ i, Fin ((b t₀).1 i j)) ≃ Two m (Fin 1) j := fun j =>
    (sigmaSingle (X := fun i => Fin ((b t₀).1 i j)) j fun i h => he i j h).trans (κ j)
  obtain ⟨φ⟩ := hS t₀ f g
  obtain ⟨E, hE, hE'⟩ := embed_of_equiv φ (diag_cell (c := fun i j => Fin ((b t₀).1 i j)) f g he
    (fun i t => by simp only [f, g, Equiv.trans_apply, sigmaSingle_mk])
    (lineRep (M := Two m (Fin 1)) τ ψ))
  refine ⟨E ∘ₗ j', hE.comp hj', fun l y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hj'' _ y _ (hA l y), hE']

end Main

theorem isIrreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : m ⊕ Fin 1 ≃ n) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Nontrivial V'] (π : Representation ℂ (GL n k) V) (π' : Representation ℂ (GL m k) V') (hπ : IsSmooth π) (hirr : π.IsIrreducible) (hπ' : IsSmooth π') (hfl : HasFiniteLength π') (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (ϖ : kˣ) (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e π)) (hS : Monotone S) (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N) (φ : (subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor π' (detRep (Fin 1) ξ))) (hother : ∀ t, t ≠ t₀ → ∃ c : ℂ, c ≠ (ξ ϖ : ℂ) ∧ ∀ w ∈ (S t.succ).toSubmodule, jac₂ e π (1, GeneralLinearGroup.scalar (Fin 1) ϖ) w - c • w ∈ (S t.castSucc).toSubmodule) (hii : ∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : m' ⊕ Fin 1 ≃ m), ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' π' (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) q = 0), π'.IsIrreducible := by
  intro k _ _ _ _ hG n m _ _ _ _ e V V' _ _ _ _ _ π π' hπ hirr hπ' hfl ξ hξ ϖ N S _ h0 hN t₀ φ hother hii
  let s : Bool → kˣ := fun j => cond j ϖ 1
  have hzs : ∀ (a : Type) [Fintype a] [DecidableEq a],
      leviTwo k a (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) = scalars (Two a (Fin 1)) s := by
    intro a _ _
    funext j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar a : kˣ →* _)).symm
    · rfl
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) ϖ) = ϖ := by
    ext; simp [GeneralLinearGroup.scalar]
  have hzc : ∀ g : GL m k × GL (Fin 1) k, g * (1, GeneralLinearGroup.scalar (Fin 1) ϖ) =
      (1, GeneralLinearGroup.scalar (Fin 1) ϖ) * g := fun g =>
    (leviTwo k m (Fin 1)).injective (by rw [map_mul, map_mul, hzs, scalars_comm])
  have hrid : ∀ g y, TensorProduct.rid ℂ V' (extTensor π' (detRep (Fin 1) ξ) g y) =
      (detChar (Fin 1) ξ g.2 : ℂ) • π' g.1 (TensorProduct.rid ℂ V' y) := by
    intro g y
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul v a => simp [detRep, smul_smul]
  have hσ : ∀ y, extTensor π' (detRep (Fin 1) ξ) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) y =
      (ξ ϖ : ℂ) • y := fun y => (TensorProduct.rid ℂ V').injective (by
    rw [hrid]; simp [hdet])
  obtain ⟨⟨q₁, h₁, k₁⟩, q₂, h₂, k₂⟩ := chain_ends
    (jac₂ e π (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) (ξ ϖ : ℂ) N (fun t => (S t).toSubmodule)
    (congrArg Subrepresentation.toSubmodule h0) (congrArg Subrepresentation.toSubmodule hN) t₀
    fun t ht => (hother t ht).elim fun c hc =>
      ⟨Polynomial.X - Polynomial.C c, by simpa using sub_ne_zero.2 hc.1.symm, fun w hw => by
        simpa [Module.algebraMap_end_apply] using hc.2 w hw⟩
  obtain ⟨⟨p, hp, hps⟩, σ, hσi, hσj⟩ := split_step _ _ φ _ hzc _ hσ q₁ q₂ h₁ h₂ k₁ k₂
  obtain ⟨M, hM⟩ := exists_coatom hfl
  let τ := π'.quotient M.toSubmodule (fun g _ hv => M.apply_mem_toSubmodule g hv)
  have hmk : ∀ g v, M.toSubmodule.mkQ (π' g v) = τ g (M.toSubmodule.mkQ v) := fun _ _ => rfl
  have hτ : IsSmooth τ := (IsSubquotient.of_surjective (ρ := π') (σ := τ)
    ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext (hmk g)⟩ M.toSubmodule.mkQ_surjective).isSmooth hπ'
  refine (?_ : ∃ F : V' →ₗ[ℂ] V' ⧸ M.toSubmodule, Function.Injective F ∧
    ∀ g v, F (π' g v) = τ g (F v)).elim fun F hF => isIrreducible_of_embed M hM F hF.1 hF.2
  have hnt : Nontrivial (V' ⧸ M.toSubmodule) := Submodule.Quotient.nontrivial_iff.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  have hsm : IsSmooth (lineRep (M := Two m (Fin 1)) τ (detChar (Fin 1) ξ)) :=
    isSmooth_twist (isSmooth_comp hτ _ (continuous_apply false))
      (hξ.detChar.comp _ (continuous_apply true))
  let P : (jac (two e) π).IntertwiningMap (lineRep (M := Two m (Fin 1)) τ (detChar (Fin 1) ξ)) :=
    ⟨M.toSubmodule.mkQ ∘ₗ (TensorProduct.rid ℂ V').toLinearMap ∘ₗ p, fun l => LinearMap.ext fun x => by
      obtain ⟨g, rfl⟩ := (leviTwo k m (Fin 1)).surjective l
      show M.toSubmodule.mkQ (TensorProduct.rid ℂ V' (p (jac₂ e π g x))) =
        (detChar (Fin 1) ξ g.2 : ℂ) • τ g.1 (M.toSubmodule.mkQ (TensorProduct.rid ℂ V' (p x)))
      rw [hp, hrid, map_smul, hmk]⟩
  have hP : Function.Surjective P :=
    M.toSubmodule.mkQ_surjective.comp ((TensorProduct.rid ℂ V').surjective.comp hps)
  obtain ⟨ι, hι⟩ := (Model.evalOne_bijective (two e) hπ _).2 P
  have hιi : Function.Injective ι := by
    refine (Representation.IsIrreducible.injective_or_eq_zero ι).resolve_right fun h => ?_
    obtain ⟨y, hy⟩ := exists_ne (0 : V' ⧸ M.toSubmodule)
    obtain ⟨x, rfl⟩ := hP y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine hy ?_
    rw [← hι, h]
    rfl
  have hJ := JacInj.jacMap_injective k _ _ _ (two e) _ _ _ _ ι (isSmooth_parInd _ _) hιi
  have hJi : ∀ g y, jacMap (two e) ι (σ (extTensor π' (detRep (Fin 1) ξ) g y)) =
      jac (two e) (parInd (two e) (lineRep (M := Two m (Fin 1)) τ (detChar (Fin 1) ξ)))
        (leviTwo k m (Fin 1) g) (jacMap (two e) ι (σ y)) := fun g y =>
    (congrArg (jacMap (two e) ι) (hσi g y)).trans
      ((jacMap (two e) ι).isIntertwining _ _ (leviTwo k m (Fin 1) g) (σ y))
  obtain ⟨N', b, hb⟩ := hG k Bool Bool n (Two m (Fin 1)) (Two m (Fin 1)) (two e) (two e)
  obtain ⟨T, -, h0', hN', hT⟩ := hb _ _ hsm
  have key := embed_of_cells τ (detChar (Fin 1) ξ) _ N' b T h0' hN' hT s rfl (ξ ϖ : ℂ)
    (fun d f hd => by
      let κ : ∀ j, Two (Fin (d false)) (Fin 1) j ≃ Fin (d j) := fun j => match j with
        | false => Equiv.refl _
        | true => finCongr hd.symm
      let e' : Fin (d false) ⊕ Fin 1 ≃ m :=
        (two (Equiv.refl _)).symm.trans ((Equiv.sigmaCongrRight κ).trans f)
      refine (hii _ e').imp fun q hq => ⟨hq.1, ?_⟩
      refine aeval_jac_eq_zero (two e') f κ (by rintro (_ | _) i <;> rfl) M.toSubmodule.mkQ hmk
        M.toSubmodule.mkQ_surjective s q ?_
      rw [← hzs]
      exact hq.2)
    ((jacMap (two e) ι).toLinearMap ∘ₗ σ) (hJ.comp hσj) _ hJi _ (hzs m) hσ
  refine key.elim fun F hF => ⟨F ∘ₗ (TensorProduct.rid ℂ V').symm.toLinearMap,
    hF.1.comp (TensorProduct.rid ℂ V').symm.injective, fun g v => ?_⟩
  have h1 : (TensorProduct.rid ℂ V').symm (π' g v) =
      extTensor π' (detRep (Fin 1) ξ) (g, 1) ((TensorProduct.rid ℂ V').symm v) := by simp
  have h2 := hF.2 (g, 1) ((TensorProduct.rid ℂ V').symm v)
  rw [← h1, lineRep_apply] at h2
  refine h2.trans ?_
  show ((detChar (Fin 1) ξ 1 : ℂˣ) : ℂ) • τ g _ = _
  rw [map_one, Units.val_one, one_smul]
  rfl

end GlobalTheory.RightEnd
