import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICHWMap

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def diagOp (A : Module.End ℂ T) (B : Module.End ℂ V) : Module.End ℂ (WithLp 2 (T × V)) :=
  (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ (A.prodMap B) ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap

theorem diagOp_fst (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).1 = A (WithLp.ofLp x).1 := rfl

theorem diagOp_snd (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).2 = B (WithLp.ofLp x).2 := rfl

theorem sum_ext {x y : WithLp 2 (T × V)} (h1 : (WithLp.ofLp x).1 = (WithLp.ofLp y).1)
    (h2 : (WithLp.ofLp x).2 = (WithLp.ofLp y).2) : x = y := by
  apply (WithLp.linearEquiv 2 ℂ (T × V)).injective
  exact Prod.ext h1 h2

theorem diag_krel {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KRel ε ET) (h2 : KRel ε E) :
    KRel ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b c d hab hcd
  have e1 := LinearMap.congr_fun (h1 a b c d hab hcd)
  have e2 := LinearMap.congr_fun (h2 a b c d hab hcd)
  refine LinearMap.ext fun x => ?_
  apply sum_ext
  · have := e1 (WithLp.ofLp x).1
    split_ifs at this ⊢ <;> exact this
  · have := e2 (WithLp.ofLp x).2
    split_ifs at this ⊢ <;> exact this

theorem diag_kunit {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KUnit ε ET) (h2 : KUnit ε E) :
    KUnit ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b hab x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, diagOp_fst, diagOp_snd, diagOp_fst, diagOp_snd,
    h1 a b hab, h2 a b hab]

theorem hwMap_of_lowSpan : LowSpan → HWMap := by
  intro hLS n ε T _ _ _ V _ _ ET E μ t v S hRT hUT hR hU ht hHT hH hS hSt hvS
  haveI := hS
  let Lm : (T × S) →ₗ[ℂ] WithLp 2 (T × V) :=
    (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ LinearMap.prodMap LinearMap.id S.subtype
  let S' : Submodule ℂ (WithLp 2 (T × V)) := LinearMap.range Lm
  have memS' : ∀ x : WithLp 2 (T × V), x ∈ S' ↔ (WithLp.ofLp x).2 ∈ S := by
    intro x
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2.2
    · intro hx
      exact ⟨((WithLp.ofLp x).1, ⟨(WithLp.ofLp x).2, hx⟩), sum_ext rfl rfl⟩
  let w0 : WithLp 2 (T × V) := WithLp.toLp 2 (t, v)
  have hw0 : w0 ≠ 0 := by
    intro h
    apply ht
    exact congrArg (fun x => (WithLp.ofLp x).1) h
  have hKR : KRel ε (fun a b => diagOp (ET a b) (E a b)) := diag_krel hRT hR
  have hKU : KUnit ε (fun a b => diagOp (ET a b) (E a b)) := diag_kunit hUT hU
  have hHW : KHighest ε (fun a b => diagOp (ET a b) (E a b)) μ w0 := by
    refine ⟨fun a => ?_, fun a b hab heq => ?_⟩
    · apply sum_ext
      · exact hHT.1 a
      · exact hH.1 a
    · apply sum_ext
      · exact hHT.2 a b hab heq
      · exact hH.2 a b hab heq
  have hStab' : KStab ε (fun a b => diagOp (ET a b) (E a b)) S' := by
    intro a b hab x hx
    rw [memS'] at hx ⊢
    exact hSt a b hab _ hx
  have hw0S' : w0 ∈ S' := (memS' w0).2 hvS
  obtain ⟨L0, -, hw0L, hL0stab, hirr, -, -⟩ :=
    hLS n ε (WithLp 2 (T × V)) (fun a b => diagOp (ET a b) (E a b)) μ w0 S' hKR hKU hw0 hHW
      inferInstance hStab' hw0S'
  let πT : WithLp 2 (T × V) →ₗ[ℂ] T := LinearMap.fst ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let πV : WithLp 2 (T × V) →ₗ[ℂ] V := LinearMap.snd ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let K : Submodule ℂ (WithLp 2 (T × V)) := L0 ⊓ LinearMap.ker πT
  have hKstab : KStab ε (fun a b => diagOp (ET a b) (E a b)) K := by
    intro a b hab x hx
    refine ⟨hL0stab a b hab x hx.1, ?_⟩
    have hx2 : πT x = 0 := hx.2
    show ET a b (πT x) = 0
    rw [hx2, map_zero]
  have hK : K = ⊥ := by
    rcases hirr K inf_le_left hKstab with h | h
    · exact h
    · exfalso
      apply ht
      have hw0K : w0 ∈ K := h ▸ hw0L
      exact hw0K.2
  let g : L0 →ₗ[ℂ] T := πT ∘ₗ L0.subtype
  have ginj : Function.Injective g := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)
    have hxK : (x : WithLp 2 (T × V)) ∈ K := ⟨x.2, hx⟩
    rw [hK] at hxK
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hxK)
  let W0 : Submodule ℂ T := LinearMap.range g
  let e : L0 ≃ₗ[ℂ] W0 := LinearEquiv.ofInjective g ginj
  have hW0stab : ∀ a b, ε a = ε b → ∀ y ∈ W0, ET a b y ∈ W0 := by
    rintro a b hab _ ⟨x, rfl⟩
    exact ⟨⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩, rfl⟩
  let P : T →L[ℂ] W0 := W0.orthogonalProjectionOnto
  have hP : ∀ a b, ε a = ε b → ∀ y : T, (P (ET a b y) : T) = ET a b (P y) := by
    intro a b hab y
    have hmem : ET a b (P y : T) ∈ W0 := hW0stab a b hab _ (P y).2
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · exact hmem
    · rw [← map_sub, hUT a b hab, Submodule.coe_orthogonalProjectionOnto_apply]
      exact Submodule.inner_left_of_mem_orthogonal (hW0stab b a hab.symm w hw)
        (Submodule.sub_starProjection_mem_orthogonal y)
  have hPe : ∀ x : L0, P (g x) = e x := by
    intro x
    have h1 : ((e x : W0) : T) = g x := LinearEquiv.ofInjective_apply _ _
    rw [← h1]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
  let φ : T →ₗ[ℂ] V := πV ∘ₗ L0.subtype ∘ₗ e.symm.toLinearMap ∘ₗ (P : T →ₗ[ℂ] W0)
  have hφ : ∀ y : T, φ y = πV (e.symm (P y) : WithLp 2 (T × V)) := fun y => rfl
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ]
    have hg0 : g ⟨w0, hw0L⟩ = t := rfl
    rw [← hg0, hPe, LinearEquiv.symm_apply_apply]
    rfl
  · intro a b hab y
    obtain ⟨x, hx⟩ : ∃ x : L0, x = e.symm (P y) := ⟨_, rfl⟩
    have hPy : P y = e x := by rw [hx, LinearEquiv.apply_symm_apply]
    let x' : L0 := ⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩
    have hgx' : g x' = ET a b (g x) := rfl
    have hPE : P (ET a b y) = e x' := by
      apply Subtype.ext
      rw [hP a b hab y, hPy, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, hgx']
    rw [hφ, hφ, hPE, LinearEquiv.symm_apply_apply, ← hx]
    rfl

end GlobalTheory.CompanionTheory.DSICHWMap
