import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSubquotFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotientAdditivity

theorem altSum_eq {k : Type u} [Field k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, FiniteDimensional k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, FiniteDimensional k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (h0 : Function.Injective (f 0)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i)) (hδf : ∀ i, Function.Exact (δ i) (f (i + 1))) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) =
      (-1 : ℤ) ^ M * Module.finrank k (LinearMap.range (δ M)) := by
  have hB : ∀ i, (Module.finrank k (B i) : ℤ) =
      Module.finrank k (LinearMap.range (f i)) + Module.finrank k (LinearMap.range (g i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (g i), LinearMap.exact_iff.1 (hfg i)]
    push_cast; ring
  have hC : ∀ i, (Module.finrank k (C i) : ℤ) =
      Module.finrank k (LinearMap.range (g i)) + Module.finrank k (LinearMap.range (δ i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (δ i), LinearMap.exact_iff.1 (hgδ i)]
    push_cast; ring
  have hA : ∀ i, (Module.finrank k (A (i + 1)) : ℤ) =
      Module.finrank k (LinearMap.range (δ i)) + Module.finrank k (LinearMap.range (f (i + 1))) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (f (i + 1)), LinearMap.exact_iff.1 (hδf i)]
    push_cast; ring
  have hA0 : (Module.finrank k (A 0) : ℤ) = Module.finrank k (LinearMap.range (f 0)) := by
    rw [← LinearMap.finrank_range_add_finrank_ker (f 0), LinearMap.ker_eq_bot.2 h0, finrank_bot]
    simp
  induction M with
  | zero => rw [Finset.sum_range_one, hA0, hB 0, hC 0]; ring
  | succ M ih => rw [Finset.sum_range_succ, ih, hA M, hB (M + 1), hC (M + 1)]; ring

section Top

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem cdeg_top (i : ℕ) : Cech.Cdeg G (fun _ => (⊤ : Submodule R _)) i = ⊤ := by
  ext s; simp [Cech.Cdeg]

theorem cocyDeg_top (i : ℕ) : Cech.cocyDeg G (fun _ => ⊤) ρ i = LinearMap.ker (Cech.d G ρ i) := by
  rw [Cech.cocyDeg, cdeg_top, inf_top_eq]

theorem bdryDeg_top (i : ℕ) : Cech.bdryDeg G (fun _ => ⊤) ρ i = Cech.bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i => rw [Cech.bdryDeg, Cech.bdry, cdeg_top, Submodule.map_top]

def hdegTopEquiv (i : ℕ) : Cech.Hdeg G (fun _ => ⊤) ρ i ≃ₗ[R] Cech.H G ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i)) (by
    ext z
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [bdryDeg_top] at hy
      exact hy
    · intro hz
      refine ⟨⟨z.1, (cocyDeg_top G ρ i).symm ▸ z.2⟩, ?_, rfl⟩
      rw [bdryDeg_top]; exact hz)

theorem hdeg_subsingleton {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
    (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J) (i : ℕ) [IsEmpty (Cech.Idx U i)] :
    Subsingleton (Cech.Hdeg G deg ρ' i) := by
  have : Subsingleton (Cech.cocyDeg G deg ρ' i) :=
    ⟨fun a b => Subtype.ext (funext fun I => isEmptyElim I)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, rfl⟩ := Cech.Hdeg_mk_surjective a
  obtain ⟨z', rfl⟩ := Cech.Hdeg_mk_surjective b
  rw [Subsingleton.elim z z']

end Top

theorem idx_isEmpty {Ω : Type w} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) : IsEmpty (Cech.Idx (support x) (N + 1)) :=
  ⟨fun I => by
    have h1 := Finset.card_le_card I.1.2.2
    have h2 := Finset.card_le_univ (support x)
    have h3 := I.2
    simp only [Fintype.card_fin] at h2
    omega⟩

section Quot

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
  (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I)
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (fun _ hy => hy)

def quotPr (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id (by intro _ hy; exact h32 I hy)

theorem quotRes_comp (F₁ F₂ : SubSystem k x E) (I J K : Chart x) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (SubSystem.quotRes F₁ F₂ J K hJK).comp (SubSystem.quotRes F₁ F₂ I J hIJ) =
      SubSystem.quotRes F₁ F₂ I K (hIJ.trans hJK) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem quotInl_comm (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotInl F₁ F₂ F₃ h21 J (SubSystem.quotRes F₂ F₃ I J h m) =
      SubSystem.quotRes F₁ F₃ I J h (quotInl F₁ F₂ F₃ h21 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotPr_comm (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :
    quotPr F₁ F₂ F₃ h32 J (SubSystem.quotRes F₁ F₃ I J h m) =
      SubSystem.quotRes F₁ F₂ I J h (quotPr F₁ F₂ F₃ h32 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotInl_injective (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    Function.Injective (quotInl F₁ F₂ F₃ h21 I) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) :
      F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact h'

theorem quotPr_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotPr F₁ F₂ F₃ h32 I (quotInl F₁ F₂ F₃ h21 I m) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact y.2

theorem exists_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I)
    (hm : quotPr F₁ F₂ F₃ h32 I m = 0) : ∃ y, quotInl F₁ F₂ F₃ h21 I y = m := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk z : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  exact ⟨Submodule.Quotient.mk ⟨z, h'⟩, rfl⟩

theorem quotPr_surjective (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    Function.Surjective (quotPr F₁ F₂ F₃ h32 I) := by
  intro m
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨Submodule.Quotient.mk z, rfl⟩

theorem finrank_quotH (F₁ F₂ : SubSystem k x E) (i : ℕ) :
    Module.finrank k (SubSystem.quotH F₁ F₂ i) =
      Module.finrank k (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun _ => ⊤)
        (SubSystem.quotRes F₁ F₂) i) :=
  (hdegTopEquiv _ _ i).finrank_eq.symm

end Quot

end SnapperQuotientAdditivity

set_option maxHeartbeats 1000000 in
open SnapperQuotientAdditivity in

theorem SnapperQuotAdd.proof (hfin : SnapperSubquotFinite.Statement.{u, v, w}) :
    SnapperQuotAdd.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ hfg h21 h32
  have h31 : ∀ I, F₃.sub I ≤ F₁.sub I := fun I => (h32 I).trans (h21 I)
  have hdd := CechDSq.proof (N + 1) (support x) k
    (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem) (quotRes_comp F₁.toSubSystem F₃.toSubSystem)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (B := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem)
    (ρB := SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := quotInl F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h21)
    (ψ := quotPr F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h32)
  have L1 := L (quotInl_comm _ _ _ h21)
  have L2 := L1 (quotPr_comm _ _ _ h32)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (quotInl_injective _ _ _ h21)
  have L5 := L4 (quotPr_quotInl _ _ _ h21 h32)
  have L6 := L5 (fun I m _ hm => (exists_quotInl _ _ _ h21 h32 I m hm).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L7 := L6 (fun I m _ => (quotPr_surjective _ _ _ h32 I m).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  have h0 := liftZP_newton.1
  have hex := liftZP_newton.2
  choose δ hgδ hδf using fun i => (hex i).2
  have fin : ∀ (G₁ G₂ : SubFamily k x E), (∀ I, G₁.sub I ≤ F₁.sub I) → (∀ I, G₂.sub I ≤ G₁.sub I) → ∀ i,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (fun _ => ⊤) (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := by
    intro G₁ G₂ h1 h2 i
    have : FiniteDimensional k (Cech.H (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := hfin k Ω N x E F₁ G₁ G₂ hfg h1 h2 i
    exact (hdegTopEquiv _ _ i).symm.finiteDimensional
  have := fin F₂ F₃ h21 h32
  have := fin F₁ F₃ (fun _ => le_rfl) h31
  have := fin F₁ F₂ (fun _ => le_rfl) h21
  have key := altSum_eq _ _ _ _ _ δ h0 (fun i => (hex i).1) hgδ hδf N
  have := idx_isEmpty x
  have hsub := hdeg_subsingleton (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)
  have hδN : Module.finrank k (LinearMap.range (δ N)) = 0 := by
    have hz : Module.finrank k (Cech.Hdeg (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact Nat.eq_zero_of_le_zero ((Submodule.finrank_le (LinearMap.range (δ N))).trans hz.le)
  rw [hδN] at key
  simp only [Nat.cast_zero, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  simp only [eulerCharQuot, finrank_quotH]
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
