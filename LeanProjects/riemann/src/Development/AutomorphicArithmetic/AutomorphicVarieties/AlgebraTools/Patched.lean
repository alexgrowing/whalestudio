import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimScal

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  {X X' : Type} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']

private theorem one_tmul_mem (a : Ideal R) {x : X} (hx : x ∈ (a • ⊤ : Submodule R X)) (s : S) :
    s ⊗ₜ[R] x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) := by
  refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

private theorem kill_tensor {r : R} (h : ∀ x : X, r • x = 0) (z : S ⊗[R] X) :
    algebraMap R S r • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul s x =>
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, h x, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem bot_tensor (a : Ideal R) (h : (a • ⊤ : Submodule R X) = ⊥) :
    (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro s hs z hz
  clear hz
  rw [Submodule.mem_bot]
  have key : ∀ t ∈ a, ∀ w : S ⊗[R] X, algebraMap R S t • w = 0 := by
    intro t ht w
    apply kill_tensor S
    intro x
    have hm : t • x ∈ (a • ⊤ : Submodule R X) := Submodule.smul_mem_smul ht Submodule.mem_top
    rw [h] at hm
    exact (Submodule.mem_bot R).mp hm
  simp only [Ideal.map] at hs
  induction hs using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact key t ht z
  | zero => exact zero_smul _ _
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

private theorem ker_tensor (a : Ideal R) (t : X →ₗ[R] X') (ht : Function.Surjective t)
    (hk : LinearMap.ker t = a • ⊤) (h' : (a • ⊤ : Submodule R X') = ⊥) :
    Function.Surjective (t.baseChange S) ∧
      LinearMap.ker (t.baseChange S) = a.map (algebraMap R S) • ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S ht
  · have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map t) ht
    ext w
    constructor
    · intro hw
      rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hw
      obtain ⟨v, rfl⟩ := (hex w).mp hw
      clear hw
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul s x =>
        rw [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        have hx : (x : X) ∈ (a • ⊤ : Submodule R X) := hk ▸ x.2
        exact one_tmul_mem S a hx s
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro hw
      have hle : (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) ≤
          LinearMap.ker (t.baseChange S) := by
        rw [Submodule.smul_le]
        intro r hr n _
        rw [LinearMap.mem_ker, LinearMap.map_smul]
        have hb := bot_tensor S a h'
        have hm : r • (t.baseChange S) n ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X')) :=
          Submodule.smul_mem_smul hr Submodule.mem_top
        rw [hb] at hm
        exact (Submodule.mem_bot S).mp hm
      exact hle hw

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.exists_patched_module :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (y : σ → R) (m : Ideal R) (f : R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      (S : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] (𝔶 : Ideal S), 𝔶 = (Ideal.span (Set.range y)).map (algebraMap R S) →
      (∀ a j : ℕ, ∀ᶠ N in F, QRegAt (M N) y (m ^ j) a) →
      ∀ (Y : Type) [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
        (g : ULim F (fun j => Ideal.span (Set.range y) ⊔ m ^ j) M →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) g], Module.Finite S Y →
      ∃ (MM : Type) (_ : AddCommGroup MM) (_ : Module S MM) (_ : Module (AdicCompletion 𝔶 S) MM) (_ : IsScalarTower S (AdicCompletion 𝔶 S) MM)
        (q : MM →ₗ[S] Y), Module.Finite (AdicCompletion 𝔶 S) MM ∧ Function.Surjective q ∧ LinearMap.ker q = 𝔶 • ⊤ ∧
        GlobalTheory.IsQuasiRegularSeq MM (fun s => algebraMap R S (y s)) ∧
        ∀ r : R, (∀ k : ℕ, ∃ e : ℕ, ∀ j : ℕ, ∀ᶠ N in F, ∀ x : M N,
            (f ^ e * r) • x ∈ ((Ideal.span (Set.range y) ^ k ⊔ m ^ j) • ⊤ : Submodule R (M N))) →
          ∀ x : MM, algebraMap R S r • x = 0 := by
  intro R σ _ _ F hF y m f M _ _ S _ _ _ 𝔶 h𝔶 hreg Y _ _ _ _ g _ hfin
  classical
  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers f)
  have haFG : (Ideal.span (Set.range y)).FG := Submodule.fg_span (Set.finite_range y)
  have hFG : 𝔶.FG := h𝔶 ▸ haFG.map _
  have anti : Antitone (fun j : ℕ => m ^ j) := fun i j hij => Ideal.pow_le_pow_right hij
  have hle : ∀ k : ℕ, Ideal.span (Set.range y) ^ (k + 1) ≤ Ideal.span (Set.range y) ^ k :=
    fun k => Ideal.pow_le_pow_right (Nat.le_succ k)
  have htk := fun k : ℕ => ULim.trans_ker R F hF (fun j => m ^ j) M
    (Ideal.span (Set.range y) ^ k) (Ideal.span (Set.range y) ^ (k + 1)) haFG.pow anti (hle k)
  have hS := fun k : ℕ => ker_tensor S (Ideal.span (Set.range y) ^ k) _ (htk k).1 (htk k).2.1 (htk k).2.2
  have hB := fun k : ℕ => bot_tensor S (Ideal.span (Set.range y) ^ k) (htk k).2.2
  have hmap : ∀ k : ℕ, (Ideal.span (Set.range y) ^ k).map (algebraMap R S) = 𝔶 ^ k := by
    intro k
    rw [Ideal.map_pow, h𝔶]
  have key : ∀ I : ℕ → Ideal R, I = (fun j => Ideal.span (Set.range y) ⊔ m ^ j) →
      Nonempty (S ⊗[R] ULim F I M ≃ₗ[S] Y) := by
    rintro I rfl
    exact ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers f) S g).equiv⟩
  obtain ⟨e1⟩ := key (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) (by funext j; rw [pow_one])
  haveI := hfin
  haveI : Module.Finite S (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) M) :=
    Module.Finite.equiv e1.symm
  obtain ⟨MM, i1, i2, i3, i4, qq, hfinMM, hsurj, hker, -, hzero⟩ :=
    exists_tower_limit_completion S 𝔶 hFG
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)
      (fun k => LinearMap.baseChange S
        (ULim.map F (fun x => sup_le_sup_right (hle k) ((fun j => m ^ j) x)) fun _ => LinearMap.id))
      (fun k => (hS k).1) (fun k => by rw [(hS k).2, hmap]) (fun k => by rw [← hmap]; exact hB k)
      inferInstance
  refine ⟨MM, i1, i2, i3, i4, e1.toLinearMap ∘ₗ qq 1, hfinMM, e1.surjective.comp (hsurj 1), ?_, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, hker 1, pow_one]
  · have hspan : Ideal.span (Set.range fun s => algebraMap R S (y s)) = 𝔶 := by
      rw [h𝔶, Ideal.map_span, ← Set.range_comp]
      rfl
    refine isQuasiRegularSeq_of_tower S σ (fun s => algebraMap R S (y s)) MM
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) qq hsurj
      (fun k => by rw [hker k, hspan]) ?_
    intro b k hbk
    have h1 := qRegAt_uLim R σ F hF (fun j => m ^ j) M y b k anti hbk (fun j => hreg b j)
    haveI : IsLocalizedModule (Submonoid.powers f)
        (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) S _).mpr
        (TensorProduct.isBaseChange R _ S)
    have h2 := (qRegAt_map R S σ y ⊥ b).2 (Submonoid.powers f) _ _
      (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) h1
    have h3 := ((qRegAt_map R S σ y ⊥ b).1
      (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)).mp h2
    rwa [Ideal.map_bot] at h3
  · intro r hr x
    apply hzero (algebraMap R S r • x)
    intro k
    obtain ⟨e, he⟩ := hr k
    have hP : ∀ z : ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M, (f ^ e * r) • z = 0 :=
      (ULim.scal_eq R ℕ F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M).2.1 (f ^ e * r) he
    have hQ : ∀ w : S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M,
        algebraMap R S (f ^ e * r) • w = 0 := kill_tensor S hP
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := S) f).pow e
    rw [LinearMap.map_smul, ← hu.smul_eq_zero, ← mul_smul, ← map_pow, ← map_mul]
    exact hQ _
