import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.LatticeStabLocal

section Gen
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  {R : Type} [CommRing R] [Algebra F R] (T : Subring R) (N : Submodule (𝓞 E) (n → E))
  {k : ℕ} (s : Fin k → N)

def IsComb (u : n → E ⊗[F] R) : Prop :=
  ∃ a : Fin k → R, (∀ j, a j ∈ T) ∧ ∀ i, u i = ∑ j, (s j : n → E) i ⊗ₜ[F] a j

variable {T N s}

theorem isComb_zero : IsComb (F := F) T N s 0 :=
  ⟨0, fun _ => zero_mem _, fun i => by simp⟩

theorem IsComb.add {y z : n → E ⊗[F] R} (hy : IsComb T N s y) (hz : IsComb T N s z) :
    IsComb T N s (y + z) := by
  obtain ⟨a, ha, ea⟩ := hy
  obtain ⟨b, hb, eb⟩ := hz
  exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
    simp only [Pi.add_apply, ea, eb, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem IsComb.neg {y : n → E ⊗[F] R} (hy : IsComb T N s y) : IsComb T N s (-y) := by
  obtain ⟨a, ha, ea⟩ := hy
  exact ⟨-a, fun j => neg_mem (ha j), fun i => by
    simp only [Pi.neg_apply, ea, TensorProduct.tmul_neg, Finset.sum_neg_distrib]⟩

theorem isComb_tmul (hs : Submodule.span ℤ (Set.range s) = ⊤) {w : n → E} (hw : w ∈ N) {a : R}
    (ha : a ∈ T) : IsComb (F := F) T N s (fun i => w i ⊗ₜ[F] a) := by
  have : (⟨w, hw⟩ : N) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  have e : w = ∑ j, m j • (s j : n → E) := by simpa using (congrArg Subtype.val hm).symm
  refine ⟨fun j => m j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
  rw [e]
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _

theorem IsComb.smul (hs : Submodule.span ℤ (Set.range s) = ⊤) {t : E ⊗[F] R}
    (ht : t ∈ tensInt (F := F) R (intOE E) T) :
    ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y) := by
  refine Subring.closure_induction
    (p := fun t _ => ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y))
    ?_ ?_ ?_ ?_ ?_ ?_ ht
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩) y ⟨a, ha, ea⟩
    · have : ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y : n → E ⊗[F] R) =
          ∑ j, fun i => (e' • (s j : n → E)) i ⊗ₜ[F] a j := by
        funext i
        rw [Pi.smul_apply, ea, smul_eq_mul, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
      change IsComb T N s ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y)
      rw [this]
      exact Finset.sum_induction _ (IsComb T N s) (fun _ _ hx hy => hx.add hy) isComb_zero
        fun j _ => isComb_tmul hs (N.smul_mem e' (s j).2) (ha j)
    · refine ⟨fun j => b * a j, fun j => mul_mem hb (ha j), fun i => ?_⟩
      change ((1 : E) ⊗ₜ[F] b) * y i = _
      rw [ea, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y _; rw [zero_smul]; exact isComb_zero
  · intro y hy; rwa [one_smul]
  · intro a b _ _ ha hb y hy; rw [add_smul]; exact (ha hy).add (hb hy)
  · intro a _ ha y hy; rw [neg_smul]; exact (ha hy).neg
  · intro a b _ _ ha hb y hy; rw [mul_smul]; exact ha (hb hy)

theorem mem_latS_iff_isComb (hs : Submodule.span ℤ (Set.range s) = ⊤) (u : n → E ⊗[F] R) :
    u ∈ latS R (tensInt (F := F) R (intOE E) T) N ↔ IsComb T N s u := by
  constructor
  · intro hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact isComb_tmul hs hw (one_mem T)
    | zero => exact isComb_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul t x _ hx => exact IsComb.smul hs t.2 hx
  · rintro ⟨a, ha, ea⟩
    have e : u = ∑ j, (⟨(1 : E) ⊗ₜ[F] a j, Subring.subset_closure (Or.inr ⟨⟨a j, ha j⟩, rfl⟩)⟩ :
        tensInt (F := F) R (intOE E) T) • fun i => inclE (F := F) R ((s j : n → E) i) := by
      funext i
      rw [ea, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = ((1 : E) ⊗ₜ[F] a j) * ((s j : n → E) i ⊗ₜ[F] (1 : R))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s j, (s j).2, rfl⟩)

end Gen

section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  (N : Submodule (𝓞 E) (n → E))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem mem_latS_adele_iff [Module.Finite (𝓞 E) N] (u : n → E ⊗[F] 𝔸) :
    u ∈ latS 𝔸 (tensInt (F := F) 𝔸 (intOE E) (intAd F)) N ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈
        latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N := by
  have : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := N)
  simp only [mem_latS_iff_isComb hs]
  constructor
  · rintro ⟨a, ha, ea⟩ v
    refine ⟨fun j => a j v, fun j => ha j v, fun i => ?_⟩
    simp only [ea, map_sum]
    rfl
  · intro h
    choose a ha ea using h
    let A : Fin k → 𝔸 := fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    refine ⟨A, fun j v => ha v j, fun i => ?_⟩
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    rw [map_sub, sub_eq_zero, map_sum]
    exact ea v i

theorem prV_mulVec [Fintype n] (v : HeightOneSpectrum (𝓞 F)) (M : Matrix n n (E ⊗[F] 𝔸))
    (u : n → E ⊗[F] 𝔸) :
    (fun i => prV (E := E) v ((M *ᵥ u) i)) =
      M.map (prV (E := E) v) *ᵥ fun i => prV (E := E) v (u i) := by
  funext i
  exact RingHom.map_mulVec _ M u i

theorem mem_stabGL_adele_iff [Fintype n] [DecidableEq n] [Module.Finite (𝓞 E) N]
    (g : GL n (E ⊗[F] 𝔸)) :
    g ∈ stabGL (latS 𝔸 (tensInt (F := F) 𝔸 (intOE E) (intAd F)) N) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈
        stabGL (latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N) := by
  constructor
  · intro hg v x
    have key := hg fun i => Formalism.UG.P.afsplitIE v (x i)
    rw [mem_latS_adele_iff, mem_latS_adele_iff] at key
    simp only [prV_mulVec] at key
    have h0 : ∀ w, w ≠ v → (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE v (x i))) = 0 :=
      fun w hw => funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w hw _
    have h1 : (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (x i))) = x :=
      funext fun i => Formalism.UG.P.afsplit_prV_IE v _
    rw [Formalism.UG.P.afsplit_coe_bc_prV]
    constructor
    · intro hx
      have := key.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw]; exact zero_mem _) v
      rwa [h1] at this
    · intro hx
      have := key.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [h1] at this
  · intro h u
    rw [mem_latS_adele_iff, mem_latS_adele_iff]
    refine forall_congr' fun v => ?_
    rw [prV_mulVec]
    exact h v _

end Adelic

theorem mem_levelAfL_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → ∀ g, g ∈ levelAfL σ J N ↔ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ levelVL σ J v N := by
  intro F E _ _ _ _ _ σ n J N hN g
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
    exact ⟨h1, fun v => Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem σ J v g h1,
      (mem_stabGL_adele_iff N g).1 h2 v⟩⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨h1, (mem_stabGL_adele_iff N g).2 fun v => (Subgroup.mem_inf.1 (h2 v)).2⟩

end GlobalTheory.LatticeStabLocal
