import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Decomp

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

def TQ {m : ℕ} (b : Fin m → 𝓞 E) (s : E ⊗[F] R) : Prop :=
  ∃ r : Fin m → R, (∀ j, r j ∈ S₂) ∧ s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

variable {R S₂}

theorem tq_zero {m : ℕ} (b : Fin m → 𝓞 E) : TQ (F := F) R S₂ b 0 :=
  ⟨0, fun _ => S₂.zero_mem, by simp⟩

theorem tq_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) :
    TQ R S₂ b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  exact ⟨r + r', fun j => S₂.add_mem (hr j) (hr' j), by
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem tq_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : E ⊗[F] R} (hx : TQ R S₂ b x) : TQ R S₂ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨-r, fun j => S₂.neg_mem (hr j), by simp [TensorProduct.tmul_neg]⟩

theorem tq_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] R)
    (h : ∀ i ∈ s, TQ R S₂ b (f i)) : TQ R S₂ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (TQ R S₂ b) (fun _ _ hx hy => tq_add b hx hy) (tq_zero b) h

theorem tq_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : R} (hy : y ∈ S₂) : TQ R S₂ b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy (c j), ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  exact TensorProduct.smul_tmul _ _ _

theorem tq_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) : TQ R S₂ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine tq_sum b _ _ fun j _ => tq_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact tq_tmul b hb _ (S₂.mul_mem (hr j) (hr' k))

theorem tq_decomp {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) S₂) : TQ R S₂ b s := by
  unfold tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, ⟨e, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact tq_tmul b hb e S₂.one_mem
    · have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) hy
      simpa using h1
  | zero => exact tq_zero b
  | one =>
    have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) (S₂.one_mem)
    simpa [Algebra.TensorProduct.one_def] using h1
  | add x y _ _ hx hy => exact tq_add b hx hy
  | neg x _ hx => exact tq_neg b hx
  | mul x y _ _ hx hy => exact tq_mul b hb hx hy

theorem tensInt_tmul_mem (e : 𝓞 E) {y : R} (hy : y ∈ S₂) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ := by
  have h1 : algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : R) ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem inclE_mem_tensInt (e : 𝓞 E) :
    inclE (F := F) R (algebraMap (𝓞 E) E e) ∈ tensInt (F := F) R (intOE E) S₂ :=
  tensInt_tmul_mem e S₂.one_mem

end Decomp

end Formalism.L2.GlobalTheoryTheory.Br
