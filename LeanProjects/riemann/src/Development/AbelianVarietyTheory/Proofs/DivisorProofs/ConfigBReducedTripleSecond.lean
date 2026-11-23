import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

namespace SwapShear

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incV_mulVec' {n m : ℕ} (A : Matrix (Fin n) (Fin m) E) (u : Fin m → E) :
    incV F (A *ᵥ u) = incM F A *ᵥ incV F u := by
  ext i
  exact RingHom.map_mulVec _ _ _ _

theorem incV_add' {n : ℕ} (u v : Fin n → E) : incV F (u + v) = incV F u + incV F v := by
  ext i; simp [incV]

theorem incV_smul' {n : ℕ} (c : E) (u : Fin n → E) : incV F (c • u) = inclR (F := F) (AF F) c • incV F u := by
  ext i; simp [incV]

theorem incV_zero' {n : ℕ} : incV F (0 : Fin n → E) = 0 := by
  ext i; simp [incV]

theorem incV_single' {n : ℕ} (j : Fin n) : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
  ext k
  by_cases h : k = j
  · subst h; simp [incV]
  · simp [incV, Pi.single_apply, h]

end Lemmas

section Lemmas2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_ext_of_span {d : ℕ} (S : Set (Fin d → E)) (hS : Submodule.span E S = ⊤)
    {A B : Matrix (Fin d) (Fin d) (AE F E)} (h : ∀ v ∈ S, A *ᵥ incV F v = B *ᵥ incV F v) : A = B := by
  let N : Submodule E (Fin d → E) :=
    { carrier := {v | A *ᵥ incV F v = B *ᵥ incV F v}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq] at *
        rw [incV_add', Matrix.mulVec_add, Matrix.mulVec_add, hu, hv]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, incV_zero', Matrix.mulVec_zero]
      smul_mem' := by
        intro c v hv
        simp only [Set.mem_setOf_eq] at *
        rw [incV_smul', Matrix.mulVec_smul, Matrix.mulVec_smul, hv] }
  have hN : ∀ v, v ∈ N := by
    intro v
    have hv : v ∈ Submodule.span E S := by rw [hS]; exact Submodule.mem_top
    exact (Submodule.span_le (p := N)).2 (fun v hv => h v hv) hv
  ext i j
  have hj := hN (Pi.single j 1)
  change A *ᵥ incV F _ = B *ᵥ incV F _ at hj
  rw [incV_single', Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hj
  exact congrFun hj i

theorem span_two_planes {B : Base F E} {d d₁ e : ℕ} {W : Spc F E d} {W₁ W₁' : Spc F E d₁} {W₂ : Spc F E e}
    {H' : Plane E d d₁} {H₂ : Plane E d₁ e} {i₀ i₁ j₀ j₁ : ℕ} (hlat : W.L.IsLattice E)
    (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (hH₂ : H₂.IsAdapted σ B W₁' W₂ j₀ j₁) (hL : W₁'.L = W₁.L) :
    Submodule.span E (({H'.x, H'.y, H'.ι *ᵥ H₂.x, H'.ι *ᵥ H₂.y} : Set (Fin d → E)) ∪
      Set.range (H'.ι * H₂.ι)ᵀ) = ⊤ := by
  set S : Set (Fin d → E) := ({H'.x, H'.y, H'.ι *ᵥ H₂.x, H'.ι *ᵥ H₂.y} : Set (Fin d → E)) ∪
      Set.range (H'.ι * H₂.ι)ᵀ with hSdef
  have htop : Submodule.span E (W.L : Set (Fin d → E)) = ⊤ := hlat.span_eq_top
  rw [eq_top_iff, ← htop, Submodule.span_le]
  intro z hz
  obtain ⟨s, t, u, -, -, hu, rfl⟩ := hH'.split z hz
  have hu' : u ∈ W₁'.L := by rw [hL]; exact hu
  obtain ⟨s₂, t₂, u₂, -, -, -, rfl⟩ := hH₂.split u hu'
  have mem : ∀ v ∈ S, v ∈ Submodule.span E S := fun v hv => Submodule.subset_span hv
  have hx : H'.x ∈ Submodule.span E S := mem _ (by simp [hSdef])
  have hy : H'.y ∈ Submodule.span E S := mem _ (by simp [hSdef])
  have hx₂ : H'.ι *ᵥ H₂.x ∈ Submodule.span E S := mem _ (by simp [hSdef])
  have hy₂ : H'.ι *ᵥ H₂.y ∈ Submodule.span E S := mem _ (by simp [hSdef])
  have hc : (H'.ι * H₂.ι) *ᵥ u₂ ∈ Submodule.span E S := by
    have h0 : (H'.ι * H₂.ι) *ᵥ u₂ ∈ LinearMap.range (H'.ι * H₂.ι).mulVecLin := ⟨u₂, rfl⟩
    rw [Matrix.range_mulVecLin] at h0
    exact Submodule.span_mono (fun v hv => Or.inr hv) h0
  show s • H'.x + H'.ι *ᵥ (s₂ • H₂.x + H₂.ι *ᵥ u₂ + t₂ • H₂.y) + t • H'.y ∈ Submodule.span E S
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  exact add_mem (add_mem (Submodule.smul_mem _ _ hx) (add_mem (add_mem (Submodule.smul_mem _ _ hx₂) hc)
    (Submodule.smul_mem _ _ hy₂))) (Submodule.smul_mem _ _ hy)

end Lemmas2

section Lemmas3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem ua_ext' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem levi_apply_ι {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {t : (AE F E)ˣ}
    {h₁ : UA σ W₁.J} {h : UA σ W.J} (hl : IsLevi H' t h₁ h) (s : Fin d₁ → AE F E) :
    mat h *ᵥ (incM F H'.ι *ᵥ s) = incM F H'.ι *ᵥ (mat h₁ *ᵥ s) := by
  rw [Matrix.mulVec_mulVec, hl.2.2, ← Matrix.mulVec_mulVec]

theorem incV_col {d k : ℕ} (P : Matrix (Fin d) (Fin k) E) (j : Fin k) :
    incV F (Pᵀ j) = incM F P *ᵥ Pi.single j 1 := by
  have hP : Pᵀ j = P *ᵥ Pi.single j 1 := (Matrix.mulVec_single_one P j).symm
  rw [hP, incV_mulVec', incV_single']

theorem incM_mul' {l k n : ℕ} (P : Matrix (Fin l) (Fin k) E) (Q : Matrix (Fin k) (Fin n) E) :
    incM F (P * Q) = incM F P * incM F Q := Matrix.map_mul

end Lemmas3

end SwapShear

open SwapShear

theorem swap_shear_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ → ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' t 1 m → (∀ h₁, emb h₁ * m = m * emb h₁) ∧
      ∃ m₂ : UA σ G₁.W.J, IsLevi (W₁ := W₂) H₂ t 1 m₂ ∧ ∀ c, w * nn c * m = emb m₂ * w * nn ((t⁻¹ : (AE F E)ˣ).1 * c) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT₁' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hn
    t m hm
  have hS := span_two_planes (hT.geo.hW.lat) hC.hH' hH₂ rfl
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : UA σ G₁.W.J, IsLevi (W₁ := W₂) H₂ t 1 m₂ := GlobalTheory.ThK.exists_isLevi F E σ B _ _ _ W₂ H₂ _ _ i₀ i₁ hT₁'.base.cm hT₁'.geo.hW hH₂ t
  have hmι : ∀ s, mat m *ᵥ (incM F H'.ι *ᵥ s) = incM F H'.ι *ᵥ s := fun s => by
    rw [levi_apply_ι hm, mat_one', Matrix.one_mulVec]
  have hm₂ι : ∀ s, mat m₂ *ᵥ (incM F H₂.ι *ᵥ s) = incM F H₂.ι *ᵥ s := fun s => by
    rw [levi_apply_ι hm₂, mat_one', Matrix.one_mulVec]
  have hembx : ∀ h₁, mat (emb h₁) *ᵥ incV F H'.x = incV F H'.x := fun h₁ => by
    rw [(hemb h₁).1]; simp
  have hemby : ∀ h₁, mat (emb h₁) *ᵥ incV F H'.y = incV F H'.y := fun h₁ => by
    rw [(hemb h₁).2.1]; simp
  refine ⟨fun h₁ => ?_, m₂, hm₂, fun c => ?_⟩
  · apply ua_ext'
    apply mat_ext_of_span _ hS
    rintro v (hv | hv)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul, hembx, hm.1]
      · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm.2.1, Matrix.mulVec_smul, hemby, hm.2.1]
      · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, incV_mulVec', hmι, levi_apply_ι (hemb h₁), hmι]
      · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, incV_mulVec', hmι, levi_apply_ι (hemb h₁), hmι]
    · obtain ⟨j, rfl⟩ := hv
      rw [incV_col, incM_mul', ← Matrix.mulVec_mulVec, mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmι, levi_apply_ι (hemb h₁), hmι]
  · obtain ⟨-, wx, wy, wx₂, wy₂, wP⟩ := hw
    have hmX₂ : mat m *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x) := by rw [incV_mulVec', hmι]
    have hmY₂ : mat m *ᵥ incV F (H'.ι *ᵥ H₂.y) = incV F (H'.ι *ᵥ H₂.y) := by rw [incV_mulVec', hmι]
    have heX₂ : mat (emb m₂) *ᵥ incV F (H'.ι *ᵥ H₂.x) = t.1 • incV F (H'.ι *ᵥ H₂.x) := by
      rw [incV_mulVec', levi_apply_ι (hemb m₂), hm₂.1, Matrix.mulVec_smul]
    have heY₂ : mat (emb m₂) *ᵥ incV F (H'.ι *ᵥ H₂.y) = cA σ (t⁻¹).1 • incV F (H'.ι *ᵥ H₂.y) := by
      rw [incV_mulVec', levi_apply_ι (hemb m₂), hm₂.2.1, Matrix.mulVec_smul]
    have hmP : ∀ s, mat m *ᵥ (incM F (H'.ι * H₂.ι) *ᵥ s) = incM F (H'.ι * H₂.ι) *ᵥ s := fun s => by
      rw [incM_mul', ← Matrix.mulVec_mulVec, hmι]
    have heP : ∀ s, mat (emb m₂) *ᵥ (incM F (H'.ι * H₂.ι) *ᵥ s) = incM F (H'.ι * H₂.ι) *ᵥ s := fun s => by
      rw [incM_mul', ← Matrix.mulVec_mulVec, levi_apply_ι (hemb m₂), hm₂ι]
    have hwP : ∀ s, mat w *ᵥ (incM F (H'.ι * H₂.ι) *ᵥ s) = incM F (H'.ι * H₂.ι) *ᵥ s := fun s => by
      rw [Matrix.mulVec_mulVec, wP]
    have hnP : ∀ c' s, mat (nn c') *ᵥ (incM F (H'.ι * H₂.ι) *ᵥ s) = incM F (H'.ι * H₂.ι) *ᵥ s := fun c' s => by
      rw [Matrix.mulVec_mulVec, (hn c').2.2.2.2]
    have nx := fun c' => (hn c').1
    have nx₂ := fun c' => (hn c').2.1
    have ny₂ := fun c' => (hn c').2.2.1
    have ny := fun c' => (hn c').2.2.2.1
    have ht : ((t⁻¹ : (AE F E)ˣ).1 * c) * t.1 = c := by
      rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    apply ua_ext'
    apply mat_ext_of_span _ hS
    rintro v (hv | hv)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · simp only [mat_mul', ← Matrix.mulVec_mulVec, hm.1, Matrix.mulVec_smul, nx, wx, heX₂]
      · simp only [mat_mul', ← Matrix.mulVec_mulVec, hm.2.1, Matrix.mulVec_smul, Matrix.mulVec_sub, ny, wy, wy₂, heY₂,
          hemby, map_mul]
        rw [smul_sub, smul_smul]
      · simp only [mat_mul', ← Matrix.mulVec_mulVec, hmX₂, Matrix.mulVec_smul, Matrix.mulVec_add, nx₂, wx, wx₂, heX₂,
          hembx, smul_smul, ht]
      · simp only [mat_mul', ← Matrix.mulVec_mulVec, hmY₂, ny₂, wy₂, hemby]
    · obtain ⟨j, rfl⟩ := hv
      simp only [incV_col, mat_mul', ← Matrix.mulVec_mulVec, hmP, hnP, hwP, heP]

end GlobalTheory.ConeSmallMidJB
