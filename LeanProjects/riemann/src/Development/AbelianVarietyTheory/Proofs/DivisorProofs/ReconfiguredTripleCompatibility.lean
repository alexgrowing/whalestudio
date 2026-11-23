import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.SwapShearLines

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inclR_injective' : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incV_add' {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  ext i; simp [incV]

theorem incV_smul' {n : ℕ} (c : E) (a : Fin n → E) : incV F (c • a) = inclR (F := F) (AF F) c • incV F a := by
  ext i; simp [incV]

theorem incV_zero' {n : ℕ} : incV F (0 : Fin n → E) = 0 := by ext i; simp [incV]

theorem incM_mulVec' {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum]

theorem incV_dot' {n : ℕ} (a b : Fin n → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [incV, dotProduct, map_sum]

theorem incM_mul' {m n k : ℕ} (A : Matrix (Fin m) (Fin n) E) (B : Matrix (Fin n) (Fin k) E) :
    incM F (A * B) = incM F A * incM F B := by
  simp [incM, Matrix.map_mul]

theorem cA_inclR' (c : E) : cA σ (inclR (F := F) (AF F) c) = inclR (F := F) (AF F) (σ c) := by
  simp [cA, inclR]

theorem sig_invol' (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem mat_mul'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul'' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem inv_mulVec_of {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {u v : Fin n → AE F E}
    (h : mat g *ᵥ v = u) : mat g⁻¹ *ᵥ u = v := by
  rw [← h, Matrix.mulVec_mulVec, mat_inv_mul'', Matrix.one_mulVec]

theorem exists_incM_of_span {d : ℕ} (M : Matrix (Fin d) (Fin d) (AE F E)) (S : Set (Fin d → E))
    (hS : Submodule.span E S = ⊤) (hM : ∀ v ∈ S, ∃ v', M *ᵥ incV F v = incV F v') :
    ∃ R : Matrix (Fin d) (Fin d) E, M = incM F R := by
  have key : ∀ v : Fin d → E, ∃ v', M *ᵥ incV F v = incV F v' := by
    intro v
    have hv : v ∈ Submodule.span E S := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact hM x hx
    | zero => exact ⟨0, by simp [incV_zero']⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [incV_add', Matrix.mulVec_add, hx', hy', incV_add']⟩
    | smul c x _ hx =>
      obtain ⟨x', hx'⟩ := hx
      exact ⟨c • x', by rw [incV_smul', Matrix.mulVec_smul, hx', incV_smul']⟩
  choose f hf using key
  refine ⟨Matrix.of fun i j => f (Pi.single j 1) i, ?_⟩
  ext i j
  have h1 := congrFun (hf (Pi.single j 1)) i
  have h2 : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
    ext k; by_cases hk : k = j <;> simp [incV, Pi.single_apply, hk]
  rw [h2, Matrix.mulVec_single_one] at h1
  simpa [incM, incV] using h1

theorem mem_ratU_of_eq_incM {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (R : Matrix (Fin n) (Fin n) E)
    (h : mat g = incM F R) : g ∈ ratU σ J := by
  have hdet : R.det ≠ 0 := by
    intro h0
    have hu : IsUnit (mat g).det := by
      have := (Matrix.GeneralLinearGroup.det g.1).isUnit
      simpa [mat] using this
    rw [h, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, isUnit_zero_iff] at hu
    have : inclR (F := F) (AF F) (0 : E) = inclR (F := F) (AF F) 1 := by rw [map_zero, map_one, hu]
    exact zero_ne_one (inclR_injective' this)
  rw [ratU, Subgroup.mem_subgroupOf]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero R hdet, ?_⟩
  ext i j
  have := congrFun (congrFun h i) j
  simp only [mat] at this
  rw [this]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, incM]

theorem exists_mat_eq_of_mem_ratU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ R : Matrix (Fin n) (Fin n) E, mat g = incM F R := by
  rw [ratU, Subgroup.mem_subgroupOf] at hg
  obtain ⟨γ₀, hγ⟩ := hg
  refine ⟨γ₀.1, ?_⟩
  rw [mat, ← hγ]
  ext i j
  simp [incM]

theorem span_plane {d d₁ : ℕ} (B : Base F E) (H : Plane E d d₁) (Y : Spc F E d) (Y₁ : Spc F E d₁) (i₀ i₁ : ℕ)
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) :
    Submodule.span E ({H.x, H.y} ∪ Set.range (fun u => H.ι *ᵥ u)) = ⊤ := by
  rw [eq_top_iff, ← hL.span_eq_top]
  refine Submodule.span_le.2 fun z hz => ?_
  obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.subset_span (Or.inr ⟨u, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem span_two_planes {d d₁ e : ℕ} (B : Base F E) (H : Plane E d d₁) (H₂ : Plane E d₁ e) (Y : Spc F E d)
    (Y₁ Y₁' : Spc F E d₁) (Y₂ : Spc F E e) (i₀ i₁ j₀ j₁ : ℕ)
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hH₂ : H₂.IsAdapted σ B Y₁' Y₂ j₀ j₁) (hLL : Y₁'.L = Y₁.L)
    (hL : Y.L.IsLattice E) :
    Submodule.span E ({H.x, H.y, H.ι *ᵥ H₂.x, H.ι *ᵥ H₂.y} ∪ Set.range (fun u => (H.ι * H₂.ι) *ᵥ u)) = ⊤ := by
  rw [eq_top_iff, ← hL.span_eq_top]
  refine Submodule.span_le.2 fun z hz => ?_
  obtain ⟨s, t, u, -, -, hu, rfl⟩ := hH.split z hz
  obtain ⟨s', t', u', -, -, -, rfl⟩ := hH₂.split u (hLL ▸ hu)
  have e1 : H.ι *ᵥ (s' • H₂.x + H₂.ι *ᵥ u' + t' • H₂.y) =
      s' • (H.ι *ᵥ H₂.x) + (H.ι * H₂.ι) *ᵥ u' + t' • (H.ι *ᵥ H₂.y) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e1]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_)) ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.subset_span (Or.inr ⟨u', rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem form_ι {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E) (u v : Fin d₁ → E) :
    form σ J (ι *ᵥ u) (ι *ᵥ v) = form σ (ιᵀ * J * ι.map σ) u v := by
  simp only [form]
  have : (fun i => σ ((ι *ᵥ v) i)) = ι.map σ *ᵥ fun i => σ (v i) := by
    ext i; simp [Matrix.mulVec, dotProduct, map_sum]
  rw [this, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem form_swap {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j)
    (u v : Fin d → E) : form σ J u v = -σ (form σ J v u) := by
  simp only [form, Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem inv_swap_shear {d d₁ e : ℕ} {J : Matrix (Fin d) (Fin d) E} {H' : Plane E d d₁} {H₂ : Plane E d₁ e}
    {w : UA σ J} (hw : IsSwap H' H₂ w) {nn : AE F E → UA σ J} (hn : IsShear H' H₂ nn) (c : AE F E) :
    mat (w * nn c)⁻¹ *ᵥ incV F H'.x = incV F (H'.ι *ᵥ H₂.x) - c • incV F H'.x := by
  rw [mul_inv_rev, mat_mul'', ← Matrix.mulVec_mulVec, inv_mulVec_of w hw.2.2.2.1]
  apply inv_mulVec_of
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, (hn c).1, (hn c).2.1, add_sub_cancel_right]

theorem unip_prop {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (x₂ : Fin d₁ → E) {u : UA σ W.J}
    (hu : u ∈ unip σ W H') :
    mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∃ a : AE F E, mat u *ᵥ incV F (H'.ι *ᵥ x₂) = incV F (H'.ι *ᵥ x₂) + a • incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha⟩ := hv.2 (incV F x₂)
    rw [incM_mulVec'] at ha
    exact ⟨hv.1, a, ha⟩
  | one => exact ⟨by simp [mat_one''], 0, by simp [mat_one'']⟩
  | mul u v _ _ hu hv =>
    obtain ⟨hu1, a, ha⟩ := hu
    obtain ⟨hv1, b, hb⟩ := hv
    refine ⟨by rw [mat_mul'', ← Matrix.mulVec_mulVec, hv1, hu1], a + b, ?_⟩
    rw [mat_mul'', ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu1, add_smul, add_assoc]
  | inv u _ hu =>
    obtain ⟨hu1, a, ha⟩ := hu
    refine ⟨inv_mulVec_of u hu1, -a, inv_mulVec_of u ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu1, neg_smul, add_neg_cancel_right]

theorem pair_incV {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (u z : Fin d → E) :
    incV F u ⬝ᵥ incV F (J *ᵥ fun i => σ (z i)) = inclR (F := F) (AF F) (form σ J u z) := by
  rw [incV_dot']; rfl

theorem incV_sub' {n : ℕ} (a b : Fin n → E) : incV F (a - b) = incV F a - incV F b := by
  ext i; simp [incV]

end GlobalTheory.SwapShearLines

namespace GlobalTheory.SwapShearLines

theorem swap_shear_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    (∀ γ ∈ ratU σ G₁.W.J, emb γ ∈ ratU σ G.W.J) ∧
    (∀ c : E, w * nn (inclR (F := F) (AF F) c) ∈ ratU σ G.W.J) ∧
    (∀ c c' : E, GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) c) * (w * nn (inclR (F := F) (AF F) c'))⁻¹) → c = c') ∧
    (∀ δ ∈ ratU σ G.W.J ⊓ unip σ G.W H', ∃ a₀ : E, ∀ c : E,
      GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) c) * δ * (w * nn (inclR (F := F) (AF F) (c + a₀)))⁻¹)) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT₁' e W₂ H₂ i₀ i₁ hH₂ emb hL w hw nn hn
  have hH' := hC.hH'
  have hlat : G.W.L.IsLattice E := hT.geo.hW.lat
  have hσ : ∀ t, σ (σ t) = t := sig_invol' hT.base.cm
  have hJ := hT.geo.hW.skew
  have fxy : form σ G.W.J H'.x H'.y = 1 := hH'.xy
  have fx2y : form σ G.W.J (H'.ι *ᵥ H₂.x) H'.y = 0 := (hH'.orth H₂.x).2
  have fxy2 : form σ G.W.J H'.x (H'.ι *ᵥ H₂.y) = 0 := by
    rw [form_swap _ hσ hJ, (hH'.orth H₂.y).1, map_zero, neg_zero]
  have fx2y2 : form σ G.W.J (H'.ι *ᵥ H₂.x) (H'.ι *ᵥ H₂.y) = 1 := by
    rw [form_ι, hH'.gram]; exact hH₂.xy
  refine ⟨fun γ hγ => ?_, fun c => ?_, fun c c' hst => ?_, fun δ hδ => ?_⟩
  · obtain ⟨γ₀, hγ₀⟩ := exists_mat_eq_of_mem_ratU hγ
    obtain ⟨h1, h2, h3⟩ := hL γ
    simp only [Units.val_one, one_smul, inv_one, map_one] at h1 h2
    suffices hM : ∀ v ∈ ({H'.x, H'.y} ∪ Set.range (fun u => H'.ι *ᵥ u) : Set _),
        ∃ v', mat (emb γ) *ᵥ incV F v = incV F v' by
      obtain ⟨R, hR⟩ := exists_incM_of_span _ _ (span_plane B H' G.W G₁.W _ _ hH' hlat) hM
      exact mem_ratU_of_eq_incM _ R hR
    rintro v ((rfl | rfl) | ⟨u, rfl⟩)
    · exact ⟨_, h1⟩
    · exact ⟨_, h2⟩
    · refine ⟨H'.ι *ᵥ (γ₀ *ᵥ u), ?_⟩
      rw [← incM_mulVec', Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, hγ₀, incM_mulVec', incM_mulVec']
  · refine mul_mem hw.1 ?_
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn (inclR (F := F) (AF F) c)
    suffices hM : ∀ v ∈ ({H'.x, H'.y, H'.ι *ᵥ H₂.x, H'.ι *ᵥ H₂.y} ∪ Set.range (fun u => (H'.ι * H₂.ι) *ᵥ u) : Set _),
        ∃ v', mat (nn (inclR (F := F) (AF F) c)) *ᵥ incV F v = incV F v' by
      obtain ⟨R, hR⟩ := exists_incM_of_span _ _
        (span_two_planes B H' H₂ G.W G₁.W _ W₂ _ _ _ _ hH' hH₂ rfl hlat) hM
      exact mem_ratU_of_eq_incM _ R hR
    rintro v ((rfl | rfl | rfl | rfl) | ⟨u, rfl⟩)
    · exact ⟨_, n1⟩
    · exact ⟨H'.y - σ c • (H'.ι *ᵥ H₂.y), by rw [n4, cA_inclR', incV_sub', incV_smul']⟩
    · exact ⟨H'.ι *ᵥ H₂.x + c • H'.x, by rw [n2, incV_add', incV_smul']⟩
    · exact ⟨_, n3⟩
    · exact ⟨(H'.ι * H₂.ι) *ᵥ u, by rw [← incM_mulVec', Matrix.mulVec_mulVec, n5]⟩
  · obtain ⟨l, hl⟩ := hst
    have e1 : mat (w * nn (inclR (F := F) (AF F) c))⁻¹ *ᵥ (l.1 • incV F H'.x) =
        mat (w * nn (inclR (F := F) (AF F) c'))⁻¹ *ᵥ incV F H'.x := by
      apply inv_mulVec_of
      rw [← hl, Matrix.mulVec_mulVec]
      rfl
    rw [Matrix.mulVec_smul, inv_swap_shear hw hn, inv_swap_shear hw hn] at e1
    have p1 := congrArg (fun v => v ⬝ᵥ incV F (G.W.J *ᵥ fun i => σ ((H'.ι *ᵥ H₂.y) i))) e1
    have p2 := congrArg (fun v => v ⬝ᵥ incV F (G.W.J *ᵥ fun i => σ (H'.y i))) e1
    simp only [smul_dotProduct, sub_dotProduct, pair_incV, fxy, fx2y, fxy2, fx2y2, map_one, map_zero,
      smul_eq_mul, mul_zero, mul_one, sub_zero, zero_sub] at p1 p2
    rw [p1, one_mul, neg_inj] at p2
    exact inclR_injective' p2
  · obtain ⟨hδr, hδu⟩ := Subgroup.mem_inf.1 hδ
    obtain ⟨D, hD⟩ := exists_mat_eq_of_mem_ratU hδr
    obtain ⟨hδ1, a', ha'⟩ := unip_prop H₂.x hδu
    have hrat : incV F (D *ᵥ (H'.ι *ᵥ H₂.x)) = incV F (H'.ι *ᵥ H₂.x) + a' • incV F H'.x := by
      rw [← incM_mulVec', ← hD, ha']
    have p := congrArg (fun v => v ⬝ᵥ incV F (G.W.J *ᵥ fun i => σ (H'.y i))) hrat
    simp only [add_dotProduct, smul_dotProduct, pair_incV, fx2y, fxy, map_zero, map_one, smul_eq_mul, mul_one,
      zero_add] at p
    have hδU : mat δ⁻¹ *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x) - a' • incV F H'.x :=
      inv_mulVec_of δ (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha', hδ1, add_sub_cancel_right])
    refine ⟨form σ G.W.J (D *ᵥ (H'.ι *ᵥ H₂.x)) H'.y, fun c => ⟨1, ?_⟩⟩
    have e2 : mat (w * nn (inclR (F := F) (AF F) c) * δ)⁻¹ *ᵥ incV F H'.x =
        mat (w * nn (inclR (F := F) (AF F) (c + form σ G.W.J (D *ᵥ (H'.ι *ᵥ H₂.x)) H'.y)))⁻¹ *ᵥ incV F H'.x := by
      rw [inv_swap_shear hw hn, mul_inv_rev, mat_mul'', ← Matrix.mulVec_mulVec, inv_swap_shear hw hn,
        Matrix.mulVec_sub, Matrix.mulVec_smul, inv_mulVec_of δ hδ1, hδU, map_add, p, add_smul]
      abel
    rw [mat_mul'', ← Matrix.mulVec_mulVec, ← e2, Matrix.mulVec_mulVec, ← mat_mul'', mul_inv_cancel, mat_one'',
      Matrix.one_mulVec, Units.val_one, one_smul]

end GlobalTheory.SwapShearLines
