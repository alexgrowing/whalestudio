import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementFormRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicDecompContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnipotentRadicalIffStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviSec

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_neg, Matrix.det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

theorem leviSection_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s →
    X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g g', m (l * l') (g * g') = m l g * m l' g') ∧ Continuous (fun x : (AE F E)ˣ × UA σ X₁.J => m x.1 x.2) ∧
    (∀ l g, m l g ∈ GlobalTheory.IwLine.lineStab σ X.J H.x) ∧
    (∀ q ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∃! z : unip σ X H × ((AE F E)ˣ × UA σ X₁.J), q = z.1.1 * m z.2.1 z.2.2) ∧
    IsClosed (GlobalTheory.IwLine.lineStab σ X.J H.x : Set (UA σ X.J)) ∧ IsClosed (unip σ X H : Set (UA σ X.J)) ∧
    unip σ X H ≤ GlobalTheory.IwLine.lineStab σ X.J H.x ∧ ∀ q ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∀ u ∈ unip σ X H, q * u * q⁻¹ ∈ unip σ X H := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm
  classical
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hσ : IsCMExt F E σ := hB.cm
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have hJ1 : X₁.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply det_ne_zero_of_hasSig (hX₁.sig w)
    have e := RingHom.map_det ((B.emb w).1) X₁.J
    rw [h0, map_zero] at e
    exact e.symm
  have hx0 : H.x ≠ 0 := by
    intro h; have := hH.xy; rw [h] at this; simp [form] at this
  have hspan := GlobalTheory.T.hyperbolic_complement_hermitian F E σ n n₁ X.J X₁.J H.x H.y H.ι hs hX.herm hH.rank hH.xx hH.yy hH.xy hH.orth hH.gram hJ1
  have hind := GlobalTheory.T.hyperbolic_complement_form_restrict F E σ n n₁ X.J X₁.J H.x H.y H.ι hs hX.herm hH.xx hH.yy hH.xy hH.orth hH.gram hJ1
  have hunip := fun u => GlobalTheory.T.mem_unipotent_radical_iff F E σ n n₁ X H u
  have ext : ∀ g g' : UA σ X.J, mat g = mat g' → g = g' := fun g g' h => Subtype.ext (Units.ext h)
  have ext₁ : ∀ g g' : UA σ X₁.J, (∀ w, mat g *ᵥ w = mat g' *ᵥ w) → g = g' := by
    intro g g' h
    refine Subtype.ext (Units.ext ?_)
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, mat] using this
  have mat_mul : ∀ g g' : UA σ X.J, mat (g * g') = mat g * mat g' := fun _ _ => rfl
  have mat_mul₁ : ∀ g g' : UA σ X₁.J, mat (g * g') = mat g * mat g' := fun _ _ => rfl
  have U : ∀ A A' : Matrix (Fin n) (Fin n) (AE F E), A *ᵥ incV F H.x = A' *ᵥ incV F H.x →
      A *ᵥ incV F H.y = A' *ᵥ incV F H.y → A * incM F H.ι = A' * incM F H.ι → A = A' := by
    intro A A' h1 h2 h3
    have key : ∀ z, A *ᵥ z = A' *ᵥ z := by
      intro z
      obtain ⟨a, b, w, rfl⟩ := hspan z
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h2, h3]
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  have hι : ∀ l g w, mat (m l g) *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g *ᵥ w) := by
    intro l g w
    rw [Matrix.mulVec_mulVec, (hm l g).2.2, ← Matrix.mulVec_mulVec]
  have hmul : ∀ l l' g g', m (l * l') (g * g') = m l g * m l' g' := by
    intro l l' g g'
    apply ext
    obtain ⟨h1, h2, h3⟩ := hm (l * l') (g * g')
    obtain ⟨k1, k2, k3⟩ := hm l g
    obtain ⟨j1, j2, j3⟩ := hm l' g'
    apply U
    · rw [h1, mat_mul, ← Matrix.mulVec_mulVec, j1, Matrix.mulVec_smul, k1, smul_smul, Units.val_mul, mul_comm]
    · rw [h2, mat_mul, ← Matrix.mulVec_mulVec, j2, Matrix.mulVec_smul, k2, smul_smul, mul_inv_rev, Units.val_mul,
        map_mul]
    · rw [h3, mat_mul, Matrix.mul_assoc, j3, ← Matrix.mul_assoc, k3, Matrix.mul_assoc, mat_mul₁]
  have h11 : m 1 1 = 1 := by
    have := hmul 1 1 1 1
    simp only [mul_one] at this
    exact mul_left_cancel (a := m 1 1) (by rw [← this, mul_one])
  have hinv : ∀ l g, (m l g)⁻¹ = m l⁻¹ g⁻¹ := by
    intro l g
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← hmul, inv_mul_cancel, inv_mul_cancel, h11]
  have hc0 : Continuous (fun p : (AE F E)ˣ × UA σ X₁.J => mat (m p.1 p.2)) :=
    GlobalTheory.T.hyperbolic_decomp_continuous F E σ n n₁ X.J X₁.J H.x H.y H.ι hspan _ (fun p => hm p.1 p.2)
  have hcont : Continuous (fun x : (AE F E)ˣ × UA σ X₁.J => m x.1 x.2) := by
    have hc1 : Continuous (fun p : (AE F E)ˣ × UA σ X₁.J => mat (m p.1⁻¹ p.2⁻¹)) :=
      hc0.comp (continuous_inv.prodMap continuous_inv)
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hc0, ?_⟩)
    convert hc1 using 2 with p
    rw [← hinv]; rfl
  have hlx : ∀ u ∈ unip σ X H, ∀ l g, mat (u * m l g) *ᵥ incV F H.x = (l : AE F E) • incV F H.x := by
    intro u hu l g
    rw [mat_mul, ← Matrix.mulVec_mulVec, (hm l g).1, Matrix.mulVec_smul, ((hunip u).1 hu).1]
  have hlι : ∀ u ∈ unip σ X H, ∀ l g w, ∃ c : AE F E,
      mat (u * m l g) *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ (mat g *ᵥ w) + c • incV F H.x := by
    intro u hu l g w
    rw [mat_mul, ← Matrix.mulVec_mulVec, hι]
    exact ((hunip u).1 hu).2 _
  have huniq : ∀ u₁ ∈ unip σ X H, ∀ u₂ ∈ unip σ X H, ∀ l₁ g₁ l₂ g₂,
      u₁ * m l₁ g₁ = u₂ * m l₂ g₂ → l₁ = l₂ ∧ g₁ = g₂ := by
    intro u₁ h₁ u₂ h₂ l₁ g₁ l₂ g₂ he
    have e1 : (l₁ : AE F E) • incV F H.x = (l₂ : AE F E) • incV F H.x := by
      rw [← hlx u₁ h₁ l₁ g₁, he, hlx u₂ h₂ l₂ g₂]
    refine ⟨Units.ext (sub_eq_zero.1 (hind ((l₁ : AE F E) - l₂) 0 0 ?_).1), ext₁ _ _ fun w => ?_⟩
    · rw [Matrix.mulVec_zero, zero_smul, add_zero, add_zero, sub_smul, e1, sub_self]
    · obtain ⟨c₁, hc₁⟩ := hlι u₁ h₁ l₁ g₁ w
      obtain ⟨c₂, hc₂⟩ := hlι u₂ h₂ l₂ g₂ w
      rw [he, hc₂] at hc₁
      have := (hind (c₁ - c₂) 0 (mat g₁ *ᵥ w - mat g₂ *ᵥ w) ?_).2.1
      · exact sub_eq_zero.1 this
      · rw [Matrix.mulVec_sub, zero_smul, add_zero, sub_smul]
        refine Eq.trans ?_ (sub_eq_zero.2 hc₁.symm)
        abel
  have hdec : ∀ q ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∃! z : unip σ X H × ((AE F E)ˣ × UA σ X₁.J),
      q = z.1.1 * m z.2.1 z.2.2 := by
    rintro q ⟨a, ha⟩
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.T.hyperbolic_complement_nondegenerate F E σ n n₁ X.J X₁.J H.x H.y H.ι hs hX.herm hH.xx hH.yy hH.xy hH.orth hH.gram hJ1 hspan q a ha
    have hu : q * (m a g₀)⁻¹ ∈ unip σ X H := by
      rw [hunip, hinv]
      refine ⟨?_, fun z => ?_⟩
      · rw [mat_mul, ← Matrix.mulVec_mulVec, (hm a⁻¹ g₀⁻¹).1, Matrix.mulVec_smul, ha, smul_smul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_smul]
      · obtain ⟨c, hc⟩ := hg₀ (mat g₀⁻¹ *ᵥ z)
        refine ⟨c, ?_⟩
        rw [mat_mul, ← Matrix.mulVec_mulVec, hι, hc, Matrix.mulVec_mulVec _ (mat g₀), GlobalTheory.StabHaar.mat_mul_inv,
          Matrix.one_mulVec]
    refine ⟨(⟨q * (m a g₀)⁻¹, hu⟩, (a, g₀)), (inv_mul_cancel_right q (m a g₀)).symm, ?_⟩
    rintro ⟨⟨u', hu'⟩, l', g'⟩ hq'
    have e : u' * m l' g' = q * (m a g₀)⁻¹ * m a g₀ := by rw [inv_mul_cancel_right]; exact hq'.symm
    obtain ⟨rfl, rfl⟩ := huniq u' hu' _ hu l' g' a g₀ e
    have : u' = q * (m l' g')⁻¹ := eq_mul_inv_of_mul_eq hq'.symm
    subst this
    rfl
  have hS : (unip σ X H : Set (UA σ X.J)) = {u : UA σ X.J | mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x} := Set.ext hunip
  have hcl := GlobalTheory.T.line_stabilizer_closed F E σ n n₁ X.J H.x H.ι hx0
  have hle : unip σ X H ≤ GlobalTheory.IwLine.lineStab σ X.J H.x := fun u hu =>
    ⟨1, by rw [Units.val_one, one_smul]; exact ((hunip u).1 hu).1⟩
  have hlevi : ∀ l g, ∀ u ∈ unip σ X H, m l g * u * (m l g)⁻¹ ∈ unip σ X H := by
    intro l g u hu
    rw [hunip, hinv]
    obtain ⟨u1, u2⟩ := (hunip u).1 hu
    refine ⟨?_, fun z => ?_⟩
    · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, (hm l⁻¹ g⁻¹).1, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, u1,
        (hm l g).1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    · obtain ⟨c, hc⟩ := u2 (mat g⁻¹ *ᵥ z)
      refine ⟨c * l, ?_⟩
      rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, hι,
        Matrix.mulVec_mulVec _ (mat g), GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec, Matrix.mulVec_smul, (hm l g).1,
        smul_smul, mul_comm]
  refine ⟨hmul, hcont, fun l g => ⟨l, (hm l g).1⟩, hdec, hcl.1, hS ▸ hcl.2, hle, ?_⟩
  intro q hq u hu
  obtain ⟨⟨⟨u₀, hu₀⟩, l, g⟩, hq0, -⟩ := hdec q hq
  simp only at hq0
  subst hq0
  have h1 := hlevi l g u hu
  have : u₀ * m l g * u * (u₀ * m l g)⁻¹ = u₀ * (m l g * u * (m l g)⁻¹) * u₀⁻¹ := by group
  rw [this]
  exact (unip σ X H).mul_mem ((unip σ X H).mul_mem hu₀ h1) ((unip σ X H).inv_mem hu₀)

end GlobalTheory.LeviSec

end
