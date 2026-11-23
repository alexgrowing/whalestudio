import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StabCosetDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incV_inj {n : ℕ} : Function.Injective (incV (E := E) (n := n) F) :=
  fun x y h => funext fun i => inclR_inj (congrFun h i)

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem eq_of_mulVec {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) {x y v : Fin n → E}
    (hx : mat h *ᵥ incV F x = incV F v) (hy : mat h *ᵥ incV F y = incV F v) : x = y := by
  apply incV_inj (F := F)
  have e : ∀ z, incV F z = mat h⁻¹ *ᵥ (mat h *ᵥ incV F z) := fun z => by
    rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
  rw [e x, e y, hx, hy]

theorem rat_desc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (δ : UA σ J) (hδ : δ ∈ ratU σ J) :
    ∃ g : Matrix (Fin n) (Fin n) E, mat δ = g.map (inclR (F := F) (AF F)) ∧ gᵀ * J * g.map σ = J := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.1 hδ
  have hm : mat δ = g₀.1.map (inclR (F := F) (AF F)) := by
    show δ.1.1 = _
    rw [← hg₀]; rfl
  refine ⟨g₀.1, hm, ?_⟩
  have hu : (mat δ)ᵀ * incM F J * (mat δ).map (cA σ) = incM F J := δ.2
  have key : (g₀.1ᵀ * J * g₀.1.map σ).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have e2 : (g₀.1.map σ).map (inclR (F := F) (AF F)) = (mat δ).map (cA σ) := by
      rw [hm]; ext i j; simp [cA_inclR]
    rw [e2, ← hm]
    exact hu
  exact Matrix.ext fun i j => inclR_inj (congrFun (congrFun key i) j)

theorem form_pres {σ : E →ₐ[F] E} {n : ℕ} {J g : Matrix (Fin n) (Fin n) E} (hg : gᵀ * J * g.map σ = J)
    (x y : Fin n → E) : form σ J (g *ᵥ x) (g *ᵥ y) = form σ J x y := by
  have h1 : (fun i => σ ((g *ᵥ y) i)) = g.map σ *ᵥ fun i => σ (y i) := by
    funext i; exact RingHom.map_mulVec (σ : E →+* E) g y i
  simp only [form]
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

end GlobalTheory.StabCosetDomain

open GlobalTheory.StabCosetDomain in

theorem GlobalTheory.StabCosetDomain.translates_isFundamentalDomain : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ γ : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J, (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H₀.x) → Pairwise (Function.onFun (AEDisjoint G.M.μ) fun x => (fun g => (γ x)⁻¹ * g) ⁻¹' G.M.dom) ∧ ∀ Q : Subgroup (UA σ G.V.J), (∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x) → IsFundamentalDomain Q (⋃ x, (fun g => (γ x)⁻¹ * g) ⁻¹' G.M.dom) G.M.μ := by
  intro _kp F E _ _ _ _ _ σ B a b G G₁ H H' _cfg X om om' om₁ om₁' hT _hT1 V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ _hh hA _hg _hev γ hγ
  classical
  have hdom := hT.geo.hM.dom
  have hx0 : H₀.x ≠ 0 := by
    intro h
    have := hA.xy
    rw [h] at this
    simp [form] at this
  let T : UA σ G.V.J → Set (UA σ G.V.J) := fun h => (fun g => h⁻¹ * g) ⁻¹' G.M.dom
  have hsmul : ∀ δ : ratU σ G.V.J, δ • G.M.dom = T δ.1 := fun δ => by
    ext g; rw [Set.mem_smul_set_iff_inv_smul_mem]; rfl
  have hdisj : ∀ δ δ' : UA σ G.V.J, δ ∈ ratU σ G.V.J → δ' ∈ ratU σ G.V.J → δ ≠ δ' →
      AEDisjoint G.M.μ (T δ) (T δ') := by
    intro δ δ' hδ hδ' hne
    have := hdom.aedisjoint (show (⟨δ, hδ⟩ : ratU σ G.V.J) ≠ ⟨δ', hδ'⟩ from fun h => hne (congrArg Subtype.val h))
    rwa [Function.onFun, hsmul, hsmul] at this
  refine ⟨fun x y hxy => hdisj _ _ (hγ x).1 (hγ y).1 fun heq => hxy
    (Subtype.ext (eq_of_mulVec (γ x) (hγ x).2 (heq ▸ (hγ y).2))), fun Q hQ => ?_⟩
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hT.geo.hM.haar
  have hnm : ∀ h, NullMeasurableSet (T h) G.M.μ := fun h =>
    hdom.nullMeasurableSet.preimage (measurePreserving_mul_left G.M.μ h⁻¹).quasiMeasurePreserving
  have hq : ∀ q : Q, q • (⋃ x, T (γ x)) = ⋃ x, T (q.1 * γ x) := by
    intro q
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr fun x => ?_
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show (γ x)⁻¹ * (q.1⁻¹ * g) ∈ G.M.dom ↔ (q.1 * γ x)⁻¹ * g ∈ G.M.dom
    rw [mul_inv_rev, mul_assoc]
  refine { nullMeasurableSet := NullMeasurableSet.iUnion fun x => hnm (γ x), ae_covers := ?_, aedisjoint := ?_ }
  · filter_upwards [hdom.ae_covers] with g ⟨δ, hδg⟩
    obtain ⟨g₀, hmat, hunit⟩ := rat_desc δ.1 δ.2
    have hmv : mat δ.1 *ᵥ incV F H₀.x = incV F (g₀ *ᵥ H₀.x) := by
      rw [hmat]; funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) g₀ H₀.x i).symm
    have hv0 : g₀ *ᵥ H₀.x ≠ 0 := by
      intro h0
      have hz : incV F (0 : Fin a → E) = 0 := funext fun i => by simp [incV]
      have hy : mat δ.1 *ᵥ incV F (0 : Fin a → E) = incV F 0 := by
        rw [hz, Matrix.mulVec_zero]
      exact hx0 (eq_of_mulVec δ.1 (hmv.trans (by rw [h0])) hy)
    have hviso : form σ G.V.J (g₀ *ᵥ H₀.x) (g₀ *ᵥ H₀.x) = 0 := by
      rw [form_pres hunit]; exact hA.xx
    let x : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} := ⟨g₀ *ᵥ H₀.x, hv0, hviso⟩
    have hmem : γ x * δ.1 ∈ Q := (hQ _).2 ⟨mul_mem (hγ x).1 δ.2, by
      rw [mat_mul, ← Matrix.mulVec_mulVec, hmv]; exact (hγ x).2⟩
    refine ⟨⟨γ x * δ.1, hmem⟩, Set.mem_iUnion.2 ⟨x, ?_⟩⟩
    show (γ x)⁻¹ * (γ x * δ.1 * g) ∈ G.M.dom
    rw [mul_assoc, inv_mul_cancel_left]
    exact hδg
  · intro q q' hqq'
    rw [Function.onFun, hq, hq, AEDisjoint.iUnion_left_iff]
    intro x
    rw [AEDisjoint.iUnion_right_iff]
    intro y
    apply hdisj _ _ (mul_mem ((hQ _).1 q.2).1 (hγ x).1) (mul_mem ((hQ _).1 q'.2).1 (hγ y).1)
    intro heq
    have hxy : x = y := by
      apply Subtype.ext
      apply eq_of_mulVec (γ y) (v := H₀.x) _ (hγ y).2
      have e : γ y = (q'.1⁻¹ * q.1) * γ x := by
        rw [mul_assoc, heq, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e, mat_mul, ← Matrix.mulVec_mulVec, (hγ x).2]
      exact ((hQ _).1 (Q.mul_mem (Q.inv_mem q'.2) q.2)).2
    subst hxy
    exact hqq' (Subtype.ext (mul_right_cancel heq))
