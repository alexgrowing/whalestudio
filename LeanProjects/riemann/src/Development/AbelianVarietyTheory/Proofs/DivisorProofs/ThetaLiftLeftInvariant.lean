import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ x / χ' x
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem I_rat_inv (hT : ThetaBasic) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (Φ : Fn F n d) (hΦ : Φ ∈ PolData B M) (γ : UA σ W.J) (hγ : γ ∈ ratU σ W.J) (h : UA σ W.J) :
    M.I om Φ (γ * h) = M.I om Φ h := by
  have hS : Φ ∈ schA F (Fin n × Fin d) := polData_le_schA B M hP.good hΦ
  have hinv := ((hT F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hS).2.1
  unfold Model.I
  congr 1
  funext g
  simpa using hinv 1 (one_mem _) γ hγ g h

theorem ratInv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ PolData B G.M, ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ _
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a a']; exact resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }
  exact ⟨fun Φ hΦ γ hγ h => I_rat_inv hTB B G.M hV Φ hΦ γ hγ h,
    fun Φ' hΦ' γ hγ h => I_rat_inv hTB B G.M' hV' Φ' (Submodule.mem_inf.1 hΦ').1 γ hγ h⟩

end GlobalTheory.ThKRatInv
