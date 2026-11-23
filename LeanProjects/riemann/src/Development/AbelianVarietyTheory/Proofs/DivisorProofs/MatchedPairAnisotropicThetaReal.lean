import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximationStatement

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DiffLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_open_fix_sum (hK : KP) (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (T : Finset (Pl F)) {m : ℕ}
    (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ i v, φ i v ∈ SB (Fin n × Fin d → Fv F v)) (hT : ∀ i, ∀ v ∉ T, φ i v = M.vac v) :
    ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U,
      (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
        om (1, k) (∑ i, pure (f i) (φ i)) = ∑ i, pure (f i) (φ i) := by
  have hev : ∀ i, ∀ᶠ v in cofinite, φ i v = M.vac v := fun i =>
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (hT i v h))
  have hex := fun i => GlobalTheory.T.exists_open_subgroup_fixing_pure_tensor F E σ B n d X W M χX χW om r s r' s' hK hP (f i) (φ i) (hSB i) (hev i)
  choose U hU hfix using hex
  refine ⟨⨅ i, U i, ?_, fun k hk hf => ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hfix i k (Subgroup.mem_iInf.1 hk i) hf

theorem I_mul_of_fix {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (k : UA σ W.J) (hk : om (1, k) Φ = Φ) (h : UA σ W.J) :
    M.I om Φ (h * k) = M.I om Φ h := by
  unfold Model.I theta
  congr 1
  funext g
  rw [show ((g, h * k) : UA σ X.J × UA σ W.J) = (g, h) * (1, k) by simp, map_mul, Module.End.mul_apply, hk]

theorem level : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      ∃ U : Subgroup (GAd σ (c₀ • G.W.J.map σ)), IsOpen (U : Set (GAd σ (c₀ • G.W.J.map σ))) ∧ ∀ k ∈ U, k ∈ finPts σ (c₀ • G.W.J.map σ) → ∀ g, φ' (g * k) = φ' g := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _ _ c Φ Φ' _ hPM c₀ hc₀ ψ' hψ'
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨T, -, m, m', f, φ, f', φ₁, hi, hj, hΦ, hΦ', -⟩ := hPM
  obtain ⟨U₁, hU₁, h₁⟩ := exists_open_fix_sum hK B (Check.isPair_of_isTriple hT).1 T f φ
    (fun i v => (hi i).2.1 v) (fun i => (hi i).2.2)
  obtain ⟨U₂, hU₂, h₂⟩ := exists_open_fix_sum hK B (Check.isPair_of_isTriple hT).2 T f' φ₁
    (fun j v => (hj j).2.1 v) (fun j => (hj j).2.2)
  set e := toGAd hσ G.W.J hc₀
  have he : Continuous e.symm := continuous_subtype_val.subtype_mk _
  refine ⟨(U₁ ⊓ U₂).comap e.symm.toMonoidHom, (hU₁.inter hU₂).preimage he, fun k hk hfin g => ?_⟩
  have hf : (mat (e.symm k)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 hfin)
  have k₁ : om (1, e.symm k) Φ = Φ := hΦ ▸ h₁ _ hk.1 hf
  have k₂ : om' (1, e.symm k) Φ' = Φ' := hΦ' ▸ h₂ _ hk.2 hf
  rw [hψ' (e.symm (g * k)) (g * k) rfl, hψ' (e.symm g) g rfl, map_mul, I_mul_of_fix _ _ _ _ k₁,
    I_mul_of_fix _ _ _ _ k₂]

end GlobalTheory.ThK.DiffLevel
