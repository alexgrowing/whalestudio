import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaVanishingStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IndLine

theorem one_mem_KInf_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {m : ℕ} (X : Spc F E m) (τ : ∀ w : InfinitePlace F, EmbOver E w) : (1 : UA σ X.J) ∈ KInf σ X τ := by
  refine ⟨fun u _ => ?_, fun w => ?_⟩
  · have : mat (1 : UA σ X.J) - 1 = 0 := by simp [mat]
    rw [this, smul_zero]
  · have : (mat (1 : UA σ X.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _

theorem frobInf_offEig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {H' : Plane E (b + 2 + a') (b + a')}
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F (b + 2) a'} {Rf : FinMaps F (b + 2) a'}
    {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W} {R₁ : RealMaps F b a'} {Rf₁ : FinMaps F b a'}
    (hM : IsMatched B G X om om' R Rf) (hM₁ : IsMatched B G₁ X om₁ om₁' R₁ Rf₁) {φ : R.Pi →ₗ[ℂ] R₁.Pi}
    (hφ : IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ) {x : R.Pi}
    (hx : IsOffEig B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) x) : φ x = 0 := by
  obtain ⟨k, hk, t, hL, c, hc, hx⟩ := hx
  have hx0 : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx0
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hM.triple.base hM.triple.geo.hM
    hM.triple.weil k hk
  have h1 := hx f hf (A f) (hA f) rfl
  have hy0 : φ (R.p f) ∈ (G₁.M.Pol B.ψ B.emb).map R₁.p := by rw [hM₁.real.quot.onto]; exact Submodule.mem_top
  obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hy0
  have hacts : Acts (evI F) (om₁ (1, 1)) g g := by
    intro r _
    rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]
    rfl
  have h2 := hφ.cpt k hk t 1 hL (one_mem_KInf_real G₁.W B.emb) f hf (A f) (hA f) g hg g hacts hgx.symm
  rw [h1, map_smul, hgx] at h2
  have h3 : (c - (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) • φ (R.p f) = 0 := by
    rw [sub_smul, h2, sub_self]
  exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)

theorem lowPart_frobInf_line : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ →
        IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ' →
        (∀ x ∈ lowPartInf B G.M R.p, φ x = 0) ∨ ∃ c : ℂ, ∀ x ∈ lowPartInf B G.M R.p, φ' x = c • φ x := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ φ' hφ hφ'
  have hdec := GlobalTheory.T.config_a_theta_unramified hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hS := GlobalTheory.T.config_a_theta_vanishing hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
    (GlobalTheory.T.config_a_theta_local_factor hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁)
    (GlobalTheory.T.config_a_theta_global_factor hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁) φ φ' hφ hφ'
  have hoff : ∀ ψ : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) ψ →
      ∀ z ∈ offPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ψ z = 0 :=
    fun ψ hψ z hz => LinearMap.mem_ker.1 ((Submodule.span_le.2 fun y hy =>
      LinearMap.mem_ker.2 (frobInf_offEig hM hM₁ hψ hy.2)) hz)
  rcases hS with h0 | ⟨c, hc⟩
  · left
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hdec hx)
    rw [map_add, h0 y hy, hoff φ hφ z hz, add_zero]
  · right
    refine ⟨c, fun x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hdec hx)
    rw [map_add, map_add, hc y hy, hoff φ hφ z hz, hoff φ' hφ' z hz, smul_add, smul_zero]

end GlobalTheory.IndLine
