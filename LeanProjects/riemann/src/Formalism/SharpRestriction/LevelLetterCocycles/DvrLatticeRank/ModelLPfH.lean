import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfG

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLH

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem γLA_smulLA (b : LetA O n) (z : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c b z) = smulLA W T π' c (W.γA W.gamK b) (γLA W T π' c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    show W.γE W.gamK (algebraMap (LetA O n) W.EE b * e) ⊗ₜ s =
      (algebraMap (LetA O n) W.EE (W.γA W.gamK b) * W.γE W.gamK e) ⊗ₜ s
    rw [map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem γA_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA W.gamK a ∈ W.AΔ := by
  intro δ hδ
  have e1 : W.γA δ (W.γA W.gamK a) = W.γA (δ * W.gamK) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  have e2 : W.γA W.gamK (W.γA δ a) = W.γA (W.gamK * δ) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  rw [e1, mul_comm, ← e2, ha δ hδ]

theorem rep_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (hr : IsRepL W T π' Eπ h' c x a y) :
    IsRepL W T π' Eπ h' c (γLA W T π' c x)
      (fun j => ⟨u₀ * W.γA W.gamK (a j), W.AΔ.mul_mem hu₀ (γA_mem_AΔ W (a j).2)⟩) y := by
  obtain ⟨hy, hx⟩ := hr
  refine ⟨hy, ?_⟩
  have e : smulLA W T π' c (Eπ ^ h') (γLA W T π' c x) =
      smulLA W T π' c u₀ (γLA W T π' c (smulLA W T π' c (Eπ ^ h') x)) := by
    rw [γLA_smulLA, MLE.smulLA_smulLA, hΛ]
  rw [e, hx, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show (algebraMap (LetA O n) W.EE u₀ * W.γE W.gamK (algebraMap (LetA O n) W.EE
      ((letE c : LetA O n) * a j))) ⊗ₜ mkL W T π' c (y j) (hy j) = _
  rw [W.γE_ext, ← map_mul]
  congr 2
  show u₀ * W.γA W.gamK ((letE c : LetA O n) * a j) = (letE c : LetA O n) * (u₀ * W.γA W.gamK (a j))
  rw [map_mul, hlet]
  ring

theorem expS_γ (ζ : LL) (u : LL) (hlev : ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => W.γA W.gamK (a j)) y i = u ^ i.toNat • expS W T c ζ a y i := by
  simp only [expS, serC, hlev, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [PowerSeries.coeff_rescale, mul_smul]
  · rw [smul_zero]

theorem nl_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c) (u : LL)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) : γLA W T π' c x ∈ NL W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, hr, hg⟩ := hx
    refine Submodule.subset_span ⟨m, _, y, rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr, fun τ ζ hpt => ?_⟩
    refine MLB.goodF_mul W T c ζ τ h' u₀ (fun j => W.γA W.gamK (a j)) y (fun i => ?_)
    rw [expS_γ W T c ζ u (hlev τ ζ hpt)]
    exact Submodule.smul_mem _ _ (hg τ ζ hpt i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

end Generic

end Formalism.MainNotions.N.Ln34.MLH

end
