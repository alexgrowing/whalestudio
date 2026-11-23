import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfE
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.TmulMkLMemInvLOfValAtMemFilC

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLF

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

def WD : Prop :=
  ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z

theorem good_all (hwd : WD W T Pt π' c) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c)
    {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T} (hr : IsRepL W T π' Eπ h' c x a y) :
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i) := by
  obtain ⟨m', a', y', ⟨hy', hx'⟩, hg⟩ := LevelExpansions.NL_rep W T hx
  obtain ⟨hy, hxr⟩ := hr
  intro τ ζ hpt i
  rw [hwd τ ζ hpt _ y hy _ y' hy' (hxr.symm.trans hx')]
  exact hg τ ζ hpt i

theorem nl_le : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, hx⟩, -⟩
  refine ⟨∑ j, a j ⊗ₜ ⟨mkL W T π' c (y j) (hy j), Submodule.mem_top⟩, ?_⟩
  rw [map_sum, hx]
  rfl

theorem nl_smulA {b : LetA O n} (hb : b ∈ W.AΔ) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    smulLA W T π' c b x ∈ NL W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, hr, hg⟩ := hx
    refine Submodule.subset_span ⟨m, _, y, MLE.rep_smul W T π' Eπ h' c hr hb, fun τ ζ hpt => ?_⟩
    exact MLB.goodF_mul W T c ζ τ h' b _ y (hg τ ζ hpt)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

theorem expS_alg_mul (ζ : LL) (o : O) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) :
    expS W T c ζ (fun j => algebraMap O (LetA O n) o * a j) y = algebraMap O LL o • expS W T c ζ a y := by
  funext i
  simp only [expS, serC, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [← Algebra.smul_def, LevelExpansions.lev_smul, mul_smul]
  · rw [smul_zero]

theorem nl_sat (hwd : WD W T Pt π' c) (hp : algebraMap O LL ((PD.p : ℕ) : O) ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (k : ℕ)
    (hk : ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c) : x ∈ NL W T Pt π' Eπ h' c := by
  obtain ⟨m, a, y, hr⟩ := MLE.rep_exists W T π' Eπ h' c hx
  have hr' := MLE.rep_smul W T π' Eπ h' c hr (W.AΔ.algebraMap_mem (((PD.p : ℕ) : O) ^ k))
  rw [← MLE.smul_eq_smulLA] at hr'
  have hg := good_all W T Pt π' Eπ h' c hwd hk hr'
  refine Submodule.subset_span ⟨m, a, y, hr, fun τ ζ hpt i => ?_⟩
  have h1 := hg τ ζ hpt i
  have e : expS W T c ζ (fun j => ((⟨algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ k) * a j,
      W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (a j).2⟩ : ↥W.AΔ) : LetA O n)) y =
      algebraMap O LL (((PD.p : ℕ) : O) ^ k) • expS W T c ζ (fun j => (a j : LetA O n)) y :=
    expS_alg_mul W T c ζ _ _ y
  rw [e, Pi.smul_apply] at h1
  exact (Submodule.smul_mem_iff _ (by rw [map_pow]; exact pow_ne_zero _ hp)).1 h1

end Generic

end Formalism.MainNotions.N.Ln34.MLF

end
