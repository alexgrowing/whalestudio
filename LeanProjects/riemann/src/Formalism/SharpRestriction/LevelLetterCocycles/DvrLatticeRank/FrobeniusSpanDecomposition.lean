import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Formalism.SharpRestriction.LevelLetterCocycles.FontExAll
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section KerLam2Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem kl2_dec_lemma (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (a : LetA O n) (s : W.DD T) (hs : s ∈ S) :
    ∃ t : Fin PD.p → W.DD T, (∀ k, t k ∈ S) ∧
      a • W.φD T s = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (t k) := by
  obtain ⟨e, he⟩ := Formalism.MainNotions.LiftingTheory.PhiBasis_of W a
  refine ⟨fun k => e k • s, fun k => S.smul_mem _ hs, ?_⟩
  rw [he, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, mul_smul]

theorem frobenius_span_decomposition (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (z : W.DD T)
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T S) :
    ∃ s : Fin PD.p → W.DD T, (∀ k, s k ∈ S) ∧
      z = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (s k) := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := kl2_dec_lemma W T S 1 s hs
    exact ⟨t, ht, by rw [← he, one_smul]⟩
  | zero => exact ⟨fun _ => 0, fun _ => S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨fun k => s k + s' k, fun k => S.add_mem (hs k) (hs' k),
      by simp only [map_add, smul_add, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    choose t ht he using fun k : Fin PD.p =>
      kl2_dec_lemma W T S (a * (letπ : LetA O n) ^ (k : ℕ)) (s k) (hs k)
    refine ⟨fun j => ∑ k, t k j, fun j => S.sum_mem fun k _ => ht k j, ?_⟩
    simp only [Finset.smul_sum, ← mul_smul, he, map_sum]
    rw [Finset.sum_comm]

theorem frobenius_span_exact_lift (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (c'' : IsCrys PD T''.ρ) (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T) (i : ZMod n)
    (z : W.DD Tp) (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Tp (W.Nl Tp i)) (h0 : W.map π z = 0) :
    ∃ z' ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i), W.map ι z' = z := by
  obtain ⟨s, hs, rfl⟩ := frobenius_span_decomposition W Tp (W.Nl Tp i) z hz
  have hπs : ∀ k, W.map π (s k) = 0 := by
    refine Formalism.MainNotions.LiftingTheory.phii_DD W T'' c'' (fun k => W.map π (s k)) ?_
    rw [← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ]
  choose y hy using fun k => hex (s k) (hπs k)
  have hyNl : ∀ k, y k ∈ W.Nl T i := by
    intro k
    obtain ⟨w, hw, hwe⟩ := (Formalism.MainNotions.LiftingTheory.wmap_mem_Nl W Tp i (s k)).1 (hs k)
    have hyN : y k ∈ W.N T := by
      apply h4
      rw [hy k, ← hwe]
      exact (W.N Tp).smul_mem _ hw
    rw [Formalism.MainNotions.LiftingTheory.wmap_mem_Nl]
    refine ⟨y k, hyN, ?_⟩
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hy k, Formalism.MainNotions.LiftingTheory.wmap_Nl_fix W Tp i (s k) (hs k)]
  refine ⟨∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (y k), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
    exact Submodule.subset_span ⟨y k, hyNl k, rfl⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ, hy k]

theorem frobenius_span_exact_local (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (π' Eπ : LetA O n) (h' : ℕ) (c'' : IsCrys PD T''.ρ)
    (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T)
    (hπ' : IsUnit (algebraMap (LetA O n) W.EE π')) :
    KerLam W ι π π' Eπ h' := by
  have hex' : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x := fun x hx => (hex x).1 hx
  have hΔ : ∀ x : W.DD T, (∀ δ ∈ W.DelF, W.γD Tp δ (W.map ι x) = W.map ι x) →
      ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro x hx δ hδ
    apply hinj
    rw [W.map_γ, hx δ hδ]
  have hL : ∀ (x : W.DD T) (a : LetA O n), a • W.map ι x = W.map ι x → a • x = x := by
    intro x a hx
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hx]
  refine ⟨hinj, ?_, fun c => ⟨?_, ?_⟩⟩
  · intro k y hy hyπ
    rw [mem_PiNS] at hy
    obtain ⟨⟨y0, hy0N, rfl⟩, hyΔ⟩ := hy
    have hz : W.map π y0 = 0 := by
      have hu : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]
        exact hπ'.pow k
      rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, ← algebraMap_smul W.EE] at hyπ
      exact (hu.smul_eq_zero).1 hyπ
    obtain ⟨x0, rfl⟩ := hex' y0 hz
    refine ⟨π' ^ k • x0, ?_, Formalism.MainNotions.LiftingTheory.wmap_map_smul W ι _ _⟩
    rw [mem_PiNS]
    refine ⟨⟨x0, h4 x0 hy0N, rfl⟩, hΔ _ ?_⟩
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul]
    exact hyΔ
  · intro y hy hyπ
    rw [mem_LamPS] at hy
    obtain ⟨hyE, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    obtain ⟨z', hz', hz'e⟩ := frobenius_span_exact_lift W ι π c'' hinj hex' h4 (c - 1) (Eπ ^ h' • W.map ι x) hyE
      (by rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hyπ, smul_zero])
    refine ⟨x, ?_, rfl⟩
    rw [mem_LamPS]
    refine ⟨?_, hΔ x hyΔ, hL x _ hyL⟩
    have e : z' = Eπ ^ h' • x := hinj (by rw [hz'e, Formalism.MainNotions.LiftingTheory.wmap_map_smul])
    rw [← e]
    exact hz'
  · intro y hy hyπ
    rw [mem_NcS] at hy
    obtain ⟨hyN, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    refine ⟨x, ?_, rfl⟩
    rw [mem_NcS]
    exact ⟨h4 x hyN, hΔ x hyΔ, hL x _ hyL⟩

end KerLam2Local

theorem kerlam2_pf : KerLamStep := by
  unfold KerLamStep kerLamR
  intro D HW F Cm CA CB CK hA hF l _ hl K LL hG π' E hp9 T Tp T'' ι π h' hses hT hTp hT'' hJ
  obtain ⟨hW, -⟩ := hA
  obtain ⟨-, -, -, -, -, h6W, -⟩ := hW l K 1 LL hG
  obtain ⟨-, -, h6ses⟩ := h6W
  obtain ⟨-, -, -, hsat, -⟩ := h6ses T Tp T'' ι π hT hTp hT'' hses
  have hEx := hF l K 1 LL hG T Tp T'' ι π hses
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  letI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [e]
    exact Formalism.MainNotions.LiftingTheory.phib_OL_complete LL
  refine frobenius_span_exact_local _ ι π π' _ h' hT'' hEx.1 hEx.2.2 hsat ?_
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (by simpa using (Formalism.MainNotions.LiftingTheory.wmap_unit _ 0).pow _)

end Formalism.MainNotions.N.Ln34

end
