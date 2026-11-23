import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSatB

noncomputable section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS.FockSupport

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fok_unif {w : Pl E} {x : w.adicCompletion E} (hx : ordL x = 1) : IsUnifV E w x := by
  unfold ordL at hx
  by_cases h1 : Valued.v x = 0
  · rw [dif_pos h1] at hx
    exact absurd hx (by norm_num)
  · rw [dif_neg h1] at hx
    unfold IsUnifV
    rw [← WithZero.coe_unzero h1]
    congr 1
    have e : Multiplicative.toAdd (WithZero.unzero h1) = -1 := by omega
    rw [← e, ofAdd_toAdd]

theorem fok_ordL_det {w : Pl E} {p : ℕ} {κ : GLw p w} (hκ : κ ∈ KGL w p) :
    ordL ((GeneralLinearGroup.det κ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 0 := by
  have hv : Valued.v ((GeneralLinearGroup.det κ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.GLintCover.det_v hκ]
  have h1 : Valued.v ((GeneralLinearGroup.det κ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by
    rw [hv]; exact one_ne_zero
  unfold ordL
  rw [dif_neg h1]
  have e : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, hv]; rfl
  rw [e, toAdd_one, neg_zero]

theorem fok_inv {n a b : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (ν : (w.adicCompletion E)ˣ →* ℂˣ)
    (hν : ∀ {p : ℕ} (κ : GLw p w), κ ∈ KGL w p → ν (GeneralLinearGroup.det κ) = 1)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) (κ : GLw a w × GLw b w) (h1 : κ.1 ∈ KGL w a)
    (h2 : κ.2 ∈ KGL w b) (m : GLw a w × GLw b w) :
    ctT h w ν ϖ k (κ * m) = ctT h w ν ϖ k m ∧ ctT h w ν ϖ k (m * κ) = ctT h w ν ϖ k m := by
  set F : GLw n w → ℂ := fun y => (fun u : UL n w => Tj ℂ n (Ov E w) ϖ k u.1) (toSub (UL n w) y) with hFdef
  have hF' : ∀ y, F y = Tj ℂ n (Ov E w) ϖ k y := fun y => by
    simp only [hFdef]; rw [SplitLevels.toSub_of_mem _ _ (SplitLevels.mem_UL_split hw _)]
  have hF : ∀ y ∈ KGL w n, ∀ x, F (y * x) = F x ∧ F (x * y) = F x := fun y hy x => by
    rw [hF', hF', hF']
    exact ⟨by simpa using (Tj_mem_hecke hϖ k).1 ⟨y, hy⟩ 1 x, by simpa using (Tj_mem_hecke hϖ k).1 1 ⟨y, hy⟩ x⟩
  have hct := SplitLevels.ct_inv_blocks h w (KGL w n) F
    (fun k' hk' x hx => mul_mem (mul_mem (inv_mem hk') hx) hk') hF κ h1 h2 (b_dgM_mem h w κ h1 h2) m
  have d1 : ν (GeneralLinearGroup.det κ.1) = 1 := hν _ h1
  have d2 : ν (GeneralLinearGroup.det κ.2) = 1 := hν _ h2
  have hnu : ∀ y : GLw a w × GLw b w, ν ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * y).1 ^ b *
        GeneralLinearGroup.det (κ * y).2 ^ a) = ν ((-1) ^ (a * b) * GeneralLinearGroup.det y.1 ^ b *
        GeneralLinearGroup.det y.2 ^ a) ∧ ν ((-1) ^ (a * b) * GeneralLinearGroup.det (y * κ).1 ^ b *
        GeneralLinearGroup.det (y * κ).2 ^ a) = ν ((-1) ^ (a * b) * GeneralLinearGroup.det y.1 ^ b *
        GeneralLinearGroup.det y.2 ^ a) := fun y => by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, d1, d2, one_pow, mul_one, one_mul]
    constructor <;> simp only [one_pow, one_mul, mul_one]
  unfold ctT ctMu
  exact ⟨by rw [(hnu m).1, hct.1], by rw [(hnu m).2, hct.2]⟩

theorem fok_Tj_top {n k : ℕ} {w : Pl E} {ϖ : w.adicCompletion E} (hk : n ≤ k) :
    Tj ℂ n (Ov E w) ϖ k = Tj ℂ n (Ov E w) ϖ n := by
  have hd : diagJ n ϖ k = diagJ n ϖ n := by
    unfold diagJ
    congr 1
    funext i
    rw [if_pos (lt_of_lt_of_le i.isLt hk), if_pos i.isLt]
  unfold Tj
  rw [hd]

theorem fok_supp_le {n a b : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (ν : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) : HasCompactSupport (ctT h w ν ϖ k) := by
  have h0 := b_unif_ne_zero hϖ
  let S : ∀ m : ℕ, ℕ → Set (GLw m w) := fun m i =>
    (fun q : GLw m w × GLw m w => q.1 * tJ h0 m i * q.2) '' ((KGL w m : Set (GLw m w)) ×ˢ (KGL w m : Set (GLw m w)))
  have hS : ∀ m i, IsCompact (S m i) := fun m i =>
    ((GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w m).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w m)).image
      ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hmem : ∀ {m i : ℕ} {g : GLw m w}, Tj ℂ m (Ov E w) ϖ i g ≠ 0 → g ∈ S m i := by
    intro m i g hg
    rw [GlobalTheory.WeylGL.Tj_eq h0] at hg
    unfold dosetInd at hg
    obtain ⟨x, hx, y, hy, e⟩ := GlobalTheory.WeylGL.mem_doset.1 (Set.mem_of_indicator_ne_zero hg)
    exact ⟨(x, y), ⟨hx, hy⟩, e.symm⟩
  refine HasCompactSupport.intro ((pairsK a b k).isCompact_biUnion fun p _ => (hS a p.1).prod (hS b p.2)) fun m hm => ?_
  by_contra hne
  obtain ⟨p, hp, h1, h2⟩ := ctT_supp h w hw ν hϖ k hk m hne
  exact hm (Set.mem_biUnion hp ⟨hmem h1, hmem h2⟩)

theorem fok_supp {n a b : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (ν : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) : HasCompactSupport (ctT h w ν ϖ k) := by
  by_cases hk : k ≤ n
  · exact fok_supp_le h w hw ν hϖ k hk
  · have e : ctT h w ν ϖ k = ctT h w ν ϖ n := by
      unfold ctT
      rw [fok_Tj_top (by omega)]
    rw [e]
    exact fok_supp_le h w hw ν hϖ n le_rfl

end PositivityTheory.Rg.BcB.F.RS.FockSupport

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Fok

theorem ctT_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : (w.adicCompletion E)ˣ), IsSplitAt w → ordL (ϖ : w.adicCompletion E) = 1 → (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) → ∀ k : ℕ, IsHecke (K2 a b w) (RS.ctT h w μ (ϖ : w.adicCompletion E) k) := by
  intro E _ _ _ n a b h w μ ϖ hw hord hμ k
  have hϖ := RS.FockSupport.fok_unif hord
  have hν : ∀ {p : ℕ} (κ : GLw p w), κ ∈ GlobalTheory.LFun.KGL w p → μ (GeneralLinearGroup.det κ) = 1 :=
    fun κ hκ => hμ _ (RS.FockSupport.fok_ordL_det hκ)
  refine ⟨RS.FockSupport.fok_supp h w hw μ hϖ k, fun κ hκ x => ?_⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  exact RS.FockSupport.fok_inv h w hw μ hν hϖ k κ h1 h2 x

end PositivityTheory.Rg.BcB.F.Fok

end
