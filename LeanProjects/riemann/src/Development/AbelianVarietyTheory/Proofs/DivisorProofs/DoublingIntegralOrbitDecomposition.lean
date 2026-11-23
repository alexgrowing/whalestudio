import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenEqOneOfDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.BotInert

theorem prod_segment (G : ℤ → ℂ) (n : ℕ) : ∏ j ∈ Finset.range n, G (2 * j + 1 - n) =
    (∏ i ∈ Finset.range (n / 2), G (n - 1 - 2 * i) * G (-(n - 1 - 2 * i))) * (if Odd n then G 0 else 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ =>
    have e1 : (n + 2) / 2 = n / 2 + 1 := by omega
    have e2 : Odd (n + 2) ↔ Odd n := by simp [Nat.odd_add]
    rw [Finset.prod_range_succ, Finset.prod_range_succ', e1, Finset.prod_range_succ']
    have e3 : ∏ j ∈ Finset.range n, G (2 * ((j + 1 : ℕ) : ℤ) + 1 - ((n + 2 : ℕ) : ℤ)) =
        ∏ j ∈ Finset.range n, G (2 * j + 1 - n) := Finset.prod_congr rfl fun j _ => by congr 1; push_cast; ring
    have e4 : ∏ i ∈ Finset.range (n / 2), G (((n + 2 : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ)) *
        G (-(((n + 2 : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ))) =
        ∏ i ∈ Finset.range (n / 2), G (n - 1 - 2 * i) * G (-(n - 1 - 2 * i)) :=
      Finset.prod_congr rfl fun j _ => by congr 2 <;> (push_cast; ring)
    rw [e3, e4, ih]
    simp only [e2]
    rw [show (2 * ((0 : ℕ) : ℤ) + 1 - ((n + 2 : ℕ) : ℤ)) = -(n + 1) by push_cast; ring,
      show (2 * ((n + 1 : ℕ) : ℤ) + 1 - ((n + 2 : ℕ) : ℤ)) = n + 1 by push_cast; ring,
      show (((n + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) = n + 1 by push_cast; ring]
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem closedForm_triv {q : ℕ} (hq : q ≠ 0) (n : ℕ) (s : ℂ) (α : Fin (n / 2) → ℂˣ)
    (hα : ∀ i, (α i : ℂ) = (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) :
    closedForm q n (varX q n 1 s) (varY q 1 s) α =
      (∏ j ∈ Finset.range n, (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹) *
        ∏ j ∈ Finset.Icc 1 n, (1 - (-1 : ℂ) ^ (n - j) * (q : ℂ) ^ (-(2 * s + (j : ℂ)))) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h1 : ∏ j ∈ Finset.range n, (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹ =
      ∏ j ∈ Finset.range n, (fun k : ℤ => (1 - varY q 1 s * (q : ℂ) ^ k)⁻¹) (2 * j + 1 - n) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [varY, one_mul]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hq0]
    congr 3
    push_cast
    ring
  have h2 : ∏ j ∈ Finset.Icc 1 n, (1 - (-1 : ℂ) ^ (n - j) * (q : ℂ) ^ (-(2 * s + (j : ℂ)))) =
      ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * varX q n 1 s) := by
    refine Finset.prod_nbij' (fun j => n - j) (fun j => n - j) ?_ ?_ ?_ ?_ fun j hj => ?_
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro j hj; simp only [Finset.mem_Icc] at *; omega
    · intro j hj; simp only [Finset.mem_range] at *; omega
    · have hj' := (Finset.mem_Icc.1 hj).2
      rw [varX, one_mul, neg_pow (q : ℂ), mul_assoc, ← Complex.cpow_natCast (q : ℂ) (n - j), ← Complex.cpow_add _ _ hq0,
        Nat.cast_sub hj']
      congr 3
      ring
  rw [h1.trans (prod_segment (fun k : ℤ => (1 - varY q 1 s * (q : ℂ) ^ k)⁻¹) n), h2, closedForm, ← Fin.prod_univ_eq_prod_range
    (fun i : ℕ => (1 - varY q 1 s * (q : ℂ) ^ ((n : ℤ) - 1 - 2 * i))⁻¹ * (1 - varY q 1 s * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * i)))⁻¹)]
  simp only [hα, zpow_neg, zpow_zero, mul_one, div_eq_mul_inv]
  ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem domain_triv {q : ℕ} (hq : 2 ≤ q) (n : ℕ) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (α : Fin (n / 2) → ℂˣ)
    (hα : ∀ i, (α i : ℂ) = (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) : Domain (varY q 1 s) α := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy : ‖varY q 1 s‖ = (q : ℝ) ^ (-(2 * s.re + 1)) := by
    rw [varY, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : ∀ i, ‖(α i : ℂ)‖ = (q : ℝ) ^ ((n : ℝ) - 1 - 2 * (i.val : ℝ)) := fun i => by
    rw [hα, norm_zpow, Complex.norm_natCast, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hy]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy, ha, ← Real.rpow_add hq0]
    have : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy, ha, ← Real.rpow_neg hq0.le, ← Real.rpow_add hq0]
    have h1 : 2 * i.val + 1 ≤ n := by have := i.2; omega
    have h2 : 2 * (i.val : ℝ) + 1 ≤ n := by exact_mod_cast h1
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem val_eq_one {χ : Chr F E} {K : Subgroup (AF F)ˣ} {d : ℕ} (hχ : ResEtaPow K χ d) (hd : Even d) {v : Pl F}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (hu : UnrAt χ w) : val χ w = 1 := by
  have h := under_eq_of_isInertAt hw
  have e : aboveF (L := E) F v = {w} := by
    ext u
    rw [mem_aboveF, Finset.mem_singleton]
    exact InertChart.under_eq_iff hw u
  have h0 : ∀ a, χ (ideleMap F E a) = 1 := hχ.triv_of_even hd
  have h1 := congrArg χ (ideleMap_localIdele (E := E) v (Formalism.L2.Host.unif v)).symm
  rw [h0, e, Finset.prod_singleton] at h1
  have h2 := congrArg Circle.toUnits h1
  rw [map_one] at h2
  refine Eq.trans (hu.locChar_eq_val ?_).symm h2
  refine (valued_alg w (algebraMap F E (Formalism.L2.Host.unif v : Fˣ))).trans ?_
  rw [valuation_up h, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, ← valued_alg]
  exact Formalism.L2.Host.unif_spec v

theorem emb_mem_iff {B : Base F E} {n : ℕ} {X : Spc F E n} (hL : X.L.IsLattice E) {K : Subgroup (UA σ X.J)}
    (hK : IsStab B K) (v : Pl F) (k : GLoc σ X.Jᵀ v) :
    GlobalTheory.IwLine.ofGAd σ X.J (emb σ X.Jᵀ v k) ∈ K ↔ k ∈ stabLoc σ X.Jᵀ X.L v := by
  rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X _).symm]
  refine ⟨fun h => ?_, fun hk => GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B n X hL _ (fun w => ?_) (fun u => ?_)⟩
  · simpa using (GlobalTheory.T.stabilizer_commutes_majorant F E σ B n X hL _ h).2 v
  · rw [projArch_emb, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _
  · by_cases hu : u = v
    · subst hu; rw [proj_emb_self]; exact hk
    · rw [proj_emb_ne σ X.Jᵀ hu]; exact one_mem _

theorem eq_emb_locEquiv {n : ℕ} (X : Spc F E n) (v : Pl F) (g : UAtSub σ X (evFin F v)) :
    g.1 = GlobalTheory.IwLine.ofGAd σ X.J (emb σ X.Jᵀ v (GlobalTheory.LocUnitaryUnimod.locEquiv σ v X g)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.proj_eq_one_of_at (X := X) g.2
  rw [← MulEquiv.symm_apply_eq]
  refine GAd_ext _ _ (fun w => ?_) fun u => ?_
  · rw [h2, projArch_emb]
  · by_cases hu : u = v
    · subst hu; rw [proj_emb_self]; rfl
    · rw [h1 u hu, proj_emb_ne σ X.Jᵀ hu]

section Reindex

variable {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)}

def toUD (hJ : X₂.J = dblGram finSumFinEquiv X.J) : UA σ X₂.J →* GlobalTheory.DblVac.UD σ X where
  toFun g := ⟨⟨(mat g).submatrix finSumFinEquiv finSumFinEquiv, (mat g⁻¹).submatrix finSumFinEquiv finSumFinEquiv,
      by rw [Matrix.submatrix_mul_equiv, GlobalTheory.StabHaar.mat_mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, GlobalTheory.StabHaar.mat_inv_mul, Matrix.submatrix_one_equiv]⟩, by
    have hg : (mat g)ᵀ * incM F X₂.J * (mat g).map (cA σ) = incM F X₂.J := g.2
    have hD : dbl (incM F X.J) = (incM F X₂.J).submatrix finSumFinEquiv finSumFinEquiv := by
      rw [hJ, dblGram, incM, incM, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), submatrix_blkMat]
      rfl
    show ((mat g).submatrix finSumFinEquiv finSumFinEquiv)ᵀ * dbl (incM F X.J) *
      ((mat g).submatrix finSumFinEquiv finSumFinEquiv).map (cA σ) = dbl (incM F X.J)
    rw [hD, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]⟩
  map_one' := Subtype.ext (Units.ext (Matrix.submatrix_one_equiv _))
  map_mul' _ _ := Subtype.ext (Units.ext (Matrix.submatrix_mul_equiv _ _ _ _ _).symm)

theorem matD_toUD (hJ : X₂.J = dblGram finSumFinEquiv X.J) (g : UA σ X₂.J) :
    GlobalTheory.DblVac.matD (toUD hJ g) = (mat g).submatrix finSumFinEquiv finSumFinEquiv := rfl

theorem toUD_mul_diagCols (hJ : X₂.J = dblGram finSumFinEquiv X.J)
    (p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) :
    GlobalTheory.DblVac.matD (toUD hJ p.1) * (diagCols (Fin n) : Matrix _ _ (AE F E)) =
      (diagCols (Fin n) : Matrix _ _ (AE F E)) * (leviOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p).1 := by
  have hk : KeepsDiag finSumFinEquiv (mat p.1) := mem_siegelOf.1 p.2
  have hl : (leviOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p).1 = leviMat finSumFinEquiv (mat p.1) := rfl
  rw [matD_toUD, hl, ← Matrix.fromBlocks_toBlocks ((mat p.1).submatrix finSumFinEquiv finSumFinEquiv), diagCols,
    Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [show ((mat p.1).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ +
    ((mat p.1).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = leviMat finSumFinEquiv (mat p.1) from hk]
  rfl

theorem mem_latD_iff (v : Pl F) (z : Fin n ⊕ Fin n → AE F E) : z ∈ GlobalTheory.DblVac.latD X v ↔ At (evFin F v) z ∧
    (fun j => compFin F E v (z (finSumFinEquiv.symm j))) ∈ latLoc F (sumLat finSumFinEquiv X.L X.L) v := by
  rw [latLoc_sumLat, mem_sumLat]
  simp only [Equiv.symm_apply_apply]
  change (_ ∈ GlobalTheory.InertSph.latAt X v ∧ _ ∈ GlobalTheory.InertSph.latAt X v) ↔ _
  rw [GlobalTheory.SplitDictHerm.mem_latAt_iff, GlobalTheory.SplitDictHerm.mem_latAt_iff]
  refine ⟨fun h => ⟨fun u hu => funext fun i => ?_, h.1.2, h.2.2⟩,
    fun h => ⟨⟨fun u hu => funext fun i => congrFun (h.1 u hu) _, h.2.1⟩,
      fun u hu => funext fun i => congrFun (h.1 u hu) _, h.2.2⟩⟩
  cases i with
  | inl i => exact congrFun (h.1.1 u hu) i
  | inr i => exact congrFun (h.2.1 u hu) i

theorem mulVec_mem_latD (hJ : X₂.J = dblGram finSumFinEquiv X.J) (v : Pl F) {k : GLoc σ X₂.Jᵀ v}
    (hk : k ∈ KFin σ X₂.Jᵀ X.L v) {z : Fin n ⊕ Fin n → AE F E} (hz : z ∈ GlobalTheory.DblVac.latD X v) :
    GlobalTheory.DblVac.matD (toUD hJ (GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v k))) *ᵥ z ∈ GlobalTheory.DblVac.latD X v := by
  rw [mem_latD_iff] at hz ⊢
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [← algebraMap_smul (AE F E) u, ← Matrix.mulVec_smul, algebraMap_smul, hz.1 u hu, Matrix.mulVec_zero]
  · have h1 := ((mem_stabLoc.1 hk) _).1 hz.2
    convert h1 using 1
    funext j
    simp only [matD_toUD, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      GlobalTheory.IwLine.mat_ofGAd, GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.compFin_mat, proj_emb_self]
    rw [← finSumFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]

theorem toUD_mem_KD (hJ : X₂.J = dblGram finSumFinEquiv X.J) (v : Pl F) {k : GLoc σ X₂.Jᵀ v}
    (hk : k ∈ KFin σ X₂.Jᵀ X.L v) : toUD hJ (GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v k)) ∈ GlobalTheory.DblVac.KD σ X v := by
  refine ⟨fun u hu => ?_, fun z hz => ⟨mulVec_mem_latD hJ v hk hz, ?_⟩⟩
  · have h := GlobalTheory.ThK.LemF.QuotInv.IwasawaAt.ofGAd_emb_mem_UAt (X := X₂) v k u hu
    rw [matD_toUD, ← Matrix.submatrix_one_equiv finSumFinEquiv]
    ext i j
    exact congrFun (congrFun h (finSumFinEquiv i)) (finSumFinEquiv j)
  · rw [← map_inv, ← map_inv, ← map_inv]
    exact mulVec_mem_latD hJ v (inv_mem hk) hz

end Reindex

theorem exists_section {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r₀ s₀ r₁ s₁ : ℕ} (hP : IsPair B M χX χW om r₀ s₀ r₁ s₁) {X₂ : Spc F E (n + n)}
    {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂)
    [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (hm : m.IsAddHaarMeasure) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (h0 : Φ ≠ 0) (S : Set (GlobalTheory.DblVac.UD σ X))
    (hS : ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
        (omd : GlobalTheory.DblVac.UD σ X →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
      ∀ g ∈ S, omd g (boxFun Φ fun x => star (Φ x)) = boxFun Φ fun x => star (Φ x)) :
    ∃ Ψ : UA σ X₂.J → ℂ, (∀ g, coef m om Φ g / coef m om Φ 1 = Ψ (i (g, 1))) ∧
      ∀ (p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) (k : UA σ X₂.J), toUD hD.gram k ∈ S →
        Ψ (p.1 * k) = χW (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) *
          GlobalTheory.Doubling.npow (absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) ((d : ℂ) / 2) := by
  obtain ⟨d', hd', hsp₁, dd, omd, hdc, hsp, hbox⟩ := hP.weil.2.1
  have hfix := hS d' hd' dd omd hdc hsp
  have hΦ' := GlobalTheory.SchAConj.star_mem_schA F _ Φ hΦ
  set T := boxFun Φ fun x => star (Φ x) with hT
  have hTs : T ∈ schA F _ := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦ _ hΦ'
  have hl : GlobalTheory.DiagForm.lDiag F _ T ≠ 0 := GlobalTheory.DblVacSiegel.lDiag_box_ne_zero hP.base.cm.1 hΦ h0
  borelize (Fin n × Fin d → AF F)
  obtain ⟨c, hc⟩ := GlobalTheory.DiagUniq.lDiag_eq m hm
  have hco : ∀ g, GlobalTheory.DiagForm.lDiag F _ (omd (toUD hD.gram (i (g, 1))) T) = c * coef m om Φ g := fun g => by
    have hg : GlobalTheory.DblVac.matD (toUD hD.gram (i (g, 1))) = Matrix.fromBlocks (mat g) 0 0 1 := by
      rw [matD_toUD, hD.emb, submatrix_blkMat]; rfl
    rw [hT, hbox g _ hg Φ hΦ _ hΦ',
      hc _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ (hsp₁.pres g Φ hΦ) _ hΦ')]
    rfl
  have hco1 : GlobalTheory.DiagForm.lDiag F _ T = c * coef m om Φ 1 := by
    have := hco 1
    rwa [show ((1 : UA σ X.J), (1 : UA σ X.J)) = 1 from rfl, map_one, map_one, map_one, Module.End.one_apply] at this
  have hc0 : c ≠ 0 := fun h => hl (by rw [hco1, h, zero_mul])
  refine ⟨fun g => GlobalTheory.DiagForm.lDiag F _ (omd (toUD hD.gram g) T) / GlobalTheory.DiagForm.lDiag F _ T, fun g => ?_,
    fun p k hk => ?_⟩
  · simp only [hco, hco1]
    rw [mul_div_mul_left _ _ hc0]
  · have hrule := hsp.2.2 _ GlobalTheory.DiagForm.lDiag_adm (fun z φ hφ => by
      have e : z * (diagCols (Fin n) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
        rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
      rw [e, Darboux.rho, hdc]
      exact GlobalTheory.DiagForm.lDiag_schr B.ψ _ _ hφ) (toUD hD.gram p.1)
        (leviOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) (toUD_mul_diagCols hD.gram p) _ hTs
    simp only [map_mul, Module.End.mul_apply]
    rw [hfix _ hk, hrule, mul_div_cancel_right₀ _ hl, GlobalTheory.ModuAdele.modu_norm_eq_absE, GlobalTheory.Doubling.npow,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    congr 2
    push_cast
    simp only [Fintype.card_fin]

set_option maxHeartbeats 1000000 in

theorem zetaOn_inert : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
    ∀ v : Pl F, (∃ w, Formalism.UG.IsInertAt F E v w) → (∀ w ∈ aboveF (L := E) F v, UnrAt χW w) → φ v = M.vac v →
    ∀ μ : Measure (UAtSub σ X (evFin F v)), μ.IsHaarMeasure → μ {g | g.1 ∈ K} = 1 → ∀ s : ℂ, (n : ℝ) / 2 < s.re →
      zetaOn m om (pure f φ) i K₂ _ μ s = (∏ j ∈ Finset.range n, Lv (charFam χW) v (s + (n : ℂ) / 2 - (j : ℂ))) * denInv E n v s := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ _ _ hd X₂ i K₂ hD _ _ m hm K hK f _ φ hSB hvac h0 v
    ⟨w, hw⟩ hunr hφv μ hμ hμK s hs
  classical
  have hcm := hP.base.cm
  have h := under_eq_of_isInertAt hw
  have hu : UnrAt χW w := hunr w (mem_aboveF.2 h)
  haveI hL : Submodule.IsLattice E X.L := hP.herm.lat
  have hL₂ : X₂.L.IsLattice E := by rw [hD.lat]; infer_instance

  have hstd : ∀ᶠ u in Filter.cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := by
    filter_upwards [hvac, hP.good.std] with u h1 h2
    rw [h1, h2]
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  obtain ⟨R, hR, hRt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have e1 : pure f φ = tens (evFin F v) (M.vac v) R := by rw [← hφv, hRt, Function.update_eq_self]
  obtain ⟨Ψ, hΨ1, hΨ2⟩ := exists_section hP hD m hm hΦ h0 (GlobalTheory.DblVac.KD σ X v) fun d' hd' dd omd hdc hsp => by
    rw [e1] at hΦ h0 ⊢
    exact GlobalTheory.PairDblVac.dbl_vac_fixed F E σ B n d X W M χX χW om r s' r₁ s₁ hP v w hw hu d' hd' dd omd hdc hsp R
      ⟨hR, hΦ⟩ h0

  have hJ : IsHermND σ X.Jᵀ := GlobalTheory.IwLine.isHermND_transpose hP.herm
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by rw [hD.gram, GlobalTheory.DblIwasawa.transpose_dblGram]
  obtain ⟨-, ⟨c, hc, -⟩, hab, hN, hch⟩ := (exists_isInertChart σ hcm v).2 w h hw
  obtain ⟨⟨ϖ₀, hU⟩, hch⟩ := hch c hc
  obtain ⟨e, he, hec, hec'⟩ := hch n X.Jᵀ X.L hJ hL.fg hL.span_eq_top
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s' hP.base hP.herm v)
  obtain ⟨ch, hchK, hio, hchP, hcha⟩ := GlobalTheory.DblInert.exists_dblChart F E σ hcm n X.Jᵀ hJ X₂.Jᵀ hQ X.L v w h hw c e he
  have hϖ0 : ϖ₀ ≠ 0 := by
    intro h1
    have := hU.2.2.2.1
    rw [h1, map_zero] at this
    exact WithZero.zero_ne_coe this
  let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ₀ hϖ0
  have hq2 : 2 ≤ Formalism.UG.qV F v := hU.2.2.2.2.2.1
  have hq : Formalism.UG.qV F v ≠ 0 := by omega
  have hval : val χW w = 1 := val_eq_one hP.resW hd hw hu
  have hϖ : ((locChar χW w ϖ : ℂˣ) : ℂ) = 1 := by
    rw [hu.locChar_eq_val (x := ϖ) hU.2.2.2.1, hval, Units.val_one]

  let Θ : UA σ X₂.J → ℂ := fun g => Ψ g *
    (((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ g : ℝ≥0) : ℝ) : ℂ) ^
      (s - ((d : ℂ) - (n : ℂ)) / 2)
  let Φ' : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n → ℂ := fun g => Θ (GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v (ch.symm g)))
  have hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (Formalism.UG.qV F v) n (locChar χW w) s Φ' := by
    intro p k hk
    have hp : ch.symm p ∈ siegelH (Fv F v) σ X₂.Jᵀ := (hchP _).2 (by rw [ch.apply_symm_apply]; exact p.2)
    have hk' : ch.symm k ∈ KFin σ X₂.Jᵀ X.L v := (hchK _).2 (by rwa [ch.apply_symm_apply])
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (toCompl h).toMonoidHom (aH _ σ X₂.Jᵀ ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (ch.apply_symm_apply _).symm)).trans (hcha ⟨_, hp⟩ ((hchP _).1 hp))
    let P : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype :=
      ⟨GlobalTheory.IwLine.ofGAd σ X₂.J (embP v ⟨_, hp⟩ : siegelH (AF F) σ X₂.Jᵀ), (embP v ⟨_, hp⟩).2⟩
    have ha : aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype P = ideleAt F E v (aH _ σ X₂.Jᵀ ⟨_, hp⟩) :=
      (Units.ext rfl).trans (aH_embP v ⟨_, hp⟩)
    have hkK : GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v (ch.symm k)) ∈ K₂ :=
      (emb_mem_iff hL₂ hD.stab v _).2 (by rw [hD.lat]; exact hk')
    have e4 : GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v (ch.symm (p * k))) =
        P.1 * GlobalTheory.IwLine.ofGAd σ X₂.J (emb σ X₂.Jᵀ v (ch.symm k)) := by
      rw [map_mul, map_mul, map_mul]; rfl
    simp only [Φ', Θ]
    rw [e4, hΨ2 P _ (toUD_mem_KD hD.gram v hk'), hD.iwa.hgtOf_mul P hkK, ha, absE_ideleAt, mul_assoc]
    change ((charAt χW v _ : Circle) : ℂ) * (_ * GlobalTheory.Doubling.npow _ _) = _
    rw [← GlobalTheory.Doubling.npow_add (hom_pos (absEv F E v) _), GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt F E χW v w h hw,
      GlobalTheory.KerInert.npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hcm v w h hw _), e3, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal,
      show (d : ℂ) / 2 + (s - ((d : ℂ) - (n : ℂ)) / 2) = s + (n : ℂ) / 2 by ring]
    rfl

  letI : MeasurableSpace (Formalism.UG.GU c n) := borel _
  haveI : BorelSpace (Formalism.UG.GU c n) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  let e₀ := GlobalTheory.LocUnitaryUnimod.locEquiv σ v X
  let ee : UAtSub σ X (evFin F v) ≃ₜ* Formalism.UG.GU c n :=
    e₀.trans { e with continuous_toFun := hec, continuous_invFun := hec' }
  have hee : ∀ g, ee g = e (e₀ g) := fun _ => rfl
  haveI : IsTopologicalRing (AE F E) := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    exact isTopologicalRing_tens
  haveI : (μ.map ee).IsHaarMeasure := ee.isHaarMeasure_map μ
  have hemb : MeasurableEmbedding ee := ee.toHomeomorph.measurableEmbedding
  have hμ' : (μ.map ee) (Formalism.UG.KU c n) = 1 := by
    rw [hemb.map_apply, ← hμK]
    congr 1
    ext g
    change e (e₀ g) ∈ Formalism.UG.KU c n ↔ g.1 ∈ K
    rw [← he.2.2, eq_emb_locEquiv X v g, emb_mem_iff hL hK]
  obtain ⟨α, hα, hz⟩ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_one (L := w.adicCompletion E) hU n
  obtain ⟨-, hint, -⟩ := (GlobalTheory.InertZeta.unramDoublingInert _ ϖ c _ n hU (μ.map ee) hμ' (locChar χW w) hu s Φ' hΦ' α _ hz).1
    (by rw [hϖ]; exact domain_triv hq2 n hs α hα)
  rw [hemb.integral_map, hϖ, closedForm_triv hq n s α hα] at hint
  have hfun : ∀ g : UAtSub σ X (evFin F v), Φ' (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (ee g)) = Θ (i (g.1, 1)) := fun g => by
    simp only [Φ']
    rw [hee, ← hio, ch.symm_apply_apply, emb_ioH, map_one]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    change _ = mat (i (g.1, 1))
    rw [hD.emb]
    conv_rhs => rw [eq_emb_locEquiv X v g]
    rfl
  have e5 : aboveF (L := E) F v = {w} := by
    ext u
    rw [mem_aboveF, Finset.mem_singleton]
    exact hab u
  simp only [hfun, mul_one] at hint
  simp only [zetaOn, hΨ1]
  refine hint.trans ?_
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Lv, e5, Finset.prod_singleton, locL, charFam_of_unrAt hu, hval, eulerFac_singleton, GlobalTheory.LFun.npow, hN,
      Units.val_one, one_mul]
    rfl
  · rw [denInv, etaAt, if_pos ⟨w, hw⟩]
    rfl

end GlobalTheory.BotInert

end
