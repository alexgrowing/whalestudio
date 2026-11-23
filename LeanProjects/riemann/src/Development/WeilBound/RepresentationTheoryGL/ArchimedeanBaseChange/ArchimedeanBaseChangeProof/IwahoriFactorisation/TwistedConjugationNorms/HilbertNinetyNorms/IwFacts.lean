import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsValueSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Matrix
open GlobalTheory.CompanionTheory.LbElem.JPredDom (torEmb_diag up_entries lo_entries ratio_lt_one exists_contract exists_value_subset
  sub_one_le levi_comm val_inv_diag)
open GlobalTheory.CompanionTheory.LbElem.MonomialInJ (nup_entries nlo_entries diag_ne_zero_of_offDiag)
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial (tor_offDiag mem_tor_of_offDiag)
open GlobalTheory.CompanionTheory.LbElem.IwahoriLDU (mem_Nup_of mem_Nlo_of)

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iw_isOpen (n : ℕ) : IsOpen (iwahori k (Fin n) : Set (GL (Fin n) k)) :=
  GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori k (Fin n)

theorem iw_isCompact (n : ℕ) : IsCompact (iwahori k (Fin n) : Set (GL (Fin n) k)) :=
  GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori k (Fin n)

theorem iw_entry_le {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ iwahori k (Fin n)) (i j : Fin n) :
    valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨g', -, rfl⟩ := Subgroup.mem_map.1 hg
  exact (g'.val i j).2

theorem iw_of_entries {n : ℕ} (g : GL (Fin n) k) (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h3 : ∀ i j, j < i → valuation k ((g : Matrix (Fin n) (Fin n) k) i j) < 1) : g ∈ iwahori k (Fin n) := by
  let M : Matrix (Fin n) (Fin n) (valuation k).integer := fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, h1 i j⟩
  let N : Matrix (Fin n) (Fin n) (valuation k).integer :=
    fun i j => ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j, h2 i j⟩
  have hinj : Function.Injective ((algebraMap (valuation k).integer k).mapMatrix : Matrix (Fin n) (Fin n) _ → _) :=
    Matrix.map_injective Subtype.val_injective
  have hM : (algebraMap (valuation k).integer k).mapMatrix M = (g : Matrix (Fin n) (Fin n) k) := by
    ext i j; rfl
  have hN : (algebraMap (valuation k).integer k).mapMatrix N = ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    ext i j; rfl
  have hMN : M * N = 1 := hinj (by rw [map_mul, map_one, hM, hN]; exact g.mul_inv)
  have hNM : N * M = 1 := hinj (by rw [map_mul, map_one, hM, hN]; exact g.inv_mul)
  refine Subgroup.mem_map.2 ⟨⟨M, N, hMN, hNM⟩, ?_, ?_⟩
  · show Matrix.BlockTriangular _ _
    intro i j hij
    simp [GlobalTheory.SmGL.blk, GlobalTheory.SmGL.points] at hij ⊢
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (h3 i j hij)
  · ext i j
    rfl

theorem iw_hasIwahoriFact (n : ℕ) : HasIwahoriFact k n (iwahori k (Fin n)) (ones n) (sum_ones n) := by
  intro x hx
  obtain ⟨u, hu, d, hd, c, hc, he⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation (Subgroup.inv_mem _ hx)
  have hx' : x = c⁻¹ * (diagT k (Fin n) d)⁻¹ * u⁻¹ := by
    rw [← inv_inv x, he]
    group
  have huI : u ∈ iwahori k (Fin n) := (GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu
  have hcI : c ∈ iwahori k (Fin n) := GlobalTheory.SmGL.KOne_le_iwahori k (Fin n) hc.2
  have hDI : diagT k (Fin n) d ∈ iwahori k (Fin n) := GlobalTheory.SmGL.diagT_mem_iwahori hd
  have hc' := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hc.1
  have hu' := (GlobalTheory.SmGL.mem_unipB k).1 hu.1
  have hDt : diagT k (Fin n) d ∈ Tor k n := by
    apply mem_tor_of_offDiag
    intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ hij]
  have hcN : c⁻¹ ∈ Nlo k n := Subgroup.inv_mem _ (mem_Nlo_of c hc'.1 hc'.2)
  have huN : u⁻¹ ∈ Nup k n := Subgroup.inv_mem _ (mem_Nup_of u hu'.1 hu'.2)
  have hDT : (diagT k (Fin n) d)⁻¹ ∈ Tor k n := Subgroup.inv_mem _ hDt
  exact ⟨c⁻¹, Subgroup.mem_inf.2 ⟨Subgroup.inv_mem _ hcI, hcN⟩, (diagT k (Fin n) d)⁻¹,
    Subgroup.mem_inf.2 ⟨Subgroup.inv_mem _ hDI, hDT⟩, u⁻¹, Subgroup.mem_inf.2 ⟨Subgroup.inv_mem _ huI, huN⟩, hx'⟩

private theorem diagT_coe_eq_diagonal (n : ℕ) (d : Fin n → kˣ) :
    ((diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i => (d i : k)) := by
  ext i j
  simp [diagT, leviEmb, leviTorus, points, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]

theorem diagT_mem_Tor (n : ℕ) (d : Fin n → kˣ) : diagT k (Fin n) d ∈ Tor k n :=
  mem_tor_of_offDiag _ fun i j hij => by rw [val_diagT, diagonal_apply_ne _ hij]

theorem diagT_incrV (n : ℕ) (d : Fin n → kˣ)
    (h : ∀ i j : Fin n, i < j → valuation k (d i : k) < valuation k (d j : k)) :
    IncrV k n (diagT k (Fin n) d) := by
  intro i j hij
  rw [diagT_coe_eq_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  exact h i j hij

theorem up_conj_int {n : ℕ} {t m : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    (hm : m ∈ iwahori k (Fin n)) (hN : m ∈ Nup k n) (i j : Fin n) :
    valuation k (((t * m * t⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨h0, h1⟩ := nup_entries hN
  obtain ⟨e0, e1, e2⟩ := up_entries ht h0 h1 1
  simp only [pow_one] at e0 e1 e2
  rcases lt_trichotomy i j with h | rfl | h
  · rw [e2]
    exact (mul_le_of_le_one_left' (ratio_lt_one (hinc i j h)).le).trans (iw_entry_le hm i j)
  · rw [e1, map_one]
  · rw [e0 i j h, map_zero]
    exact zero_le'

theorem lo_conj_int {n : ℕ} {t m : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    (hm : m ∈ iwahori k (Fin n)) (hN : m ∈ Nlo k n) (i j : Fin n) :
    valuation k (((t⁻¹ * m * t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤
      valuation k ((m : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨hup, hdiag⟩ := nlo_entries hN
  obtain ⟨-, -, e2⟩ := lo_entries ht hup hdiag 1
  simp only [pow_one] at e2
  rw [e2]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hup i j hij, map_zero, mul_zero]
  · have hne : valuation k (d i) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact GlobalTheory.CompanionTheory.LbElem.JPredDom.diag_ne_zero ht i
    rw [div_self hne, one_mul]
  · calc valuation k (d j) / valuation k (d i) * valuation k ((m : Matrix (Fin n) (Fin n) k) i j)
        ≤ 1 * valuation k ((m : Matrix (Fin n) (Fin n) k) i j) := by
          gcongr
          exact (ratio_lt_one (hinc j i hij)).le
      _ = _ := one_mul _

theorem iw_up_mem {n : ℕ} {t : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    {m : GL (Fin n) k} (hm : m ∈ KN k n (iwahori k (Fin n)) (ones n) (sum_ones n)) :
    t * m * t⁻¹ ∈ KN k n (iwahori k (Fin n)) (ones n) (sum_ones n) := by
  obtain ⟨h0, h1⟩ := nup_entries hm.2
  obtain ⟨e0, e1, -⟩ := up_entries ht h0 h1 1
  simp only [pow_one] at e0 e1
  have hinv : (t * m * t⁻¹)⁻¹ = t * m⁻¹ * t⁻¹ := by group
  refine ⟨iw_of_entries _ (up_conj_int ht hinc hm.1 hm.2) (fun i j => ?_) fun i j hij => ?_,
    mem_Nup_of _ e0 e1⟩
  · rw [hinv]
    exact up_conj_int ht hinc (inv_mem hm.1) (inv_mem hm.2) i j
  · rw [e0 i j hij, map_zero]
    exact zero_lt_one

theorem iw_lo_mem {n : ℕ} {t : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    {m : GL (Fin n) k} (hm : m ∈ KNl k n (iwahori k (Fin n)) (ones n) (sum_ones n)) :
    t⁻¹ * m * t ∈ KNl k n (iwahori k (Fin n)) (ones n) (sum_ones n) := by
  obtain ⟨h0, h1⟩ := nlo_entries hm.2
  obtain ⟨e0, e1, -⟩ := lo_entries ht h0 h1 1
  simp only [pow_one] at e0 e1
  have hinv : (t⁻¹ * m * t)⁻¹ = t⁻¹ * m⁻¹ * t := by group
  refine ⟨iw_of_entries _ (fun i j => (lo_conj_int ht hinc hm.1 hm.2 i j).trans (iw_entry_le hm.1 i j))
    (fun i j => ?_) fun i j hij => ?_, mem_Nlo_of _ e0 e1⟩
  · rw [hinv]
    exact (lo_conj_int ht hinc (inv_mem hm.1) (inv_mem hm.2) i j).trans (iw_entry_le (inv_mem hm.1) i j)
  · exact (lo_conj_int ht hinc hm.1 hm.2 i j).trans_lt ((mem_iwahori.1 hm.1).2 i j hij)

theorem iw_up_contract {n : ℕ} {t : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    {U : Set (GL (Fin n) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r : ℕ, ∀ m ∈ KN k n (iwahori k (Fin n)) (ones n) (sum_ones n), t ^ r * m * (t ^ r)⁻¹ ∈ U := by
  obtain ⟨γ, hγ, hsub⟩ := exists_value_subset hU h1
  obtain ⟨r, hr⟩ := exists_contract (GlobalTheory.CompanionTheory.LbElem.JPredDom.diag_ne_zero ht) hinc hγ
  refine ⟨r, fun m hm => hsub _ ?_⟩
  obtain ⟨h0, h1'⟩ := nup_entries hm.2
  obtain ⟨e0, e1, e2⟩ := up_entries ht h0 h1' r
  refine sub_one_le e1 fun i j hij => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · rw [e2]
    exact (mul_le_of_le_one_right' (iw_entry_le hm.1 i j)).trans (hr i j h).le
  · rw [e0 i j h, map_zero]
    exact zero_le'

theorem iw_lo_contract {n : ℕ} {t : GL (Fin n) k} {d : Fin n → k}
    (ht : (t : Matrix (Fin n) (Fin n) k) = Matrix.diagonal d)
    (hinc : ∀ i j : Fin n, i < j → valuation k (d i) < valuation k (d j))
    {U : Set (GL (Fin n) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r : ℕ, ∀ m ∈ KNl k n (iwahori k (Fin n)) (ones n) (sum_ones n), (t ^ r)⁻¹ * m * t ^ r ∈ U := by
  obtain ⟨γ, hγ, hsub⟩ := exists_value_subset hU h1
  obtain ⟨r, hr⟩ := exists_contract (GlobalTheory.CompanionTheory.LbElem.JPredDom.diag_ne_zero ht) hinc hγ
  refine ⟨r, fun m hm => hsub _ ?_⟩
  obtain ⟨h0, h1'⟩ := nlo_entries hm.2
  obtain ⟨e0, e1, e2⟩ := lo_entries ht h0 h1' r
  refine sub_one_le e1 fun i j hij => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · rw [e0 i j h, map_zero]
    exact zero_le'
  · rw [e2]
    exact (mul_le_of_le_one_right' (iw_entry_le hm.1 i j)).trans (hr j i h).le

theorem iw_domT_strDomT (n : ℕ) (x : GL (Fin n) k) (hx : x ∈ Tor k n) (hinc : IncrV k n x) :
    DomT k n (iwahori k (Fin n)) x ∧ StrDomT k n (iwahori k (Fin n)) x := by
  obtain ⟨s, rfl⟩ := hx
  have ht := torEmb_diag s
  have dom : IsDominant k n (iwahori k (Fin n)) (ones n) (sum_ones n) s := by
    refine ⟨fun m hm => iw_up_mem ht hinc hm, fun m hm => iw_lo_mem ht hinc hm, fun y hy => ?_⟩
    have e1 : s * y * s⁻¹ = y := by rw [levi_comm s y, mul_inv_cancel_right]
    have e2 : s⁻¹ * y * s = y := by rw [levi_comm s⁻¹ y, inv_mul_cancel_right]
    rw [e1, e2]
    exact ⟨hy, hy⟩
  exact ⟨⟨s, rfl, dom⟩, s, rfl, ⟨dom, fun U hU h1 => iw_up_contract ht hinc hU h1⟩,
    fun U hU h1 => iw_lo_contract ht hinc hU h1⟩

theorem map_one_aut {G : Type} [Group G] (H : Subgroup G) : H.map (1 : MulAut G).toMonoidHom = H := by
  ext g
  simp [Subgroup.mem_map]

theorem iwahori_trivial_aut_admissible (n : ℕ) : admitted k n (iwahori k (Fin n)) 1 1 :=
  ⟨iw_isOpen n, iw_isCompact n, iw_hasIwahoriFact n, continuous_id, one_pos, one_pow 1, map_one_aut _,
    map_one_aut _, map_one_aut _, map_one_aut _⟩

theorem tnorm_one_one {G : Type} [Group G] (x : G) : tnorm (1 : MulAut G) 1 x = x := by
  simp [tnorm]

theorem iw_goodT_one (n : ℕ) (t : GL (Fin n) k) (ht : t ∈ Tor k n) (hinc : IncrV k n t) :
    GoodT k n (iwahori k (Fin n)) 1 1 t := by
  obtain ⟨hd, hs⟩ := iw_domT_strDomT n t ht hinc
  refine ⟨ht, fun i hi => ?_, ?_⟩
  · obtain rfl : i = 0 := by omega
    simpa using hd
  · rw [tnorm_one_one]
    exact hs

theorem iw_tor_entries (n : ℕ) (κ : GL (Fin n) k) (hκ : κ ∈ iwahori k (Fin n) ⊓ Tor k n) :
    (∀ i j : Fin n, i ≠ j → (κ : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      ∀ i, valuation k ((κ : Matrix (Fin n) (Fin n) k) i i) = 1 := by
  refine ⟨fun i j hij => tor_offDiag hκ.2 hij, fun i => ?_⟩
  have hmul : (κ : Matrix (Fin n) (Fin n) k) i i * ((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = 1 := by
    have h1 : ((κ * κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · exact h1
    · intro b _ hb
      rw [tor_offDiag hκ.2 (Ne.symm hb), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have ha := iw_entry_le hκ.1 i i
  have hb := iw_entry_le (inv_mem hκ.1) i i
  have hm := congrArg (valuation k) hmul
  rw [map_mul, map_one] at hm
  refine le_antisymm ha ?_
  calc (1 : ValueGroupWithZero k) = _ := hm.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _

end General

section Completion

open NumberField IsDedekindDomain GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tdiag_mem_Tor (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (n : ℕ) (y : Fin n → ℤ) :
    tdiag ϖ y ∈ Tor (w.adicCompletion E) n :=
  diagT_mem_Tor n _

omit [IsCMField E] in

theorem unif_val_lt_one (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1) :
    Valued.v (ϖ : w.adicCompletion E) < 1 := by
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by simp
  unfold ordL at hϖ
  rw [dif_neg h0] at hϖ
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    omega
  rw [← WithZero.coe_unzero h0, hu]
  exact WithZero.coe_lt_coe.2 (Multiplicative.ofAdd_lt.2 (by norm_num))

theorem tdiag_incrV (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) : IncrV (w.adicCompletion E) n (tdiag ϖ y) := by
  haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion E) _)
  have hlt : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (ValuativeRel.isEquiv (Valued.v : Valuation (w.adicCompletion E) _)
      (valuation _)).lt_one_iff_lt_one.1 (unif_val_lt_one w ϖ hϖ)
  have hpos : 0 < valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact ϖ.ne_zero
  refine diagT_incrV n _ (fun i j hij => ?_)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_lt_zpow_right_of_lt_one₀ hpos hlt (hy hij)

theorem iw_tor_TO (w : Pl E) (n : ℕ) (κ : GLw n w) (hκ : κ ∈ iwGL n w ⊓ Tor (w.adicCompletion E) n) :
    κ ∈ TO n w := by
  obtain ⟨hoff, hdiag⟩ := iw_tor_entries n κ hκ
  refine ⟨hoff, fun i => ?_⟩
  haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion E) _)
  exact (ValuativeRel.isEquiv (Valued.v : Valuation (w.adicCompletion E) _)
    (valuation _)).eq_one_iff_eq_one.2 (hdiag i)

theorem iwahori_GL_trivial_admissible (w : Pl E) (n : ℕ) : admitted (w.adicCompletion E) n (iwGL n w) 1 1 :=
  iwahori_trivial_aut_admissible n

theorem goodT_id (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (hy : StrictAnti y) : GoodT (w.adicCompletion E) n (iwGL n w) 1 1 (tdiag ϖ y) :=
  iw_goodT_one n _ (tdiag_mem_Tor w ϖ n y) (tdiag_incrV w ϖ hϖ.1 n y hy)

end Completion

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
