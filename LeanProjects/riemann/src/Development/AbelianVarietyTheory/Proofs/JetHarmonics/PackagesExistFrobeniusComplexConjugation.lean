import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotInPsiConj
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlacesStatement

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PkgConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

noncomputable def gaC (N : NumDatum) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ)
    (z : RPl N.R) (s : ZMod 2) : ℕ → ℕ :=
  gap (Dw.mult (tauC N pl z s)) fun i => a (tauC N pl z s, i)

theorem exists_rowFam (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => PhiC N l →
      Function.Bijective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) ∧
      ∃ R : RF.RowFam (parOf N j l) l 2, (∀ z, (R.X z).Alt) ∧
        (∀ z s, (R.X z).rkF 0 s = Dw.mult (tauC N pl z s)) ∧
        @RF.ValBlocksC R.C R.fC R.V (parOf N j l).Pl _ R.I R.J R.fI R.fJ R.X R.F nW (gaC N Dw pl a) ν := by
  intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 _ _ hM _ T io e hover y hy C3 nW ν hν hC
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hla, hunit, hconv⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (hVl ▸ (fun h => h2 (h ▸ N.H.two_mem_small) : resCharOf la ≠ 2)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  obtain ⟨hA, hS⟩ := GlobalTheory.LabSelf.arithS_tauC E H lv c N pl hP la T io C V ι hι hVl hla (hVl ▸ hC)
    (N.R.k - 1) j (N.R.m - j)
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hrk : (⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ : LabS E (RPl N.R)).RankOK Dw := by
    intro z
    have h10 : ¬ (1 : ZMod 2) = 0 := by decide
    have t0 : tauC N pl z 0 = pl z := if_pos rfl
    have t1 : tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := if_neg h10
    have m0 : Dw.mult (pl z) = Dw.p := if_pos (hpsi z)
    have m1 : Dw.mult (ComplexEmbedding.conjugate (pl z)) = Dw.q :=
      if_neg (GlobalTheory.LabSelf.not_inPsi_conj H (hpsi z))
    refine ⟨?_, ?_⟩
    · show Dw.mult (tauC N pl z 0) = N.R.k - 1 + j
      rw [t0, m0]; omega
    · show Dw.mult (tauC N pl z 1) = N.R.m - j
      rw [t1, m1, hq']
  obtain ⟨I, J, fI, fJ, X, F, hX, hval⟩ := GlobalTheory.T.rowData_supplied_at_selfConjugate_places hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy
    (RPl N.R) ⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ hA hS hrk (by show N.R.m - j < N.R.k - 1; omega) a hdom nW ν
    (hconv y C3 lv.M a nW ν hν)
  refine ⟨⟨hA.inj, hS⟩, { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F, hn := ?_ },
    fun z => (hX z).2.2.1, fun z => (hX z).2.2.2, hval⟩
  intro z
  refine ⟨(hX z).1, (hX z).2.1.trans ?_⟩
  show j + (N.R.m - j) = N.R.m
  omega

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (ga : ZMod 2 → ℕ → ℕ) :
    ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) =
      ∑ s : ZMod 2, ((∑ k ∈ Finset.Icc 1 K, k * ga s k : ℕ) : ℝ) - (n : ℝ) * ga 0 n := by
  have e : (n : ℝ) * ga 0 n =
      ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, if s = 0 ∧ k = n then (k : ℝ) * ga s k else 0 := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem packages_conj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC T0 θ0 C1 hdeg hrows
    obtain ⟨hbij, R, halt, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hmain : ∀ z, gaC N Dw pl a z 0 (N.R.k - 1) = gapW N pl a z := by
      intro z
      have t0 : tauC N pl z 0 = pl z := if_pos rfl
      have hm : Dw.mult (pl z) = Dw.p := if_pos (hpsi _)
      unfold gaC
      rw [t0, hm]
      unfold gap gapW
      rw [if_pos (by omega), if_pos (by omega)]
      rfl
    have hDF : DF Dw a = ∑ z, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r, k * gaC N Dw pl a z s k := by
      unfold DF
      rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2.symm
    refine ⟨{ R := R, alt := halt, gaC := gaC N Dw pl a, W := gapW N pl a, nW := nW, T := T0, θ0 := θ0,
              rest := restOf N Dw pl a, ν := ν, supp := ?_, main := hmain, rest_eq := ?_, what₂ := hrows,
              deg := hdeg, val := hval }, rfl, rfl⟩
    · intro z s k hk
      rw [hrk]
      exact (hgs _).1 k hk
    · show restOf N Dw pl a = ∑ z : RPl N.R, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r,
        (if s = 0 ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * gaC N Dw pl a z s k)
      simp only [rest_add (N.R.k - 1) N.R.r (by omega) (by omega), hmain]
      unfold restOf
      rw [hDF, Finset.sum_sub_distrib, ← Finset.mul_sum]
      push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
      rfl
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC hw s hfirst hrows
    obtain ⟨-, R, -, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hcard : Fintype.card (RPl N.R) = N.R.f := by
      simp [RPl, Ranks.f, Ranks.n, ZMod.card, N.R.card_A]
    refine ⟨{ R := R, gaC := gaC N Dw pl a, K := N.R.r, s := s, nW := nW, T := 1, ν := ν, T_one := le_rfl,
              w_nonneg := hw, supp := ?_, first := ?_, what₂ := ?_, val := hval }, rfl⟩
    · intro z σ k hk
      rw [hrk]
      have h := (hgs _).1 k hk
      exact ⟨h.1, h.2, h.2.trans (hmul _)⟩
    · intro z σ
      rcases Nat.eq_zero_or_pos (Dw.mult (tauC N pl z σ)) with h0 | h0
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun k _ => ?_)) (Nat.zero_le _)
        by_contra hk
        have h := (hgs _).1 k hk
        omega
      · exact le_trans (le_of_eq (((hgs _).2 _ (hmul _)).1 0 h0)) (hfirst _ h0)
    · show 4 * N.R.r * s * Fintype.card (RPl N.R) ≤ nW
      rw [hcard]; exact hrows

end GlobalTheory.PkgConj
