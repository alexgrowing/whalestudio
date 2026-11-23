import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsOrbitLabellingAtInertPrimeOfOddOrder
import Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfEvenOfRankOKOfNotDvdDiscr
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth UpperTheory.G2 NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace UpperTheory.OrbitFamilyRestriction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private noncomputable def gaT (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) : ℕ → ℕ :=
  GlobalTheory.RowAt.gap (Dw.mult τ) fun i => a (τ, i)

private theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) : Z.card * P.d = Fintype.card P.Pl := by
  haveI := P.nz
  have hbij : Function.Bijective (fun x : {z // z ∈ Z} × ZMod P.d => P.pos x.1.1 x.2.val) := by
    constructor
    · rintro ⟨⟨z1, hz1⟩, s1⟩ ⟨⟨z2, hz2⟩, s2⟩ heq
      obtain ⟨q, -, hq⟩ := h (P.pos z1 s1.val)
      have e1 := hq (z1, s1) ⟨hz1, rfl⟩
      have e2 := hq (z2, s2) ⟨hz2, by simpa using heq.symm⟩
      have e := e1.trans e2.symm
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rfl
    · intro w
      obtain ⟨q, ⟨hq1, hq2⟩, -⟩ := h w
      exact ⟨(⟨q.1, hq1⟩, q.2), hq2⟩
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_prod, Fintype.card_coe, ZMod.card] at hc
  exact hc

private theorem exists_rowFamS (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) →
      ∃ (Z : Finset (parOf N j l).Pl) (tau : {z // z ∈ Z} → ZMod (2 * (parOf N j l).d) → (E →+* ℂ))
        (R : RowFamS (parOf N j l) l Z), RF.IsReps (parOf N j l) Z ∧
        Function.Bijective (fun x : {z // z ∈ Z} × ZMod (2 * (parOf N j l).d) => tau x.1 x.2) ∧
        (∀ o s, InPsi H (tau o s) ↔ Even s.val) ∧
        (∀ o s, Even s.val → tau o s = pl (N.pos l o.1 (s.val % N.ordP l))) ∧
        (∀ o s, (R.X o).rkF 0 s = Dw.mult (tau o s)) ∧
        ValBlocksS ((parOf N j l).d : ZMod (2 * (parOf N j l).d)) R.X R.F nW (fun o s => gaT Dw a (tau o s)) ν := by
  intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 T io e hover y halg C3 nW ν hν hcls hodd
  obtain ⟨C, hF, hCZ, V, ι, hVl, hemb, halgc, hcpl, hMM, hvm, hnu⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  have hl2 : V.l ≠ 2 := hVl ▸ ne_two_of_not_small hsmall
  have hνC := hnu y C3 lv.M a nW ν hν
  have hvM : V.v (lv.M : C) = 0 := hvm _ hM
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hemb halgc hcpl hl2
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M hvM
  rw [← hVl] at hcls hodd ⊢
  haveI : NeZero (N.ordP V.l) := ⟨hodd.pos.ne'⟩
  haveI : NeZero (2 * N.ordP V.l) := ⟨by have := hodd.pos; omega⟩
  obtain ⟨Z, hZ⟩ := GlobalTheory.InertLabelling.exists_reps N V.l
  have hZ' : RF.IsReps (parOf N j V.l) Z := hZ
  obtain ⟨lab, hari, hhd, hn, hj, hj', hbig, htau, hsurj, hdisc⟩ :=
    UpperTheory.exists_orbit_labelling_at_inert_prime_of_odd_order E H lv c N pl htie la T io C V ι hemb hcpl hVl hl2 hMM hcls hodd j Z hZ' (N.R.k - 1) j (N.R.m - j)
  have hinP : ∀ o s, lab.tau o s ↑H.rt = H.rt0 ↔ Even s.val := by
    intro o s
    rw [htau o s]
    split_ifs with he
    · simp only [he, iff_true]
      exact (htie.psi _).2 ⟨_, rfl⟩
    · simp only [he, iff_false]
      exact fun h => (RowLab.inPsi_conj_iff (H := H) _).1 h ((htie.psi _).2 ⟨_, rfl⟩)
  have hmult : ∀ o s, Dw.mult (lab.tau o s) = if Even s.val then Dw.p else Dw.q := by
    intro o s
    simp only [Datum.mult, hinP]
  have h2 : ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l)) + (N.ordP V.l : ℕ) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  have hpar : ∀ s : ZMod (2 * N.ordP V.l), Even (s - ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l))).val ↔ ¬Even s.val := by
    intro s
    have e1 : s - ((N.ordP V.l : ℕ) : ZMod (2 * N.ordP V.l)) = s + (N.ordP V.l : ℕ) := by
      rw [sub_eq_iff_eq_add, add_assoc, h2, add_zero]
    have hlt : N.ordP V.l < 2 * N.ordP V.l := by have := hodd.pos; omega
    rw [e1, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]
    obtain ⟨t, ht⟩ := hodd
    omega
  have hk3 := N.R.m_add_three_le_k
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g s
      rw [hbig, hbig]
      fin_cases g <;> simp
    · intro s hs
      rw [hbig] at hs
      simp only [iff_true] at hs
      rw [hmult, if_pos hs, hn, hj, hp]
      simp only [Ranks.sigW]
      omega
    · intro s hs
      rw [hbig] at hs
      simp only [iff_true] at hs
      rw [hmult, if_neg hs, hj', hq]
      simp only [Ranks.sigW]
    · intro s hs
      rw [hbig] at hs
      simp at hs
      rw [hhd, hmult, if_pos ((hpar s).2 (Nat.not_even_iff_odd.2 hs)), hn, hj, hp]
      simp only [Ranks.sigW]
      omega
    · intro s hs
      rw [hbig] at hs
      simp at hs
      rw [hhd, hmult, if_neg (fun h => (hpar s).1 h hs), hj', hq]
      simp only [Ranks.sigW]
  have hbig0 : ∀ o s, lab.big o 0 s ↔ Even s.val := fun o s => by rw [hbig]; simp
  have hlt : lab.j' < lab.n := by rw [hj', hn]; omega
  have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
    fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
  have hsupp : ∀ o s k', gaT Dw a (lab.tau o s) k' ≠ 0 → 1 ≤ k' ∧ k' ≤ Dw.mult (lab.tau o s) :=
    fun o s k' h => (GlobalTheory.RowAt.gap_sums _ _ (hmono _)).1 k' h
  have hwt : WtTieS Dw.mult lab.tau (fun o s => gaT Dw a (lab.tau o s)) fun τ i => a (τ, i) := by
    refine ⟨fun o s i hi => ?_, fun σ hσ => ?_⟩
    · exact (((GlobalTheory.RowAt.gap_sums _ _ (hmono _)).2 _ le_rfl).1 i hi).symm
    · obtain ⟨x, hx⟩ := hsurj σ
      exact absurd hx (hσ x.1 x.2)
  obtain ⟨X, F, hX, hval⟩ := UpperTheory.labelSetGeo_of_even_of_rankOK_of_not_dvd_discr hUp E H Dw lv Xo c hstar T io y C3 C V ι hemb lv.M Y hY halg
    {z // z ∈ Z} (2 * N.ordP V.l) lab hari hdisc ⟨N.ordP V.l, by ring⟩ hrank hbig0 hlt a
    (fun o s => gaT Dw a (lab.tau o s)) hsupp hwt nW ν hνC
  have key : ∀ v w : ℕ, v < 2 * N.ordP V.l → w < 2 * N.ordP V.l → (Even v ↔ Even w) →
      v % N.ordP V.l = w % N.ordP V.l → v = w := by
    intro v w hv hw hpw hvw
    have hm := hodd.pos
    have h1 := Nat.div_add_mod v (N.ordP V.l)
    have h2 := Nat.div_add_mod w (N.ordP V.l)
    have h3 : v / N.ordP V.l < 2 := (Nat.div_lt_iff_lt_mul hm).2 hv
    have h4 : w / N.ordP V.l < 2 := (Nat.div_lt_iff_lt_mul hm).2 hw
    rw [Nat.even_iff, Nat.even_iff] at hpw
    obtain ⟨t, ht⟩ := hodd
    generalize v / N.ordP V.l = p1 at *
    generalize w / N.ordP V.l = p2 at *
    generalize v % N.ordP V.l = r1 at *
    generalize w % N.ordP V.l = r2 at *
    interval_cases p1 <;> interval_cases p2 <;> omega
  have hinj : Function.Injective (fun x : {z // z ∈ Z} × ZMod (2 * N.ordP V.l) => lab.tau x.1 x.2) := by
    rintro ⟨o, s⟩ ⟨o', s'⟩ heq
    simp only at heq
    have hps : Even s.val ↔ Even s'.val := by rw [← hinP o s, ← hinP o' s', heq]
    have hpos : N.pos V.l o.1 s.val = N.pos V.l o'.1 s'.val := by
      rw [htau, htau] at heq
      by_cases he : Even s.val
      · rw [if_pos he, if_pos (hps.1 he)] at heq
        exact htie.inj heq
      · rw [if_neg he, if_neg (fun h => he (hps.2 h))] at heq
        exact htie.inj ((ComplexEmbedding.involutive_conjugate E).injective heq)
    obtain ⟨q, -, hq'⟩ := hZ (N.pos V.l o.1 s.val)
    have e1 := hq' (o.1, (s.val : ZMod (N.ordP V.l))) ⟨o.2, by simp only [ZMod.val_natCast, RowLab.pos_mod]⟩
    have e2 := hq' (o'.1, (s'.val : ZMod (N.ordP V.l))) ⟨o'.2, by simp only [ZMod.val_natCast, RowLab.pos_mod, hpos]⟩
    have e3 := e1.trans e2.symm
    simp only [Prod.mk.injEq] at e3
    obtain ⟨ho, hs⟩ := e3
    have hmod : s.val % N.ordP V.l = s'.val % N.ordP V.l := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hs
    have hv := key _ _ (ZMod.val_lt s) (ZMod.val_lt s') hps hmod
    exact Prod.ext (Subtype.ext ho) (ZMod.val_injective _ hv)
  have hnm : lab.j + lab.j' = N.R.m := by rw [hj, hj']; omega
  refine ⟨Z, lab.tau,
    { C := C, V := V, hVl := rfl, I := fun o x ↦ lab.II Dw o, J := fun o ↦ JJ fun x ↦ lab.II Dw o, X := X, F := F,
      hn := fun o => ⟨(hX o).1.trans hn, (hX o).2.1.trans hnm⟩,
      alt := fun o => (hX o).2.2.1 },
    hZ', ⟨hinj, hsurj⟩, fun o s => hinP o s, fun o s he => ?_, fun o s => (hX o).2.2.2 s, ?_⟩
  · exact (htau o s).trans ((if_pos he).trans (congrArg pl (RowLab.pos_mod N V.l o.1 s.val).symm))
  · rw [hhd] at hval
    exact hval

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (p : Prop) [Decidable p] (g : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (if p ∧ k = n then (0 : ℝ) else (k : ℝ) * g k) =
      ((∑ k ∈ Finset.Icc 1 K, k * g k : ℕ) : ℝ) - (n : ℝ) * if p then (g n : ℝ) else 0 := by
  push_cast
  by_cases hp : p
  · have hn : n ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨h1, hK⟩
    simp only [hp, true_and, if_true]
    rw [← Finset.add_sum_erase _ _ hn, ← Finset.add_sum_erase (Finset.Icc 1 K) (fun k => (k : ℝ) * (g k : ℝ)) hn]
    rw [if_pos rfl, Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
    ring
  · simp [hp]

end UpperTheory.OrbitFamilyRestriction

open UpperTheory.OrbitFamilyRestriction in
theorem UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)],
    (AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → ∀ T θ0 C1 : ℝ,
      RF.DegHyp2 (parOf N j l) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 →
      N.R.f * ((RF.i0 N.R.k l + 1) * (N.R.k - 1) + 4 * N.R.r) ≤ nW →
      ∃ Pk : PkgCs (parOf N j l) l C1, Pk.T = T ∧ Pk.ν = ν) ∧
    (AllPts Xo c fun N j l _ a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → (∀ z, 0 ≤ N.w j z) →
      ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∃ Pk : PkgZeroCs (parOf N j l) l, Pk.ν = ν) := by
  intro hUp E _ _ _ H Dw lv Xo c _
  have hR := exists_rowFamS hUp Xo c
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
      T θ0 C1 hdeg hrows
    obtain ⟨Z, tau, R, hZ, hbij, hpsi, hev, hrk, hval⟩ :=
      hR hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
    have hk3 := N.R.m_add_three_le_k
    have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
      fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
    have hmr : ∀ τ, Dw.mult τ ≤ N.R.r := by
      intro τ
      unfold Datum.mult
      rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      split_ifs <;> omega
    have hmain : ∀ (o : {z // z ∈ Z}) (s : ZMod (2 * (parOf N j (resCharOf la)).d)), Even s.val →
        gaT Dw a (tau o s) (N.R.k - 1) = gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) := by
      intro o s he
      rw [hev o s he]
      have hin : pl (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) ↑H.rt = H.rt0 :=
        (htie.psi _).2 ⟨_, rfl⟩
      simp only [gaT, GlobalTheory.RowAt.gap, Datum.mult, hin, if_true, hp, Ranks.sigW, gapW]
      split_ifs with hc1 hc2
      · rw [show N.R.k - 1 - 1 = N.R.k - 2 by omega]
      · omega
      · omega
    have hstep : ∀ (o : {z // z ∈ Z}) (s : ZMod (2 * (parOf N j (resCharOf la)).d)),
        (∑ k ∈ Finset.Icc 1 N.R.r, if Even s.val ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * (gaT Dw a (tau o s) k : ℝ)) =
          (∑ i : Fin (Dw.mult (tau o s)), (a (tau o s, i) : ℝ)) - ((N.R.k - 1 : ℕ) : ℝ) *
            (if Even s.val then (gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) : ℝ) else 0) := by
      intro o s
      rw [rest_add (N.R.k - 1) N.R.r (by omega) (by simp only [Ranks.r]; omega) (Even s.val) (gaT Dw a (tau o s))]
      have hg : (∑ k ∈ Finset.Icc 1 N.R.r, k * gaT Dw a (tau o s) k) = ∑ i : Fin (Dw.mult (tau o s)), a (tau o s, i) :=
        ((GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o s))).2 _ (hmr _)).2
      congr 1
      · rw [hg]
        push_cast
        rfl
      · by_cases he : Even s.val
        · rw [if_pos he, if_pos he, hmain o s he]
        · rw [if_neg he, if_neg he]
    have hsumW : ∑ z, (gapW N pl a z : ℝ) = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        (if Even s.val then (gapW N pl a (N.pos (resCharOf la) o.1 (s.val % N.ordP (resCharOf la))) : ℝ) else 0) := by
      let G : (E →+* ℂ) → ℝ := fun τ => ∑ z, if pl z = τ then (gapW N pl a z : ℝ) else 0
      calc ∑ z, (gapW N pl a z : ℝ) = ∑ τ, G τ := by
            simp only [G]
            rw [Finset.sum_comm]
            simp
        _ = ∑ x : {z // z ∈ Z} × ZMod (2 * (parOf N j (resCharOf la)).d), G (tau x.1 x.2) := (hbij.sum_comp G).symm
        _ = ∑ o, ∑ s, G (tau o s) := Fintype.sum_prod_type' (fun o s => G (tau o s))
        _ = _ := by
            refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun s _ => ?_
            by_cases he : Even s.val
            · rw [if_pos he, hev o s he]
              simp [G, htie.inj.eq_iff]
            · rw [if_neg he]
              refine Finset.sum_eq_zero fun z _ => if_neg ?_
              intro hz
              have h1 : InPsi H (pl z) := (htie.psi _).2 ⟨z, rfl⟩
              rw [hz] at h1
              exact he ((hpsi o s).1 h1)
    have hDF : ((DF Dw a : ℕ) : ℝ) = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        ∑ i : Fin (Dw.mult (tau o s)), (a (tau o s, i) : ℝ) := by
      let g : (E →+* ℂ) → ℝ := fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)
      calc ((DF Dw a : ℕ) : ℝ) = ∑ τ, g τ := by simp only [DF, Nat.cast_sum, g]
        _ = ∑ x : {z // z ∈ Z} × ZMod (2 * (parOf N j (resCharOf la)).d), g (tau x.1 x.2) := (hbij.sum_comp g).symm
        _ = ∑ o, ∑ s, g (tau o s) := Fintype.sum_prod_type' (fun o s => g (tau o s))
    have hrest : restOf N Dw pl a = ∑ o : {z // z ∈ Z}, ∑ s : ZMod (2 * (parOf N j (resCharOf la)).d),
        ∑ k ∈ Finset.Icc 1 N.R.r, if Even s.val ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * (gaT Dw a (tau o s) k : ℝ) := by
      rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun s _ => hstep o s]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← hsumW, ← hDF]
      unfold restOf
      rw [Nat.cast_sub (by omega : 1 ≤ N.R.k), Nat.cast_one]
    exact ⟨⟨hodd, Z, hZ, R, fun o s => gaT Dw a (tau o s), gapW N pl a, nW, T, θ0, restOf N Dw pl a, ν,
      fun o s k hk => by rw [hrk]; exact (GlobalTheory.RowAt.gap_sums _ _ (hmono _)).1 k hk,
      fun o s he => hmain o s he, hrest, hrows, hdeg, hval⟩, rfl, rfl⟩
  · intro hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
      hw s ha hrows
    obtain ⟨Z, tau, R, hZ, hbij, hpsi, hev, hrk, hval⟩ :=
      hR hstar N j pl a hj1 hjm htie hp hq hdom la hsmall hqq hdd hM hin5 Tc io e hover y halg C3 nW ν hν hcls hodd
    have hk3 := N.R.m_add_three_le_k
    have hmono : ∀ τ, ∀ i k, i ≤ k → k < Dw.mult τ → a (τ, k) ≤ a (τ, i) :=
      fun τ i k hik hk => hdom τ ⟨i, by omega⟩ ⟨k, hk⟩ (Fin.mk_le_mk.2 hik)
    have hmr : ∀ τ, Dw.mult τ ≤ N.R.r := by
      intro τ
      unfold Datum.mult
      rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      split_ifs <;> omega
    have hc := card_reps _ Z hZ
    have hf : Fintype.card (parOf N j (resCharOf la)).Pl = N.R.f := by
      show Fintype.card (Bool × N.R.A) = N.R.f
      simp [Fintype.card_prod, Formalism.HC.Frame.card_A, Ranks.f, Ranks.n]
    refine ⟨⟨Z, R, fun o σ => gaT Dw a (tau o σ), N.R.r, s, nW, 1, ν, le_rfl, hw, ?_, ?_, ?_, hval⟩, rfl⟩
    · intro o σ k hk
      have h := (GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o σ))).1 k hk
      rw [hrk]
      exact ⟨h.1, h.2, h.2.trans (hmr _)⟩
    · intro o σ
      by_cases h0 : 0 < Dw.mult (tau o σ)
      · have h := ((GlobalTheory.RowAt.gap_sums _ _ (hmono (tau o σ))).2 _ (hmr _)).1 0 h0
        exact le_of_eq_of_le h (ha _ h0)
      · have hz : ∀ k, gaT Dw a (tau o σ) k = 0 := by
          intro k
          simp only [gaT, GlobalTheory.RowAt.gap]
          split_ifs <;> omega
        simp [hz]
    · show 4 * N.R.r * s * (Z.card * (parOf N j (resCharOf la)).d) ≤ nW
      rw [hc, hf]
      exact hrows
