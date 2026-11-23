import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupplyExtend
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RestDegAdd

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SplitPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  have hd : 0 < H.d := H.d_prime.pos
  have e2 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
    have h1 : τ (H.rt : E) = H.rt0 := h
    have h2 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rw [h2, h1]
  have e3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) H.rt_sq
    simpa using this
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast hd
  nlinarith [sq_nonneg r]

theorem pkgSplit : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd' hM _ T io e hov y hy C3 nW ν hν
    hsp Tr θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hMM, hunit, hnu⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hov
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (by rw [hVl]; intro h; exact h2 (h ▸ N.H.two_mem_small)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E :=
    hpl.unr V.l V.l_prime (by rw [hVl]; exact h2) (by rw [hVl]; exact hq') (by rw [hVl]; exact hd')
  obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hpl la T io C V ι hι hVl hMM
    (by rw [hVl]; exact hsp) j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq'' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d :=
    { tau := fun o => tauSp N pl pos o.1, n := N.R.k - 1, j := j, j' := N.R.m - j, big := fun _ g _ => g = 0 }
  have hsep := (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => by simp [lab, tauSp]
      frob := fun o g s x => hfr o.1 g s x
      sep := fun x x' hx => hsep _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr d _ (hfr o.1 g) }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · change (1 - g = 0) ↔ ¬ g = 0
      revert g; decide
    · change g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.k - 1 + j
      rw [tauSp, if_pos hg]
      have : Dw.mult (pl (pos o.1 s.val)) = Dw.p := if_pos (hpsi _)
      omega
    · change ¬ g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.m - j
      rw [tauSp, if_neg hg]
      have : Dw.mult (ComplexEmbedding.conjugate (pl (pos o.1 s.val))) = Dw.q :=
        if_neg (not_inPsi_conjugate H (hpsi _))
      omega
  have hsup := GlobalTheory.T.rowData_supplied_at_pairs_of_places hU E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z d lab harith hbij.2 hrank
    (by change N.R.m - j < N.R.k - 1; omega) (fun o => Or.inr fun _ => rfl) a hdom nW ν (hnu y C3 lv.M a nW ν hν)
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hval⟩ := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g _ => g = 0) (fun z g s => Dw.mult (tauSp N pl pos z g s))
    (fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)) nW ν hne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom d pos Z (fun _ => 0) (tauSp N pl pos) hZ hbij
    (fun z s => by simp [tauSp])
  refine ⟨d, inferInstance, pos,
    { R := { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F,
             hn := fun z => ⟨(hn z).1, (hn z).2.trans (by change j + (N.R.m - j) = N.R.m; omega)⟩ }
      Z := Z
      hZ := hZ
      allBig := fun z hz s => ((hbig z hz 0 s).1).2 rfl
      ga := fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)
      W := gapW N pl a
      nW := nW
      T := Tr
      θ0 := θ0
      rest := restOf N Dw pl a
      ν := ν
      wt := ⟨fun z hz g s k hk => ?_, hwt.main, hwt.rest_eq⟩
      what₂ := hrows
      deg := ⟨hdeg.T_one, hdeg.w_pos, hdeg.TW_lo, hdeg.TW_hi, hdeg.th_rng, hdeg.th_m, hdeg.rest_nonneg, hdeg.rest_le⟩
      val := hval }, rfl, rfl⟩
  have h1 := hwt.supp z hz g s k hk
  exact ⟨h1.1, h1.2.trans (hbig z hz g s).2.ge⟩

end GlobalTheory.SplitPackage
