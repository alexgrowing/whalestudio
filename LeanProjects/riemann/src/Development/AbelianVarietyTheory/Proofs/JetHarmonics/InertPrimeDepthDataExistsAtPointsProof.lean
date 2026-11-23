import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupplyExtend
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RestDegAdd

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) (h1 : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have e3 := H.sqrt_neg_disc_sq
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem zero_eq_bg_iff {d : ℕ} [NeZero d] (s : ZMod d) : (0 : Fin 2) = RF.bg s ↔ Even s.val := by
  unfold RF.bg
  split_ifs with h <;> simp [h]

theorem pkgInert : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hqq hdd hM _ T io e hover y hy C3 nW ν hν
    hin hphi TT θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hl, hι, hac, hcpl, hla, hunit, hval⟩ := GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  have hν' := hval y C3 lv.M a nW ν hν
  have hMu := hunit lv.M hM
  rw [← hl] at h2 hqq hdd hin hphi hdeg hrows ⊢
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M hMu
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E := hpl.unr V.l V.l_prime h2 hqq hdd
  obtain ⟨Z, hZ, hZne, heven, hbij, hfr⟩ := GlobalTheory.InertLabelling.main E H lv c N pl hpl la T io C V ι hι hl hla hin hphi j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  let lab : Lab E Z (N.ordP V.l) :=
    { tau := fun o => tauIn N pl V.l o.1
      n := N.R.k - 1
      j := j
      j' := N.R.m - j
      big := fun _ g s => g = RF.bg s }
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => (hfr o.1 0).2 s
      frob := fun o g => (hfr o.1 g).1
      sep := fun x x' hx => (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr _ _ (hfr o.1 g).1 }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · show 1 - g = RF.bg s ↔ ¬ g = RF.bg s
      generalize RF.bg s = b
      revert g b
      decide
    · have hg' : g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.k - 1 + j
      unfold tauIn Datum.mult
      rw [if_pos hg']
      refine (if_pos (hpsi _)).trans ?_
      rw [hp]
      show N.R.k + j - 1 = _
      omega
    · have hg' : ¬ g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.m - j
      unfold tauIn Datum.mult
      rw [if_neg hg']
      exact (if_neg (not_inPsi_conjugate H _ (hpsi _))).trans hq
  have hsup := GlobalTheory.T.rowData_supplied_at_pairs_of_places hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z (N.ordP V.l) lab harith
    hbij.2 hrank (show N.R.m - j < N.R.k - 1 by omega) (fun _ => Or.inl ⟨heven, fun s => zero_eq_bg_iff s⟩) a hdom nW ν hν'
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hvb⟩ := GlobalTheory.RowAt.supply_extend C V (N.ordP V.l) (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g s => g = RF.bg s) (fun z g s => Dw.mult (tauIn N pl V.l z g s))
    (fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)) nW ν hZne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom (N.ordP V.l) (N.pos V.l) Z RF.bg (tauIn N pl V.l) hZ hbij
    (fun z s => if_pos rfl)
  refine ⟨{ R := { C := C, V := V, hVl := rfl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F
                   hn := fun z => ⟨(hn z).1, (hn z).2.trans (by show j + (N.R.m - j) = N.R.m; omega)⟩ }
            Z := Z
            hZ := hZ
            alt := fun z hz => ⟨heven, fun s => ((hbig z hz 0 s).1).trans (zero_eq_bg_iff s)⟩
            ga := fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)
            W := gapW N pl a
            nW := nW
            T := TT
            θ0 := θ0
            rest := restOf N Dw pl a
            ν := ν
            wt := ⟨fun z hz g s k' hk => ?_, hwt.main, hwt.rest_eq⟩
            what₂ := hrows
            deg := hdeg
            val := hvb }, rfl, rfl⟩
  have h := hwt.supp z hz g s k' hk
  exact ⟨h.1, h.2.trans_eq (hbig z hz g s).2.symm⟩

end GlobalTheory.InertPackage
