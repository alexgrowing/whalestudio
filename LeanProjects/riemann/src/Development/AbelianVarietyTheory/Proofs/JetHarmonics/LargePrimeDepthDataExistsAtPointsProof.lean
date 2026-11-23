import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CmHostIdempotentTraceEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupplyExtend
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConjStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlaceStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramifiedStatement

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LargePkg

theorem not_inPsi_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h] at h'
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h'
  have e := H.sqrt_neg_disc_sq
  rw [hr] at e
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem pkg_of_supply (P : RF.Par) (l : ℕ) {C : Type} [Field C] (V : VF C) (hV : V.l = l) (Z : Finset P.Pl)
    (hZ : RF.IsReps P Z) (hw : ∀ z, 0 ≤ P.w z) (big : P.Pl → Fin 2 → ZMod P.d → Prop)
    (rk : P.Pl → Fin 2 → ZMod P.d → ℕ) (b : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ) (K s nW : ℕ) (ν : ℝ)
    (hK : ∀ z g a, rk z g a ≤ K) (hb : ∀ z g a i j, i ≤ j → j < rk z g a → b z g a j ≤ b z g a i)
    (h0 : ∀ z g a, 0 < rk z g a → b z g a 0 ≤ s * (l - 1)) (hrows : 2 * K * s * Z.card ≤ nW)
    (hS : Supply V P.d P.Pl Z (P.k - 1) P.m big rk (fun z g a => gap (rk z g a) (b z g a)) nW ν) :
    ∃ Pk : RF.PkgZero P l, Pk.ν = ν := by
  obtain ⟨I, J, fI, fJ, X, F, hn, hrk, hval⟩ := hS
  refine ⟨{ R := { C := C, V := V, hVl := hV, I := I, J := J, X := X, F := F, hn := hn }
            Z := Z, hZ := hZ, ga := fun z g a => gap (rk z g a) (b z g a), K := K, s := s, nW := nW, T := 1, ν := ν
            T_one := le_rfl, w_nonneg := hw, supp := ?_, first := ?_, what₂ := hrows, val := hval }, rfl⟩
  · intro z hz g a k hk
    obtain ⟨h1, h2⟩ := (GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)).1 k hk
    exact ⟨h1, h2.trans_eq (hrk z hz g a).2.symm, h2.trans (hK z g a)⟩
  · intro z _ g a
    obtain ⟨h1, h2⟩ := GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)
    rcases Nat.eq_zero_or_pos (rk z g a) with h | h
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) (Nat.zero_le _)
      by_contra hk
      have := h1 k hk
      omega
    · exact le_of_eq_of_le ((h2 K (hK z g a)).1 0 h) (h0 z g a h)

theorem pkg_of_labels (hU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {lv : Level H}
    {Xo : Moduli Dw lv} {c : Coeff lv} [StarRing (𝓞 E)] (hstar : ∀ x : 𝓞 E, star x = H.bar x)
    (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ N.R.m)
    (hpsi : ∀ z, InPsi H (pl z)) (hp : Dw.p = (N.R.sigW j).1) (hq : Dw.q = (N.R.sigW j).2) (ha : DomW Dw a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (hy : y.IsAlg) (C3 : IntChart T io y)
    {C : Type} [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C) (hι : EmbOK T V ι) {k : ℕ}
    (Y : FBChart C V (𝓞 E) (chD C3.ch)) (hY : IsBC C3 ι k Y) (hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E)
    (nW : ℕ) (ν : ℝ) (hν : (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW)
    (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (sel : ZMod d → Fin 2)
    (hsel : (Even d ∧ ∀ s : ZMod d, (0 = sel s ↔ Even s.val)) ∨ ∀ s, 0 = sel s)
    (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ))
    (htau : ∀ z g s, tau z g s = if g = sel s then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val)))
    (Z : Finset (RPl N.R)) (hZ : RF.IsReps (parAt N j d pos) Z) (hne : Z.Nonempty)
    (hbij : Function.Bijective fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2)
    (hfrob : ∀ z g, FrobOrd V io ι (tau z g)) (hw : ∀ z, 0 ≤ N.w j z) (s : ℕ)
    (hs : ∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (V.l - 1)) (hrows : 2 * N.R.r * s * N.R.f ≤ nW) :
    ∃ Pk : RF.PkgZero (parAt N j d pos) V.l, Pk.ν = ν := by
  have hk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d := ⟨fun o => tau o.1, N.R.k - 1, j, N.R.m - j, fun _ g s => g = sel s⟩
  have hconj : ∀ z s, tau z 1 s = ComplexEmbedding.conjugate (tau z 0 s) := by
    intro z s
    rw [htau, htau]
    generalize sel s = g
    fin_cases g
    · simp
    · have : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
        ext x; simp
      simp [this]
  have hA : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => hconj o.1 s
      frob := fun o g s x => hfrob o.1 g s x
      sep := fun x x' hx => (GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι hunr d (tau o.1 g) (hfrob o.1 g) }
  have hR : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s h => ?_, fun g s h => ?_⟩
    · change 1 - g = sel s ↔ ¬ g = sel s
      generalize sel s = g'
      revert g g'
      decide
    · change Dw.mult (tau o.1 g s) = N.R.k - 1 + j
      rw [htau, if_pos (show g = sel s from h), Datum.mult]
      exact (if_pos (hpsi _)).trans (by omega)
    · change Dw.mult (tau o.1 g s) = N.R.m - j
      rw [htau, if_neg (show ¬ g = sel s from h), Datum.mult]
      exact (if_neg (not_inPsi_conj H (hpsi _))).trans hq'
  have h1 := GlobalTheory.T.rowData_supplied_at_pairs_of_places hU E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hunr Z d lab hA hbij.2 hR
    (show N.R.m - j < N.R.k - 1 by omega) (fun _ => hsel) a ha nW ν hν
  have hm : lab.j + lab.j' = N.R.m := show j + (N.R.m - j) = N.R.m by omega
  rw [hm] at h1
  have h2 := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) N.R.m (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) nW ν hne h1
  have hcard : Z.card ≤ N.R.f := by
    refine (Finset.card_le_univ Z).trans_eq ?_
    simp [Ranks.f_eq_ord, Formalism.HC.Frame.card_A]
  refine pkg_of_supply (parAt N j d pos) V.l V rfl Z hZ hw (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s i => a (tau z g s, i)) N.R.r s nW ν ?_ ?_ ?_ ?_ h2
  · intro z g s
    unfold Datum.mult Ranks.r
    split_ifs <;> omega
  · intro z g s i i' h h'
    exact ha (tau z g s) ⟨i, h.trans_lt h'⟩ ⟨i', h'⟩ h
  · intro z g s h
    exact hs _ h
  · exact (Nat.mul_le_mul_left _ hcard).trans hrows

theorem pkgZero : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hT hp hq ha la h2 hlq hld hM _ T io e hO y hy C3 nW ν hν
    hphi hw s hs hrows
  obtain ⟨C, _, _, V, ι, hV, hι, hac, hcpl, hla, hunit, hnu⟩ := GlobalTheory.T.exists_closedComplete_field_over_place E H Dw lv Xo c la T io e hO
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (hV ▸ ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hν' := hnu y C3 lv.M a nW ν hν
  rw [← hV] at h2 hlq hld hphi hs ⊢
  have hunr := hT.unr V.l V.l_prime h2 hlq hld
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  by_cases hin : Inert N V.l
  · obtain ⟨Z, hZ, hne, hev, hbij, hfr⟩ := GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj E H lv c N pl hT la T io C V ι hι hV hla hin hphi j
    refine ⟨N.ordP V.l, inferInstance, N.pos V.l, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' (N.ordP V.l) (N.pos V.l) RF.bg (Or.inl ⟨hev, fun s => ?_⟩) (tauIn N pl V.l) (fun _ _ _ => rfl)
      Z hZ hne hbij (fun z g => (hfr z g).1) hw s hs hrows⟩
    unfold RF.bg
    split_ifs with h <;> simp [h]
  · have hsp : N.cls V.l = PrimeClass.splitK := by
      unfold Inert NumDatum.cls primeClass at *
      rw [if_neg h2, if_neg hlq, if_neg hld] at hin ⊢
      split_ifs at hin ⊢ <;> simp_all
    obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hT la T io C V ι hι hV hla hsp j
    exact ⟨d, inferInstance, pos, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' d pos (fun _ => 0) (Or.inr fun _ => rfl) (tauSp N pl pos) (fun _ _ _ => rfl)
      Z hZ hne hbij hfr hw s hs hrows⟩

end GlobalTheory.LargePkg
