import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfEqSumHeis
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeriesTw
open GlobalTheory.AdTh.MovedDatum GlobalTheory.AdTh.ShortSeries

theorem smul_eq_of_hatC_ne_zero_of (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (Ω : GlobalTheory.OnCmp.DatFn D i) (hΩ : GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω) (l₂ : Geo.Tor.Level H)
    (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ) (hφ : GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ)
    (q : Fin (Vc D i).rank → LevQ Dw l₂) (hq : hatC l₂ φ q ≠ 0) (s : 𝓞 D.host.E)
    (hs : ∀ PP ∈ R.Pg ∪ Q, s ∈ PP.asIdeal) (b : Fin (Vc D i).rank) :
    ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := GlobalTheory.HatInt.dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      have e3 : ∀ PP ∈ R.Pg ∪ Q,
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add, map_smul]
          rfl
        rw [e4, GlobalTheory.HatInt.uMat_add_smul, GlobalTheory.HatInt.sig_bar]
        exact GlobalTheory.HatInt.redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [hΩ _ _ e3, ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add, LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

theorem isPair_tw (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i)
    (χ : (AE D)ˣ →* Circle) (ω : GlobalTheory.OnTies.WeilRep D i) (hω : GlobalTheory.OnCmp.IsWeilTw R i χ ω)
    (ξ : Formalism.L2.Host.HChar D.host.E) (hchr : ChrEq χ ξ) (hfin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (hram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP)
    (e : AE D) (he : IsIdemSum e (R.Pg ∪ Q)) :
    IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
  have hL := hC.lev
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := hω
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  have hexp : ∀ τ, ∃ a : ℤ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 τ a := fun τ => by
    have h1 : HasInfExp D (R.mu0 ((i : ℕ) + 1)) τ (-(D.hc τ).e i) := by
      obtain ⟨n, hn, hi⟩ := (R.C.isMu0 i).inf
      refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => -(D.hc τ).e i) (hL.mu0 i)
        ⟨fun τ => n (D.eTau τ), fun τ => ?_, fun k => ?_⟩ τ
      · simp only [hn, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]
      · rw [hi k]
        exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
          ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm
    have h2 : HasInfExp D χ τ 0 := by
      obtain ⟨n, hn, ho⟩ := hfin
      have := D.host.isCMField_hostE
      refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) hchr ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
      simp
    obtain ⟨z, hz⟩ := (D.hc τ).e_int i
    refine ⟨-z, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h2
    rw [hz, add_zero, ← Int.cast_neg] at h3
    exact h3
  refine ⟨hW, hC.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, hexp, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩
  · obtain ⟨a, ha⟩ := hexp τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨⟨es, hes, -⟩, -⟩ := he
    have hne : ∀ PP ∈ R.Pg ∪ Q, PP.under (𝓞 D.host.F) ≠ v := fun PP hPP =>
      GlobalTheory.AdTh.RecPair.under_ne (hes PP hPP) hv
    have kx : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → ξ.UnrAt P := fun P hP => by
      by_contra hc
      rcases (hram P).1 hc with h' | ⟨PP', h', hc'⟩
      · exact hne P (Finset.mem_union_right _ h') hP
      · exact hne PP' (Finset.mem_union_right _ h') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hP)
    have km : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (R.C.mu0 i).UnrAt P := fun P hP => by
      refine (R.C.isMu0 i).unr P fun k hk => ?_
      rcases GlobalTheory.LevelPlaces.div_or_div_conj R.C.P k P hk with h | h
      · exact hne P (Finset.mem_union_left _ ((hL.Pg P).2 ⟨k, h⟩)) hP
      · exact hne _ (Finset.mem_union_left _ ((hL.Pg _).2 ⟨k, h⟩))
          ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.LevelPlaces.isConjPl_conjSpec P)).symm.trans hP)
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 km
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hchr v ε hv.1 kx
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (Lift.tup R.mu0 χ ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * χ x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show Lift.tup R.mu0 χ ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]

example {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ}
    (h : GlobalTheory.OnCmp.KerDat R i ξ χ ξR Q ω φ) :
    (∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP) := h.ram

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem moved_datum_tw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (ξ : Formalism.L2.Host.HChar D.host.E), ChrEq χ ξ → (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) → (∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP) → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → ω (h, k) φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (ω (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourierOnCmp.vecOf_eq_sum_heis D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  have hp := isPair_tw D G Pl0 T0 A Ks R F hR i hV χ ω hω ξ hchr hfin Q hram e he
  obtain ⟨-, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 hV
  obtain ⟨hψ, hvac⟩ := hvec.1
  rw [hδ χ Q Ω ω φv hω hQ hΩ hvec l φ hφ hP e he, map_smul]
  by_cases hfin' : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin'
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := GlobalTheory.AdTh.MovedDatum.step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨t, ht⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd
      rw [ht, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => smul_eq_of_hatC_ne_zero_of D G Pl0 T0 A Ks R i H Dw ι Q Ω hΩ l φ hφ q hq s hs)
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (ω (h, k) (R.vacP i)) =
      ω (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (ω (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

set_option maxHeartbeats 1000000 in

theorem thetaKO_eq_short_series_tw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (ξ : Formalism.L2.Host.HChar D.host.E), ChrEq χ ξ → (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) → (∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP) → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (ω (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (ω) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (φv) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i hstd H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := moved_datum_tw D G Pl0 T0 A Ks R F hC i hstd H Dw ι hι hiso
  refine ⟨δ, ?_⟩
  intro χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l₂ φ hφ hl hrt g q0 X hq bas idx x₀ vr hM hS hx hinv hbas hvr bad N h k Λ mk e
    Ps y hbad he hPs hh hsupp hdet hΛ htriv hlev hmk Y hY v a hv hR P d hd
  obtain ⟨e₀, he₀, -⟩ := hvec.2
  have hP := isPair_tw D G Pl0 T0 A Ks R F hC i hstd χ ω hω ξ hchr hfin Q hram e₀ he₀
  obtain ⟨-, -, hV0, hW0, hVs, hWs, hVstd⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hC i A.μ0 hstd
  have hψ := hP.weil.std
  have hvac : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) :=
    hvec.1
  choose p hp using fun q => exists_finOf (Vc D i) (Wc D i) (rank_Wc i) ((δ : ℤ) • Y q)
  have hdat := hδ χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l₂ φ hφ hl bad N h k Λ mk hbad ⟨hh, e, Ps, he, hPs, hsupp⟩ hΛ
    htriv hlev hmk Y (fun q => (p q).1) (fun q => (p q).2) hY hp
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin (Vc D i).rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin (Vc D i) 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ k) * cart (R.MW i (sg0 D A)) τ * compAt R.θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat (Wc D i) (fin (Wc D i) k), w = a • v} →
      latR (rank_Wc i) (latG (Wc D i) k) = latR (rank_Wc i) L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := GlobalTheory.T.weilRepresentation_split_support_projects_vacuum D _ _ _ _ _ _ _ hP _ g (rank_Wc i) X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move (rank_Wc i) X hinv k) _ hvac' _ hR e Ps h y he hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl (hatC l₂ φ) (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hthP : IsThetaFunO R.ψ (Vc D i) (Wc D i) φv := by
    have h1 := hP.weil.om_pres (h, k)⁻¹ _ (hdat ▸ GlobalTheory.OrientedHeis.theta_smul _ hth :
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (ω (h, k) φv))
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hrd := (reads_linear_injective D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (hatC l₂ φ _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP (rank_Wc i) X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ (hatC l₂ φ) Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rcases Int.units_eq_one_or δ with rfl | rfl
  · simp only [Units.val_one, one_smul]
    rw [hpar]
    push_cast
    ring
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg, Int.cast_neg, Int.cast_one, ← mul_pow]
    rw [neg_mul_neg, one_mul, one_mul]
    ring

end GlobalTheory.AdTh.ShortSeriesTw
