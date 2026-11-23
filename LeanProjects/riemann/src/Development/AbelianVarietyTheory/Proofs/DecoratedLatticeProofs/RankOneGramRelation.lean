import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterUnramifiedAwayLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGramStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem cu_mul {χ χ' : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x)
    (h' : CharUnramAt D χ' x) : CharUnramAt D (χ * χ') x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h y h1 h2 h3 h4, h' y h1 h2 h3 h4, one_mul]

theorem cu_inv {χ : (AE D)ˣ →* Circle} {x : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ x) :
    CharUnramAt D χ⁻¹ x := fun y h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h y h1 h2 h3 h4, inv_one]

theorem eta_unr : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ x : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (pk W).eta x := by
  intro D L hT Gi Gl Kc Yd cX ex W hP x
  have hC := hP.bot.hyp.2.2.2.1
  exact fun y h1 _ h3 h4 => GlobalTheory.Mem.TupChar.unramEverywhere hC.lev.eta ((pk W).C.isEta.unr) y h1 h3 h4

theorem mem_under (PP : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem not_both (PP : HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

end GlobalTheory.FamChars

namespace GlobalTheory.FamChars

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

theorem weil_rec {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

theorem family_chars : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → f.ColOK → VTie f v → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t (w : VTup (f.t t)), (∀ p, p ∈ w.Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 D.host.F)) → WeilOK (t := f.t t) v ∧ (f.t t).UnrOn (offP v w) ∧ (f.t t).UnrOn (· ∈ v.tP) ∧ (f.t t).UnrK (· ∈ v.tP) ∧ Disjoint w.Q v.gP ∧ Disjoint w.Q v.tP ∧ ∀ (n : ℕ) (G : Fin n → GLoc v) pl, GRead f G pl → ∀ i, (G i).Chars (f.t t) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hV hτ t w hQ
  have hC3 := hP.bot.hyp.2.2.2.1
  have hL := hC3.lev
  have eU : ∀ x, CharUnramAt D (pk W).eta x := eta_unr W hP
  have gIn : ∀ PP ∈ (pk W).Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    refine ⟨k, ?_⟩
    have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
      have hk' : PP.under (𝓞 D.host.K) = (pk W).C.P.pb k := hk
      rw [hk']
      exact (pk W).C.P.pb_over k
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2

  have tG : ∀ x ∈ v.tP, ∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ x := by
    intro x hx PP hPP e
    obtain ⟨k, hk⟩ := gIn PP hPP
    have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := (mem_under PP _).1 (e ▸ (hV.tP x).1 hx)
    exact not_both PP ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime k)).2 (D.T_ne_g u k)) hT hk
  have tQ : ∀ x ∈ v.tP, ∀ PP ∈ (pk W).Q t, PP.under (𝓞 D.host.F) ≠ x := by
    intro x hx PP hPP e
    exact (hL.Q_off t PP hPP).2 u ((mem_under PP _).1 (e ▸ (hV.tP x).1 hx))
  have muU := fun n x h1 h2 hg hq => GlobalTheory.T.character_unramified_away_level W hP t n x h1 h2 hg hq

  have unr : ∀ P : HeightOneSpectrum (𝓞 D.host.F) → Prop,
      (∀ x, P x → ∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ x) →
      (∀ x, P x → ∀ PP ∈ (pk W).Q t, PP.under (𝓞 D.host.F) ≠ x) → (f.t t).UnrOn P := by
    intro P hg hq
    refine ⟨fun j ρ h x hx => ?_, fun j σ h x hx => ?_, fun j h => ?_⟩
    · obtain ⟨-, -, e1, e2⟩ := (hR.row t).sBF j ρ h
      have m1 := muU (j + 1) x (by omega) (by omega) (hg x hx) (hq x hx)
      show CharUnramAt D ((f.row t).sBF j ρ h).χV x ∧ CharUnramAt D ((f.row t).sBF j ρ h).χW x
      rw [e1, e2]
      exact ⟨cu_mul m1 (cu_inv (eU x)), m1⟩
    · obtain ⟨-, -, e1, e2⟩ := (hR.row t).sFB j σ h
      have m1 := muU (j + 1 + 1) x (by omega) (by omega) (hg x hx) (hq x hx)
      show CharUnramAt D ((f.row t).sFB j σ h).χV x ∧ CharUnramAt D ((f.row t).sFB j σ h).χW x
      rw [e1, e2]
      exact ⟨m1, cu_mul m1 (cu_inv (eU x))⟩
    · refine ⟨(Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).1, (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).2,
        weil_rec ((pk W).ωX t) (hC3.chain.ωX t) (j + 1) (idx_top h), fun x hx => ?_⟩
      have m1 := muU D.R.m x (by omega) le_rfl (hg x hx) (hq x hx)
      unfold Lift.chrStep
      split_ifs
      · exact ⟨cu_mul m1 (cu_inv (eU x)), m1⟩
      · exact ⟨m1, cu_mul m1 (cu_inv (eU x))⟩
  refine ⟨GlobalTheory.T.weil_datum_of_rank_one_gram W u hP f v hR hC hτ t, ?_, ?_, ?_, ?_, ?_, fun n G pl hG i => GlobalTheory.T.local_groups_characters_family W u hP f v hR hV t n G pl hG i⟩
  · exact unr _ (fun x hx PP hPP e => hx.1 ((hV.gP x).2 ⟨PP, hPP, e.symm⟩))
      (fun x hx PP hPP e => hx.2 ((hQ x).2 ⟨PP, hPP, e.symm⟩))
  · exact unr _ tG tQ
  · intro j hj
    have hx : ∀ x ∈ v.tP, CharUnramAt D ((pk W).toLevCh.mu t (j + 1)) x := fun x hx =>
      muU (j + 1) x (by omega) (by omega) (tG x hx) (tQ x hx)
    exact ⟨_, _, hC.kom t j hj, fun x h => ⟨hx x h, hx x h⟩⟩
  · rw [Finset.disjoint_left]
    intro x hx hxg
    obtain ⟨PP, hPP, rfl⟩ := (hQ x).1 hx
    obtain ⟨PP', hPP', e⟩ := (hV.gP _).1 hxg
    obtain ⟨k, hk⟩ := gIn PP' hPP'
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := (mem_under PP _).1 (e ▸ (mem_under PP' _).2 hk)
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hPP
    haveI : PP.asIdeal.IsPrime := PP.isPrime
    haveI : Finite (Formalism.L2.DIV.kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    haveI : Fintype (Formalism.L2.DIV.kP PP) := Fintype.ofFinite _
    have hq0 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have h0q : ((q : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP PP)
      exact (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).1 (by simpa using h0q)
    exact not_both PP ((Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)) hq0 hg
  · rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨PP, hPP, rfl⟩ := (hQ x).1 hx
    exact tQ _ hxT PP hPP rfl

end GlobalTheory.FamChars
