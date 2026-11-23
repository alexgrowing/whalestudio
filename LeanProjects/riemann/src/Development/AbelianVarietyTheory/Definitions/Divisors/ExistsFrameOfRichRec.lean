import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullRunHoldsOfCore
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotIsUnitNatCastPrimeRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRichRecordOverChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn.CoreWit

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.JoinChr in

theorem exists_val_of_chrEq {c : (Formalism.L2.Theta.AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (x : (Formalism.L2.Theta.AE D)ˣ) : ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  have hχ := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.2 c χ h
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · refine (hcoe _).trans ?_
      have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
        (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
      exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
    · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
      change Θ (x : Formalism.L2.Theta.AE D) = _
      rw [hx, hloc P e he]
  exact ⟨u x, by rw [(GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 c c' χ h h', hcoe]⟩

theorem level_of_is {T : Core D} (hT : LawsM T) {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) (hO : T.pb = Lc.C.P.pb) :
    T.Q.l.Mb = ∏ PP ∈ Lc.Pg, PP.asIdeal := by
  have hprod := T.Q.l.prod
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
  · rw [hT.pins.2.1.1] at hprod
    exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
  · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
    rfl

theorem exists_half_of_is {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ P.asIdeal ∧ ∀ t, ∀ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal →
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  obtain ⟨P, hP⟩ := hL.Q_de p hp
  by_cases h : ∃ t, ∃ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨t, PP, h1, h2⟩ := h
    refine ⟨P, ?_, fun t PP h1 h2 => ?_⟩
    · rw [← hP t PP h1 h2]
      change algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (p : 𝓞 D.host.K) ∈ PP.asIdeal
      rwa [map_natCast]
    · rw [← hP t PP h1 h2]
      exact Ideal.map_comap_le
  · have hpp : p.Prime := by
      rcases hp with rfl | rfl
      exacts [D.host.pde_prime, D.host.pde'_prime]
    obtain ⟨P', hP'⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hpp
    exact ⟨P', hP', fun t PP h1 h2 => absurd ⟨t, PP, h1, h2⟩ h⟩

theorem ownAt_special (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v = D.host.pde ∨ ownAt D v = D.host.pde' := by
  unfold ownAt
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem oneHalf_of_is {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v,
      ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧ ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
        (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  classical
  choose P h1 h2 using fun (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde') => exists_half_of_is hL hp
  refine ⟨fun p => if hp : p = D.host.pde ∨ p = D.host.pde' then P p hp else R.C.P.pb 0, fun v => ?_⟩
  simp only [dif_pos (ownAt_special v)]
  refine ⟨h1 _ _, fun PP hPP => ?_⟩
  have h3 := Finset.mem_filter.1 hPP
  exact h2 _ _ _ PP h3.1 h3.2

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (v₁ : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (v₂ : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v, v₁, v₂⟩

theorem exists_frame_of_richRec (D : D7) (EX : ErrX D) (h : RichRec D) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') : ∃ C : Formalism.L2.Host.CharFrame D,
      (∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
      (∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D) ∧ (∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) ∧
      ∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
        (∃ PP ∈ Lc.Q (some false), ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
        ∃ PP ∈ Lc.Q (some true), ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  choose pb g1 g2 using exists_prime_bar_piG D EX
  obtain ⟨C, hC⟩ := exists_charFrame D ⟨pb, g1⟩ h.1 h.2.1 h.2.2.1
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde_prime
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde'_prime
  obtain ⟨Lc, a1, a2, a3, a4, a5, a6⟩ := exists_levCh_twisted C h.1 h.2.1 h₁.split h₂.split P₁ P₂ hP₁ hP₂
  obtain ⟨w₁, hw₁⟩ := aboveK_nonempty P₁
  obtain ⟨w₂, hw₂⟩ := aboveK_nonempty P₂
  exact ⟨C, by rw [hC]; exact g2, isDelta_mem C.isDel h.2.2.2, isDelta_mem C.isDel' h.2.2.2, Lc, a1, a2, a3, a4,
    ⟨w₁, a5 ▸ hw₁, overP_of_under hP₁ (mem_aboveK.1 hw₁)⟩, w₂, a6 ▸ hw₂, overP_of_under hP₂ (mem_aboveK.1 hw₂)⟩

theorem exists_runsHold : ∃ CK x₁ : ℝ, ∀ (D : D7) (G : Type) (J : CoreJ D) (r : TwoRuns J G) (EX : ErrX D) (L : SizeData₂ D)
    (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D),
    (∀ v j, InR D j → ParOK (r.used v).full.toTop EX (ownAt D v) j) → PageNum Tp x₁ → FieldSmall D L →
      RunsHold Tp hK EX CK r := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  refine ⟨CK, max ((10 : ℝ) ^ 60) (x₀ 20 CK), ?_⟩
  rintro D G J r EX L Pm Tp hK hpar ⟨S, hCnW, hg, hC, hCZ, hx⟩ hF v h hinj j hj
  have hP := hCK D L Pm Tp hK S hCnW hg ((le_max_left _ _).trans hx) hC hCZ _ _ j (recPJ h j hj) hj
    ((GlobalTheory.FinalJoin2.fieldSmall_iff_opo D _ h L).1 hF)
  exact (hrun D _ h hinj EX _ (hpar v) j hj L _ _ _ _ _ _ _ _ _ _ _ hP ((le_max_right _ _).trans hx)).2

theorem exists_all : ∃ CK x₁ : ℝ, ∀ (D : D7), RecOK D x₁ → RichRec D → ∀ (G : Type) [Group G] [Fintype G],
    ∃ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D)
      (J : CoreJ D) (r : TwoRuns J G), LawsJ J ∧ J.pb = C.P.pb ∧ (∀ v, LawsFull (r.used v).full) ∧
      OwnPin r ∧ PageNum Tp x₁ ∧ RunsHold Tp hK EX CK r ∧
      (∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
        (∃ PP ∈ Lc.Q (some false), ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
        ∃ PP ∈ Lc.Q (some true), ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
      (∃ a : Algebra J.Q.c.F D.what₂.LL, @AlgTie D J a) ∧
      ∀ (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0),
        R.C = C → R.toLevCh.Is μ0 → ∀ (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T0) (S : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))),
          CoreTies L EX J R ∧ CoreTies L EX J { R with mu := mu, twPl := S } := by
  obtain ⟨CK, x₁, H⟩ := exists_runsHold
  refine ⟨CK, x₁, fun D hD hR G _ _ => ?_⟩
  obtain ⟨x₀, hext⟩ := GlobalTheory.FinalJoin2.exists_full_runHolds_of_core
  obtain ⟨EX⟩ := hD.err
  obtain ⟨C, c1, c2, c3, c4⟩ := exists_frame_of_richRec D EX hR hD.one hD.two
  obtain ⟨J, hJ, hC, hcan, hJpb, hrk, -⟩ :=
    exists_coreJ_of_chiOK_noVol D hD.one.full hD.one.zetaM C.P.pb C.P.pb_over _ (chiOK_one D)
  have hE : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hJpb]
    exact c1 i
  obtain ⟨T, -, -, hT⟩ := hext D J EX hJ hC hcan hrk hE hD.one.kpsi
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde_prime
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K D.host.pde'_prime
  obtain ⟨xi₁, hxi₁⟩ := hD.xi1
  obtain ⟨xi₂, hxi₂⟩ := hD.xi2
  obtain ⟨_, T₁, h₁, -, hJ₁, -, -, -, hpar₁, -⟩ := hT _ hD.one P₁ hP₁ xi₁ hxi₁
  obtain ⟨_, T₂, h₂, -, hJ₂, -, -, -, hpar₂, -⟩ := hT _ hD.two P₂ hP₂ xi₂ hxi₂
  subst hJ₁
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : RunData T₁.J, r₂.full = T₂ := by
    rw [← hJ₂]; exact ⟨RunData.of T₂, rfl⟩
  obtain ⟨L, Pm, Tp, hK, S, hCnW, hg, hCP, hCZ, hx, hF⟩ := hD.num
  let r : TwoRuns T₁.J G := ⟨RunData.of T₁, r₂, fun _ _ => 1⟩
  have hpar : ∀ v j, InR D j → ParOK (r.used v).full.toTop EX (ownAt D v) j := by
    intro v j hj
    unfold TwoRuns.used ownAt
    split_ifs
    · show ParOK r₂.full.toTop EX _ j
      rw [hr₂]; exact hpar₂ j hj
    · exact hpar₁ j hj
  have hnum : PageNum Tp x₁ := ⟨S, hCnW, hg, hCP, hCZ, hx⟩
  refine ⟨L, Pm, Tp, hK, EX, C, T₁.J, r, hJ, hJpb, fun v => ?_, fun v j n hj => (hpar v j hj).own n, hnum,
    H D G _ r EX L Pm Tp hK hpar hnum hF, c4, ⟨_, algTie_algTop _ hJ.pins.2.2.1⟩, ?_⟩
  · unfold TwoRuns.used
    split_ifs
    · show LawsFull r₂.full
      rw [hr₂]; exact h₂
    · exact h₁
  · rintro Pl0 T0 A _ R μ0 rfl hL mu S
    exact ⟨coreTies_of_is hL hJpb hC hcan hrk hE hD.one hD.two hF c2 c3,
      coreTies_of_is (R := { R with mu := mu, twPl := S }) hL hJpb hC hcan hrk hE hD.one hD.two hF c2 c3⟩

end GlobalTheory.BigOn.CoreWit

end
