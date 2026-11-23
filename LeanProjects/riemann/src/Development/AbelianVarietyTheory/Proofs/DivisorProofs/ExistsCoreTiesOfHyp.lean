import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotIsUnitNatCastPrimeRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRichRecordOverChoices

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

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

theorem level_and_oneHalf (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0) (hL : R.toLevCh.Is μ0)
    (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) :
    J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
        ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
          (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal :=
  ⟨level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v⟩

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (hd : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (hd' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, (level_and_oneHalf J R μ0 hL hO hc).1, (level_and_oneHalf J R μ0 hL hO hc).2, hd, hd'⟩

def IsParametersCompatibleWithCharFrame (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ [Algebra J.Q.c.F D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (R : RealDat D A J.Q.c.F) (μ0 : T0), R.C = C → R.toLevCh.Is μ0 → CoreTies L EX J R ∧
      ∀ (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T0) (S : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))),
        CoreTies L EX J { R with mu := mu, twPl := S }

theorem exists_core_coreTies (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D)
    (h₁ : FieldOK0 D D.host.pde) (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L)
    (hE : ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)))
    (hd : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D) (hd' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D)
    (chi₀ : ℕ → (Formalism.L2.Theta.AE D)ˣ →* Circle) (hchi : ChiOK D chi₀) :
    ∃ J : CoreJ D, LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) ∧ HalfEX J.toCore EX ∧
      J.pb = C.P.pb ∧ (∀ j, J.chiW j J.σ₀ = chi₀ j) ∧ (∃ a : Algebra J.Q.c.F D.what₂.LL, @AlgTie D J a) ∧ IsParametersCompatibleWithCharFrame L EX J C := by
  obtain ⟨J, hJ, hc, hcan, hpb, hr, hχ⟩ := exists_coreJ_of_chiOK_noVol D h₁.full h₁.zetaM C.P.pb C.P.pb_over chi₀ hchi
  have hH : HalfEX J.toCore EX := fun i => by
    show barE D (EX.piG i) ∈ (J.pb i).asIdeal.map _
    rw [hpb]
    exact hE i
  refine ⟨J, hJ, hc, hcan, hr, hH, hpb, hχ, ⟨_, algTie_algTop J hJ.pins.2.2.1⟩, ?_⟩
  rintro _ G _ _ Pl0 T0 A R μ0 rfl hL
  exact ⟨coreTies_of_is hL hpb hc hcan hr hH h₁ h₂ hs hd hd', fun mu S =>
    coreTies_of_is (R := { R with mu := mu, twPl := S }) hL hpb hc hcan hr hH h₁ h₂ hs hd hd'⟩

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

theorem exists_coreTies_of_zeroFreeRegion : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount →
    Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → GlobalTheory.NT.RayField →
    ∀ x : ℝ, ∃ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D)
      (J : CoreJ D), RecOK D x ∧ DV.KapDef D ∧ PageNum Tp x ∧ FieldSmall D L ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D ∧
      (∀ y, ((C.del.1 y : ℂˣ) : ℂ) ∈ FO D) ∧ (∀ y, ((C.del'.1 y : ℂˣ) : ℂ) ∈ FO D) ∧
      (∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
        (∃ PP ∈ Lc.Q (some false), ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
        ∃ PP ∈ Lc.Q (some true), ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
      LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ HalfEX J.toCore EX ∧ J.pb = C.P.pb ∧
      (∃ a : Algebra J.Q.c.F D.what₂.LL, @AlgTie D J a) ∧ IsParametersCompatibleWithCharFrame L EX J C := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 x
  obtain ⟨D, hD, hR⟩ := exists_richRec_of_zeroFreeRegion p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 x
  obtain ⟨EX⟩ := hD.err
  obtain ⟨L, Pm, Tp, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hD.num
  obtain ⟨C, c1, c2, c3, c4⟩ := exists_frame_of_richRec D EX hR hD.one hD.two
  obtain ⟨J, j1, j2, j3, -, j5, j6, -, j8, j9⟩ := exists_core_coreTies D L EX C hD.one hD.two n8 c1 c2 c3 _ (chiOK_one D)
  exact ⟨D, L, Pm, Tp, EX, C, J, hD, n1, ⟨n2, n3, n4, n5, n6, n7⟩, n8, hR.2.2.2, c2, c3, c4, j1, j2, j3, j5, j6, j8, j9⟩

end GlobalTheory.BigOn

end
