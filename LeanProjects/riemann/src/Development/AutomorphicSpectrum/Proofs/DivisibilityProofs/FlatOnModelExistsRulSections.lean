import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLineIdempotentSectionsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLineIdempotentSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CvRule

open GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_cspB_rule {C : Set (Xo.XF c)} (hC : IsClopen C) (e : Formalism.L2.Pj.Rul Xo c)
    (he : ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F),
      (¬ Set.range (fpt z ψ) ⊆ C → ψ (e p z) = 0) ∧ (Set.range (fpt z ψ) ⊆ C → ψ (e p z) = 1)) :
    e = Formalism.L2.Pj.CompSplitPfB.cspB_rule Xo c C hC := by
  funext p z
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine sub_eq_zero.1 (eq_zero_of_fields _ fun F _ ψ => ?_)
  have hsp := Formalism.L2.Pj.CompSplitPfB.cspB_idem_spec C hC z.x z.x_over (kerPt ψ)
  have hid := Formalism.L2.Pj.CompSplitPfB.cspB_idem_idem C hC z.x z.x_over
  have hl : Formalism.L2.Pj.CompSplitPfB.cspB_lift z.x z.x_over = frPtF z := rfl
  rw [hl, ← range_fpt_subset_iff] at hsp
  have hi : Formalism.L2.Pj.CompSplitPfB.cspB_rule Xo c C hC p z =
      Formalism.L2.Pj.CompSplitPfB.cspB_idem C hC z.x z.x_over := rfl
  rw [hi, map_sub]
  set i := Formalism.L2.Pj.CompSplitPfB.cspB_idem C hC z.x z.x_over
  have hker : i ∉ (kerPt ψ).asIdeal ↔ ψ i ≠ 0 := Iff.rfl
  rw [hker] at hsp
  have h01 : ψ i = 0 ∨ ψ i = 1 := IsIdempotentElem.iff_eq_zero_or_one.1 (hid.map ψ)
  by_cases hr : Set.range (fpt z ψ) ⊆ C
  · rw [(he p z F ψ).2 hr]
    rcases h01 with h | h
    · exact absurd h (hsp.2 hr)
    · rw [h, sub_self]
  · rw [(he p z F ψ).1 hr]
    rcases h01 with h | h
    · rw [h, sub_self]
    · exact absurd (hsp.1 (by rw [h]; exact one_ne_zero)) hr

theorem exOf_add_detE (τ : GlobalTheory.AllWt.Psi H) (i : Formalism.L2.Pj.Ix D) :
    GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i + (detE D τ.1 i : ℤ) =
      (detE D (ComplexEmbedding.conjugate τ.1) i : ℤ) := by
  classical
  have f1 : ∀ (τ' : GlobalTheory.AllWt.Psi H) (j : Fin (D.p + D.q)), τ' = τ → GlobalTheory.FlatLine.flatWt D τ τ' j = -1 :=
    fun τ' j h => by simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, h]
  have f0 : ∀ (τ' : GlobalTheory.AllWt.Psi H) (j : Fin (D.p + D.q)), τ' ≠ τ → GlobalTheory.FlatLine.flatWt D τ τ' j = 0 :=
    fun τ' j h => by simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, h]
  rcases i with _ | ⟨σ, i⟩
  · have : GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 none = 0 := rfl
    simp [this, detE, Formalism.L2.Pj.ex]
  · have hne : τ.1 ≠ ComplexEmbedding.conjugate τ.1 := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ ((DFunLike.congr_fun h.symm _).trans τ.2)
    have hex : GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 (some ⟨σ, i⟩) =
        (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0).1 (σ, i) := rfl
    rw [hex]
    simp only [detE, Formalism.L2.Pj.ex]
    by_cases h : σ (H.rt : E) = H.rt0
    · have hm : D.mult σ = D.p := by rw [Datum.mult, if_pos h]
      have hi : (i : ℕ) < D.p := hm ▸ i.2
      have hw := GlobalTheory.AllWt.wtOf_big (GlobalTheory.FlatLine.flatWt D τ) 0 ⟨σ, h⟩ i hi
      simp only at hw
      rw [hw]
      have hc : σ ≠ ComplexEmbedding.conjugate τ.1 := fun e =>
        GlobalTheory.AllWt.conj_not_mem τ ((DFunLike.congr_fun e.symm _).trans h)
      by_cases e : σ = τ.1
      · rw [f1 _ _ (Subtype.ext e)]
        simp [e, hne]
      · rw [f0 _ _ fun h' => e (congrArg Subtype.val h')]
        simp [e, hc]
    · have h' := GlobalTheory.AllWt.conj_mem h
      have hm : D.mult σ = D.q := by rw [Datum.mult, if_neg h]
      have hi : (i : ℕ) < D.q := hm ▸ i.2
      have hw := GlobalTheory.AllWt.wtOf_small (GlobalTheory.FlatLine.flatWt D τ) 0 ⟨conjEmb σ, h'⟩ i hi
      simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at hw
      rw [hw]
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) = τ.1 :=
        GlobalTheory.AllWt.conjEmb_conjEmb τ.1
      have hσ : σ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases e : σ = ComplexEmbedding.conjugate τ.1
      · rw [f1 _ _ (Subtype.ext (by show conjEmb σ = τ.1; rw [e]; exact hcc))]
        simp [e, hne.symm]
      · rw [f0 _ _ fun h2 => e (by
          have h3 : conjEmb σ = τ.1 := congrArg Subtype.val h2
          rw [← h3]
          exact (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm)]
        simp [e, hσ]

theorem wchar_eq_units {S : Type} [CommRing S] (b : Formalism.L2.Pj.Ix D → ℕ) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    Formalism.L2.Pj.wchar b t = ((∏ i, t i ^ (b i : ℤ) : Sˣ) : S) := by
  simp [Formalism.L2.Pj.wchar, Units.coe_prod]

theorem prod_exOf_mul {S : Type} [CommRing S] (τ : GlobalTheory.AllWt.Psi H) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : Sˣ) : S) * Formalism.L2.Pj.wchar (detE D τ.1) t =
      Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t := by
  rw [wchar_eq_units, wchar_eq_units, ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add, exOf_add_detE]

end GlobalTheory.CompanionTheory.Ar.Br.CvRule

namespace GlobalTheory.CompanionTheory.Ar.Br

open GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue GlobalTheory.CompanionTheory.Ar.Br.CvRule

set_option maxHeartbeats 1600000 in

theorem exists_flat_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))) (τ : GlobalTheory.AllWt.Psi H) (φ : FrameFn Xo c), FlatOnModel Z' τ.1 φ → ∃ s s' : Formalism.L2.Pj.Rul Xo c, s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ s' ∈ GlobalTheory.AllWt.secZ Xo c (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * s' = s' ∧ s * s' = GlobalTheory.FlatLine.idem Z ∧ Reads (Z : Set (Xo.XF c)) τ.1 s φ := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' τ φ hf
  have hτ := τ.2
  have hC : IsClopen (Z : Set (Xo.XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) Z
  have hl := hf.1
  obtain ⟨s, s', e, -, hss₀, hsE₀, hs'E₀, -, hval⟩ :=
    GlobalTheory.T.flat_line_idempotent_sections E H D l Xo c (Z : Set (Xo.XF c)) τ.1 O β Y Z' φ hτ hC hl hf
  have hp : D.mult τ.1 = D.p := by rw [Datum.mult, if_pos hτ]
  have hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q := conj_mult hτ
  have red : ∀ p : Formalism.L2.Pj.TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hss : ∀ p z, s p z * s' p z = e p z := fun p z => congrFun (congrFun hss₀ p) z
  have hsE : ∀ p z, s p z * e p z = s p z := fun p z => congrFun (congrFun hsE₀ p) z
  have hs'E : ∀ p z, s' p z * e p z = s' p z := fun p z => congrFun (congrFun hs'E₀ p) z
  have hse : ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F)
      (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) →
      (¬ Set.range y ⊆ (Z : Set (Xo.XF c)) → ψ (e p z) = 0 ∧ ψ (s p z) = 0) ∧
      (Set.range y ⊆ (Z : Set (Xo.XF c)) → ψ (e p z) = 1 ∧
        ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ.1 = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q),
          (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ.1 (i.cast hp.symm)) →
          (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ.1) (j.cast hq.symm)) →
          ψ (s p z) = φ F y v w) := fun p z F _ ψ y h1 h2 => by
    have Dv := hval p z F ψ y h1 h2
    refine ⟨fun hr => ⟨Dv.1 hr, ?_⟩, Dv.2⟩
    have := congrArg ψ (hsE p z)
    rw [map_mul, Dv.1 hr, mul_zero] at this
    exact this.symm
  have C := fun (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) =>
    hse p z F ψ (fpt z ψ) (fpt_under z ψ) (fpt_snd z ψ)
  have zero : ∀ (p : Formalism.L2.Pj.TRing c.F) (x : p.R), (∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ x = 0) → x = 0 :=
    fun p x h => by
      haveI := red p
      exact eq_zero_of_fields x h
  have hE : e = GlobalTheory.FlatLine.idem Z := eq_cspB_rule _ e fun p z F _ ψ =>
    ⟨fun hr => ((C p z F ψ).1 hr).1, fun hr => ((C p z F ψ).2 hr).1⟩
  have hnat : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → e q z = f (e p y) ∧ s q z = f (s p y) := fun p q f y z h => by
    have key : ∀ (F : Type) [Field F] (ψ : q.R →+* F), ψ (e q z) = ψ (f (e p y)) ∧ ψ (s q z) = ψ (f (s p y)) := by
      intro F _ ψ
      let ψ' : p.R →+* F := ψ.comp f.toRingHom
      have h1 : under (fpt z ψ) = spMap ψ' ≫ y.x := by
        rw [fpt_under, h.1, ← Category.assoc, ← spMap_comp']
      have h2 : fpt z ψ ≫ pullback.snd _ _ = spMap (ψ'.comp (algebraMap c.F p.R)) := by
        rw [fpt_snd]
        congr 1
        ext a
        simp [ψ']
      have D2 := hse p y F ψ' (fpt z ψ) h1 h2
      have D1 := C q z F ψ
      have e1 : ∀ x : p.R, ψ (f x) = ψ' x := fun _ => rfl
      rw [e1, e1]
      by_cases hr : Set.range (fpt z ψ) ⊆ (Z : Set (Xo.XF c))
      · obtain ⟨v, w, ev, ew, -⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 q.R z F ψ (fpt z ψ) hp hq (fpt_under z ψ) (fpt_snd z ψ)
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v w hp hq (fun i => ?_) (fun j => ?_)]
        · rw [ev i, h.2.1, ← Category.assoc, dualMap_spMap_comp]
        · rw [ew j, h.2.1, ← Category.assoc, dualMap_spMap_comp]
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        exact ⟨rfl, rfl⟩
    exact ⟨sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [map_sub, (key F ψ).1, sub_self]),
      sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [map_sub, (key F ψ).2, sub_self])⟩
  have hnat' : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → s' q z = f (s' p y) := fun p q f y z h => by
    obtain ⟨h1, h2⟩ := hnat p q f y z h
    have h3 := hss q z
    have h4 := congrArg f (hss p y)
    have h5 := hs'E q z
    have h6 := congrArg f (hs'E p y)
    rw [map_mul] at h4 h6
    rw [← h2] at h4
    rw [← h1] at h4 h6
    linear_combination (f (s' p y)) * h3 - (s' q z) * h4 - h5 + h6
  have hwt : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' → e p y' = e p y ∧
        s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t = s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t := fun p t y y' h => by
    have key : ∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ (e p y') = ψ (e p y) ∧
        ψ (s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t) = ψ (s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t) := by
      intro F _ ψ
      have h1 : under (fpt y ψ) = spMap ψ ≫ y'.x := by rw [fpt_under, h.1]
      have D2 := hse p y' F ψ (fpt y ψ) h1 (fpt_snd y ψ)
      have D1 := C p y F ψ
      rw [map_mul, map_mul]
      by_cases hr : Set.range (fpt y ψ) ⊆ (Z : Set (Xo.XF c))
      · obtain ⟨v, w, ev, ew, hfr⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 p.R y F ψ (fpt y ψ) hp hq (fpt_under y ψ) (fpt_snd y ψ)
        obtain ⟨v', w', ev', ew', hfr'⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 p.R y' F ψ (fpt y ψ) hp hq h1 (fpt_snd y ψ)
        obtain ⟨A, B, hA, hB, dA, dB⟩ := GlobalTheory.T.frame_borel_change_vectors E H D l Xo c τ.1 p.R t y y' h F ψ (fpt y ψ) hp hq v v' w w' (fpt_under y ψ) ev ew ev' ew'
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v' w' hp hq ev' ew', wchar_detE τ.1 hp, wchar_detE _ hq, map_prod, map_prod,
          ← dA, ← dB]
        exact hl.chg F _ _ v w v' w' A B (hfr _ hr) (hfr' _ hr) hA hB
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        simp
    have k1 : e p y' - e p y = 0 := zero p _ fun F _ ψ => by rw [map_sub, (key F ψ).1, sub_self]
    have k2 : s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t - s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t = 0 :=
      zero p _ fun F _ ψ => by
        have := (key F ψ).2
        exact (map_sub ψ _ _).trans (sub_eq_zero.2 this)
    exact ⟨sub_eq_zero.1 k1, sub_eq_zero.1 k2⟩
  have hunitW : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (b : Formalism.L2.Pj.Ix D → ℕ),
      IsUnit (Formalism.L2.Pj.wchar b t) := fun p t b => IsUnit.prod_univ_iff.2 fun i => (t i).isUnit.pow _
  have hS : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' →
        s p y' = ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : (p.R)ˣ) : p.R) * s p y := fun p t y y' h => by
    refine (hunitW p t (detE D τ.1)).mul_right_cancel ?_
    have h1 := (hwt p t y y' h).2
    have h2 := prod_exOf_mul τ t
    rw [h1, ← h2]
    ring
  refine ⟨s, s', GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q f y z h => (hnat p q f y z h).2, hS⟩,
    GlobalTheory.AllWt.mem_secZ.2 ⟨hnat', fun p t y y' h => ?_⟩, ?_, ?_, ?_, ?_⟩
  · set T := ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : (p.R)ˣ) : p.R) with hTdef
    set T' := ((∏ i, t i ^ (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) i : (p.R)ˣ) : p.R) with hT'def
    have hT : T' * T = 1 := by
      rw [hTdef, hT'def, ← Units.val_mul, ← Finset.prod_mul_distrib]
      simp
    have hw := hS p t y y' h
    have h1 := (hwt p t y y' h).1
    have h3 := hss p y
    have h4 := hss p y'
    have h5 := hs'E p y
    have h6 := hs'E p y'
    rw [h1] at h4 h6
    linear_combination (-1) * h6 + (-(s' p y')) * h3 + (-(s' p y') * s p y * s' p y) * hT +
      (-T' * s' p y' * s' p y) * hw + (T' * s' p y) * h4 + T' * h5
  · rw [← hE, mul_comm]; exact hsE₀
  · rw [← hE, mul_comm]; exact hs'E₀
  · rw [← hE]; exact hss₀
  · exact fun p z F _ ψ y h1 h2 hr v w hp' hq' ev ew => ((hval p z F ψ y h1 h2).2 hr).2 v w hp' hq' ev ew

end GlobalTheory.CompanionTheory.Ar.Br
