import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransport
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

section Datum

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.OnTies GlobalTheory.DatumInverseCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

def DetOne (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : Prop :=
  LinearMap.det (LinearMap.baseChange (𝓞 E ⧸ l.Mb) (liftLa γ)) = 1

theorem natCast_mem_half (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb ∧ ((l.M : ℕ) : 𝓞 E) ∈ Mfr l := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact ⟨(Ideal.mul_le_inf.trans inf_le_left) h, (Ideal.mul_le_inf.trans inf_le_right) h⟩

theorem exists_rightMul (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) {n : ℕ} {rk : Bool} {x : Fin n → Dw.La}
    (hx : AdmX (l := l) rk x) : ∃ x' : Fin n → Dw.La, IsRightMul γ x x' ∧ AdmX (l := l) rk x' := by
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  obtain ⟨g, -, hγ, -⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ Dw l γ
  obtain ⟨g', hg'⟩ := g.inv l.M hM₁
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw (g.f l.M)
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, fa b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨ga a, mem_of_modN Dw (natCast_mem_half l).2 (modN_of_dvd Dw hM₁ fun v => by
      rw [map_sub, LinearMap.sub_apply, hfa, hga, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).1)⟩
  refine ⟨fun b => fa (x b), fun b a => ?_,
    GlobalTheory.DatumCoverAdjoint.span_image_sup_eq_top (Mfr l) fa hsurj x _ hx⟩
  rw [hfa, map_smul, ← map_sub, ← smul_sub]
  exact dvd_pair_of_mem _ ((Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm))

theorem datum_move {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hM : d.l₂.M = l.M * d.pd)
    (hb : d.l₂.Mb = l.Mb * d.I) {ph : (Fin n → LaJ Xo c d) → c.F} {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ}
    {x₀ : Fin n → LaJ Xo c d} (hpin : d.PhiPin ph ψ x₀) (f : Dw.La →ₗ[𝓞 E] Dw.La)
    (hg : ∀ a, f a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) {γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l}
    (hγ : ∀ a, f a - liftLa γ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) (σ : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂)
    (hσ : ∀ a, σ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a)) {x x' : Fin n → Dw.La}
    (hx : IsRightMul γ x' x) (q : Fin n → LevQ Dw d.l₂) : d.w x (fun b => σ.symm (q b)) = d.w x' q := by
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hq : ∀ b, f (levRep (σ.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x (fun b => levRep (σ.symm (q b))) =
      zetaM c ^ pairL (l := l) x' (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have h1 := sub_mem (Submodule.smul_mono hbM le_rfl (hq b)) (hγ (levRep (σ.symm (q b))))
    have h2 := dvd_pair_of_mem (l := l) (x' b) h1
    rw [sub_sub_sub_cancel_left, smul_sub, map_sub] at h2
    have h3 := dvd_add (hx b (levRep (σ.symm (q b)))) h2
    rwa [sub_add_sub_cancel] at h3
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

theorem char_eq_one_of_detOne (h3 : ¬ 3 ∣ l.M) {A : Type} [CommGroup A] (χ : (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) →* A)
    {γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l} (hγ : DetOne γ) : χ γ = 1 := by
  haveI := Dw.fin
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ fun h => by
    have := (natCast_mem_half l).1
    rw [h, Ideal.mem_bot] at this
    exact hM0 (by exact_mod_cast this)
  have h4 : ∀ 𝔪 : Ideal (𝓞 E ⧸ l.Mb), 𝔪.IsMaximal → 4 ≤ Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := by
    intro 𝔪 h
    haveI : Nontrivial ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.2 h.ne_top
    haveI : Finite ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    haveI : Fintype ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Fintype.ofFinite _
    have h1 : 1 < Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Finite.one_lt_card
    have h0 : ((Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) : ℕ) : (𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hN' : (l.M : (𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪), ← map_natCast (Ideal.Quotient.mk l.Mb),
        Ideal.Quotient.eq_zero_iff_mem.2 (natCast_mem_half l).1, map_zero]
    by_contra hlt
    have hc : Nat.Coprime (Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪)) l.M := by
      have : Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 2 ∨ Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 3 := by omega
      rcases this with h | h <;> rw [h]
      · exact Nat.coprime_two_left.2 l.odd
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have := hc.cast (R := (𝓞 E ⧸ l.Mb) ⧸ 𝔪)
    rw [h0, hN'] at this
    exact not_isCoprime_zero_zero this
  have h := GlobalTheory.char_eq_one_of_inverse_reduction_det_one (𝓞 E) Dw.La Dw.La l.Mb A χ LinearMap.id (liftLa γ) γ⁻¹ h4
    (fun b => ⟨b, by simp⟩) (fun _ h => h) hγ fun a => by
      obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _ (γ⁻¹ (Submodule.Quotient.mk a))
      refine ⟨a', ha', (Submodule.Quotient.eq _).1 ?_⟩
      exact (liftLa_spec γ a').trans ((congrArg γ ha').trans (γ.apply_symm_apply _))
  rwa [map_inv, inv_eq_one] at h

end Datum

section Move

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.ShortMove
open scoped TensorProduct

variable {D : D7}

def TwistTrivialOnRational (T : Full D) (j : ℕ) : Prop :=
  ∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀),
    T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1

def GoodDatum (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ j w.n).l₂.M ∧ Λ.LevOK N (T.dδ j w.n).l₂.M ∧ P ∈ harmL T.Q.c Λ (wtA w)

def IsSeries (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (x : Fin w.n → (T.Q.Dw j).La) (f : T.R j) : Prop :=
  AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x ∧ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x P f

variable {j : ℕ} {w : WeightFamilies.Wt D j}

theorem IsSeries.mem_sh {T : Top D} {Λ N P x f} (hG : GoodDatum T j w Λ N P) (hf : IsSeries T j w Λ N P x f) :
    f ∈ T.sh j w :=
  ⟨hf.2.1, Λ, N, x, P, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hf.1, hG.2.2.2.2, hf.2.2⟩

theorem exists_isSeries {T : Top D} (hT : LawsSh T) (hj : InR D j) {Λ N P} (hG : GoodDatum T j w Λ N P)
    {x : Fin w.n → (T.Q.Dw j).La} (hx : AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x) : ∃ f, IsSeries T j w Λ N P x f := by
  obtain ⟨f, hf, hR⟩ := (hT.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x P hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hx hG.2.2.2.2).2
  exact ⟨f, hx, hf, hR⟩

theorem IsSeries.unique {T : Top D} (hT : LawsSh T) (hj : InR D j) {Λ N P x f f'} (hG : GoodDatum T j w Λ N P)
    (hf : IsSeries T j w Λ N P x f) (hf' : IsSeries T j w Λ N P x f') : f = f' := by
  have tot := (hT.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x P hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hf.1 hG.2.2.2.2).1
  have hd := hT.dLev j hj w.n
  obtain ⟨-, h1, h2⟩ := hf
  obtain ⟨-, h1', h2'⟩ := hf'
  generalize T.dδ j w.n = d at *
  refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric h1 h1' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap T.Q.c.F k).comp (d.eF.symm : d.c₂.F →+* T.Q.c.F)).toAlgebra
  have hk : ∀ a : T.Q.c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap T.Q.c.F k a := fun a => by
    show algebraMap T.Q.c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h2 k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h2' k hk y y₂ hy
  rw [e, e', (tot k y₂).unique hv hv']

abbrev mv (T : Top D) (j : ℕ) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_const (T : Full D) (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hw : D.R.r ≤ w.n)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) :
    ∃ u : T.Q.c.F, u ≠ 0 ∧ ∀ Λ N P x x' f f', GoodDatum T.toTop j w Λ N P → IsRightMul γ x' x →
      IsSeries T.toTop j w Λ N P x f → IsSeries T.toTop j w Λ N P x' f' → mv T.toTop j γ f = u • f' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hL := GlobalTheory.firstFiveLaws.1
  have hpq := rank_eq hT.p.pins hj
  have hA : T.Q.l.A = 1 := hT.p.pins.2.1.2
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hA
  have hLev := hT.sh.dLev j hj w.n
  have hA₂ := hT.lvA j hj w.n
  obtain ⟨inst, hnab⟩ := hT.sh.dNab j hj w.n
  obtain ⟨ph, ψ, x₀, -, hpin, htie⟩ := hT.sh.dPhi j hj w.n hw
  have hTot := hT.sh.shTot j hj (wtA w) w.n (dom_wtA w)
  obtain ⟨g, hν, hγ, hg⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ (T.Q.Dw j) T.Q.l γ
  obtain ⟨ρ₂, hρ₂⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq (T.dδ j w.n).Xo₂ g (by rw [hν, sub_self]; exact dvd_zero _)
  obtain ⟨u, hu, hcd⟩ := exists_root T hT hj hxi hw g hν ρ₂ hρ₂
  refine ⟨u, hu, fun Λ N P x0 x0' f f' hG hx hf hf' => ?_⟩
  suffices key : IsSeries T.toTop j w Λ N P x0' ((u : T.Q.c.F)⁻¹ • mv T.toTop j γ f) by
    rw [← key.unique hT.sh hj hG hf', smul_inv_smul₀ hu]
  obtain ⟨hX, hsec, hR⟩ := hf
  obtain ⟨hU, hb, hb₂, hO, hP⟩ := hG
  refine ⟨hf'.1, Submodule.smul_mem _ _ (actL_mem _ _ _ _ hAct.total hAct.nat hAct.bor _ γ hsec), ?_⟩
  clear hf'
  generalize T.dδ j w.n = d at *
  have hM := hLev.2.1
  have hM₁ : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ (by have := d.l₂.three_le; omega : 0 < d.l₂.M))
  have hI : ∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have hpI : ((d.pd : ℕ) : 𝓞 D.host.E) ∈ d.I := by
      refine (Ideal.mul_le_inf.trans inf_le_left : d.I * d.I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ d.I) ?_
      rw [GlobalTheory.DatumInverseCharacter.half_prod hM hLev.2.2.2.1]
      exact Ideal.mem_span_singleton_self _
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (g.tower d.pd T.Q.l.M hpd hM₁ a)
    have h2 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (hg d.pd hpd hLev.2.2.1 a)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, mul_comm, ← hM] at this
  have hγ' : ∀ a, g.f d.l₂.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ (natCast_mem_half T.Q.l).1 (g.tower T.Q.l.M d.pd hM₁ hpd a)
    have h2 : g.f T.Q.l.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) :=
      (Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, ← hM] at this
  obtain ⟨σq, hσ, -⟩ := GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport _ _ _ _ _ _ _ d hM hLev.2.2.2.1 ph ψ x₀ hpin g hI
  have hw' := datum_move d hM hLev.2.2.2.1 hpin _ hI hγ' σq hσ hx
  obtain ⟨hρs, ν₂, hη, hηA⟩ := hρ₂
  have hmv₂ : IsLevMove ρ₂.hom ν₂ (g.f d.l₂.M) (g.f d.l₂.A) := ⟨hρs, hη, hηA⟩
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ d).2 _ P hP.1
  intro k _ _ _ _ hk y y₂ ho
  have hev := evalAt_actL hAct (hT.p.evalWD j hj) frMap_trans_id γ hsec.1 y
  obtain ⟨ρ, ν, -, hmv, hfr⟩ := mvPt_spec hAct.total γ y
  generalize mvPt _ _ γ y = y' at hev hfr
  obtain ⟨y₂', hfr₂⟩ := (GlobalTheory.exists_unique_frMove _ _ _ _ d.Xo₂ d.c₂ ρ₂.hom ν₂ hρs k y₂).1
  obtain ⟨r', m', hr', hm', hE'⟩ := GlobalTheory.T.exists_conj_levelMap_by_levelMoves _ _ _ _ _ _ _ d hLev.2.2.2.2.2.1 ρ ν ρ₂ ν₂ _ _ _ _ hmv hmv₂ hγ'
    (fun a => ⟨_, by rw [hA, one_smul]⟩)
  have ho' := GlobalTheory.T.liesOverFramed_of_square_levelMoves _ _ _ _ _ _ _ d ρ ν ρ₂.hom ν₂ r' m' hr' hm' k y y' y₂ y₂' ho hfr hfr₂
  obtain ⟨z₂, hz₂⟩ := hLev.2.2.2.2.2.2.1 k hk y'
  obtain ⟨v, hv, hfv⟩ := hR k hk y' z₂ hz₂
  obtain ⟨v', hv', -⟩ := (hTot Λ N x0 P hU hb hb₂ hO hX hP).1 k y₂'
  have e₁ := GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift hL hC _ _ _ _ _ _ _ d
    (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 _ _ _ hpq).1 hLev (hA₂.trans hA.symm) hnab ⟨ph, ψ, x₀, hpin, htie⟩ Λ N hU hb₂ hO _ _ hP₂ x0 _
    r' m' hE' k hk y' z₂ y₂' hz₂ ho' v v' hv hv'
  have e₂ := GlobalTheory.T.shortThetaValue_under_levelMove hL hC _ _ _ _ d.Xo₂ d.c₂ d.nab₂ hnab k ρ₂.hom ν₂ _ _ y₂ y₂' hmv₂ hfr₂ σq hσ
    _ _ _ hP₂ (d.w x0) Λ _ N v' hv'
  rw [funext hw'] at e₂
  refine ⟨v', e₂, (evalAt_smul _ _ _ _ y).trans ?_⟩
  refine (congrArg (_ * ·) (hev.trans (hfv.trans e₁))).trans ?_
  rw [hcd k y₂ y₂' hfr₂.1, hk, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]

theorem not_three_dvd_level {T : Top D} (h : LawsP T) : ¬ 3 ∣ T.Q.l.M := by
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have key : ∀ k, ¬ 3 ∣ D.host.g k := fun k hk => by
    have hc := D.ntypes.g_cond k
    have h4 : D.host.g k % 4 = 1 := by
      rw [← Nat.mod_mod_of_dvd (D.host.g k)
        (show 4 ∣ D.host.QS * D.host.q * D.host.d from ((((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (D.host.g_prime k)).1 hk
    omega
  rw [hM, Nat.prime_three.dvd_mul]
  exact fun h => h.elim (key 0) (key 1)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mv_series (T : Full D) (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hw : D.R.r ≤ w.n)
    {γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l} (hγ : DetOne γ) {Λ N P x x' f f'}
    (hG : GoodDatum T.toTop j w Λ N P) (hx : IsRightMul γ x' x) (hf : IsSeries T.toTop j w Λ N P x f)
    (hf' : IsSeries T.toTop j w Λ N P x' f') : mv T.toTop j γ f = f' := by
  choose u hu0 hu using exists_const (w := w) T hT hj hxi hw
  rw [hu γ _ _ _ _ _ _ _ hG hx hf hf']
  by_cases h0 : f' = 0
  · rw [h0, smul_zero]
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j (rank_eq hT.p.pins hj) hT.p.pins.2.1.2
  have hmul : ∀ a b, u (a * b) = u a * u b := fun a b => by
    obtain ⟨x₁, r₁, a₁⟩ := exists_rightMul a hf'.1
    obtain ⟨x₂, r₂, a₂⟩ := exists_rightMul b a₁
    obtain ⟨f₁, s₁⟩ := exists_isSeries hT.sh hj hG a₁
    obtain ⟨f₂, s₂⟩ := exists_isSeries hT.sh hj hG a₂
    have e : mv T.toTop j (a * b) f₂ = mv T.toTop j a (mv T.toTop j b f₂) :=
      actL_mul _ _ _ hAct.total hAct.func hAct.mul a b s₂.2.1.1
    rw [hu _ _ _ _ _ _ _ _ hG (r₁.mul r₂) s₂ hf', hu _ _ _ _ _ _ _ _ hG r₂ s₂ s₁, map_smul,
      hu _ _ _ _ _ _ _ _ hG r₁ s₁ hf', smul_smul, mul_comm] at e
    exact smul_left_injective _ h0 e
  have h1 := char_eq_one_of_detOne (not_three_dvd_level hT.p)
    (MonoidHom.mk' (fun a => Units.mk0 (u a) (hu0 a)) fun a b => Units.ext (hmul a b)) hγ
  rw [show u γ = 1 from congrArg Units.val h1, one_smul]

end Move

end GlobalTheory.TraceLattice
