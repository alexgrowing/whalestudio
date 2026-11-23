import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsEigFrameOfFrPt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ofAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsOver V V ⟶ G) :
    (ofAt V ≫ f).left = f.left := Category.id_comp _

theorem toAt_left (V : Type) [CommRing V] {G : Over (Sp V)} (f : epsAt (𝟙 (Sp V)) ⟶ G) :
    (toAt V ≫ f).left = f.left := Category.id_comp _

theorem isIntFrame_of_basis (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    {y' : Sp T.Fr ⟶ Xo.XF c} (m : SABMap t' Xo.univ.t (under y'))
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ' : E →+* ℂ) {N n : ℕ} (hn : N = n)
    (ub : Fin N → (epsOver T.V T.V ⟶ G.G)) (htan : ∀ i, IsTan (ub i))
    (heig : ∀ i, Formalism.L2.Pj.IsEigV c io G τ' (ub i))
    (hbas : ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → Formalism.L2.Pj.IsEigV c io G τ' w →
      ∃! a : Fin N → T.V, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsComb ub a w)
    (v : Vecs y' n)
    (hv : ∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m.φ = (v i).left ∧
      u' ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (ub (i.cast hn.symm)).left) :
    IsIntFrame m m2 (io.comp (tauIn c τ')) v := by
  subst hn
  obtain ⟨σV, hσ⟩ := exists_lift_int T (io.comp (tauIn c τ'))
  have hσa : ∀ a, algebraMap T.V T.Fr (σV a) = io (tauIn c τ' a) := fun a => RingHom.congr_fun hσ a
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨σV, fun i => ofAt T.V ≫ ub i, hσ, ⟨fun i => ⟨?_, fun a => ?_⟩, fun w hw => ?_⟩, fun a => ?_⟩
  · show _ ≫ (ofAt T.V ≫ ub i).left = _
    rw [ofAt_left, one_left_at]
    exact htan i
  · rw [Category.assoc, ofAt_left, ofAt_left]
    exact heig i a (σV a) (hσa a)
  · have htan' : IsTan (toAt T.V ≫ w) := by
      show _ ≫ (toAt T.V ≫ w).left = _
      rw [toAt_left, ← one_left_at]
      exact hw.1
    have heig' : Formalism.L2.Pj.IsEigV c io G τ' (toAt T.V ≫ w) := fun a z hz => by
      have hz' : z = σV a := hinj (hz.trans (hσa a).symm)
      subst hz'
      rw [Category.assoc, toAt_left, toAt_left]
      exact hw.2 a
    obtain ⟨a, ⟨u, hu1, hu2⟩, huniq⟩ := hbas _ htan' heig'
    refine ⟨a, ⟨fun i => ofAt T.V ≫ u i, fun i => ?_, ?_⟩, fun b hb => huniq b ?_⟩
    · rw [ofAt_left, ofAt_left]
      exact hu1 i
    · rw [← pre_prod, ← hu2, ← Category.assoc, ofAt_toAt, Category.id_comp]
    · obtain ⟨u', h1, h2⟩ := hb
      refine ⟨fun i => toAt T.V ≫ u' i, fun i => ?_, ?_⟩
      · rw [toAt_left, h1, ofAt_left]
        rfl
      · rw [← pre_prod, ← h2]
  · obtain ⟨u', h1, h2⟩ := hv a
    refine ⟨u', h1, ?_⟩
    rw [ofAt_left, h2]
    rfl

theorem exists_factor (f : Formalism.L2.Pj.Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : Formalism.L2.Pj.FrPt Xo c S)
    (h : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => Formalism.L2.Pj.FrPt Xo c S)
      (fun φ y z => Formalism.L2.Pj.FrMap φ y z) y) :
    ∃ (p : Formalism.L2.Pj.TRing c.F) (ψ : p.R →ₐ[c.F] S) (z : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrMap ψ z y ∧ Formalism.L2.Pj.evR Xo c f y = ψ (f p z) :=
  ⟨_, _, _, h.choose_spec.choose_spec.choose_spec, by
    unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
    rw [dif_pos h]⟩

theorem norm_le_one_iff_log_valuation (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (a : c.F) (ha : a ≠ 0)
    {e : ℕ} (he : 0 < e) {ρ r : ℝ} (hρ : ρ < 0) (hr : 0 < r)
    (h : Real.log r = ((e : ℤ) * Formalism.L2.Pj.vLa la a : ℤ) * ρ) :
    la.valuation c.F a ≤ 1 ↔ r ≤ 1 := by
  have h0 : la.valuation c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have c1 : la.valuation c.F a ≤ 1 ↔ 0 ≤ Formalism.L2.Pj.vLa la a := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one, Formalism.L2.Pj.vLa]
    omega
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : 0 < (e : ℝ) * (-ρ) := mul_pos he' (neg_pos.2 hρ)
  have h' : Real.log r = ((e : ℝ) * (-ρ)) * (-(Formalism.L2.Pj.vLa la a : ℝ)) := by
    rw [h]; push_cast; ring
  rw [c1]
  constructor
  · intro hL
    have hL' : (0 : ℝ) ≤ Formalism.L2.Pj.vLa la a := by exact_mod_cast hL
    have : Real.log r ≤ 0 := by rw [h']; nlinarith [mul_nonneg hc.le hL']
    by_contra hgt
    have := Real.log_pos (not_le.1 hgt)
    linarith
  · intro hr1
    have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    by_contra hL
    have hL' : (Formalism.L2.Pj.vLa la a : ℝ) < 0 := by exact_mod_cast not_le.1 hL
    have := mul_pos hc (neg_pos.2 hL')
    linarith

end GlobalTheory.CompanionTheory.Ar.Flat.RuleVal

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem GlobalTheory.CompanionTheory.Ar.Flat.nval_flat_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : Formalism.L2.Pj.Rul Xo c) (t : ∀ p : Nat.Primes, (c.F →+* ℂ_[p]) → ℝ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → (∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ (s p z) = φ F y v w) → (∀ p κ, HasFinNorm U τ φ p κ (t p κ)) → ∀ (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : Formalism.L2.Pj.IntFr Xo c T io) (y' : Sp T.Fr ⟶ Xo.XF c), Formalism.L2.Pj.OverLa la T.V io e → y.IsAlg → under y' = (letI := io.toAlgebra; y.1.x) → y' ≫ pullback.snd _ _ = spMap io → Set.range y' ⊆ U → ∃ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ ∀ π : c.F, la.valuation c.F π = WithZero.exp (-1 : ℤ) → Formalism.L2.Pj.nval T.V e (Formalism.L2.Pj.evI y s) = ((t p κ / Real.log ‖κ π‖ : ℝ) : EReal) := by
  intro E _ _ _ H D l Xo c U τ φ s t hτ hφ hs hN la T io e y y' ho halg hy hyo hyU
  letI := io.toAlgebra
  obtain ⟨p, j, hj⟩ := RuleVal.exists_embed T halg
  obtain ⟨ρ, hρ, hlog⟩ := RuleVal.exists_log_norm T j hj
  have hI : Formalism.L2.Pj.Integral T io y.1 := y.2.2
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, -⟩ := hI
  obtain ⟨m, hm⟩ := RuleVal.exists_cast hy.symm m1
  have hp : D.mult τ = D.p := if_pos hτ
  have hq : D.mult (ComplexEmbedding.conjugate τ) = D.q := RuleVal.mult_conj τ hτ
  obtain ⟨v, hv⟩ := RuleVal.exists_vecs y.1 hy τ hp
  obtain ⟨w, hw⟩ := RuleVal.exists_vecs y.1 hy (ComplexEmbedding.conjugate τ) hq
  have hfr : IsFramed U τ io y' v w :=
    ⟨hyo, hyU, RuleVal.isEigFrame_of_frPt y.1 hy τ hp v hv, RuleVal.isEigFrame_of_frPt y.1 hy _ hq w hw⟩
  have hi1 : IsIntFrame m m2 (io.comp (tauIn c τ)) v :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 τ hp (ub τ) (htan τ) (heig τ) (hbas τ) v fun i => by
      obtain ⟨u', h1, h2⟩ := hlift τ (i.cast hp.symm)
      exact ⟨u', by rw [hm, h1, hv], h2⟩
  have hi2 : IsIntFrame m m2 (io.comp (tauIn c (ComplexEmbedding.conjugate τ))) w :=
    RuleVal.isIntFrame_of_basis T io G t' m m2 _ hq (ub _) (htan _) (heig _) (hbas _) w fun i => by
      obtain ⟨u', h1, h2⟩ := hlift (ComplexEmbedding.conjugate τ) (i.cast hq.symm)
      exact ⟨u', by rw [hm, h1, hw], h2⟩
  have hval : Real.log ‖j (φ T.Fr y' v w)‖ = t p (j.comp io) :=
    hN p (j.comp io) T.V T.Fr j io y' v w G t' m m2 hj rfl hfr hi1 hi2
  have hev : Formalism.L2.Pj.evI y s = φ T.Fr y' v w := by
    obtain ⟨pz, ψ, z, hm', he⟩ := RuleVal.exists_factor s y.1 y.2.1
    have hcomp : ψ.toRingHom.comp (algebraMap c.F pz.R) = io := ψ.comp_algebraMap
    refine he.trans (hs pz z T.Fr ψ.toRingHom y' (hy.trans hm'.1) (by rw [hcomp]; exact hyo) hyU v w hp hq
      (fun i => (hv i).trans (hm'.2.1 τ _)) (fun i => (hw i).trans (hm'.2.1 _ _)))
  have hne : φ T.Fr y' v w ≠ 0 := hφ.ne T.Fr io y' v w hfr
  refine ⟨p, j.comp io, fun a => ?_, fun π hπ => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      simp
    have hio : io a ≠ 0 := (map_ne_zero io).2 ha
    refine RuleVal.norm_le_one_iff_log_valuation la a ha ho.1 hρ (norm_pos_iff.2 ((map_ne_zero j).2 hio)) ?_
    rw [RingHom.comp_apply, hlog _ hio, ho.2 a]
  · have hπ0 : π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hio : io π ≠ 0 := (map_ne_zero io).2 hπ0
    have hvL : Formalism.L2.Pj.vLa la π = 1 := by
      rw [Formalism.L2.Pj.vLa, hπ, WithZero.log_exp]
      simp
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
    have h1 : Real.log ‖(j.comp io) π‖ = (e : ℝ) * ρ := by
      rw [RingHom.comp_apply, hlog _ hio, ho.2 π, hvL]
      simp
    rw [hev, Formalism.L2.Pj.nval_of_ne hne, ← hval, h1, hlog _ hne]
    congr 1
    field_simp [hρ.ne]
