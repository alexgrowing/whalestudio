import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianLineMetricBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogCardQuotientBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRatioProductFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndepStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RootHt
open GroundTheory.Heights₂.Heights

theorem gram_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li}
    (h : LieMetric M y) {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X} {B : HermitianBundle.{0} L}
    {MB : LieModel G z B.carrier} (hfib : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (σ : L →+* ℂ) {n : ℕ}
    (g : Fin n → B.carrier) (v : Fin n → (epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G))
    (hl : ∀ a, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) (g a) (v a)) :
    B.gramDet σ g = (gramAt h _ v).det := by
  unfold HermitianBundle.gramDet gramAt
  congr 1
  ext a b
  exact hfib σ (g a) (g b) (v a) (v b) (hl a) (hl b)

theorem one_label (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J)
    (hc : CharZero Ω) (hall : ∀ q : X, genPt ξ ⤳ q)
    (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hm : 0 < m)
    (hind : LinearIndependent Ω b₀) (hsw : Sandwich M V b₀ m) (hdeg : (V.gr b₀ i).IsDegOn Set.univ y A.a e₀)
    (hsm : IsSmoothHerm A) :
    ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ F : SatFlag B r,
      (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      |Ht.lineHt A L w - F.grDeg i| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.hermitian_line_metric_bound X Ω ξ K J y G Li M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm
  refine ⟨Real.log m + |C₀|, ?_⟩
  intro L _ _ w z hw B MB hfib F hsub
  have hne : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := fun k => (hw.1 k).imp fun c hc => hc.ne_zero
  choose c₀ hc₀ using hne
  have hne : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := fun k => ⟨c₀ k, hc₀ k⟩
  obtain ⟨f, ef, s, e, t, u, vf, ve, hf, hfi, hs1, hs0, hef, he, hv, hve, hsv, hcls, hu, hu0⟩ :=
    GlobalTheory.T.coord_degree_bound_of_flag X Ω ξ K J y G Li M V r b₀ m i A.a e₀ hc hall htie hm hind hsw hdeg L w z hw B MB F hsub c₀ hc₀
  have hsub₀ : IsSubFibre M (flagStep Ω b₀ i) z MB (F.F i.castSucc) := by simpa using hsub i.castSucc
  have hsub₁ : IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB (F.F i.succ) := by simpa using hsub i.succ
  obtain ⟨φ, hker, hval⟩ := GlobalTheory.T.coord_degree_bound_generic X Ω ξ K J y G Li M V r b₀ m i A.a e₀ hc hall htie hm hind hsw hdeg L w z hw
    B MB (F.F i.castSucc) (F.F i.succ) hsub₀ hsub₁ c₀ hc₀
  have hloc := GlobalTheory.T.coord_degree_bound_char_zero X Ω ξ K J y G Li M V r b₀ m i A.a e₀ hc hall htie hm hind hsw hdeg L w z hw
    B MB (F.F i.castSucc) (F.F i.succ) hsub₀ hsub₁ c₀ hc₀ φ hval
  have hφ : φ ⟨s, hs1⟩ = u := hval ⟨s, hs1⟩ e ve t u he hve hsv hcls hu
  obtain ⟨hρ, hfin, hsum⟩ := GlobalTheory.T.local_ratio_product_formula L K J A.a w c₀ u hne hc₀ hu0
  have hidx := GlobalTheory.T.log_card_quotient_bound L B.carrier (F.F i.castSucc) (F.F i.succ) φ ⟨s, hs1⟩ m (locRatio A.a w c₀)
    (IsNoetherian.noetherian _) hker (by rw [hφ]; exact hu0) hm hρ hfin hloc
  rw [hφ, hsum] at hidx
  have hgr := GlobalTheory.T.graded_degree_formula L B r F i f s hf hfi hs1 hs0
  have harch : ∀ σ : L →+* ℂ, |(1 / 2) * (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ -
      Real.log ‖B.gramDet σ f‖) - Real.log ‖σ u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ +
      Real.log (A.h fun p => σ (w p))| ≤ C₀ := by
    intro σ
    choose v' hv' hl' using fun j => GlobalTheory.T.lie_model_value_lift X Ω ξ G Li M L z σ B.carrier MB (f j) (ef j) (vf j) (hv j).1 (hv j).2
    obtain ⟨ve', hve', hle'⟩ := GlobalTheory.T.lie_model_value_lift X Ω ξ G Li M L z σ B.carrier MB s e ve hve hsv
    have g0 : B.gramDet σ f = (gramAt h _ v').det := gram_eq h hfib σ f v' hl'
    have g1 : B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier) =
        (gramAt h _ (Fin.snoc v' ve' : Fin (i + 1) → (epsAt _ ⟶ G))).det := by
      refine gram_eq h hfib σ _ _ fun a => ?_
      refine Fin.lastCases ?_ (fun j => ?_) a
      · simpa using hle'
      · simpa using hl' j
    have hd : (gramAt h _ v').det ≠ 0 := by rw [← g0]; exact GlobalTheory.T.gram_det_ne_zero_of_indep L B σ _ f hfi
    have := hC₀ _ _ (GlobalTheory.T.coords_at_complex_embedding X Ω ξ K J y L w z σ hw) c₀ (fun k => by simpa using hc₀ k) ef e v' ve' t (σ u)
      hef he hv' hve' hcls (GlobalTheory.T.val_at_complex_embedding X Ω ξ L z σ _ u hu) (by simpa using hu0) hd
    rw [g0, g1]
    exact this
  have hN : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (L →+* ℂ) : ℝ) = Module.finrank ℚ L := by
    exact_mod_cast NumberField.Embeddings.card L ℂ
  set N : ℝ := ((Module.finrank ℚ L : ℕ) : ℝ) with hNdef
  set gd : (L →+* ℂ) → ℝ := fun σ => Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ -
      Real.log ‖B.gramDet σ f‖ with hgd
  set wu : (L →+* ℂ) → ℝ := fun σ => Real.log ‖σ u‖ + ∑ k, (A.a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ with hwu
  set hh : (L →+* ℂ) → ℝ := fun σ => Real.log (A.h fun p => σ (w p)) with hhh
  set P : ℝ := ∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) with hP
  set lc : ℝ := Real.log (Nat.card (F.F i.succ ⧸ (F.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (F.F i.succ).subtype)) with hlc
  have hsumd : |∑ σ : L →+* ℂ, ((1 / 2) * gd σ - wu σ + hh σ)| ≤ N * |C₀| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun σ _ => ?_).trans (b := ∑ _σ : L →+* ℂ, |C₀|) ?_
    · have := (harch σ).trans (le_abs_self C₀)
      have e1 : (1 / 2) * gd σ - wu σ + hh σ = (1 / 2) * gd σ - Real.log ‖σ u‖ -
          ∑ k, (A.a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ + hh σ := by simp only [hwu]; ring
      rw [e1]; exact this
    · simp [hcard, hNdef]
  have hSS : ∑ σ : L →+* ℂ, ((1 / 2) * gd σ - wu σ + hh σ) = (1 / 2) * ∑ σ, gd σ - ∑ σ, wu σ + ∑ σ, hh σ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hl : Ht.lineHt A L w = N⁻¹ * (P + ∑ σ, hh σ) := rfl
  rw [hSS] at hsumd
  rw [hgr, hl]
  have e2 : N⁻¹ * (P + ∑ σ, hh σ) - N⁻¹ * (lc - (1 / 2) * ∑ σ, gd σ) =
      N⁻¹ * (-(lc - (P + ∑ σ, wu σ)) + ((1 / 2) * ∑ σ, gd σ - ∑ σ, wu σ + ∑ σ, hh σ)) := by ring
  rw [e2, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have e3 := (abs_add_le (-(lc - (P + ∑ σ, wu σ))) ((1 / 2) * ∑ σ, gd σ - ∑ σ, wu σ + ∑ σ, hh σ))
  rw [abs_neg] at e3
  have e4 : N⁻¹ * (N * Real.log m + N * |C₀|) = Real.log m + |C₀| := by field_simp
  rw [← e4]
  exact mul_le_mul_of_nonneg_left (e3.trans (add_le_add hidx hsumd)) (inv_pos.mpr hN).le

end GlobalTheory.CompanionTheory.Ar.RootHt

namespace GlobalTheory.CompanionTheory.Ar.RootHt
open GroundTheory.Heights₂.Heights

section Dual

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def dualLine (A : HermLine J) : HermLine J where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [_root_.zpow_neg]

theorem isSmoothHerm_dualLine {A : HermLine J} (hA : IsSmoothHerm A) : IsSmoothHerm (dualLine A) :=
  hA.inv fun z hz => (A.pos z hz).ne'

theorem lineHt_dualLine (A : HermLine J) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, J k) → L) : Ht.lineHt (dualLine A) L w = -Ht.lineHt A L w := by
  unfold Ht.lineHt Ht.ptHt
  simp only [dualLine, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Real.log_inv, finsum_neg_distrib]
  ring

end Dual

section Deg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem isDegOn_of_tens_one {Λ : Lat ξ Ω} (hΛ : ∀ p, ∃ t, Λ.IsGenAt p t) {a : K → ℤ} {e₀ : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => 1).IsDegOn Set.univ y a e₀) : Λ.IsDegOn Set.univ y a e₀ := by
  refine ⟨h.1, fun p hp c hc => ?_⟩
  obtain ⟨t, ht⟩ := hΛ p
  have tg := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => 1) p (fun _ => t) fun _ => ht
  have := h.2 p hp c hc
  rw [tg.2] at this
  rw [ht.2, ← this]
  simp

theorem isDegOn_of_tens_neg_one {Λ : Lat ξ Ω} (hΛ : ∀ p, ∃ t, Λ.IsGenAt p t) {a : K → ℤ} {e₀ : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => -1).IsDegOn Set.univ y a e₀) :
    Λ.IsDegOn Set.univ y (-a) e₀⁻¹ := by
  refine ⟨inv_ne_zero h.1, fun p hp c hc => ?_⟩
  obtain ⟨t, ht⟩ := hΛ p
  have tg := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => -1) p (fun _ => t) fun _ => ht
  have hs := h.2 p hp c hc
  rw [tg.2] at hs
  simp only [Finset.univ_unique, Finset.prod_singleton, _root_.zpow_neg, zpow_one] at hs
  set g : Ω := (∏ k, y ⟨k, c k⟩ ^ a k) • e₀ with hg
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k hk => hc.1 (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hg0 : g ≠ 0 := by
    rw [hg, smul_eq_mul]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy k)) h.1
  have hgi : (∏ k, y ⟨k, c k⟩ ^ (-a) k) • e₀⁻¹ = g⁻¹ := by
    rw [hg, smul_eq_mul, smul_eq_mul, mul_inv, ← Finset.prod_inv_distrib]
    simp [_root_.zpow_neg]
  rw [hgi, ht.2]
  have h1 : t⁻¹ ∈ Submodule.span (regAt ξ p) {g} := hs ▸ Submodule.mem_span_singleton_self _
  have h2 : g ∈ Submodule.span (regAt ξ p) {t⁻¹} := hs ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_span_singleton.mp h2
  have ht0 := ht.1
  have e₁ : (r₁ : Ω) * g = t⁻¹ := hr₁
  have e₂ : (r₂ : Ω) * t⁻¹ = g := hr₂
  apply le_antisymm
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_span_singleton.mpr ⟨r₂, ?_⟩)
    show (r₂ : Ω) * g⁻¹ = t
    have hr : (r₂ : Ω) = g * t := by
      calc (r₂ : Ω) = r₂ * t⁻¹ * t := by field_simp
        _ = g * t := by rw [e₂]
    rw [hr]; field_simp
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_span_singleton.mpr ⟨r₁, ?_⟩)
    show (r₁ : Ω) * t = g⁻¹
    have hr : (r₁ : Ω) = t⁻¹ * g⁻¹ := by
      calc (r₁ : Ω) = r₁ * g * g⁻¹ := by field_simp
        _ = t⁻¹ * g⁻¹ := by rw [e₁]
    rw [hr]; field_simp

end Deg

section Root

open HodgeCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}

theorem isDegOn_inl (Fl : 𝔐.Flag) {a : CMType H × Fin (D.p + D.q) → K → ℤ} {e : CMType H × Fin (D.p + D.q) → Ω}
    (h : Fl.RootLines a e) (τ : CMType H) (i : Fin D.p) :
    ((𝔐.V (.inl τ)).gr (Fl.b (.inl τ)) i).IsDegOn Set.univ y (a (τ, Fin.castAdd D.q i)) (e (τ, Fin.castAdd D.q i)) := by
  have h₁ := h (τ, Fin.castAdd D.q i)
  have hi : rootIdx D (τ, Fin.castAdd D.q i) = ⟨.inl τ, i⟩ := by simp [rootIdx]
  have hs : rootSgn D (τ, Fin.castAdd D.q i) = 1 := by simp [rootSgn]
  unfold Flag.rootLat at h₁
  rw [hs] at h₁
  generalize rootIdx D (τ, Fin.castAdd D.q i) = q at h₁ hi
  subst hi
  exact isDegOn_of_tens_one (fun p => Flag.gr_gen_of_isFlagVBOn (Fl.sub _) (Set.mem_univ p) _) h₁

theorem isDegOn_inr (Fl : 𝔐.Flag) {a : CMType H × Fin (D.p + D.q) → K → ℤ} {e : CMType H × Fin (D.p + D.q) → Ω}
    (h : Fl.RootLines a e) (τ : CMType H) (i : Fin D.q) :
    ((𝔐.V (.inr τ)).gr (Fl.b (.inr τ)) i.rev).IsDegOn Set.univ y (-a (τ, Fin.natAdd D.p i)) (e (τ, Fin.natAdd D.p i))⁻¹ := by
  have h₁ := h (τ, Fin.natAdd D.p i)
  have hi : rootIdx D (τ, Fin.natAdd D.p i) = ⟨.inr τ, i.rev⟩ := by
    have h2 := i.2
    simp only [rootIdx, Fin.val_natAdd]
    rw [dif_neg (by omega)]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega
  have hs : rootSgn D (τ, Fin.natAdd D.p i) = -1 := by simp [rootSgn]
  unfold Flag.rootLat at h₁
  rw [hs] at h₁
  generalize rootIdx D (τ, Fin.natAdd D.p i) = q at h₁ hi
  subst hi
  exact isDegOn_of_tens_neg_one (fun p => Flag.gr_gen_of_isFlagVBOn (Fl.sub _) (Set.mem_univ p) _) h₁

end Root

end GlobalTheory.CompanionTheory.Ar.RootHt

namespace GlobalTheory.CompanionTheory.Ar.RootHt
open GroundTheory.Heights₂.Heights

theorem root_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y) (x : CMType H × Fin (D.p + D.q) → HermLine J) (e : CMType H × Fin (D.p + D.q) → Ω), (∀ r, IsSmoothHerm (x r)) → Fl.RootLines (fun r => (x r).a) e → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ 𝔐.X), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier) (A : FlagPair B (CMType H) D.p D.q), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ((∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i)) → (∀ τ (i : Fin D.p), |Ht.lineHt (x (τ, Fin.castAdd D.q i)) L w - (A.W τ).grDeg i| ≤ C) ∧ ∀ τ (i : Fin D.q), |Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w + (A.S τ).grDeg i.rev| ≤ C := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h x e hx hR
  obtain ⟨m, hm, hsw⟩ := GlobalTheory.T.flag_label_bases_exist E H D l Xo c Y S Ω K J y 𝔐 Fl
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hc : CharZero Ω := by
    haveI : CharZero c.F := inferInstance
    exact charZero_of_injective_ringHom 𝔐.cst.injective
  have hind : ∀ s, LinearIndependent Ω (Fl.b s) := by
    obtain ⟨c', u, _, _, _, h4, _⟩ := Fl.generic
    exact h4
  have hW : ∀ τ (i : Fin D.p), _ := fun τ i => one_label 𝔐.X Ω 𝔐.ξ K J y 𝔐.t.G 𝔐.Li 𝔐.M (𝔐.V (.inl τ)) D.p (Fl.b (.inl τ)) m i
    (e (τ, Fin.castAdd D.q i)) h (x (τ, Fin.castAdd D.q i)) hc 𝔐.all 𝔐.tie hm (hind _) (fun p => hsw (.inl τ) p)
    (isDegOn_inl Fl hR τ i) (hx _)
  have hS : ∀ τ (i : Fin D.q), _ := fun τ i => one_label 𝔐.X Ω 𝔐.ξ K J y 𝔐.t.G 𝔐.Li 𝔐.M (𝔐.V (.inr τ)) D.q (Fl.b (.inr τ)) m i.rev
    (e (τ, Fin.natAdd D.p i))⁻¹ h (dualLine (x (τ, Fin.natAdd D.p i))) hc 𝔐.all 𝔐.tie hm (hind _) (fun p => hsw (.inr τ) p)
    (isDegOn_inr Fl hR τ i) (isSmoothHerm_dualLine (hx _))
  choose CW hCW using hW
  choose CS hCS using hS
  refine ⟨∑ τ, ((∑ i, |CW τ i|) + ∑ i, |CS τ i|), ?_⟩
  intro L _ _ w z hw B MB A hfib hsub
  have hnn : ∀ τ, 0 ≤ (∑ i, |CW τ i|) + ∑ i, |CS τ i| := fun τ =>
    add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hτ : ∀ τ, (∑ i, |CW τ i|) + ∑ i, |CS τ i| ≤ ∑ τ, ((∑ i, |CW τ i|) + ∑ i, |CS τ i|) := fun τ =>
    Finset.single_le_sum (f := fun τ => (∑ i, |CW τ i|) + ∑ i, |CS τ i|) (fun τ _ => hnn τ) (Finset.mem_univ τ)
  constructor
  · intro τ i
    have := hCW τ i L w z hw B MB hfib (A.W τ) (hsub.1 τ)
    have h1 : |CW τ i| ≤ ∑ i, |CW τ i| :=
      Finset.single_le_sum (f := fun i => |CW τ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i, |CS τ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact this.trans ((le_abs_self _).trans (h1.trans ((le_add_of_nonneg_right h2).trans (hτ τ))))
  · intro τ i
    have := hCS τ i L w z hw B MB hfib (A.S τ) (hsub.2 τ)
    rw [lineHt_dualLine, ← abs_neg] at this
    have e1 : -(-Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w - (A.S τ).grDeg i.rev) =
      Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w + (A.S τ).grDeg i.rev := by ring
    rw [e1] at this
    have h1 : |CS τ i| ≤ ∑ i, |CS τ i| :=
      Finset.single_le_sum (f := fun i => |CS τ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i, |CW τ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact this.trans ((le_abs_self _).trans (h1.trans ((le_add_of_nonneg_left h2).trans (hτ τ))))

end GlobalTheory.CompanionTheory.Ar.RootHt
