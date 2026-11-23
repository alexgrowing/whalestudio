import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar GlobalTheory.ConjDS GlobalTheory.CoverDS GlobalTheory.Chain.RealIt.LocalFromCover
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverModel

section Bar

variable {n : ℕ} {ε ε' : Fin n → Bool}

def barRev (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := rv (g.map (starRingEnd ℂ))

theorem barRev_barRev (g : Matrix (Fin n) (Fin n) ℂ) : barRev (barRev g) = g := by
  ext i j; simp [barRev, rv]

theorem barRev_mul (g h : Matrix (Fin n) (Fin n) ℂ) : barRev (g * h) = barRev g * barRev h := by
  simp only [barRev, Matrix.map_mul, rv_mul]

theorem barRev_one : barRev (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [barRev, rv_one]

theorem barRev_ct (g : Matrix (Fin n) (Fin n) ℂ) : barRev gᴴ = (barRev g)ᴴ := rfl

theorem barRev_diag (d : Fin n → ℂ) : barRev (diagonal d) = diagonal fun a => starRingEnd ℂ (d a.rev) := by
  rw [barRev, Matrix.diagonal_map (map_zero _), rv_diag]

theorem barRev_cont : Continuous (barRev : Matrix (Fin n) (Fin n) ℂ → _) :=
  rv_cont.comp (continuous_id.matrix_map Complex.continuous_conj)

theorem barRev_Jm (he : ∀ a, ε' a = ε a.rev) : barRev (Formalism.REAL.Jm ε') = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [barRev_diag]
  simp only [← sg_symm he]
  congr 1
  funext a
  split_ifs <;> simp

theorem barRev_UJ (he : ∀ a, ε' a = ε a.rev) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε') :
    barRev g ∈ UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε' * g = Formalism.REAL.Jm ε' := hg
  show (barRev g)ᴴ * Formalism.REAL.Jm ε * barRev g = Formalism.REAL.Jm ε
  rw [← barRev_Jm he, ← barRev_ct, ← barRev_mul, ← barRev_mul, hg']

theorem barRev_K (he : ∀ a, ε' a = ε a.rev) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε') :
    barRev g ∈ Formalism.REAL.Kset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  refine ⟨(Matrix.mem_unitaryGroup_iff').2 ?_, ?_⟩
  · show (barRev g)ᴴ * barRev g = 1
    rw [← barRev_ct, ← barRev_mul, hg1, barRev_one]
  · rw [← barRev_Jm he, ← barRev_mul, ← barRev_mul, hg.2]

def barRevU (he : ∀ a, ε' a = ε a.rev) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨⟨barRev g.1.1, barRev g.1.2, by rw [← barRev_mul, g.1.3, barRev_one],
    by rw [← barRev_mul, g.1.4, barRev_one]⟩, barRev_UJ he g.2⟩
  invFun g := ⟨⟨barRev g.1.1, barRev g.1.2, by rw [← barRev_mul, g.1.3, barRev_one],
    by rw [← barRev_mul, g.1.4, barRev_one]⟩, barRev_UJ (sg_symm he) g.2⟩
  left_inv g := Subtype.ext (Units.ext (barRev_barRev _))
  right_inv g := Subtype.ext (Units.ext (barRev_barRev _))
  map_mul' g h := Subtype.ext (Units.ext (barRev_mul _ _))

theorem barRevU_cont (he : ∀ a, ε' a = ε a.rev) : Continuous (barRevU he) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact barRev_cont.comp (Units.continuous_val.comp continuous_subtype_val)
  · exact barRev_cont.comp (Units.continuous_coe_inv.comp continuous_subtype_val)

theorem memLp_barRev (he : ∀ a, ε' a = ε a.rev) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ barRevU he) 2 (Formalism.REAL.muG ε') := by
  haveI : ((Formalism.REAL.muG ε').map (barRevU he)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ (barRevU he) (barRevU_cont he) (barRevU_cont (sg_symm he))
  refine MemLp.comp_of_map ?_ (barRevU_cont he).measurable.aemeasurable
  rw [Measure.isMulLeftInvariant_eq_smul ((Formalism.REAL.muG ε').map (barRevU he)) (Formalism.REAL.muG ε)]
  exact hF.smul_measure ENNReal.coe_ne_top

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem wt_barRev (he : ∀ a, ε' a = ε a.rev) (h : ∀ g, σ g = σ' (barRev g))
    {μ : Fin n → ℝ} {v : H} (hv : IsWtOn (Formalism.REAL.Kset ε') σ' μ v) :
    IsWtOn (Formalism.REAL.Kset ε) σ (nr μ) v := by
  intro θ hθ
  have h1 := barRev_K (sg_symm he) hθ
  have h2 : barRev (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      diagonal fun a : Fin n => Complex.exp (((-θ a.rev : ℝ) : ℂ) * Complex.I) := by
    rw [barRev_diag]
    congr 1
    funext a
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  rw [h2] at h1
  rw [h, h2, hv (fun a => -θ a.rev) h1]
  have : ∑ a, nr μ a * θ a = ∑ a, μ a * -θ a.rev :=
    Fintype.sum_equiv Fin.revPerm _ _ fun a => by simp [nr]
  rw [this]

theorem ktype_barRev (he : ∀ a, ε' a = ε a.rev) (h : ∀ g, σ g = σ' (barRev g))
    {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε' σ' Λ S) : IsKTypeOf ε σ (nr Λ) S := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  have h' : ∀ g, σ' g = σ (barRev g) := fun g => by rw [h, barRev_barRev]
  refine ⟨h1, fun g hg x hx => ?_, fun S' hle hst => h3 S' hle fun g hg x hx => ?_,
    ⟨v, hv, hv0, wt_barRev (σ := σ) (σ' := σ') he h hvw⟩, fun μ x hx h0 hw => ?_⟩
  · rw [h]; exact h2 _ (barRev_K (sg_symm he) hg) _ hx
  · rw [h']; exact hst _ (barRev_K he hg) _ hx
  · have h6 := cdom_rev he (h5 (nr μ) x hx h0 (wt_barRev (σ := σ') (σ' := σ) (sg_symm he) h' hw))
    rwa [nr_nr] at h6

theorem isDS_barRev (he : ∀ a, ε' a = ε a.rev) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) :
    IsDS ε' (nr lam) fun g => σ (barRev g) := by
  obtain ⟨c1, c2, ⟨⟨r1, r2⟩, r3, r4⟩, c4, c5, ⟨S, hS⟩, c7⟩ := hσ
  refine ⟨c1, c2, ⟨⟨by simp only [barRev_one, r1], fun a ha b hb => ?_⟩, fun g hg => r3 _ (barRev_UJ he hg), fun v => ?_⟩,
    fun S' hcl hst => c4 S' hcl fun g hg x hx => ?_, fun v w => ?_,
    ⟨S, by rw [lowK_rev he lam]; exact ktype_barRev (σ' := σ) (sg_symm he) (fun _ => rfl) hS⟩, fun μ S' hS' => ?_⟩
  · simp only [barRev_mul, r2 _ (barRev_UJ he ha) _ (barRev_UJ he hb)]
  · exact ContinuousOn.comp (g := fun g => σ g v) (r4 v) barRev_cont.continuousOn fun g hg => barRev_UJ he hg
  · have := hst _ (barRev_UJ (sg_symm he) hg) x hx
    simpa only [barRev_barRev] using this
  · have : coefOn (ε := ε') (fun g => σ (barRev g)) v w = coefOn (ε := ε) σ v w ∘ barRevU he := funext fun _ => rfl
    rw [this]
    exact memLp_barRev he (c5 v w)
  · have := c7 _ _ (ktype_barRev (σ := σ) (σ' := fun g => σ (barRev g)) he (fun g => by rw [barRev_barRev]) hS')
    rw [lowK_rev he, vNormSq_rev he]
    rwa [vNormSq_rev (sg_symm he)] at this

end Bar

section Cover

variable {p q n : ℕ} {T : GrpData p q}

theorem exists_pull (T : GrpData p q)
    (hM : ∀ U : URep T, Formalism.MainNotions.SchurIrreducible.IrrU U → ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io)
    (P : SignedPar n) {e : Ix p q ≃ Fin n} (h : BlockOrd e P.sgn) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDSPar P σ) :
    ∃ (R : DSRep T) (U : H ≃ₗᵢ[ℂ] R.U.H), HasParam R (blockPar P e) ∧
      ∀ g x, R.U.π g (U x) = U (σ (Matrix.reindex e e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) := by
  haveI : CompleteSpace H := hσ.1
  have hU := hσ.2.2.1
  have hirr : Formalism.MainNotions.SchurIrreducible.IrrU (GlobalTheory.Published.CoverSeries.pull h T hU) :=
    ⟨hσ.2.1, fun S hS hst => hσ.2.2.2.1 S hS fun g hg v hv => by
      obtain ⟨x, rfl⟩ := h.cov_surj T hg
      exact hst x v hv⟩
  obtain ⟨M, io, m1, m2, m3⟩ := hM _ hirr
  haveI := SqInt.isHaarMeasure_map_covU h T
  have hμ := Measure.isMulLeftInvariant_eq_smul (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn)
  obtain ⟨d, hd, hI⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n P.sgn P.lam H σ hσ _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn))
  refine ⟨⟨GlobalTheory.Published.CoverSeries.pull h T hU, hirr.1, hirr.2, d, hd, fun x y => ?_, M, io, m1, m2, m3⟩,
    LinearIsometryEquiv.refl ℂ H, ?_, fun _ _ => rfl⟩
  · change H at x y
    obtain ⟨i1, i2⟩ := hI x y x y
    rw [← ENNReal.smul_def, ← hμ] at i1 i2
    have hf : (fun g => coefOn (ε := P.sgn) σ x y g * star (coefOn (ε := P.sgn) σ x y g)) =
        fun g => ((‖coefOn (ε := P.sgn) σ x y g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hf] at i1 i2
    have hm := (SqInt.continuous_covU h T).measurable.aemeasurable (μ := T.haar)
    rw [integral_map hm i1.aestronglyMeasurable] at i2
    have i3 := (integrable_map_measure i1.aestronglyMeasurable hm).1 i1
    refine ⟨i3.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at i2
    have i4 : ((∫ g, ‖coefOn (ε := P.sgn) σ x y (SqInt.covU h T g)‖ ^ 2 ∂T.haar : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      push_cast
      exact i2
    exact_mod_cast i4
  · exact (hasParam_iff_isDSPar _ P h (σ := σ) fun _ => rfl).2 hσ

theorem isParam_add_half {lam : Ix p q → ℚ} (hl : IsParam lam) (k : ℤ) : IsParam fun a => lam a + k / 2 :=
  ⟨fun x y e => hl.1 (add_left_injective _ e), fun x y e => by simpa using hl.2.1 x y e,
    fun x => by
      obtain ⟨j, hj⟩ := hl.2.2.1 x
      exact ⟨j + k, by push_cast; linarith⟩,
    fun x y => by simpa using hl.2.2.2 x y⟩

theorem exists_twist_equiv (hD : GlobalTheory.Published.DiscreteSeriesCover) (hn : 1 ≤ p + q) (m : ℤ) :
    ∀ lam : Ix p q → ℚ, IsParam lam → ∀ R R' : DSRep T, HasParam R (fun a => lam a + m / 2) → HasParam R' lam →
      ∃ U : R.U.H ≃ₗᵢ[ℂ] R'.U.H, ∀ g x, R'.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (R.U.π g x) := by
  induction m using Int.induction_on with
  | zero =>
    intro lam hl R R' h h'
    obtain ⟨U, hU⟩ := unitEquiv_of_hasParam hD hn hl (by simpa using h) h'
    exact ⟨U, fun g x => by simp [hU]⟩
  | succ k ih =>
    intro lam hl R R' h h'
    obtain ⟨U, hU⟩ : ∃ U : R.U.H ≃ₗᵢ[ℂ] R'.U.H, ∀ g x, R'.U.π g (U x) =
        ((T.sq g : ℂˣ) : ℂ) ^ (-(k : ℤ)) • U (((T.sq g : ℂˣ) : ℂ)⁻¹ • R.U.π g x) :=
      ih lam hl (Cover.twist R) R' ((Cover.hasParam_twist R _).2 (by convert h using 2; push_cast; ring)) h'
    refine ⟨U, fun g x => (hU g x).trans ?_⟩
    rw [map_smul, smul_smul, neg_add, zpow_add₀ (Units.ne_zero _), _root_.zpow_neg_one]
  | pred k ih =>
    intro lam hl R R' h h'
    obtain ⟨U, hU⟩ : ∃ U : R.U.H ≃ₗᵢ[ℂ] R'.U.H, ∀ g x, ((T.sq g : ℂˣ) : ℂ)⁻¹ • R'.U.π g (U x) =
        ((T.sq g : ℂˣ) : ℂ) ^ (- -(k : ℤ)) • U (R.U.π g x) :=
      ih _ (isParam_add_half hl (-1)) R (Cover.twist R') (by convert h using 2; push_cast; ring)
        ((Cover.hasParam_twist R' _).2 (by convert h' using 2; push_cast; ring))
    refine ⟨U, fun g x => ?_⟩
    have h1 := hU g x
    rw [inv_smul_eq_iff₀ (Units.ne_zero _), smul_smul] at h1
    rw [h1, neg_sub, sub_eq_add_neg, zpow_add₀ (Units.ne_zero _), zpow_one]

theorem exists_numbering {l₁ l₂ : List ℚ} {c : ℚ} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h₁ : l₁.length = p)
    (h₂ : l₂.length = q) (hl : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ))
    (hE : IsEnum (dualPar (GlobalTheory.Chain.signed l₁ l₂ c)) lam ε) :
    ∃ e : Ix p q ≃ Fin n, BlockOrd e (fun a => ε a.rev) ∧
      ∀ a, nr lam (e a) = (((ofBlocks l₁ l₂ : Ix p q → ℚ) a + c : ℚ) : ℝ) := by
  obtain ⟨hs, r, hr, hS⟩ := hE
  let f : Ix p q → ℚ × Bool := fun a => (-((ofBlocks l₁ l₂ : Ix p q → ℚ) a + c), a.isLeft)
  let g : Fin n → ℚ × Bool := fun a => (r a, ε a)
  have hf : Function.Injective f := fun a b h => hl.1 (by simpa [f] using congrArg Prod.fst h)
  have hg : Function.Injective g := fun a b h => hs.injective (by
    rw [hr, hr, show r a = r b from congrArg Prod.fst h])
  have hrange : Set.range f = Set.range g := by
    rw [← Set.image_univ (f := g), ← Finset.coe_univ, ← Finset.coe_image, ← hS]
    subst h₁ h₂
    ext x
    simp only [dualPar, GlobalTheory.Chain.signed, Set.mem_range, Sum.exists, Finset.coe_image, Finset.coe_union,
      List.coe_toFinset, List.mem_map, Set.mem_image, Set.mem_union, f, ofBlocks, Set.mem_setOf_eq]
    simp only [List.mem_iff_get]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨_, .inl ⟨_, ⟨i, rfl⟩, rfl⟩, by simp⟩
      · exact ⟨_, .inr ⟨_, ⟨i, rfl⟩, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      · exact .inl ⟨i, by simp⟩
      · exact .inr ⟨i, by simp⟩
  let e₀ : Ix p q ≃ Fin n := (Equiv.ofInjective f hf).trans ((Equiv.setCongr hrange).trans (Equiv.ofInjective g hg).symm)
  have he : ∀ a, g (e₀ a) = f a := fun a => by
    simp only [e₀, Equiv.trans_apply, Equiv.apply_ofInjective_symm]
    rfl
  have h1 : ∀ a, lam (e₀ a) = -((((ofBlocks l₁ l₂ : Ix p q → ℚ) a + c : ℚ)) : ℝ) := fun a => by
    rw [hr, show r (e₀ a) = _ from congrArg Prod.fst (he a)]
    push_cast [f]
    ring
  have h2 : ∀ a, ε (e₀ a) = a.isLeft := fun a => congrArg Prod.snd (he a)
  refine ⟨e₀.trans Fin.revPerm, ⟨fun i => by simp [h2], fun j => by simp [h2], fun a b hab => ?_⟩,
    fun a => by simp [nr, h1]⟩
  refine Fin.rev_lt_rev.2 (hs.lt_iff_gt.1 ?_)
  rw [h1, h1, neg_lt_neg_iff]
  exact_mod_cast add_lt_add_left (hl.2.1 a b hab) c

end Cover

section Match

variable {p q n : ℕ}

structure IsFormIso (ε : Fin n → Bool) (φ : Mat p q → Matrix (Fin n) (Fin n) ℂ) : Prop where
  bij : Function.Bijective φ
  mul : ∀ a b, φ (a * b) = φ a * φ b
  add : ∀ a b, φ (a + b) = φ a + φ b
  ct : ∀ a, φ aᴴ = (φ a)ᴴ
  form : φ (Jm p q) = Formalism.REAL.Jm ε
  exp : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z))

variable {ε : Fin n → Bool} {φ : Mat p q → Matrix (Fin n) (Fin n) ℂ}

theorem isFormIso_plainMat {e : Ix p q ≃ Fin n} (h : SignCompat ε e) : IsFormIso ε (plainMat e) where
  bij := (Matrix.reindex e e).bijective
  mul a b := by simp [plainMat]
  add _ _ := rfl
  ct _ := rfl
  form := reindex_form h
  exp := exp_plainMat e

theorem isFormIso_barMat {e : Ix p q ≃ Fin n} (h : SignCompat ε e) : IsFormIso ε (barMat e) where
  bij := (Matrix.reindex e e).bijective.comp (Function.Involutive.bijective
    (f := fun g : Mat p q => g.map (starRingEnd ℂ)) fun g => by ext a b; simp)
  mul a b := by simp [barMat, Matrix.map_mul]
  add a b := by ext; simp [barMat]
  ct _ := rfl
  form := by
    have hJ : (Jm p q).map (starRingEnd ℂ) = Jm p q := by
      conv_rhs => rw [← KStabLie.Jm_ct, KStabLie.Jm_eq, Matrix.diagonal_conjTranspose]
      rw [KStabLie.Jm_eq, Matrix.diagonal_map (map_zero _)]
      rfl
    rw [barMat, hJ]
    exact reindex_form h
  exp := exp_barMat e

theorem IsFormIso.mem_UJ (h : IsFormIso ε φ) (g : Mat p q) : φ g ∈ UJset ε ↔ gᴴ * Jm p q * g = Jm p q := by
  change (φ g)ᴴ * Formalism.REAL.Jm ε * φ g = Formalism.REAL.Jm ε ↔ _
  rw [← h.form, ← h.ct, ← h.mul, ← h.mul, h.bij.1.eq_iff]

theorem IsFormIso.mem_lie (h : IsFormIso ε φ) (Z : Mat p q) : Formalism.REAL.inG ε (φ Z) ↔ Z ∈ upq p q := by
  have h0 : φ 0 = 0 := by
    have := h.add 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  change (φ Z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * φ Z = 0 ↔ Zᴴ * Jm p q + Jm p q * Z = 0
  rw [← h.form, ← h.ct, ← h.mul, ← h.mul, ← h.add, ← h0, h.bij.1.eq_iff]

theorem mem_K_iff {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ Formalism.REAL.Kset ε ↔ g ∈ UJset ε ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := by
  refine and_congr_left fun h3 => ?_
  change _ ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc]
  refine ⟨fun h => by rw [h, one_mul], fun h1 => ?_⟩
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h1
  simpa only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] using h4

theorem IsFormIso.mem_K (h : IsFormIso ε φ) (T : GrpData p q) (x : T.G) :
    φ ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.REAL.Kset ε ↔ x ∈ T.Kset := by
  rw [mem_K_iff, ← h.form, ← h.mul, ← h.mul, h.bij.1.eq_iff, ← KStabLie.isKC_iff]
  exact and_iff_right ((h.mem_UJ _).2 (T.cov_mem x))

theorem IsFormIso.surj (h : IsFormIso ε φ) (T : GrpData p q) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ x : T.G, φ ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  obtain ⟨g, rfl⟩ := h.bij.2 g
  have h1 := (h.mem_UJ g).1 hg
  have hJ : (Jm p q).det ≠ 0 :=
    left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, KStabLie.Jm_sq, Matrix.det_one])
  have hd : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ this.symm
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq g.det two_pos
  have hw0 : w ≠ 0 := by rintro rfl; exact hd (by simpa using hw.symm)
  obtain ⟨x, hx, -⟩ := T.bij (Matrix.GeneralLinearGroup.mkOfDetNeZero g hd) h1 (Units.mk0 w hw0) hw
  exact ⟨x, by rw [hx.1]; rfl⟩

variable {s : ℂ →+* ℂ} [RingHomInvPair s s] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

theorem finite_comap' (U : H ≃ₛₗᵢ[s] H') (S : Submodule ℂ H') [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (S.comap (U.toLinearEquiv : H →ₛₗ[s] H')) := by
  obtain ⟨b, hb⟩ : S.FG := Module.Finite.iff_fg.1 inferInstance
  haveI := FiniteDimensional.span_of_finite ℂ (b.finite_toSet.image (U.symm.toLinearEquiv : H' →ₛₗ[s] H))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ ((U.symm.toLinearEquiv : H' →ₛₗ[s] H) '' (b : Set H'))) fun x hx => ?_
  rw [← Submodule.map_span, hb]
  exact ⟨U x, hx, U.symm_apply_apply x⟩

theorem kFin_iff (h : IsFormIso ε φ) {T : GrpData p q} {π : T.G →* (H' →L[ℂ] H')}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (U : H ≃ₛₗᵢ[s] H') {c : T.G → ℂ} (hc : ∀ g, c g ≠ 0)
    (hU : ∀ g x, π g (U x) = c g • U (σ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)) (x : H) :
    IsKFin ε σ x ↔ KFin T π (U x) := by
  constructor
  · rintro ⟨S, hS, hx, hK⟩
    haveI := finite_comap' U.symm S
    refine Submodule.finiteDimensional_of_le (S₂ := S.comap (U.symm.toLinearEquiv : H' →ₛₗ[s] H))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    beta_reduce
    rw [hU]
    refine Submodule.smul_mem _ _ ?_
    change U.symm (U _) ∈ S
    rw [U.symm_apply_apply]
    exact hK _ ((h.mem_K T k).2 k.2) x hx
  · intro hx
    unfold KFin at hx
    have h1 : (1 : T.G) ∈ T.Kset := (KStabLie.isKC_iff _).2 (by simp)
    refine ⟨_, finite_comap' U (Submodule.span ℂ (Set.range fun k : T.Kset => π k (U x))),
      Submodule.subset_span ⟨⟨1, h1⟩, by simp⟩, fun g hg y hy => ?_⟩
    obtain ⟨k, rfl⟩ := h.surj T (mem_K_iff.1 hg).1
    have hk := (h.mem_K T k).1 hg
    have h2 : (Submodule.span ℂ (Set.range fun k : T.Kset => π k (U x))).map (π k : H' →ₗ[ℂ] H') ≤
        Submodule.span ℂ (Set.range fun k : T.Kset => π k (U x)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨j, rfl⟩
      have hj : k * j ∈ T.Kset := (KStabLie.isKC_iff _).2 (by
        rw [map_mul, Units.val_mul, mul_assoc, (KStabLie.isKC_iff _).1 j.2, ← mul_assoc,
          (KStabLie.isKC_iff _).1 hk, mul_assoc])
      exact Submodule.subset_span ⟨⟨_, hj⟩, by simp⟩
    have h3 : π k (U y) ∈ _ := h2 ⟨U y, hy, rfl⟩
    rw [hU, Submodule.smul_mem_iff _ (hc k)] at h3
    exact h3

def realCLM (hs : ∀ r : ℝ, s r = r) (U : H ≃ₛₗᵢ[s] H') : H →L[ℝ] H' where
  toFun := U
  map_add' := map_add U
  map_smul' r x := by
    rw [← Complex.coe_smul, map_smulₛₗ, hs, Complex.coe_smul, RingHom.id_apply]
  cont := U.continuous

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem toFrame_image (M : DSModel V S) (τ : D.what₂.Tau) :
    toFrame M τ '' {Y | Formalism.REAL.inG (M.ε τ) Y} = lieAt V τ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ X, (M.fr τ)ᴴ * ((M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) +
      Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹)) * M.fr τ = Xᴴ * gramAt D V τ + gramAt D V τ * X := by
    intro X
    have h1 : (M.fr τ)ᴴ * ((M.fr τ)⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.conjTranspose_one]
    rw [← M.fr_gram τ]
    simp only [Matrix.conjTranspose_mul, mul_add, add_mul, ← mul_assoc, h1, one_mul]
    simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, mul_one]
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change _ + _ = 0
    rw [← key, fr_toFrame, show Yᴴ * _ + _ = 0 from hY, mul_zero, zero_mul]
  · intro hX
    refine ⟨M.fr τ * X * (M.fr τ)⁻¹, ?_, ?_⟩
    · have h2 := (key X).trans hX
      rwa [(M.fr_unit τ).mul_left_eq_zero, ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul_right_eq_zero] at h2
    · rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul, mul_assoc,
        Matrix.nonsing_inv_mul _ hd, mul_one]

theorem matches_of_grp (hH : GlobalTheory.Published.HarishChandraModules) (hs : ∀ r : ℝ, s r = r) {T : GrpData p q} (R : DSRep T)
    (M : DSModel V S) (τ : D.what₂.Tau) {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsFormIso (M.ε τ) φ) (m : ℤ) (U : M.H τ ≃ₛₗᵢ[s] R.U.H)
    (hU : ∀ (g : T.G) (x : M.H τ), R.U.π g (U x) =
      ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)) :
    Matches R M τ φ m U := by
  classical
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hk : ∀ x, IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι := fun x =>
    (kFin_iff h U (fun g => zpow_ne_zero _ (Units.ne_zero _)) hU x).trans (R.ι_range _).symm
  have hder : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x)
        (U.symm (R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v))) 0 := by
    intro Z hZ v x hx
    have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ v)
    have h2 := (realCLM hs U.symm).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    convert h2 using 1
    · funext t
      apply U.injective
      change _ = U (U.symm _)
      rw [U.apply_symm_apply, rep_exp, h.exp, ← hx]
      beta_reduce
      rw [hU, T.expt_cov _ (KStabLie.smul_mem_upq hZ t), smul_smul,
        ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
    · change _ = U.symm _
      rw [show (m : ℂ) * (Z.trace / 2) = m / 2 * Z.trace by ring]
      simp [T.expt_zero]
  refine ⟨hU, hk, fun x hx => ?_, ?_, fun Z hZ v x hx => ?_, fun Z hZ v x y hx hy w => ?_⟩
  · exact hH.smoothVec (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 ((hk x).2 hx) (M.fr_unit τ) (M.fr_gram τ)
  · rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) φ]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := h.bij.2 Y
    rw [h.bij.1.mem_set_image, ← h.mem_lie]
    rfl
  · rw [dRep, (hder Z hZ v x hx).deriv, U.apply_symm_apply]
  · have h1 := hder Z hZ v _ hx
    rw [← hy, U.symm_apply_apply] at h1
    have h2 := (((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).mul_const
      (∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (x ρ : M.H ρ)⟫_ℂ)
    refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
    · simp only [ellT, actT, inclT, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
      congr 1
      · simp
      · exact Finset.prod_congr rfl fun ρ hρ => by simp [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
    · simp only [ellT, inclT, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
      congr 1
      · simp
      · exact Finset.prod_congr rfl fun ρ hρ => by simp [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

end Match

section Bridge

variable {p q n : ℕ}

theorem exists_renumber {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {e e' : Ix p q ≃ Fin n}
    (h : SignCompat ε e) (h' : SignCompat ε e') :
    ∃ A : H ≃ₗᵢ[ℂ] H, ∀ g : Mat p q, plainMat e g ∈ UJset ε → ∀ x,
      σ (plainMat e' g) (A x) = A (σ (plainMat e g) x) := by
  have key : ∀ {e e' : Ix p q ≃ Fin n}, SignCompat ε e → SignCompat ε e' →
      Matrix.reindex e' e (1 : Mat p q) ∈ UJset ε := by
    intro e e' h h'
    change (Matrix.reindex e' e (1 : Mat p q))ᴴ * Formalism.REAL.Jm ε * Matrix.reindex e' e (1 : Mat p q) = Formalism.REAL.Jm ε
    conv_lhs => rw [← reindex_form h']
    rw [← reindex_form h]
    simp
  have inv : ∀ {e e' : Ix p q ≃ Fin n}, SignCompat ε e → SignCompat ε e' → ∀ x,
      σ (Matrix.reindex e' e (1 : Mat p q)) (σ (Matrix.reindex e e' (1 : Mat p q)) x) = x := by
    intro e e' h h' x
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (key h h') _ (key h' h)]
    simp [hσ.1.1]
  refine ⟨⟨⟨(σ (Matrix.reindex e' e (1 : Mat p q)) : H →ₗ[ℂ] H), σ (Matrix.reindex e e' (1 : Mat p q)),
    inv h' h, inv h h'⟩, hσ.2.1 _ (key h h')⟩, fun g hg x => ?_⟩
  have hg' : plainMat e' g ∈ UJset ε := ((isFormIso_plainMat h').mem_UJ g).2 (((isFormIso_plainMat h).mem_UJ g).1 hg)
  change σ _ (σ (Matrix.reindex e' e (1 : Mat p q)) x) = σ (Matrix.reindex e' e (1 : Mat p q)) (σ _ x)
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hg' _ (key h h'), ← ContinuousLinearMap.comp_apply,
    ← hσ.1.2 _ (key h h') _ hg]
  simp [plainMat]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem bridge (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (X : ProvA)
    (M : DSModel V S) (τ : D.what₂.Tau) {l₁ l₂ : List ℚ} {c : ℚ} (hS : HidaSetting X p q l₁ l₂ c S τ)
    {s : ℂ →+* ℂ} [RingHomInvPair s s] (hs : ∀ r : ℝ, s r = r) (ψ : Mat p q → Mat p q)
    (hψ : ∀ e, SignCompat (M.ε τ) e → IsFormIso (M.ε τ) fun g => plainMat e (ψ g))
    {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ' : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H' →L[ℂ] H')} (hσ' : IsDS (fun a => M.ε τ a.rev) (nr (M.lam τ)) σ')
    (C : M.H τ ≃ₛₗᵢ[s] H') (hC : ∀ (e : Ix p q ≃ Fin V.rank) g x,
      σ' (plainMat e g) (C x) = C (M.σ τ (plainMat (e.trans Fin.revPerm) (ψ g)) x)) :
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₛₗᵢ[s] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (fun g => plainMat e (ψ g)) m U := by
  obtain ⟨hn, h₁, h₂, hl, hX, hτ⟩ := hS
  obtain ⟨e₁, he₁, hlam⟩ := exists_numbering h₁ h₂ hl (hτ ▸ M.enum τ)
  have he' : SignCompat (M.ε τ) (e₁.trans Fin.revPerm) := by
    rintro (a | a)
    · exact he₁.1 a
    · exact he₁.2.1 a
  let P : SignedPar V.rank := ⟨nr (M.lam τ), fun a => M.ε τ a.rev,
    GlobalTheory.DSParam.isHCParam_of_isDS _ _ _ _ _ (isEnum_dual (M.enum τ)).1 hσ'⟩
  have hP : ∀ a, blockPar P e₁ a = (ofBlocks l₁ l₂ : Ix p q → ℚ) a + c := fun a => by
    have : ((blockPar P e₁ a : ℚ) : ℝ) = _ := (ratEntry_cast P (e₁ a)).trans (hlam a)
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℚ) = 2 * c := by
    obtain ⟨a⟩ : Nonempty (Ix p q) := Fintype.card_pos_iff.1 (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; exact hn)
    obtain ⟨j, hj⟩ := (isParam_blockPar P he₁).2.2.1 a
    obtain ⟨k, hk⟩ := hl.2.2.1 a
    rw [hP] at hj
    exact ⟨j - k, by push_cast; linarith⟩
  refine ⟨⟨_, he'⟩, m, hm, fun e he => ?_⟩
  obtain ⟨R, U₀, hR, hU₀⟩ := exists_pull (X.grp p q) (fun U hU => ((hH.1 p q hn _).1 U hU).2.1) P he₁ hσ'
  obtain ⟨U₁, hU₁⟩ := exists_twist_equiv hD hn m _ hl R _ (by
    convert hR using 2
    rw [hP, hm]
    ring) hX
  obtain ⟨A, hA⟩ := exists_renumber (M.ds τ).2.2.1 he he'
  refine ⟨A.trans (C.trans (U₀.trans U₁)), matches_of_grp hH hs _ M τ (hψ e he) m _ fun g x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [hU₁, hU₀, ← plainMat, hC, hA _ (((hψ e he).mem_UJ _).2 ((X.grp p q).cov_mem g))]

theorem modelsAreCoverSeries (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) :
    ModelsAreCoverSeries D :=
  ⟨fun X _ _ M τ _ _ _ _ _ hS => bridge hD hH X M τ hS (s := RingHom.id ℂ) (fun _ => rfl)
      (fun g => g.map (starRingEnd ℂ)) (fun _ he => isFormIso_barMat he)
      (isDS_barRev (fun _ => rfl) (M.ds τ)) (LinearIsometryEquiv.refl ℂ _) fun _ _ _ => rfl,
    fun X _ _ M τ _ _ _ _ _ hS => bridge hD hH X M τ hS (s := starRingEnd ℂ) Complex.conj_ofReal
      (fun g => g) (fun _ he => isFormIso_plainMat he) ((conjModel M).ds τ) (cj (M.H τ)).symm fun _ _ _ => rfl⟩

end Bridge

end GlobalTheory.CoverModel

end
