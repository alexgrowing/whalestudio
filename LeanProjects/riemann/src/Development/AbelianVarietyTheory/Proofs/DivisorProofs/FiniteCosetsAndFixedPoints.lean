import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyFormGroupToPadicPointsComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedConjClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparableStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinPtsSep
open scoped Pointwise in
open IsDedekindDomain GlobalTheory.OrbFinAf GlobalTheory.OrbFinAf.AwayIrr in

theorem fin_cosets_away_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∃ R : Finset G.GAf, ∀ h : G.GAf, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∃ c : G.GAf, c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ L.K.toSubgroup, h = c * r * k := by
  intro p _ G L f hf β x t hx y₀ hsep0 hdeg
  set y : G.Cˣ := (y₀ : G.Cˣ × ℚˣ).1 with hy
  have hsep : (minpoly G.F (y : G.C)).Separable := hsep0
  set γ := toAfF G β x t hx y₀ with hγ
  have hg0 : ∀ v, ((piV G v γ : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G y v * (xV G x v)⁻¹ := fun v => piV_toAfF_fst G β x t hx y₀ v
  set T := GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) γ with hT
  set K := L.K.toSubgroup with hK
  obtain ⟨S, hSf⟩ := hf.2.2.2
  let Ω : Set G.GAf := ⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((K : Set G.GAf) ×ˢ (K : Set G.GAf))
  have hΩ : IsCompact Ω := S.isCompact_biUnion fun s _ =>
    (L.compact.prod L.compact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hsupp : ∀ g : G.GAf, f g ≠ 0 → g ∈ Ω := by
    intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hSf g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, e.symm⟩
  let Good : Set (AwayP p) := {v | piV G v '' Ω ⊆ IntV G v ∧
    (∀ g : Gv G v, g⁻¹ * piV G v γ * g ∈ IntV G v → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ),
      ∃ d ∈ IntV G v, g = c * d) ∧ ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v}
  have hGood : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), v ∈ Good := by
    filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G Ω hΩ, kottwitz_almost' G y hdeg hsep x (fun v => piV G v γ) hg0, GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem p G]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hL1 := fun v : AwayP p => local_fin' G v y hdeg hsep (xV G x v) (piV G v γ) (hg0 v) (piV G v '' Ω)
    (hΩ.image (GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit p G v))
  choose D₁ hD₁ hD₁g using hL1
  let D' : ∀ v : AwayP p, Set (Gv G v) := fun v => if v ∈ Good then IntV G v else D₁ v
  have hD'c : ∀ v, IsCompact (D' v) := by
    intro v; by_cases hv : v ∈ Good
    · simp only [D', if_pos hv]; exact GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace p G v
    · simp only [D', if_neg hv]; exact hD₁ v
  have hD'i : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D' v ⊆ IntV G v := by
    filter_upwards [hGood] with v hv
    simp only [D', if_pos hv]; exact le_rfl
  have key : ∀ g : G.GAf, g⁻¹ * γ * g ∈ Ω → ∃ c ∈ T, ∃ d ∈ {g : G.GAf | ∀ v, piV G v g ∈ D' v}, g = c * d := by
    intro g hg
    have hloc : ∀ v, ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ), ∃ d ∈ D' v, piV G v g = c * d := by
      intro v
      have hgv : (piV G v g)⁻¹ * piV G v γ * piV G v g ∈ piV G v '' Ω :=
        ⟨_, hg, by simp only [map_mul, map_inv]⟩
      by_cases hv : v ∈ Good
      · obtain ⟨c, hc, d, hd, e⟩ := hv.2.1 _ (hv.1 hgv)
        exact ⟨c, hc, d, by simp only [D', if_pos hv]; exact hd, e⟩
      · obtain ⟨c, hc, d, hd, e⟩ := hD₁g v _ hgv
        exact ⟨c, hc, d, by simp only [D', if_neg hv]; exact hd, e⟩
    choose c hc d hd e using hloc
    have hcint : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), c v ∈ IntV G v := by
      filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G {g} isCompact_singleton, hGood] with v h1 h2
      have hdv : d v ∈ IntV G v := by have := hd v; simp only [D', if_pos h2] at this; exact this
      have ec : c v = piV G v g * (d v)⁻¹ := by rw [e v]; group
      rw [ec]
      exact h2.2.2 _ (h1 ⟨g, rfl, rfl⟩) _ (inv_mem_IntV G v hdv)
    obtain ⟨tt, htt⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local p G c hcint
    refine ⟨tt, ?_, tt⁻¹ * g, ?_, by group⟩
    · show tt * γ = γ * (MonoidHom.id _) tt
      apply GlobalTheory.T.unitaryAdelicPoint_ext_of_components p G
      intro v
      have h1 : c v * piV G v γ = piV G v γ * (MonoidHom.id _) (c v) := hc v
      simp only [map_mul, htt, MonoidHom.id_apply] at h1 ⊢
      exact h1
    · intro v
      have : piV G v (tt⁻¹ * g) = d v := by rw [map_mul, map_inv, htt, e v]; group
      rw [this]; exact hd v
  set D := {g : G.GAf | ∀ v, piV G v g ∈ D' v}
  have hD : IsCompact D := GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts p G D' hD'c hD'i
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : G.GAf => d • (K : Set G.GAf))
    (fun d => L.K.isOpen.smul d) (fun d _ => Set.mem_iUnion.2 ⟨d, ⟨1, one_mem _, mul_one d⟩⟩)
  refine ⟨I, fun h hh => ?_⟩
  obtain ⟨c, hc, d, hd, e⟩ := key _ (hsupp _ hh)
  obtain ⟨i, hi, hdi⟩ := Set.mem_iUnion₂.1 (hI hd)
  obtain ⟨k, hk, rfl⟩ := hdi
  refine ⟨c, hc, i, hi, k, hk, ?_⟩
  rw [e]; simp only [smul_eq_mul]; group

end GlobalTheory.FinPtsSep

noncomputable section

namespace GlobalTheory.FinPtsSep

variable {p : ℕ} [Fact p.Prime]

theorem exists_finset_doubleCoset_cover_of_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (y₀ : grp G β),
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ R : Finset (Gr G 1), ∀ h : Gr G 1, f' (h⁻¹ * toP1 G β y₀ * h) ≠ 0 →
      ∃ c : Gr G 1, c * toP1 G β y₀ = toP1 G β y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ K', h = c * r * k := by
  intro p _ G K' f' hT β y₀ hsep hdeg
  obtain ⟨hcomm, -, -, S₀, hS₀⟩ := hT
  obtain ⟨S, hS⟩ := GlobalTheory.FinAtP.prod_fin G (toP1 G β y₀)
    (fun w => by rw [GlobalTheory.FinAtP.charpoly_formGroupToPadicPoints_component]; exact (GlobalTheory.FinAtP.rho_charpoly_sep G w _ hdeg hsep).map) S₀
  obtain ⟨T, hT⟩ := GlobalTheory.FinAtP.exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hcomm.1
  refine ⟨(S ×ˢ T).image fun x => x.1 * x.2, fun h hh => ?_⟩
  obtain ⟨a, ha, s, hs, k, hk, rfl⟩ := hS h (hS₀ _ hh)
  obtain ⟨t, ht, k', hk', rfl⟩ := hT k hk
  exact ⟨a, ha, s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩, k', hk', by group⟩

theorem posV_toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) :
    0 < (star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hs := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have e : star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1)) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) * (star z.1 ⬝ᵥ (herm G v β *ᵥ z.1)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e]
  have hpos : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
  rw [show (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) = ((((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by exact_mod_cast hpos) z.2

def mapPosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) : PosV G v β :=
  ⟨(toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1, posV_toV G v β y z⟩

def conjC (G : HTGroup p) (y : G.Cˣ) : G.C ≃ₐ[G.F] G.C where
  toFun x := y * x * ((y⁻¹ : G.Cˣ) : G.C)
  invFun x := ((y⁻¹ : G.Cˣ) : G.C) * x * y
  left_inv x := by simp [_root_.mul_assoc]
  right_inv x := by simp [_root_.mul_assoc]
  map_mul' a b := by simp [_root_.mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' a := by
    show (y : G.C) * algebraMap G.F G.C a * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C a
    rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem minpoly_conjC (G : HTGroup p) (y g : G.Cˣ) :
    minpoly G.F ((y * g * y⁻¹ : G.Cˣ) : G.C) = minpoly G.F (g : G.C) := by
  have := minpoly.algEquiv_eq (conjC G y) (g : G.C)
  rw [← this]
  rfl

theorem fixL_conj (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g y : grp G β) (z : Fin G.n → ℂ)
    (h : FixL G v β (g * y * g⁻¹) z) : FixL G v β y ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
  calc (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
      = (toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β (g * y * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]
    _ = c • ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by rw [hc, Matrix.mulVec_smul]

theorem finite_pts_conj_fixL_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsees hsym htr y₀
  classical
  by_cases hne : ∃ (b : Dat G v β) (γ : grp G β), FixL G v β (γ * y₀ * γ⁻¹) b.2.1 ∧
      f (b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1) * f' (b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2) ≠ 0
  swap
  · convert Set.finite_empty
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨γ, h1, h2⟩
    exact hne ⟨_, γ, h1, h2⟩
  obtain ⟨b₀, γ₀, hfix₀, hne₀⟩ := hne
  have hsd : (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    have h := hsees (γ₀ * y₀ * γ₀⁻¹) b₀.1.1 (left_ne_zero_of_mul hne₀) ⟨b₀.2.1, b₀.2.2, hfix₀⟩
    have e : (((γ₀ * y₀ * γ₀⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) =
        ((γ₀ : G.Cˣ × ℚˣ).1) * ((y₀ : G.Cˣ × ℚˣ).1) * ((γ₀ : G.Cˣ × ℚˣ).1)⁻¹ := by simp
    rw [e, minpoly_conjC] at h
    exact h
  let z₀ : PosV G v β := mapPosV G v β γ₀⁻¹ b₀.2
  have hz₀ : FixL G v β y₀ z₀.1 := fixL_conj G v β γ₀ y₀ _ hfix₀
  obtain ⟨R1, hR1⟩ := fin_cosets_away_sep p G L f hf β x t hx y₀ hsd.2 hsd.1
  obtain ⟨R2, hR2⟩ := exists_finset_doubleCoset_cover_of_separable p G K' f' hf' β y₀ hsd.2 hsd.1
  have h3 := GlobalTheory.T.finite_classNumber_centraliserTorus_separable p G L K' hf'.1 β x t hx hsym y₀ hsd.2 hsd.1
  choose R3 hR3 using h3
  let Fs : Finset (G.GAf × Gr G 1) := (R1 ×ˢ R2).biUnion R3
  refine (Fs.finite_toSet.image (fun s => (Quot.mk _ (s, z₀) : Pts G v β x t hx L.K.toSubgroup K'))).subset ?_
  rintro q ⟨γ, hfix, hne⟩
  have hq : Quot.mk (Same G v β x t hx L.K.toSubgroup K') (Quot.out q) = q := Quot.out_eq q
  generalize Quot.out q = b at hfix hne hq
  have e1 : (toAfF G β x t hx γ⁻¹ * b.1.1)⁻¹ * toAfF G β x t hx y₀ * (toAfF G β x t hx γ⁻¹ * b.1.1) =
      b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1 := by
    simp only [map_mul, map_inv]; group
  have e2 : (toP1 G β γ⁻¹ * b.1.2)⁻¹ * toP1 G β y₀ * (toP1 G β γ⁻¹ * b.1.2) =
      b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2 := by
    simp only [map_mul, map_inv]; group
  obtain ⟨c1, hc1, r1, hr1, k1, hk1, hh1⟩ := hR1 _ (by rw [e1]; exact left_ne_zero_of_mul hne)
  obtain ⟨c2, hc2, r2, hr2, k2, hk2, hh2⟩ := hR2 _ (by rw [e2]; exact right_ne_zero_of_mul hne)
  obtain ⟨y, hy, s, hs, k3, hk31, hk32, hcr⟩ := hR3 (r1, r2) (c1, c2) (Prod.ext hc1 hc2)
  have hfix' : FixL G v β y₀ (mapPosV G v β γ⁻¹ b.2).1 := fixL_conj G v β γ y₀ _ hfix
  let w : PosV G v β := mapPosV G v β y⁻¹ (mapPosV G v β γ⁻¹ b.2)
  have hw : FixL G v β y₀ w.1 := by
    have e : y * y₀ * y⁻¹ = y₀ := by rw [hy]; group
    exact fixL_conj G v β y y₀ _ (by rw [e]; exact hfix')
  obtain ⟨c, hc⟩ := GlobalTheory.LKCx.fixL_pos_unique_of_sep p G v hv β hsym htr y₀ hsd.1 hsd.2 z₀.1 w.1 z₀.2 w.2 hz₀ hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := w.2
    rw [hc, zero_smul] at h
    simp at h
  have hb2 : b.2.1 = c • ((toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀.1) := by
    rw [← Matrix.mulVec_smul, ← hc]
    show b.2.1 = (toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β γ⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b.2.1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    simp
  have hb1 : b.1 = ((toAfF G β x t hx (γ * y), toP1 G β (γ * y)) : G.GAf × Gr G 1) * s * (k3 * (k1, k2)) := by
    have hh : ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) =
        (c1, c2) * (r1, r2) * (k1, k2) := Prod.ext hh1 hh2
    rw [hcr] at hh
    have hb : b.1 = ((toAfF G β x t hx γ, toP1 G β γ) : G.GAf × Gr G 1) *
        ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) := by
      ext <;> simp [← mul_assoc]
    rw [hb, hh]
    ext <;> simp [mul_assoc]
  have hsF : s ∈ Fs := Finset.mem_biUnion.2 ⟨(r1, r2), Finset.mem_product.2 ⟨hr1, hr2⟩, hs⟩
  refine ⟨s, hsF, ?_⟩
  rw [← hq]
  exact Quot.sound ⟨γ * y, k3 * (k1, k2), c, mul_mem hk31 hk1, mul_mem hk32 hk2, hc0, hb1, hb2⟩

end GlobalTheory.FinPtsSep
