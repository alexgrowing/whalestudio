import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmoothStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Alg

open Polynomial

theorem exists_sep_poly {E : Type} [Field E] [NumberField E] (w : 𝓞 E) :
    ∃ f : ℤ[X], f.Monic ∧ aeval w f = 0 ∧ aeval w (derivative f) ≠ 0 := by
  have hw : IsIntegral ℤ (w : E) := RingOfIntegers.isIntegral_coe w
  have e : ∀ p : ℤ[X], aeval (w : E) p = algebraMap (𝓞 E) E (aeval w p) :=
    fun p => aeval_algebraMap_apply E w p
  refine ⟨minpoly ℤ (w : E), minpoly.monic hw, ?_, ?_⟩
  · apply RingOfIntegers.coe_injective
    have := e (minpoly ℤ (w : E))
    rw [minpoly.aeval ℤ (w : E)] at this
    simpa using this.symm
  · intro h0
    have hsep : (minpoly ℚ (w : E)).Separable := Algebra.IsSeparable.isSeparable ℚ (w : E)
    have hq : minpoly ℚ (w : E) = (minpoly ℤ (w : E)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hw
    apply hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ (w : E))
    rw [hq, derivative_map, aeval_map_algebraMap, e, h0, map_zero]

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

def scal (V : Type) [AddCommGroup V] [Module Ω V] (σ : 𝓞 E →+* Ω) : 𝓞 E →+* Module.End Ω V :=
  (algebraMap Ω (Module.End Ω V)).comp σ

theorem scal_apply (σ : 𝓞 E →+* Ω) (c : 𝓞 E) (v : V) : scal V σ c v = σ c • v := by
  simp [scal, Module.algebraMap_end_apply]

theorem commute_scal (σ : 𝓞 E →+* Ω) (c : 𝓞 E) (T : Module.End Ω V) : Commute (scal V σ c) T :=
  Algebra.commute_algebraMap_left (σ c) T

def opRing (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) : Subring (Module.End Ω V) :=
  Subring.closure (Set.range ρ ∪ Set.range (scal V σ))

theorem commute_opRing {ρ : 𝓞 E →+* Module.End Ω V} {σ : 𝓞 E →+* Ω} {T : Module.End Ω V}
    (hT : T ∈ opRing ρ σ) (w : 𝓞 E) : Commute T (ρ w) := by
  induction hT using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · change ρ a * ρ w = ρ w * ρ a
      rw [← map_mul, ← map_mul, mul_comm]
    · exact commute_scal σ a _
  | zero => exact Commute.zero_left _
  | one => exact Commute.one_left _
  | add x y _ _ hx hy => exact hx.add_left hy
  | neg x _ hx => exact hx.neg_left
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem opRing_stable {ρ : 𝓞 E →+* Module.End Ω V} {σ : 𝓞 E →+* Ω} (L : AddSubgroup V)
    (hρ : ∀ x, ∀ e ∈ L, ρ x e ∈ L) (hσ : ∀ c, ∀ e ∈ L, σ c • e ∈ L) {T : Module.End Ω V}
    (hT : T ∈ opRing ρ σ) : ∀ e ∈ L, T e ∈ L := by
  induction hT using Subring.closure_induction with
  | mem x hx =>
    intro e he
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact hρ a e he
    · rw [scal_apply]; exact hσ a e he
  | zero => intro e _; simpa using L.zero_mem
  | one => intro e he; simpa using he
  | add x y _ _ hx hy => intro e he; exact L.add_mem (hx e he) (hy e he)
  | neg x _ hx => intro e he; exact L.neg_mem (hx e he)
  | mul x y _ _ hx hy => intro e he; exact hx _ (hy e he)

theorem eval₂_mem_opRing (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (w : 𝓞 E) (h : (𝓞 E)[X]) :
    eval₂ (scal V σ) (ρ w) h ∈ opRing ρ σ := by
  rw [eval₂_eq_sum]
  refine Subring.sum_mem _ fun n _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _)
  · exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

theorem eval₂_apply_of_eigen (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (w : 𝓞 E) {v : V}
    (hv : ρ w v = σ w • v) (p : (𝓞 E)[X]) : eval₂ (scal V σ) (ρ w) p v = σ (eval w p) • v := by
  have hpow : ∀ n : ℕ, (ρ w ^ n) v = σ w ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, pow_succ, mul_smul, smul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, eval_add, map_add, LinearMap.add_apply, hp, hq, add_smul]
  | monomial n a =>
    rw [eval₂_monomial, Module.End.mul_apply, hpow, scal_apply, eval_monomial, map_mul, map_pow, mul_smul]

theorem exists_factor (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (w : 𝓞 E) :
    ∃ T ∈ opRing ρ σ, ∃ x : 𝓞 E, x ≠ 0 ∧ (ρ w - scal V σ w) * T = 0 ∧
      ∀ v, ρ w v = σ w • v → T v = σ x • v := by
  obtain ⟨f, hm, hr, hd⟩ := exists_sep_poly w
  have hroot : (f.map (algebraMap ℤ (𝓞 E))).IsRoot w := by
    rw [IsRoot.def, eval_map_algebraMap]; exact hr
  obtain ⟨h, hh⟩ := dvd_iff_isRoot.2 hroot
  refine ⟨eval₂ (scal V σ) (ρ w) h, eval₂_mem_opRing ρ σ w h, eval w h, ?_, ?_, ?_⟩
  · intro h0
    apply hd
    have e1 : eval w (derivative (f.map (algebraMap ℤ (𝓞 E)))) = eval w h := by
      rw [hh]; simp [derivative_mul]
    rw [derivative_map, eval_map_algebraMap] at e1
    rw [e1, h0]
  · have e2 : eval₂ (scal V σ) (ρ w) (f.map (algebraMap ℤ (𝓞 E))) = 0 := by
      rw [eval₂_map, RingHom.ext_int ((scal V σ).comp (algebraMap ℤ (𝓞 E))) (ρ.comp (algebraMap ℤ (𝓞 E))),
        ← hom_eval₂]
      have : eval₂ (algebraMap ℤ (𝓞 E)) w f = 0 := hr
      rw [this, map_zero]
    rw [hh, eval₂_mul_noncomm _ _ fun k => commute_scal σ _ _] at e2
    simpa [eval₂_sub] using e2
  · intro v hv
    exact eval₂_apply_of_eigen ρ σ w hv h

theorem exists_product (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (W : Finset (𝓞 E)) :
    ∃ T ∈ opRing ρ σ, ∃ x : 𝓞 E, x ≠ 0 ∧ (∀ w ∈ W, (ρ w - scal V σ w) * T = 0) ∧
      ∀ v ∈ eigSp ρ σ, T v = σ x • v := by
  classical
  have heig : ∀ v ∈ eigSp ρ σ, ∀ a, ρ a v = σ a • v := by
    intro v hv a
    have := (Submodule.mem_iInf _).1 hv a
    simpa [sub_eq_zero] using this
  induction W using Finset.induction_on with
  | empty => exact ⟨1, Subring.one_mem _, 1, one_ne_zero, by simp, by simp⟩
  | insert a W _ ih =>
    obtain ⟨T, hT, x, hx, h1, h2⟩ := ih
    obtain ⟨Ta, hTa, xa, hxa, h3, h4⟩ := exists_factor ρ σ a
    refine ⟨Ta * T, Subring.mul_mem _ hTa hT, xa * x, mul_ne_zero hxa hx, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [← _root_.mul_assoc, h3, zero_mul]
      · have hc : Commute (ρ w - scal V σ w) Ta :=
          ((commute_opRing hTa w).sub_right (commute_scal σ w Ta).symm).symm
        rw [← _root_.mul_assoc, hc.eq, _root_.mul_assoc, h1 w hw, mul_zero]
    · intro v hv
      rw [Module.End.mul_apply, h2 v hv, map_smul, h4 v (heig v hv a), map_mul, mul_comm, mul_smul]

theorem exists_eigen_op [CharZero Ω] (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) :
    ∃ D : ℕ, 0 < D ∧ ∃ T ∈ opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  classical
  obtain ⟨W, hW⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  obtain ⟨T, hT, x, hx, h1, h2⟩ := exists_product ρ σ W
  have hall : ∀ y, (ρ y - scal V σ y) * T = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℤ (W : Set (𝓞 E)) := hW ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem w hw => exact h1 w hw
    | zero => simp
    | add a b _ _ ha hb =>
      have : ρ (a + b) - scal V σ (a + b) = (ρ a - scal V σ a) + (ρ b - scal V σ b) := by
        rw [map_add, map_add]; abel
      rw [this, add_mul, ha, hb, add_zero]
    | smul n a _ ha =>
      have : ρ (n • a) - scal V σ (n • a) = n • (ρ a - scal V σ a) := by
        rw [map_zsmul, map_zsmul, smul_sub]
      rw [this, smul_mul_assoc, ha, smul_zero]
  have hn : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨_, Nat.pos_of_ne_zero hn, scal V σ y * T, Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨_, rfl⟩)) hT, ?_, ?_⟩
  · intro v
    refine (Submodule.mem_iInf _).2 fun a => ?_
    have h3 : ((ρ a - scal V σ a) * T) v = 0 := by rw [hall a]; rfl
    simp only [Module.End.mul_apply, LinearMap.sub_apply, scal_apply] at h3
    simp only [LinearMap.mem_ker, Module.End.mul_apply, LinearMap.sub_apply, scal_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul]
    rw [sub_eq_zero.1 h3, sub_self, smul_zero]
  · intro v hv
    rw [Module.End.mul_apply, h2 v hv, scal_apply, ← mul_smul, ← map_mul, hy]
    simp

end Alg

section Reg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem map_mem_of_span {Li : Type} [AddCommGroup Li] [Module Ω Li] (R : Subring Ω) {r : ℕ} (b : Fin r → Li)
    (φ : Li →ₗ[Ω] Ω) (h : ∀ j, φ (b j) ∈ R) {x : Li} (hx : x ∈ Submodule.span R (Set.range b)) : φ x ∈ R := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    have : φ (c • a) = (c : Ω) * φ a := by
      rw [show c • a = (c : Ω) • a from rfl, map_smul, smul_eq_mul]
    rw [this]
    exact R.mul_mem c.2 ha

theorem exists_pow_mul_mem (U : X.Opens) (hU : IsAffineOpen U) (hall : ∀ x ∈ U, genPt ξ ⤳ x) (hg : genPt ξ ∈ U)
    (N : ℕ) (hN : (N : Ω) ≠ 0) (f : Ω) (hf : ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q N → f ∈ regAt ξ q) :
    ∃ k : ℕ, ∀ q : Cpt ξ, q.1 ∈ U → (N : Ω) ^ k * f ∈ regAt ξ q := by
  let φ : Γ(X, U) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (genPt ξ) hg).hom
  have key : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = φ r := by
    intro q hq r
    have : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) hg :=
      TopCat.Presheaf.germ_stalkSpecializes _ _ _
    have e2 := congrArg (fun g => g ≫ Scheme.stalkClosedPointTo ξ) this
    exact congrArg (fun g => g.hom r) e2
  let I : Ideal Γ(X, U) :=
    { carrier := {r | ∃ r', φ r * f = φ r'}
      add_mem' := by
        rintro a b ⟨a', ha⟩ ⟨b', hb⟩
        exact ⟨a' + b', by rw [map_add, add_mul, ha, hb, map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨a', ha⟩
        exact ⟨c * a', by rw [smul_eq_mul, map_mul, _root_.mul_assoc, ha, map_mul]⟩ }
  have hrad : (N : Γ(X, U)) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    by_contra hNJ
    let y : PrimeSpectrum Γ(X, U) := ⟨J, hJ⟩
    have hy : hU.fromSpec y ∈ U := by
      change hU.fromSpec y ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hy⟩ : U)
    haveI hloc : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
      hU.isLocalization_stalk' y hy
    let q : Cpt ξ := ⟨hU.fromSpec y, hall _ hy⟩
    have hu : IsUnit ((X.presheaf.germ U q.1 hy).hom (N : Γ(X, U))) :=
      IsLocalization.map_units (M := y.asIdeal.primeCompl) (X.presheaf.stalk (hU.fromSpec y)) ⟨(N : Γ(X, U)), hNJ⟩
    have hφN : φ (N : Γ(X, U)) = N := map_natCast φ N
    have hunit : unitAt ξ q N := by
      refine ⟨hN, ⟨_, (key q hy _).trans hφN⟩, ⟨((hu.unit⁻¹ : _ˣ) : X.presheaf.stalk q.1), ?_⟩⟩
      have := map_units_inv (genMap ξ q) hu.unit
      rw [this, IsUnit.unit_spec, key q hy, hφN]
    obtain ⟨s, rfl⟩ := hf q hy hunit
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj y.asIdeal.primeCompl s
    refine t.2 (hIJ ⟨r, ?_⟩)
    have h1 := congrArg (genMap ξ q) hrt
    rw [map_mul] at h1
    have h2 : genMap ξ q (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t) = φ t := key q hy _
    have h3 : genMap ξ q (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) r) = φ r := key q hy _
    rw [h2, h3] at h1
    rw [mul_comm]
    exact h1
  obtain ⟨k, r', hk⟩ := hrad
  refine ⟨k, fun q hq => ⟨(X.presheaf.germ U q.1 hq).hom r', ?_⟩⟩
  rw [key q hq, ← hk]
  simp

end Reg

section Sand

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_sandwich {Li : Type} [AddCommGroup Li] [Module Ω Li] (L Vb : Lat ξ Li) (U : X.Opens)
    (hU : IsAffineOpen U) (hall : ∀ x ∈ U, genPt ξ ⤳ x) (hg : genPt ξ ∈ U) (N : ℕ) (hN : (N : Ω) ≠ 0) {r g : ℕ}
    (b : Fin r → Li) (c : Fin g → Li) (hb : LinearIndependent Ω b) (hc : LinearIndependent Ω c)
    (hcs : Submodule.span Ω (Set.range c) = ⊤)
    (hbf : ∀ q : Cpt ξ, q.1 ∈ U → Vb q = Submodule.span (regAt ξ q) (Set.range b))
    (hcf : ∀ q : Cpt ξ, q.1 ∈ U → L q = Submodule.span (regAt ξ q) (Set.range c))
    (T : Li →ₗ[Ω] Li) (D : ℕ) (hD : (D : Ω) ≠ 0) (hTb : ∀ j, T (b j) = (D : Ω) • b j)
    (hsub : ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q N → ∀ e ∈ Vb q, e ∈ L q)
    (hT : ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q N → ∀ e ∈ L q, T e ∈ Vb q) :
    ∃ (m : ℕ) (π : Fin r → Module.Dual Ω Li), 0 < m ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
      ∀ q : Cpt ξ, q.1 ∈ U → (∀ i, (m : Ω) • b i ∈ L q) ∧ ∀ i, ∀ e ∈ L q, (m : Ω) * π i e ∈ regAt ξ q := by
  classical
  let B := Module.Basis.mk hc hcs.ge
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination Ω b)
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hb))
  let π₀ : Fin r → Module.Dual Ω Li := fun i => LinearMap.proj i ∘ₗ G
  have hπ₀ : ∀ i j, π₀ i (b j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : Fintype.linearCombination Ω b (Pi.single j 1) = b j := by simp
    have h2 := congrArg (fun F => F (Pi.single j (1 : Ω)) i) hG
    simp only [LinearMap.comp_apply, h1, LinearMap.id_apply] at h2
    change G (b j) i = _
    rw [h2, Pi.single_apply]
  have hBc : ∀ j l, B.coord j (c l) = if j = l then 1 else 0 := by
    intro j l
    have : c l = B l := (Module.Basis.mk_apply hc hcs.ge l).symm
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  have ha : ∀ i j, ∃ k : ℕ, ∀ q : Cpt ξ, q.1 ∈ U → (N : Ω) ^ k * B.coord j (b i) ∈ regAt ξ q := by
    intro i j
    refine exists_pow_mul_mem U hU hall hg N hN _ fun q hq hu => ?_
    have hm : b i ∈ L q := hsub q hq hu _ (by rw [hbf q hq]; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [hcf q hq] at hm
    refine map_mem_of_span (regAt ξ q) c (B.coord j) (fun l => ?_) hm
    rw [hBc]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hu : ∀ i j, ∃ k : ℕ, ∀ q : Cpt ξ, q.1 ∈ U → (N : Ω) ^ k * π₀ i (T (c j)) ∈ regAt ξ q := by
    intro i j
    refine exists_pow_mul_mem U hU hall hg N hN _ fun q hq hu => ?_
    have hm : T (c j) ∈ Vb q := hT q hq hu _ (by rw [hcf q hq]; exact Submodule.subset_span ⟨j, rfl⟩)
    rw [hbf q hq] at hm
    refine map_mem_of_span (regAt ξ q) b (π₀ i) (fun l => ?_) hm
    rw [hπ₀]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  choose ka hka using ha
  choose ku hku using hu
  let k : ℕ := ∑ i, ∑ j, (ka i j + ku i j)
  have hle : ∀ i j, ka i j + ku i j ≤ k := fun i j =>
    (Finset.single_le_sum (f := fun j => ka i j + ku i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, (ka i j + ku i j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have mono : ∀ (f : Ω) (k' : ℕ), k' ≤ k → ∀ q : Cpt ξ, (N : Ω) ^ k' * f ∈ regAt ξ q → (N : Ω) ^ k * f ∈ regAt ξ q := by
    intro f k' h q hf
    have : (N : Ω) ^ k * f = (N : Ω) ^ (k - k') * ((N : Ω) ^ k' * f) := by
      rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel h]
    rw [this]
    exact mul_mem (pow_mem (natCast_mem _ N) _) hf
  have hN0 : N ≠ 0 := fun h => hN (by simp [h])
  have hD0 : D ≠ 0 := fun h => hD (by simp [h])
  refine ⟨N ^ k * D, fun i => (D : Ω)⁻¹ • (π₀ i ∘ₗ T), Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hN0) _) (Nat.pos_of_ne_zero hD0),
    ?_, fun q hq => ⟨fun i => ?_, fun i e he => ?_⟩⟩
  · intro i j
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, hTb, map_smul, smul_eq_mul, hπ₀]
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hD, _root_.one_mul]
  · have hs : b i = ∑ j, B.coord j (b i) • c j := by
      conv_lhs => rw [← B.sum_repr (b i)]
      exact Finset.sum_congr rfl fun j _ => by rw [Module.Basis.mk_apply, Module.Basis.coord_apply]
    have e : ((N ^ k * D : ℕ) : Ω) • b i = ∑ j, ((D : Ω) * ((N : Ω) ^ k * B.coord j (b i))) • c j := by
      conv_lhs => rw [hs, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hr : (D : Ω) * ((N : Ω) ^ k * B.coord j (b i)) ∈ regAt ξ q :=
      mul_mem (natCast_mem _ D) (mono _ _ ((Nat.le_add_right _ _).trans (hle i j)) q (hka i j q hq))
    have hc' : c j ∈ L q := by rw [hcf q hq]; exact Submodule.subset_span ⟨j, rfl⟩
    exact (L q).smul_mem ⟨_, hr⟩ hc'
  · rw [hcf q hq] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have e : ((N ^ k * D : ℕ) : Ω) * ((D : Ω)⁻¹ • (π₀ i ∘ₗ T)) (c j) = (N : Ω) ^ k * π₀ i (T (c j)) := by
        simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
        push_cast
        field_simp
      rw [e]
      exact mono _ _ ((Nat.le_add_left _ _).trans (hle i j)) q (hku i j q hq)
    | zero => simpa using zero_mem _
    | add a b' _ _ ha hb' =>
      rw [map_add, mul_add]
      exact add_mem ha hb'
    | smul t a _ ha =>
      have : ((D : Ω)⁻¹ • (π₀ i ∘ₗ T)) (t • a) = (t : Ω) * ((D : Ω)⁻¹ • (π₀ i ∘ₗ T)) a := by
        rw [show t • a = (t : Ω) • a from rfl, map_smul, smul_eq_mul]
      rw [this, mul_left_comm]
      exact mul_mem t.2 ha

end Sand

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

include 𝔐 in
theorem charZero_of_hodgeCpt : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance

theorem emb_mem (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (a : 𝓞 E) : 𝔐.emb s a ∈ regAt 𝔐.ξ q := by
  have h : IsIntegral ℤ (labelEmb c s a) :=
    IsIntegral.map (labelEmb c s).toIntAlgHom (Algebra.IsIntegral.isIntegral a)
  let o : 𝓞 c.F := IsIntegralClosure.mk' (𝓞 c.F) _ h
  have ho : algebraMap (𝓞 c.F) c.F o = labelEmb c s a := IsIntegralClosure.algebraMap_mk' _ _ _
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have h1 := (Flat.ConstReg.regular_const 𝔐.X Ω 𝔐.ξ (𝓞 c.F) (𝔐.f ≫ Y.s) 𝔐.cst_over q o).1
  have e : algebraMap (𝓞 c.F) Ω o = 𝔐.emb s a := by
    change 𝔐.cst (algebraMap _ _ o) = 𝔐.cst (labelEmb c s a)
    rw [ho]
  rwa [e] at h1

set_option backward.isDefEq.respectTransparency false in

theorem lat_act (q : Cpt 𝔐.ξ) (x : 𝓞 E) (e : 𝔐.Li) (he : e ∈ 𝔐.M.lat q) : 𝔐.ρ x e ∈ 𝔐.M.lat q := by
  rw [LieModel.mem_lat_iff] at he ⊢
  obtain ⟨v, hv⟩ := he
  refine ⟨v ≫ 𝔐.t.act.act x, ?_⟩
  rw [LieModel.extends_iff] at hv ⊢
  haveI := 𝔐.t.act.hom x
  refine ⟨?_, ?_⟩
  · have h1 := hv.1
    rw [LieTangent.isTanAt_iff] at h1 ⊢
    rw [← Category.assoc, h1, one_comp]
  · rw [𝔐.act x e, hv.2, Category.assoc]

theorem V_eq (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (hq : unitAt 𝔐.ξ q ((∏ p ∈ S, p : ℕ) : Ω)) :
    𝔐.V s q = 𝔐.dR s q := by
  haveI := charZero_of_hodgeCpt 𝔐
  have hn : ¬ ∃ p ∈ S, InFibre 𝔐.ξ p q := by
    rintro ⟨p, hp, hin⟩
    apply hin
    obtain ⟨t, ht⟩ : p ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem (fun p => p) hp
    have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (𝔐.S_prime p hp).ne_zero
    refine ⟨hp0, natCast_mem _ p, ?_⟩
    have e : (p : Ω)⁻¹ = t * ((∏ p ∈ S, p : ℕ) : Ω)⁻¹ := by
      have hN := hq.1
      rw [ht] at hN ⊢
      push_cast at hN ⊢
      have ht0 : (t : Ω) ≠ 0 := right_ne_zero_of_mul hN
      field_simp
    rw [e]
    exact mul_mem (natCast_mem _ t) hq.2.2
  exact if_neg hn

theorem mem_regAt_gen (hgen : IsCptGen 𝔐.ξ) (a : Ω) :
    a ∈ regAt 𝔐.ξ (⟨genPt 𝔐.ξ, specializes_rfl⟩ : Cpt 𝔐.ξ) := by
  obtain ⟨t, rfl⟩ := hgen.bij.2 a
  refine ⟨t, ?_⟩
  change (𝔐.X.presheaf.stalkSpecializes specializes_rfl ≫ Scheme.stalkClosedPointTo 𝔐.ξ).hom t = _
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

def Good (Fl : 𝔐.Flag) (m : ℕ) (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) : Prop :=
  ∃ (b : Fin (labelRk D s) → 𝔐.Li) (π : Fin (labelRk D s) → Module.Dual Ω 𝔐.Li),
    (∀ i, flagStep Ω b i = flagStep Ω (Fl.b s) i) ∧ (𝔐.V s).IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ 𝔐.M.lat p) ∧
    (∀ i j, π i (b j) = if i = j then 1 else 0) ∧ ∀ i, ∀ e ∈ 𝔐.M.lat p, (m : Ω) * π i e ∈ regAt 𝔐.ξ p

variable {𝔐}

theorem Good.of_dvd {Fl : 𝔐.Flag} {m m' : ℕ} {s : CMType H ⊕ CMType H} {p : Cpt 𝔐.ξ} (h : Good 𝔐 Fl m s p)
    (hd : m ∣ m') : Good 𝔐 Fl m' s p := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨b, π, h1, h2, h3, h4, h5⟩ := h
  refine ⟨b, π, h1, h2, fun i => ?_, h4, fun i e he => ?_⟩
  · have : ((m * k : ℕ) : Ω) • b i = (⟨(k : Ω), natCast_mem _ k⟩ : regAt 𝔐.ξ p) • ((m : Ω) • b i) := by
      rw [show ∀ (t : regAt 𝔐.ξ p) (v : 𝔐.Li), t • v = (t : Ω) • v from fun _ _ => rfl, smul_smul]
      push_cast
      rw [mul_comm]
    rw [this]
    exact (𝔐.M.lat p).smul_mem _ (h3 i)
  · have : ((m * k : ℕ) : Ω) * π i e = (k : Ω) * ((m : Ω) * π i e) := by
      push_cast
      ring
    rw [this]
    exact mul_mem (natCast_mem _ k) (h5 i e he)

variable (𝔐)

theorem connectedSpace_X : ConnectedSpace 𝔐.X := by
  have hcl : closure {genPt 𝔐.ξ} = (Set.univ : Set 𝔐.X) :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.1 (𝔐.all z)
  exact connectedSpace_iff_univ.2 (hcl ▸ isIrreducible_singleton.closure.isConnected)

theorem compactSpace_X : CompactSpace 𝔐.X := by
  have tie := 𝔐.tie
  refine ⟨?_⟩
  have hU := fun c' : {c' : (k : K) → J k // ∏ k, y ⟨k, c' k⟩ ≠ 0} => tie.affine c'.1 c'.2
  choose U hUa hU using hU
  have e : (Set.univ : Set 𝔐.X) = ⋃ c', (U c' : Set 𝔐.X) := by
    refine (Set.eq_univ_of_forall fun z => ?_).symm
    obtain ⟨c', hc⟩ := tie.cover ⟨z, 𝔐.all z⟩
    exact Set.mem_iUnion.2 ⟨⟨c', hc.1⟩, (hU _ z).2 ⟨𝔐.all z, hc⟩⟩
  rw [e]
  exact isCompact_iUnion fun c' => (hUa c').isCompact

theorem exists_local (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) (x : 𝔐.X) :
    ∃ W : 𝔐.X.Opens, x ∈ W ∧ ∃ m : ℕ, 0 < m ∧ ∀ p : Cpt 𝔐.ξ, p.1 ∈ W → Good 𝔐 Fl m s p := by
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := charZero_of_hodgeCpt 𝔐
  haveI := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.geomConnected
  haveI := connectedSpace_X 𝔐
  haveI : ConnectedSpace 𝔐.t.G.left := GeometricallyConnected.connectedSpace 𝔐.t.G.hom 𝔐.t.G.hom.isOpenMap
  obtain ⟨g, hdim⟩ := exists_dim_of_preconnected 𝔐.t.G.hom (Classical.arbitrary _)
  have hVB := (GlobalTheory.T.lie_lattice_vector_bundle_of_smooth 𝔐.X 𝔐.t.G g Ω 𝔐.ξ 𝔐.Li 𝔐.M hgen hdim).1
  let p₀ : Cpt 𝔐.ξ := ⟨x, 𝔐.all x⟩
  obtain ⟨U₁, hx₁, b, hbs, hbf⟩ := Fl.sub s p₀ (Set.mem_univ _)
  obtain ⟨U₂, hx₂, c', hcs, hcf⟩ := hVB p₀ (Set.mem_univ _)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hle⟩ := 𝔐.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((U₁ ⊓ U₂ : 𝔐.X.Opens) : Set 𝔐.X) from ⟨hx₁, hx₂⟩) (U₁ ⊓ U₂).isOpen
  replace hW : IsAffineOpen W := hW
  have hgW : genPt 𝔐.ξ ∈ W := (𝔐.all x).mem_open W.isOpen hxW
  obtain ⟨Dn, hDpos, T, hT, hTe, hTD⟩ := exists_eigen_op 𝔐.ρ (𝔐.emb s)
  have hN : ((∏ p ∈ S, p : ℕ) : Ω) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p hp => (𝔐.S_prime p hp).ne_zero)
  have hb' : ∀ q : Cpt 𝔐.ξ, q.1 ∈ W → (𝔐.V s).IsFrameAt b q := fun q hq => hbf q (Set.mem_univ _) (hle hq).1
  have hc' : ∀ q : Cpt 𝔐.ξ, q.1 ∈ W → 𝔐.M.lat.IsFrameAt c' q := fun q hq => hcf q (Set.mem_univ _) (hle hq).2
  let qg : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hug : unitAt 𝔐.ξ qg ((∏ p ∈ S, p : ℕ) : Ω) := ⟨hN, mem_regAt_gen 𝔐 hgen _, mem_regAt_gen 𝔐 hgen _⟩
  have hbe : ∀ j, b j ∈ eigSp 𝔐.ρ (𝔐.emb s) := fun j => by
    have h1 : b j ∈ 𝔐.V s qg := by
      rw [(hb' qg hgW).2]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [V_eq 𝔐 s qg hug] at h1
    exact h1.2
  have hst : ∀ q : Cpt 𝔐.ξ, ∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.M.lat q := fun q =>
    opRing_stable (𝔐.M.lat q).toAddSubgroup (fun a e he => lat_act 𝔐 q a e he)
      (fun a e he => (𝔐.M.lat q).smul_mem ⟨_, emb_mem 𝔐 s q a⟩ he) hT
  obtain ⟨m, π, hm, hδ, hq⟩ := exists_sandwich 𝔐.M.lat (𝔐.V s) W hW (fun z _ => 𝔐.all z) hgW (∏ p ∈ S, p) hN b c'
    (hb' p₀ hxW).1 (hc' p₀ hxW).1 hcs (fun q hq => (hb' q hq).2) (fun q hq => (hc' q hq).2) T Dn
    (Nat.cast_ne_zero.2 hDpos.ne') (fun j => hTD _ (hbe j))
    (fun q _ hu e he => by
      rw [V_eq 𝔐 s q hu] at he
      exact he.1)
    (fun q _ hu e he => by
      rw [V_eq 𝔐 s q hu]
      exact ⟨hst q e he, hTe e⟩)
  exact ⟨W, hxW, m, hm, fun p hp => ⟨b, π, hbs, hb' p hp, (hq p hp).1, hδ, (hq p hp).2⟩⟩

theorem exists_global (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : Cpt 𝔐.ξ, Good 𝔐 Fl m s p := by
  haveI := compactSpace_X 𝔐
  choose W hx m hm hg using exists_local 𝔐 Fl s
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (W x : Set 𝔐.X))
    (fun x => (W x).isOpen.mem_nhds (hx x))
  refine ⟨∏ x ∈ t, m x, Finset.prod_pos fun x _ => hm x, fun p => ?_⟩
  have h1 : p.1 ∈ ⋃ x ∈ t, (W x : Set 𝔐.X) := ht ▸ Set.mem_univ _
  obtain ⟨x, hxt, hp⟩ := Set.mem_iUnion₂.1 h1
  exact (hg x p hp).of_dvd (Finset.dvd_prod_of_mem m hxt)

end Main

theorem lat_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ m : ℕ, 0 < m ∧ ∀ (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ), ∃ (b : Fin (labelRk D s) → 𝔐.Li) (π : Fin (labelRk D s) → Module.Dual Ω 𝔐.Li), (∀ i, flagStep Ω b i = flagStep Ω (Fl.b s) i) ∧ (𝔐.V s).IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ 𝔐.M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧ ∀ i, ∀ e ∈ 𝔐.M.lat p, (m : Ω) * π i e ∈ regAt 𝔐.ξ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 Fl
  have h := fun s => exists_global 𝔐 Fl s
  choose m hm hg using h
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  exact ⟨∏ s, m s, Finset.prod_pos fun s _ => hm s, fun s p =>
    (hg s p).of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ s))⟩

end GlobalTheory.CompanionTheory.Ar.Sandwich
