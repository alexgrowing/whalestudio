import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TaylorComp

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

section JetAlg

variable {K : Type} [Field K] {ι : Type} {m : ℕ}

theorem jetAug_mk (p : MvPolynomial ι K) :
    (jetAug : Jet K ι m →ₐ[K] K) (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p := by
  show (MvPolynomial.aeval fun _ : ι => (0 : K)) p = MvPolynomial.constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X]

theorem constantCoeff_of_mem_orig {p : MvPolynomial ι K} (hp : p ∈ orig K ι) : MvPolynomial.constantCoeff p = 0 := by
  have hle : orig K ι ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι K →+* K) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp
  exact (RingHom.mem_ker).1 (hle hp)

theorem isUnit_of_jetAug (a : Jet K ι m) (h : (jetAug : Jet K ι m →ₐ[K] K) a ≠ 0) : IsUnit a := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [jetAug_mk] at h
  set c := MvPolynomial.constantCoeff p with hc

  have hq : p - MvPolynomial.C c ∈ orig K ι := by
    rw [orig, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    have hmo0 : mo ≠ 0 := by
      intro h0
      subst h0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
        ← MvPolynomial.constantCoeff_eq, ← hc, sub_self] at hmo
      exact hmo rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hmo0
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c)) := by
    refine ⟨m + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c)) :=
    (isUnit_iff_ne_zero.2 h).map (Ideal.Quotient.mk (orig K ι ^ (m + 1)) |>.comp MvPolynomial.C)
  have hsplit : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
      Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c) +
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit]
  exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)

theorem jetAug_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') (a : Jet K ι m) :
    (jetAug : Jet K ι' m →ₐ[K] K) (jetMap φ hφ a) = (jetAug : Jet K ι m →ₐ[K] K) a := by
  have hcc : ∀ {ι' : Type} (φ : ι → MvPolynomial ι' K), (∀ i, φ i ∈ orig K ι') →
      ∀ q : MvPolynomial ι K, MvPolynomial.constantCoeff (MvPolynomial.aeval φ q) = MvPolynomial.constantCoeff q := by
    intro ι' φ hφ q
    induction q using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.aeval_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, hp, MvPolynomial.constantCoeff_X, mul_zero,
        constantCoeff_of_mem_orig (hφ i)]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hmap : jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl
  rw [hmap, jetAug_mk, jetAug_mk, hcc φ hφ p]

theorem jetMap_congr {ι' : Type} (φ φ' : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι')
    (hφ' : ∀ i, φ' i ∈ orig K ι')
    (h : ∀ i, Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ i) = Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ' i))
    (a : Jet K ι m) : jetMap φ hφ a = jetMap φ' hφ' a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hext : (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ) =
      (Ideal.Quotient.mkₐ K (orig K ι' ^ (m + 1))).comp (MvPolynomial.aeval φ') := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using h i
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ' p)
  exact DFunLike.congr_fun hext p

theorem isLocalHom_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') :
    IsLocalHom ((jetMap (m := m) φ hφ : Jet K ι m →ₐ[K] Jet K ι' m) : Jet K ι m →+* Jet K ι' m) := by
  refine ⟨fun a ha => isUnit_of_jetAug a ?_⟩
  rw [← jetAug_jetMap φ hφ a]
  exact (ha.map (jetAug : Jet K ι' m →ₐ[K] K)).ne_zero

end JetAlg

variable {g : ℕ} {Y : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in

theorem jetPt_precomp (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (hol' : IsHolFam e')
    (h0 : e' 0 = e 0) (m : ℕ) (χ : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) [hχl : IsLocalHom χ]
    (hχ : ∀ (U : Y.Opens) (_ : e 0 cpt ∈ U) (f : Γ(Y, U)),
      χ (jetOf m (fun z => valAt' (e z) U f)) = jetOf m (fun z => valAt' (e' z) U f)) :
    spMap χ ≫ jetPt e hol m = jetPt e' hol' m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom χ) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom χ :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom χ) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol m U hU f (hχl.map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hpt' := nbhdPt_closedPoint (y₀ := e' 0 cpt) _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m)
  refine hom_ext_of_local (hpt.trans (by rw [hpt', h0])) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  have hU' : e' 0 cpt ∈ U := by rw [h0]; exact hU
  rw [nbhdPt_appLE _ hres hloc U hU h₁, nbhdPt_appLE _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m) U hU' h₂]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact hχ U hU f

def jetScaleP (m : ℕ) (c : Fin g → ℂ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun p => MvPolynomial.C (c p.2) * MvPolynomial.X p)
    fun p => Ideal.mul_mem_left _ _ (X_mem_orig p)

theorem jetOf_scale (m : ℕ) (c : Fin g → ℂ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    jetOf m (fun z => θ fun i => c i * z i) = jetScaleP m c (jetOf m θ) := by
  have ha : ∀ p : Fin 1 × Fin g, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) = 0 := by
    intro p
    simp
  unfold jetOf jetScaleP
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA θ hθ c, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ ha]
  refine jetMap_congr _ _ _ _ (fun p => ?_) _
  have hco : (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C (c p.2) * MvPolynomial.X p : MvPolynomial (Fin 1 × Fin g) ℂ) :
        MvPowerSeries (Fin 1 × Fin g) ℂ) := by
    simp
  rw [hco, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
