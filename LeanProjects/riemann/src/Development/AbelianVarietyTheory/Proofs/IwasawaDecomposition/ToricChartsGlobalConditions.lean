import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftThroughEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRingStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.PhiOrder

theorem lift_trait {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) (hξ : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (χ : Sp W ⟶ Y.X)
    (hχ : χ (closedPoint W) = genι Y (ξ (closedPoint _))) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V),
      CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y :=
  GlobalTheory.T.exists_dvr_lift_through_etale_chart Y ξ hξ W hW χ hχ

theorem form_compare {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (mC : SABMap tC Y.t (ξ ≫ genι Y))
    (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X)
    (hγ : IsMonomial PC.D.toPre (bdParam k m e) γ)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : IsMonomial P.D.toPre ![ϖ] ![be])
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (ϖ' : V) (hϖ' : Irreducible ϖ')
    (f : W →+* V) (ψ : ChartRing k m e →+* V) (hf : Function.Injective f) [hfl : IsLocalHom f] [hψl : IsLocalHom ψ]
    (hc : spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y) (r : ℕ) (u : Vˣ) (hu : f ϖ = u * ϖ' ^ r)
    (n : Fin m → ℕ) (v : Fin m → Vˣ) (hv : ∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) :
    ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) :=
  GlobalTheory.T.monomial_form_on_chart_ring Y ξ mC PC γ hγ W hW ϖ hϖ χ t mχ P hr be hbe V hV ϖ' hϖ' f ψ hf hfl hψl hc r u hu n v hv

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem comb_evalZ (ψ φ : InvFun (𝓞 E)) (d : ℕ) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (be : LinearMap.BilinForm ℤ X) : (comb 0 ψ d φ).evalZ be = d * φ.evalZ be := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold InvFun.evalZ
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  show (0 : ℕ) * ψ.toFun n _ + d * φ.toFun n _ = _
  simp

theorem eq_of_diag {X : Type} [AddCommGroup X] (B₁ B₂ : LinearMap.BilinForm ℤ X) (h₁ : ∀ y z, B₁ y z = B₁ z y)
    (h₂ : ∀ y z, B₂ y z = B₂ z y) (h : ∀ y, B₁ y y = B₂ y y) (y z : X) : B₁ y z = B₂ y z := by
  have e1 := h (y + z)
  simp only [map_add, LinearMap.add_apply] at e1
  rw [h y, h z, h₁ z y, h₂ z y] at e1
  omega

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have hw : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  show (Y.jQ ≫ pullback.fst _ _) w ∈ _
  rw [Scheme.Hom.comp_apply]
  exact hw

end SlopeTestRemainingChoices

section Cases

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_abelian (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (φ : InvFun (𝓞 E))
    (hsupp : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (be : LinearMap.BilinForm ℤ P.D.toPre.X) (hab : χ (closedPoint W) ∈ abLocus Y.t.G) :
    ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus t.G :=
    (abLocus_pullback abLocusOne Y.t.semi mχ.cart.1 _).1 hab
  have hs : Subsingleton P.D.toPre.X := (closed_mem_abLocus_iff T P).1 hc
  refine ⟨0, ?_, ?_⟩
  · rw [InvFun.evalZ, φ.eval_of_subsingleton]; simp
  · have hns : χ (closedPoint W) ∉ BD.idealSheaf.support := fun h => hsupp _ h hab
    have htop : FinalTheorems.stalkId BD.idealSheaf (χ (closedPoint W)) = ⊤ := by
      by_contra h
      exact hns ((mem_support_iff_stalkId _ _).2 h)
    rw [pow_zero, Ideal.span_singleton_one, idlAlong, htop, Ideal.map_top]

end Cases

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_chart (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) (hch : GlobalTheory.MumfordChart.HasChartOf φ Y BD d x)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : ∀ y z, be y z = be z y) (hmon : IsMonomial P.D.toPre ![ϖ] ![be])
    (hx : χ (closedPoint W) = genι Y x) :
    ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨k, _, m, e, ξ, tC, PC, γ, δ, a, hξx, h₁, -, h₃, ⟨mC⟩, h₅, -, hcone, hγδ, ha, hid⟩ := hch
  have := hW.1
  obtain ⟨V, _, _, _, f, ψ, hV, hfi, hfl, hψl, hcomm⟩ := lift_trait Y ξ h₁ W hW χ (by rw [hx, hξx])
  have := hV.1
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfϖ : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hfi (h.trans (map_zero f).symm))
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'

  have hψt : ∀ i, ψ (bdParam k m e i) ≠ 0 := by
    let q : Sp V := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : spMap f q = (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hfi)
    have hw : (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) = jK W (⟨⊥, Ideal.isPrime_bot⟩ : Sp (FractionRing W)) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective W (FractionRing W))).symm
    have e1 : χ (spMap f q) = genι Y (ξ (spMap ψ q)) := by
      rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have hab : genι Y (ξ (spMap ψ q)) ∈ abLocus Y.t.G := by
      rw [← e1, hq, hw]
      exact range_j_subset_abLocus Y (hr ⟨_, Scheme.Hom.comp_apply (jK W) χ _⟩)
    have hnb : ξ (spMap ψ q) ∉ genBd Y := fun h => (mem_genBd_iff.1 h) hab
    have hp : ∏ i, bdParam k m e i ∉ (spMap ψ q).asIdeal := fun h => hnb ((h₃ _).2 h)
    have hp' : ψ (∏ i, bdParam k m e i) ≠ 0 := fun h => hp (by
      show ψ (∏ i, bdParam k m e i) ∈ (⊥ : Ideal V)
      rw [h]; exact Ideal.zero_mem _)
    rw [map_prod] at hp'
    exact fun i => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i)
  choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψt i) hϖ'
  obtain ⟨ε, hε⟩ := form_compare Y ξ mC PC (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) h₅ W hW ϖ hϖ χ t mχ P
    hr be hmon V hV ϖ' hϖ' f ψ hfi hcomm r u hu nn vv hvv

  have hU : IsUnit (∏ i, (vv i : V) ^ a i) := by
    have := (∏ i, vv i ^ a i).isUnit
    push_cast at this
    exact this
  have hmapψ : idlAlong BD.idealSheaf (spMap f ≫ χ) = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [hcomm, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp_rw [map_pow, hvv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    exact Ideal.span_singleton_mul_left_unit hU _
  have hmapf : (idlAlong BD.idealSheaf χ).map f = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp]; exact hmapψ
  have hne : idlAlong BD.idealSheaf χ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmapf
    exact pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)
  obtain ⟨n0, hn0⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hrN : r * n0 = ∑ i, nn i * a i := by
    rw [hn0, Ideal.map_span, Set.image_singleton, map_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow _)] at hmapf
    have hass := (Ideal.span_singleton_eq_span_singleton.1 hmapf)
    exact le_antisymm ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.dvd)
      ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.symm.dvd)
  refine ⟨n0, ?_, hn0⟩

  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  let εZ : P.D.toPre.X →ₗ[ℤ] PC.D.toPre.X := ε.toLinearMap.toAddMonoidHom.toIntLinearMap
  let B₂ : LinearMap.BilinForm ℤ P.D.toPre.X :=
    ∑ i, (nn i : ℤ) • (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X).compl₁₂ εZ εZ
  have hB₂ : ∀ y z, B₂ y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    simp [B₂, εZ, LinearMap.sum_apply]
  have hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    have := eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z])
      (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(γ i).2.1])
      (fun y => by rw [hB₂, ← hε y]; simp) y z
    rw [hB₂] at this
    simpa using this
  have hlin : φ.LinearOn (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have e' : (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) = fun i => (l.M' : ℤ) • δ i := funext hγδ
    rw [e']; exact hcone.linearOn_smul l.M'
  have hφbe : φ.evalZ be = ∑ i, ((nn i : ℝ) / r) * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) := by
    rw [← hlin (fun i => (nn i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv ε]
    unfold InvFun.evalZ
    congr 1
    funext y z
    have h := congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)
    push_cast at h
    rw [eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hN : (r : ℝ) * n0 = ∑ i, (nn i : ℝ) * (d * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hrN
    push_cast at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [ha]
  rw [hφbe, ← mul_right_inj' hr', hN, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end Chart

theorem isPhiDiv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)), IsPolFan H.bar (min D.p D.q) φ →
    NoSelfInt H.bar (min D.p D.q) φ → ∀ (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ),
    SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) →
    (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) →
    IsPhiDiv (comb 0 φ d φ) Y BD := by
  intro E _ _ _ H D l Xo c φ _ _ Y BD d _ _ hsupp hch W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon
  by_cases hab : χ (closedPoint W) ∈ abLocus Y.t.G
  · exact order_of_abelian Y BD _ hsupp W hW ϖ χ t mχ P be hab
  · rcases GlobalTheory.GenFan.exists_of_id Y (χ (closedPoint W)) with ⟨x, hxb, hxz⟩ | hj
    · obtain ⟨n, hn, hI⟩ := order_of_chart φ Y BD d x (hch x hxb) W hW ϖ hϖ χ t mχ P hr be hbe.1 hmon hxz.symm
      exact ⟨n, hn.trans (comb_evalZ φ φ d be).symm, hI⟩
    · exact absurd (range_j_subset_abLocus Y hj) hab

end GlobalTheory.GenFan.PhiOrder
