import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnitsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFinitePartsStatement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeConj

def arg2 : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / starRingEnd ℂ (z : ℂ), by
    simp [Submonoid.unitSphere, norm_div]⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by
    show ((x * y : ℂˣ) : ℂ) / starRingEnd ℂ ((x * y : ℂˣ) : ℂ) =
      (x : ℂ) / starRingEnd ℂ (x : ℂ) * ((y : ℂ) / starRingEnd ℂ (y : ℂ))
    rw [Units.val_mul, map_mul, mul_div_mul_comm])

theorem continuous_unitsDivConjCircleChar : Continuous arg2 := by
  refine Continuous.subtype_mk ?_ _
  exact Units.continuous_val.div (Complex.continuous_conj.comp Units.continuous_val)
    fun z => by simp

theorem exists_transport {G K : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [Field K]
    (σ₀ σ : K →+* ℂ) (f : G →* Circle) (hy : ∀ x, ∃ y, ((f x : Circle) : ℂ) = σ₀ y) (m : ℕ) (hm : 0 < m)
    (hf : ∀ x, f x ^ m = 1) (U : Set G) (hU : U ∈ 𝓝 (1 : G)) (h1 : ∀ x ∈ U, f x = 1) :
    ∃ ψ : G →* Circle, Continuous ψ ∧ ∀ x y, ((f x : Circle) : ℂ) = σ₀ y → ((ψ x : Circle) : ℂ) = σ y := by
  choose y hy using hy
  have hn : ∀ x, ‖σ (y x)‖ = 1 := by
    intro x
    have h2 : y x ^ m = 1 := σ₀.injective (by rw [map_pow, ← hy, ← Circle.coe_pow, hf, map_one, Circle.coe_one])
    have h3 : ‖σ (y x)‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  have hone : ∀ x, f x = 1 → y x = 1 := fun x h => σ₀.injective (by rw [← hy, h, map_one, Circle.coe_one])
  let ψ : G →* Circle :=
    { toFun := fun x => ⟨σ (y x), by simp [Submonoid.unitSphere, hn]⟩
      map_one' := Circle.ext (by
        show σ (y 1) = 1
        rw [hone 1 (map_one f), map_one])
      map_mul' := fun a b => Circle.ext (by
        show σ (y (a * b)) = σ (y a) * σ (y b)
        have : y (a * b) = y a * y b := σ₀.injective (by rw [map_mul, ← hy, ← hy, ← hy, map_mul, Circle.coe_mul])
        rw [this, map_mul]) }
  refine ⟨ψ, continuous_of_continuousAt_one ψ ?_, fun x z h => ?_⟩
  · refine (continuousAt_const (y := (1 : Circle))).congr ?_
    filter_upwards [hU] with x hx
    refine Circle.ext ?_
    show (1 : ℂ) = σ (y x)
    rw [hone x (h1 x hx), map_one]
  · show σ (y x) = σ z
    rw [σ₀.injective ((hy x).symm.trans h)]

theorem one_mem_intAE (D : D7) : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩

theorem mul_mem_intAE (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

def intIdeles (D : D7) : Subgroup (AE D)ˣ where
  carrier := {x | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D}
  one_mem' := ⟨by rw [Units.val_one, RingHom.map_one]; exact one_mem_intAE D,
    by rw [inv_one, Units.val_one, RingHom.map_one]; exact one_mem_intAE D⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul, RingHom.map_mul]; exact mul_mem_intAE D ha.1 hb.1,
    by rw [mul_inv, Units.val_mul, RingHom.map_mul]; exact mul_mem_intAE D ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def angle (D : D7) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : (AE D)ˣ →* Circle :=
  arg2.comp (Units.map (θ.comp (infPart D)).toMonoidHom)

theorem angle_coe (D : D7) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    ((angle D θ x : Circle) : ℂ) = θ (infPart D (x : AE D)) / starRingEnd ℂ (θ (infPart D (x : AE D))) := rfl

theorem continuous_angle (D : D7) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : Continuous θ) :
    Continuous (angle D θ) :=
  continuous_unitsDivConjCircleChar.comp (Continuous.units_map _ (h.comp (GlobalTheory.Member.continuous_infPart D)))

theorem coe_prod_zpow {ι : Type} [Fintype ι] (u : ι → Circle) (k : ι → ℤ) :
    ((∏ i, u i ^ k i : Circle) : ℂ) = ∏ i, (u i : ℂ) ^ k i := by
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
  exact Circle.coe_zpow _ _

set_option maxHeartbeats 2000000 in
open GlobalTheory.FockCompare in

theorem exists_type (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (χ : (AE D)ˣ →* Circle) (hc : Continuous χ) (hF : ∀ a, χ (idF D a) = 1) :
    ∃ k : D.what₂.Tau → ℤ, ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = ∏ τ, angle D (θ τ) x ^ k τ := by
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have rr : ∀ z : D.what₂.Tau → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → ∀ τ,
      θ τ (ρ (fun i => (z i : ℂ).re) ⊗ₜ[D.host.F] (1 : D.host.E)) = z τ := fun z hz τ => by
    rw [r1]; exact Complex.ext rfl (hz τ).symm
  have rm : ∀ z : D.what₂.Tau → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) →
      ρ (fun i => (z i : ℂ).re) * ρ (fun i => (z⁻¹ i : ℂ).re) = 1 := fun z hz => by
    have hz' : ∀ i, ((z⁻¹ i : ℂˣ) : ℂ).im = 0 := fun i => by simp [hz i]
    rw [← sub_eq_zero]
    refine r0 _ fun τ => ?_
    rw [TensorProduct.sub_tmul, RingHom.map_sub, ← mul_one (1 : D.host.E), ← Algebra.TensorProduct.tmul_mul_tmul,
      RingHom.map_mul, rr z hz, rr z⁻¹ hz', mul_one, ← Algebra.TensorProduct.one_def, RingHom.map_one]
    simp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_zpow_prod_div_conj_of_continuous_trivial_on_real D.what₂.Tau (χ.comp T.toHomUnits) (hc.comp Tc) fun z hz => by
    let a : (AF D.host.F)ˣ := Units.mkOfMulEqOne (pairA D.host.F (ρ (fun i => (z i : ℂ).re)) 1)
      (pairA D.host.F (ρ (fun i => (z⁻¹ i : ℂ).re)) 1) (Prod.ext (rm z hz) (mul_one (1 : Af D.host.F)))
    have : T.toHomUnits z = idF D a := Units.ext (ext _ _ ((tf z).trans rfl) fun τ => (ti z τ).trans (rr z hz τ).symm)
    exact (congrArg χ this).trans (hF a)
  refine ⟨k, fun x hx => Circle.ext ?_⟩
  let z : D.what₂.Tau → ℂˣ := fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  have : x = T.toHomUnits z := Units.ext (ext _ _ (hx.trans (tf z).symm) fun τ => (ti z τ).symm)
  refine ((congrArg (fun u => ((χ u : Circle) : ℂ)) this).trans (hk z)).trans ?_
  rw [coe_prod_zpow]
  rfl

theorem angle_idF (D : D7) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : ∀ z, θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z)) (a : (AF D.host.F)ˣ) :
    angle D θ (idF D a) = 1 := by
  refine Circle.ext ?_
  have h0 : θ (infPart D (idF D a : AE D)) ≠ 0 := (Units.map (θ.comp (infPart D)).toMonoidHom (idF D a)).ne_zero
  have h1 : sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (idF D a : AE D)) = infPart D (idF D a : AE D) := by
    show fstA D.host.F (a : AF D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig 1 = fstA D.host.F (a : AF D.host.F) ⊗ₜ[D.host.F] 1
    rw [map_one]
  rw [angle_coe, ← h, h1, div_self h0, Circle.coe_one]

theorem angle_inc (D : D7) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (e : D.host.Eˣ) :
    ((angle D θ (Units.map (incA D).toMonoidHom e) : Circle) : ℂ) =
      τ ((e : D.host.E) / IsCMField.complexConj D.host.E (e : D.host.E)) := by
  have h1 : θ (infPart D ((Units.map (incA D).toMonoidHom e : (AE D)ˣ) : AE D)) = τ e := h.1 e
  rw [angle_coe, h1, map_div₀, IsCMField.complexEmbedding_complexConj]

set_option maxHeartbeats 2000000 in

theorem exists_conjugates : ∀ (D : D7) (Q : Par D) (χ₀ : (AE D)ˣ →* Circle), IsHeckeChar D χ₀ → (∀ a, χ₀ (idF D a) = 1) → (∀ x, FinUnit x → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y) → ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, χ Q.c.F.val.toRingHom = χ₀ ∧ ∀ σ, IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ χ₀ (χ σ) := by
  intro D Q χ₀ hH hF hy
  obtain ⟨⟨θ, hθ⟩, hθ'⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θc, θs, -⟩ := hθ' θ hθ
  obtain ⟨k, hk⟩ := exists_type D (fun τ => θ (tauE D τ)) (fun τ => hθ _) χ₀ hH.1 hF
  obtain ⟨hop, a, b, -, bc, hab, ha, hb⟩ := GlobalTheory.T.isOpen_congruence_ideles_and_real_finite_parts D
  obtain ⟨N, hN, hN1, m, hm, hm1⟩ := GlobalTheory.T.continuous_character_finite_order_integral_units D χ₀ hH.1
  have Hopen : IsOpen (intIdeles D : Set (AE D)ˣ) := by
    convert hop 1 one_pos using 1
    ext x
    exact ⟨fun h => ⟨h.1, h.2, _, sub_mem h.1 (one_mem_intAE D), (one_nsmul _).symm⟩, fun h => ⟨h.1, h.2.1⟩⟩
  have hbu : ∀ x : intIdeles D, FinUnit (b x) := fun x =>
    ⟨(hb x).1, (hb x).2 ▸ x.2.1, by rw [← map_inv, (hb _).2]; exact x.2.2⟩
  have key : ∀ σ : Q.c.F →+* ℂ, ∃ χ : (AE D)ˣ →* Circle,
      IsHeckeChar D χ ∧ (∀ a, χ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ χ₀ χ := by
    intro σ
    obtain ⟨ψ, ψc, hψ⟩ := exists_transport Q.c.F.val.toRingHom σ ((χ₀.comp b).comp (intIdeles D).subtype)
      (fun x => hy _ (hbu x)) m hm (fun x => hm1 _ (hbu x)) (Subtype.val ⁻¹' _)
      (((hop N hN).preimage continuous_subtype_val).mem_nhds
        ⟨(intIdeles D).one_mem.1, (intIdeles D).one_mem.2, 0, zero_mem _, by
          show finPart D 1 - 1 = _
          rw [RingHom.map_one, sub_self, nsmul_zero]⟩)
      (fun x hx => hN1 _ (hbu x) (by rw [(hb _).2]; exact hx.2.2))
    let A : (AE D)ˣ →* Circle := ∏ τ, angle D (θ (relab Q.c σ (tauE D τ))) ^ k τ
    have hA : ∀ x, A x = ∏ τ, angle D (θ (relab Q.c σ (tauE D τ))) x ^ k τ := fun x => by
      simp only [A, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply]
    have Ac : Continuous A := by
      rw [show (A : _ → _) = _ from funext hA]
      exact continuous_finset_prod _ fun τ _ => (continuous_angle D (θc _)).zpow _
    obtain ⟨χ, χc, χ1, χ2⟩ := GlobalTheory.T.exists_continuous_circle_char_extension' (AE D)ˣ (intIdeles D)
      ((Units.map (incA D).toMonoidHom).range ⊔ (idF D).range) (A.comp (intIdeles D).subtype * ψ) Hopen
      ((Ac.comp continuous_subtype_val).mul ψc) (by
        intro x hx
        obtain ⟨_, ⟨e, rfl⟩, _, ⟨r, rfl⟩, hx⟩ := Subgroup.mem_sup.1 hx
        have han : ∀ τ, ((angle D (θ τ) x : Circle) : ℂ) =
            τ ((e : D.host.E) / IsCMField.complexConj D.host.E (e : D.host.E)) := fun τ => by
          rw [← hx, map_mul, angle_idF D (θs τ), mul_one, angle_inc D (hθ τ)]
        generalize (e : D.host.E) / IsCMField.complexConj D.host.E (e : D.host.E) = w at han
        have h0 : χ₀ (a x) * χ₀ (b x) = 1 := by
          rw [← map_mul, ← hab, ← hx, map_mul, hH.2, hF, mul_one]
        have h1 : ((χ₀ (a x) : Circle) : ℂ) = Q.c.F.val.toRingHom (∏ τ, embF Q.c (tauE D τ) w ^ k τ) := by
          rw [hk _ (ha _).2, coe_prod_zpow, map_prod]
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [map_zpow₀, angle_coe, (ha _).1, ← angle_coe, han]
          rfl
        have h2 := hψ x (∏ τ, embF Q.c (tauE D τ) w ^ k τ)⁻¹ (by
          rw [map_inv₀, ← h1, ← Circle.coe_inv, ← eq_inv_of_mul_eq_one_right h0]
          rfl)
        have h3 : ((A x : Circle) : ℂ) = σ (∏ τ, embF Q.c (tauE D τ) w ^ k τ) := by
          rw [hA, coe_prod_zpow, map_prod]
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [map_zpow₀, han]
          rfl
        refine Circle.ext ?_
        show ((A x : Circle) : ℂ) * ((ψ x : Circle) : ℂ) = 1
        rw [h2, map_inv₀, ← h3, mul_inv_cancel₀ (Circle.coe_ne_zero _)])
    refine ⟨χ, ⟨χc, fun e => χ1 _ (Subgroup.mem_sup_left ⟨e, rfl⟩)⟩,
      fun r => χ1 _ (Subgroup.mem_sup_right ⟨r, rfl⟩), fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hy x hx
    have han : ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → ∀ τ, angle D (θ τ) u = 1 := fun u hu τ =>
      Circle.ext (by rw [angle_coe, hu]; simp)
    have h1 : χ₀ (b x) = χ₀ x := by
      conv_rhs => rw [hab x, map_mul, hk _ (ha _).2]
      simp only [han _ ((ha x).1.trans hx.1), one_zpow, Finset.prod_const_one, one_mul]
    refine ⟨y, hy, ?_⟩
    have h2 := χ2 ⟨x, hx.2⟩
    have h3 : A x = 1 := by simp only [hA, han _ hx.1, one_zpow, Finset.prod_const_one]
    have h4 : χ x = A x * ψ ⟨x, hx.2⟩ := h2
    rw [h4, h3, one_mul]
    exact hψ ⟨x, hx.2⟩ y ((congrArg _ h1).trans hy)
  choose χ hχ using key
  classical
  refine ⟨fun σ => if σ = Q.c.F.val.toRingHom then χ₀ else χ σ, if_pos rfl, fun σ => ?_⟩
  by_cases h : σ = Q.c.F.val.toRingHom
  · subst h
    simp only [if_true]
    exact ⟨hH, hF, fun x hx => (hy x hx).imp fun y h => ⟨h, h⟩⟩
  · simp only [if_neg h]
    exact hχ σ

end GlobalTheory.HeckeConj
