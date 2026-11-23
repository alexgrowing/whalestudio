import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.SplitInf

section Abstract

variable {G H : Type} [Group G] [Group H]

theorem map_twCent_prod {A B : Type} [Group A] [Group B] (e : G ≃* A × B) (θ : Monoid.End G) (θ₁ : Monoid.End A)
    (θ₂ : Monoid.End B) (h : ∀ g, e (θ g) = (θ₁ (e g).1, θ₂ (e g).2)) (δ : G) :
    (twCent θ δ).map e.toMonoidHom = (twCent θ₁ (e δ).1).prod (twCent θ₂ (e δ).2) := by
  have key : ∀ g, g⁻¹ * δ * θ g = δ ↔ (e g).1⁻¹ * (e δ).1 * θ₁ (e g).1 = (e δ).1 ∧
      (e g).2⁻¹ * (e δ).2 * θ₂ (e g).2 = (e δ).2 := by
    intro g
    rw [← e.injective.eq_iff, map_mul, map_mul, map_inv, h, Prod.ext_iff]
    simp
  ext ⟨a, b⟩
  simp only [Subgroup.mem_map, Subgroup.mem_prod, mem_twCent]
  constructor
  · rintro ⟨g, hg, hgab⟩
    have hgab' : e g = (a, b) := hgab
    have := (key g).1 hg
    rw [hgab'] at this
    exact this
  · rintro hab
    refine ⟨e.symm (a, b), (key _).2 (by simpa using hab), by simp⟩

def splitE (p : G →* H) (s : H →* G) (hps : ∀ y, p (s y) = y) (hc : ∀ y, ∀ k ∈ p.ker, s y * k = k * s y) :
    G ≃* H × p.ker where
  toFun g := (p g, ⟨g * (s (p g))⁻¹, by simp [MonoidHom.mem_ker, hps]⟩)
  invFun x := s x.1 * x.2
  left_inv g := by
    have hk : p (g * (s (p g))⁻¹) = 1 := by simp [hps]
    change s (p g) * (g * (s (p g))⁻¹) = g
    rw [hc (p g) _ hk]; simp
  right_inv x := by
    have h2 : p (x.2 : G) = 1 := x.2.2
    refine Prod.ext (by simp [hps, h2]) (Subtype.ext ?_)
    have := hc x.1 x.2 x.2.2
    simp only [map_mul, hps, h2, mul_one]
    rw [this]; simp
  map_mul' a b := by
    refine Prod.ext (map_mul p a b) (Subtype.ext ?_)
    have hk : p (b * (s (p b))⁻¹) = 1 := by simp [hps]
    have h1 := hc (p a) (b * (s (p b))⁻¹) hk
    have h2 : b * (s (p b))⁻¹ * (s (p a))⁻¹ = (s (p a))⁻¹ * (b * (s (p b))⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h1, inv_mul_cancel_left]
    change a * b * (s (p (a * b)))⁻¹ = a * (s (p a))⁻¹ * (b * (s (p b))⁻¹)
    rw [map_mul, map_mul, _root_.mul_inv_rev, mul_assoc a (s (p a))⁻¹, ← h2]
    group

def splitC [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] (p : G →* H) (s : H →* G)
    (hps : ∀ y, p (s y) = y) (hc : ∀ y, ∀ k ∈ p.ker, s y * k = k * s y) (hp : Continuous p) (hs : Continuous s) :
    G ≃ₜ* H × p.ker where
  toMulEquiv := splitE p s hps hc
  continuous_toFun := hp.prodMk (Continuous.subtype_mk (continuous_id.mul ((hs.comp hp).inv)) _)
  continuous_invFun := (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

def endK (p : G →* H) (θ : Monoid.End G) (θ₁ : Monoid.End H) (h : ∀ g, p (θ g) = θ₁ (p g)) : Monoid.End p.ker where
  toFun k := ⟨θ k, by
    have h2 : p (k : G) = 1 := k.2
    rw [MonoidHom.mem_ker, h, h2, map_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem splitE_theta (p : G →* H) (s : H →* G) (hps : ∀ y, p (s y) = y) (hc : ∀ y, ∀ k ∈ p.ker, s y * k = k * s y)
    (θ : Monoid.End G) (θ₁ : Monoid.End H) (h : ∀ g, p (θ g) = θ₁ (p g)) (h' : ∀ y, θ (s y) = s (θ₁ y)) (g : G) :
    splitE p s hps hc (θ g) = (θ₁ (splitE p s hps hc g).1, endK p θ θ₁ h (splitE p s hps hc g).2) := by
  refine Prod.ext (h g) (Subtype.ext ?_)
  change θ g * (s (p (θ g)))⁻¹ = θ (g * (s (p g))⁻¹)
  rw [h, map_mul, map_inv, h']

theorem haar_split {A B : Type} [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] (e : G ≃ₜ* A × B) (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ (μ₁ : Measure A) (μ₂ : Measure B), μ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ μ.map e = μ₁.prod μ₂ := by
  have h0 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let μ₁ : Measure A := Measure.haar
  let ν : Measure B := Measure.haar
  have h1 := Measure.isMulLeftInvariant_eq_smul (μ.map e) (μ₁.prod ν)
  have hc : Measure.haarScalarFactor (μ.map e) (μ₁.prod ν) ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  refine ⟨μ₁, Measure.haarScalarFactor (μ.map e) (μ₁.prod ν) • ν, inferInstance, ?_, ?_⟩
  · first | exact Measure.IsHaarMeasure.nnreal_smul _ hc | exact IsHaarMeasure.nnreal_smul _ hc | exact Measure.isHaarMeasure_nnreal_smul _ hc
  · rw [Measure.prod_smul_right]
    exact h1

end Abstract

section Concrete

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_thetaR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  refine Units.ext ?_
  ext i j
  rw [thetaR_val, ← map_inv]
  change f (σ (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i)) =
    τ (f (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i))
  exact h _

theorem thetaR_one' {A : Type} [CommRing A] (σ : A →+* A) : thetaR σ n 1 = 1 := map_one _

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) : cV v (conjAd E x) = starRingEnd ℂ (cV v x) :=
  congrFun ((infEq E).symm_apply_apply _) v

theorem continuous_cV (v : InfinitePlace E) : Continuous (cV (E := E) v) := by
  have h : Continuous fun x : InfiniteAdeleRing E => (infEq E).symm x :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        (continuous_apply w)
  exact (continuous_apply v).comp (h.comp continuous_fst)

theorem ga_ext' {g h : GA E n} (h1 : ∀ w, GeneralLinearGroup.map (cV w) g = GeneralLinearGroup.map (cV w) h)
    (h2 : GeneralLinearGroup.map (pFin E) g = GeneralLinearGroup.map (pFin E) h) : g = h := by
  refine ga_ext ?_ h2
  ext i j w
  exact congrArg (fun x : GL (Fin n) ℂ => x i j) (h1 w)

open Classical in

def sV (v : InfinitePlace E) : ℂ →ₙ+* Ad E where
  toFun x := sInf E (Pi.single v x)
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]

open Classical in
theorem cV_sV (v w : InfinitePlace E) (x : ℂ) : cV w (sV v x) = (Pi.single v x : InfinitePlace E → ℂ) w :=
  congrFun ((infEq E).symm_apply_apply _) w

theorem continuous_sV (v : InfinitePlace E) : Continuous (sV (E := E) v) := by
  classical
  have h0 : Continuous fun x : ℂ => (Pi.single v x : InfinitePlace E → ℂ) := continuous_pi fun w => by
    by_cases h : w = v
    · subst h; simpa using (continuous_id' : Continuous fun a : ℂ => a)
    · simpa [Pi.single_eq_of_ne h] using continuous_const
  have h : Continuous fun x : ℂ => infEq E (Pi.single v x) := (continuous_infEq E).comp h0
  exact h.prodMk continuous_const

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) : Continuous (cornerGL n s) := by
  refine Continuous.units_map _ ?_
  exact continuous_const.add (Continuous.matrix_map continuous_id hs)

theorem continuous_mapGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) : Continuous (GeneralLinearGroup.map (n := Fin n) f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

open Classical in
theorem cV_embInf (v w : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV w) (embInf n v y) = if w = v then y else 1 := by
  ext i j
  change (GeneralLinearGroup.map (pInf E) (embInf n v y)) i j w = _
  unfold embInf
  rw [MonoidHom.comp_apply, pInf_infGL]
  change (MonoidHom.mulSingle (fun _ : InfinitePlace E => GL (Fin n) ℂ) v y w).val i j = _
  by_cases h : w = v
  · subst h
    simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem pFin_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (pFin E) (embInf n v y) = 1 := by
  unfold embInf
  exact pFin_infGL _

theorem embInf_eq_cornerGL (v : InfinitePlace E) (y : GL (Fin n) ℂ) : embInf n v y = cornerGL n (sV v) y := by
  classical
  refine ga_ext' (fun w => ?_) ?_
  · rw [cV_embInf]
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, map_cornerGL_of_hom (sV w) (cV w) (RingHom.id ℂ) (fun x => by rw [cV_sV, Pi.single_eq_same]; rfl) y]
      ext i j
      rfl
    · rw [if_neg h, map_cornerGL_of_zero (sV v) (cV w) (fun x => by rw [cV_sV, Pi.single_eq_of_ne h]) y]
  · rw [pFin_embInf, map_cornerGL_of_zero (sV v) (pFin E) (fun x => rfl) y]

theorem continuous_embInf (v : InfinitePlace E) : Continuous (embInf (E := E) n v) := by
  have h : (embInf (E := E) n v : GL (Fin n) ℂ → GA E n) = cornerGL n (sV v) := funext (embInf_eq_cornerGL v)
  rw [h]
  exact continuous_cornerGL _ (continuous_sV v)

theorem cV_embInf_self (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV v) (embInf n v y) = y := by
  classical
  rw [cV_embInf, if_pos rfl]

theorem embInf_comm (v : InfinitePlace E) (y : GL (Fin n) ℂ) (k : GA E n)
    (hk : k ∈ (GeneralLinearGroup.map (n := Fin n) (cV (E := E) v)).ker) : embInf n v y * k = k * embInf n v y := by
  classical
  have hk' : GeneralLinearGroup.map (cV v) k = 1 := hk
  refine ga_ext' (fun w => ?_) ?_
  · rw [map_mul, map_mul, cV_embInf]
    by_cases h : w = v
    · subst h
      rw [hk']; simp
    · rw [if_neg h]; simp
  · rw [map_mul, map_mul, pFin_embInf]; simp

theorem cV_thetaA (v : InfinitePlace E) (g : GA E n) :
    GeneralLinearGroup.map (cV v) (thetaA E n g) = thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map (cV v) g) :=
  map_thetaR _ _ _ (cV_conjAd v) g

theorem thetaA_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    thetaA E n (embInf n v y) = embInf n v (thetaR (starRingEnd ℂ) n y) := by
  classical
  refine ga_ext' (fun w => ?_) ?_
  · rw [cV_thetaA, cV_embInf, cV_embInf]
    by_cases h : w = v
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, thetaR_one']
  · rw [pFin_embInf, map_thetaR (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun _ => rfl),
      pFin_embInf, thetaR_one']

theorem cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = PositivityTheory.Rg.BcB.D4.locGL v d := by
  ext i j
  exact pInf_algebraMap (d i j) v

theorem locallyCompact_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL {R : Type} [CommRing R] [TopologicalSpace R] [SecondCountableTopology R] :
    SecondCountableTopology (GL (Fin n) R) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem splitAt : PositivityTheory.Rg.BcB.D4.SplitAt := by
  intro E _ _ _ n v _ _ μ _
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (GA E n) := locallyCompact_GL
  haveI : SecondCountableTopology (GA E n) := secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin n) ℂ) := locallyCompact_GL
  haveI : SecondCountableTopology (GL (Fin n) ℂ) := secondCountable_GL
  letI mH : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI bH : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  let p : GA E n →* GL (Fin n) ℂ := GeneralLinearGroup.map (cV v)
  let s : GL (Fin n) ℂ →* GA E n := embInf n v
  have hp : Continuous p := continuous_mapGL _ (continuous_cV v)
  have hs : Continuous s := continuous_embInf v
  have hps : ∀ y, p (s y) = y := cV_embInf_self v
  have hc : ∀ y, ∀ k ∈ p.ker, s y * k = k * s y := embInf_comm v
  have hcl : IsClosed (p.ker : Set (GA E n)) := by
    have : (p.ker : Set (GA E n)) = p ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hp
  haveI lK : LocallyCompactSpace p.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI sK : SecondCountableTopology p.ker := TopologicalSpace.Subtype.secondCountableTopology _
  letI mK : MeasurableSpace p.ker := borel _
  haveI bK : BorelSpace p.ker := ⟨rfl⟩
  have hθ : ∀ g, p (thetaA E n g) = thetaR (starRingEnd ℂ) n (p g) := cV_thetaA v
  have hθ' : ∀ y, thetaA E n (s y) = s (thetaR (starRingEnd ℂ) n y) := thetaA_embInf v
  obtain ⟨μ₁, μ₂, h1, h2, h3⟩ := haar_split (splitC p s hps hc hp hs) μ
  refine ⟨p.ker, inferInstance, inferInstance, inferInstance, lK, sK, mK, bK, mH, bH,
    splitC p s hps hc hp hs, μ₁, μ₂, endK p (thetaA E n) (thetaR (starRingEnd ℂ) n) hθ, h1, h2, h3, fun _ => rfl, ?_, ?_, ?_⟩
  · intro y
    refine Prod.ext (hps y) (Subtype.ext ?_)
    change s y * (s (p (s y)))⁻¹ = 1
    rw [hps, mul_inv_cancel]
  · exact splitE_theta p s hps hc _ _ hθ hθ'
  · intro d
    have h := map_twCent_prod (splitE p s hps hc) (thetaA E n) (thetaR (starRingEnd ℂ) n)
      (endK p (thetaA E n) (thetaR (starRingEnd ℂ) n) hθ) (splitE_theta p s hps hc _ _ hθ hθ') (ratGL E n d)
    have h4 : (splitE p s hps hc (ratGL E n d)).1 = PositivityTheory.Rg.BcB.D4.locGL v d := cV_ratGL v d
    rw [h4] at h
    exact h

end Concrete

end GlobalTheory.CompanionTheory.SplitInf
