import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniversalJetCoordinatesPullbackStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartBaseChange

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem sp_sp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section Alg

variable {V V' : Type} [CommRing V] [CommRing V']

theorem jet_algHom_ext {κ B : Type} [CommRing B] [Algebra V B] {m : ℕ} (f g : Jet V κ m →ₐ[V] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

def asJet {κ κ' : Type} {m m' : ℕ} (g : JetR V κ m →ₐ[V] JetR V κ' m') : Jet V κ m →ₐ[V] Jet V κ' m' := g

theorem aug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  rw [GlobalTheory.JetTest.jetAug_mk]; simp

theorem jetZero_eq (κ : Type) (m : ℕ) :
    (asJet (jetZeroR V κ m)) = (Algebra.ofId V (Jet V κ 0)).comp jetAug := by
  apply jet_algHom_ext
  intro i
  rw [AlgHom.comp_apply, aug_X, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)

theorem aug_jetZero (κ : Type) (m : ℕ) :
    (jetAug : Jet V κ 0 →ₐ[V] V).comp (asJet (jetZeroR V κ m)) = jetAug := by
  apply jet_algHom_ext
  intro i
  rw [aug_X]
  exact aug_X (m := 0) i

theorem ker_aug_pow (κ : Type) (m : ℕ) : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ≤
      (orig V κ).map (Ideal.Quotient.mk (orig V κ ^ (m + 1))) := by
    intro w hw
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [RingHom.mem_ker, GlobalTheory.JetTest.jetAug_mk] at hw
    have h := sub_const_mem_orig p
    rw [hw, map_zero, sub_zero] at h
    exact Ideal.mem_map_of_mem _ h
  apply le_bot_iff.1
  refine (Ideal.pow_right_mono hle _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem zero_iff {κ κ' : Type} {m : ℕ} (ψ : Jet V κ m →ₐ[V] Jet V κ' m) :
    (∀ j, jetZeroR V κ' m (ψ (zR m j)) = 0) ↔ (jetAug : Jet V κ' m →ₐ[V] V).comp ψ = jetAug := by
  constructor
  · intro h
    apply jet_algHom_ext
    intro i
    rw [aug_X, AlgHom.comp_apply, ← aug_jetZero, AlgHom.comp_apply]
    exact (congrArg (jetAug : Jet V κ' 0 →ₐ[V] V) (h i)).trans (map_zero _)
  · intro h j
    have h1 := AlgHom.congr_fun h (Ideal.Quotient.mk _ (MvPolynomial.X j))
    rw [aug_X, AlgHom.comp_apply] at h1
    have h2 := AlgHom.congr_fun (jetZero_eq (V := V) κ' m) (ψ (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    rw [AlgHom.comp_apply, h1, map_zero] at h2
    exact h2

theorem coef_sq (φ : V →+* V') {κ κ' : Type} {m : ℕ} (g : Jet V κ m →ₐ[V] Jet V κ' m)
    (g' : Jet V' κ m →ₐ[V'] Jet V' κ' m)
    (h : ∀ i, g' (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      jetCoef φ κ' m (g (Ideal.Quotient.mk _ (MvPolynomial.X i)))) :
    (g' : Jet V' κ m →+* Jet V' κ' m).comp (jetCoef φ κ m) =
      (jetCoef φ κ' m).comp (g : Jet V κ m →+* Jet V κ' m) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show g' (Ideal.Quotient.mk _ (MvPolynomial.map φ (MvPolynomial.C r))) = jetCoef φ κ' m (g (algebraMap V _ r))
    rw [MvPolynomial.map_C, g.commutes]
    refine (g'.commutes (φ r)).trans ?_
    show _ = Ideal.Quotient.mk _ (MvPolynomial.map φ (MvPolynomial.C r))
    rw [MvPolynomial.map_C]
    rfl
  · intro i
    show g' (Ideal.Quotient.mk _ (MvPolynomial.map φ (MvPolynomial.X i))) = _
    rw [MvPolynomial.map_X]
    exact h i

theorem psJet_eq {n d : ℕ} (m : ℕ) (q : Fin n × Fin d) (f : PS V n d) (P : MvPolynomial (Fin n × Fin d) V)
    (h : ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = P.coeff e) :
    (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.psJet m f : Jet V (Fin n × Fin d) m) = Ideal.Quotient.mk _ P := by
  unfold ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.psJet
  refine Ideal.Quotient.eq.2 (Ideal.Quotient.eq_zero_iff_mem.1 ((GlobalTheory.JetTest.mk_eq_zero_iff (m := m) _).2 ?_))
  intro e he
  have hle : ∀ i, e i ≤ m := fun i => (Finsupp.le_degree i e).trans he
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_trunc, if_pos, h e he, sub_self]
  refine lt_of_le_of_ne (fun i => ?_) (fun hh => ?_)
  · simpa using (hle i).trans (Nat.le_succ m)
  · have := hle q
    rw [hh] at this
    simp at this

theorem substJ_X {n d : ℕ} (m : ℕ) (f : Fin d → PS V n d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0)
    (q : Fin 1 × Fin d) :
    substJ m f hf (Ideal.Quotient.mk _ (MvPolynomial.X q)) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.psJet m (f q.2) := by
  show MvPolynomial.aeval _ (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem subst_sq (φ : V →+* V') {n d : ℕ} (i0 : Fin n) (m : ℕ) (f : Fin d → PS V n d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (f' : Fin d → PS V' n d)
    (hf' : ∀ j, MvPowerSeries.constantCoeff (f' j) = 0) (e : ∀ j, f' j = MvPowerSeries.map φ (f j)) :
    (asJet (substJ m f' hf') :
        Jet V' (Fin 1 × Fin d) m →+* Jet V' (Fin n × Fin d) m).comp (jetCoef φ _ m) =
      (jetCoef φ _ m).comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2) :
        Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
          Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) := by
  apply coef_sq
  intro q
  refine (substJ_X m f' hf' q).trans ?_
  unfold jetSubstP
  rw [GlobalTheory.JetTest.jetMap_mk, MvPolynomial.aeval_X]
  refine psJet_eq m (i0, q.2) _ (MvPolynomial.map φ _) fun a ha => ?_
  have hc : MvPolynomial.constantCoeff (psTrunc m (f q.2)) = 0 := by
    rw [MvPolynomial.constantCoeff_eq, GlobalTheory.JetTest.coeff_psTrunc, if_pos (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  rw [hc, map_zero, sub_zero, MvPolynomial.coeff_map, GlobalTheory.JetTest.coeff_psTrunc, if_pos ha, e,
    MvPowerSeries.coeff_map]

theorem copy_sq (φ : V →+* V') {n d : ℕ} (i : Fin n) (m : ℕ) :
    (asJet (jetPt (T := V') (d := d) i m) :
        Jet V' (Fin 1 × Fin d) m →+* Jet V' (Fin n × Fin d) m).comp (jetCoef φ _ m) =
      (jetCoef φ _ m).comp ((jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) :
          Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) := by
  apply coef_sq
  intro q
  refine (substJ_X m (fun j => (MvPowerSeries.X (i, j) : PS V' n d)) (fun j => by simp) q).trans ?_
  unfold jetCopy
  rw [GlobalTheory.JetTest.jetMap_mk, MvPolynomial.aeval_X]
  refine psJet_eq m (i, q.2) _ (MvPolynomial.map φ _) fun a _ => ?_
  rw [MvPolynomial.map_X, ← MvPolynomial.coe_X, MvPolynomial.coeff_coe]

theorem coef_alg (φ : V →+* V') (κ : Type) (m : ℕ) :
    (jetCoef φ κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap V' (Jet V' κ m)).comp φ := by
  ext r
  show Ideal.Quotient.mk _ (MvPolynomial.map φ (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C]
  rfl

end Alg

section Geo

variable {V V' : Type} [CommRing V] [CommRing V']

def toAlg {G : Over (Sp V)} {A : Type} [CommRing A] [Algebra V A] (y : overAt (𝟙 (Sp V)) A ⟶ G) : algOver V A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofAlg {G : Over (Sp V)} {A : Type} [CommRing A] [Algebra V A] (y : algOver V A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem univ_toAlg (G : Over (Sp V)) [GrpObj G] (κ : Type) (z : GlobalTheory.PowGerm.JetPts G κ)
    (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) :
    (∀ m, algOverHom (jetTruncR V κ m) ≫ toAlg (z (m + 1)) = toAlg (z m)) ∧
    (∀ m, algOverHom (jetZeroR V κ m) ≫ toAlg (z m) = toUnit _ ≫ η[G]) ∧
    ∀ (κ' : Type) (m : ℕ) (y : algOver V (JetR V κ' m) ⟶ G),
      algOverHom (jetZeroR V κ' m) ≫ y = toUnit _ ≫ η[G] →
      ∃! ψ : JetR V κ m →ₐ[V] JetR V κ' m,
        (∀ j, jetZeroR V κ' m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ toAlg (z m) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => ?_, fun m => ?_, fun κ' m y hy => ?_⟩
  · apply Over.OverMorphism.ext
    exact congrArg CommaMorphism.left (h1 m)
  · apply Over.OverMorphism.ext
    have h := congrArg CommaMorphism.left (h2 m)
    change spMap _ ≫ (z m).left = (spMap (algebraMap V V) ≫ 𝟙 _) ≫ η[G].left at h
    change spMap ((asJet (jetZeroR V κ m)) : Jet V κ m →+* Jet V κ 0) ≫ (z m).left =
      spMap (algebraMap V (Jet V κ 0)) ≫ η[G].left
    rw [jetZero_eq, AlgHom.comp_toRingHom, ← sp_sp, Category.assoc, h, Category.comp_id, ← Category.assoc, sp_sp]
    rfl
  · let y' : overAt (𝟙 (Sp V)) (Jet V κ' m) ⟶ G := ofAlg (A := Jet V κ' m) y
    have hy' : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V κ' m →ₐ[V] V) ≫ y' = 1 := by
      apply Over.OverMorphism.ext
      have h := congrArg CommaMorphism.left hy
      change spMap ((asJet (jetZeroR V κ' m)) : Jet V κ' m →+* Jet V κ' 0) ≫ (y' : overAt (𝟙 (Sp V)) (Jet V κ' m) ⟶ G).left =
        spMap (algebraMap V (Jet V κ' 0)) ≫ η[G].left at h
      change spMap ((jetAug : Jet V κ' m →ₐ[V] V) : Jet V κ' m →+* V) ≫ (y' : overAt (𝟙 (Sp V)) (Jet V κ' m) ⟶ G).left =
        (spMap (algebraMap V V) ≫ 𝟙 _) ≫ η[G].left
      rw [← aug_jetZero, AlgHom.comp_toRingHom, ← sp_sp, Category.assoc, h, Category.comp_id, ← Category.assoc,
        spMap_comp_alg]
    obtain ⟨ψ, ⟨a1, a2⟩, hu⟩ := h3 (Jet V κ' m) jetAug m (ker_aug_pow κ' m) _ hy'
    refine ⟨ψ, ⟨(zero_iff ψ).2 a1, ?_⟩, fun ψ' h' => hu ψ' ⟨(zero_iff ψ').1 h'.1, ?_⟩⟩
    · apply Over.OverMorphism.ext
      exact congrArg CommaMorphism.left a2
    · apply Over.OverMorphism.ext
      exact congrArg CommaMorphism.left h'.2

variable (φ : V →+* V') (G : Over (Sp V)) [GrpObj G] (G' : Over (Sp V')) [GrpObj G'] (Fm : G'.left ⟶ G.left)
  (hP : IsGrpPullback G' G (spMap φ) Fm)

include hP in
theorem pb_ext {T : Over (Sp V')} (a b : T ⟶ G') (h : a.left ≫ Fm = b.left ≫ Fm) : a = b := by
  apply Over.OverMorphism.ext
  exact hP.1.hom_ext h ((Over.w a).trans (Over.w b).symm)

variable {d : ℕ} (z : GlobalTheory.PowGerm.JetPts G (Fin 1 × Fin d)) (z' : GlobalTheory.PowGerm.JetPts G' (Fin 1 × Fin d))
  (hz : ∀ m, (z' m).left ≫ Fm = spMap (jetCoef φ (Fin 1 × Fin d) m) ≫ (z m).left)

include hz in
theorem left_sq {n : ℕ} (m : ℕ) (g : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m)
    (g' : Jet V' (Fin 1 × Fin d) m →ₐ[V'] Jet V' (Fin n × Fin d) m)
    (h : (g' : Jet V' (Fin 1 × Fin d) m →+* Jet V' (Fin n × Fin d) m).comp (jetCoef φ _ m) =
      (jetCoef φ _ m).comp (g : Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m)) :
    (algOverHom g' ≫ toAlg (z' m)).left ≫ Fm =
      spMap (jetCoef φ (Fin n × Fin d) m) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ z m).left := by
  change (spMap (g' : Jet V' (Fin 1 × Fin d) m →+* Jet V' (Fin n × Fin d) m) ≫ (z' m).left) ≫ Fm =
    spMap _ ≫ spMap (g : Jet V (Fin 1 × Fin d) m →+* Jet V (Fin n × Fin d) m) ≫ (z m).left
  rw [Category.assoc, hz, ← Category.assoc, sp_sp, h, ← sp_sp, Category.assoc]

include hP hz in
theorem law_bc (m : ℕ) (F : Fin d → PS V 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin d → PS V' 2 d) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (e : ∀ j, F' j = MvPowerSeries.map φ (F j))
    (hl : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ z m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ z m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ z m)) :
    algOverHom (substJ m F' hF') ≫ toAlg (z' m) =
      (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ toAlg (z' m)) *
        (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ toAlg (z' m)) := by
  apply pb_ext φ G G' Fm hP
  let c : Over.mk ((algOver V' (Jet V' (Fin 2 × Fin d) m)).hom ≫ spMap φ) ⟶
      overAt (𝟙 (Sp V)) (Jet V (Fin 2 × Fin d) m) :=
    Over.homMk (spMap (jetCoef φ (Fin 2 × Fin d) m)) (by
      change spMap _ ≫ spMap (algebraMap V (Jet V (Fin 2 × Fin d) m)) ≫ 𝟙 _ =
        spMap (algebraMap V' (Jet V' (Fin 2 × Fin d) m)) ≫ spMap φ
      rw [Category.comp_id, sp_sp, sp_sp, coef_alg])
  have h := hP.2 (algOver V' (Jet V' (Fin 2 × Fin d) m))
    (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ toAlg (z' m))
    (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ toAlg (z' m))
    (c ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ z m)
    (c ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ z m)
    (left_sq φ G G' Fm z z' hz m _ _ (copy_sq φ 0 m)).symm
    (left_sq φ G G' Fm z z' hz m _ _ (copy_sq φ 1 m)).symm
  refine Eq.trans ?_ h
  rw [← MonObj.comp_mul, ← hl]
  exact left_sq φ G G' Fm z z' hz m _ _ (subst_sq φ 0 m F hF F' hF' e)

include hP hz in
theorem act_bc (m : ℕ) (α : G ⟶ G) (α' : G' ⟶ G') (hα : α'.left ≫ Fm = Fm ≫ α.left)
    (F : Fin d → PS V 1 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin d → PS V' 1 d) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (e : ∀ j, F' j = MvPowerSeries.map φ (F j))
    (hl : z m ≫ α =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ z m) :
    toAlg (z' m) ≫ α' = algOverHom (substJ m F' hF') ≫ toAlg (z' m) := by
  apply pb_ext φ G G' Fm hP
  refine Eq.trans ?_ (left_sq φ G G' Fm z z' hz m _ _ (subst_sq φ 0 m F hF F' hF' e)).symm
  rw [← hl]
  change ((z' m).left ≫ α'.left) ≫ Fm = spMap _ ≫ (z m).left ≫ α.left
  rw [Category.assoc, hα, ← Category.assoc, hz, Category.assoc]

end Geo

end GlobalTheory.ChartBaseChange

open GlobalTheory.ChartBaseChange in

theorem GlobalTheory.integralChart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' Ch.I.G (spMap φ)), ∃ (F' : FGLaw T'.V (chD Ch.ch)) (x' : ∀ m : ℕ, algOver T'.V (JetR T'.V (Fin 1 × Fin (chD Ch.ch)) m) ⟶ t'.G) (act' : Germ.OAct (𝓞 E) F'), F'.F = (fun i => MvPowerSeries.map φ (Ch.FT i)) ∧ (∀ a, act'.act a = fun i => MvPowerSeries.map φ (Ch.actT a i)) ∧ IsChartJ t'.G F' x' ∧ ChartActs t'.G x' t'.act.toRingAct act' := by
  intro E _ _ _ H Dw l Xo c T io y Ch T' φ t' mp
  letI := H.starRing
  obtain ⟨BT, hF, hA, -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y Ch
  have hU := GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y Ch
  obtain ⟨z', hU', hz⟩ := GlobalTheory.T.exists_universalJetCoordinates_pullback T.V T'.V φ Ch.I.G.G t'.G mp.cm.F mp.cart _ Ch.xT hU
  obtain ⟨u1, u2, u3⟩ := univ_toAlg t'.G _ z' hU'
  refine ⟨Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap.mapG φ BT.G, fun m => toAlg (z' m), Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap.mapA φ BT.A,
    ?_, fun a => ?_, ⟨u1, u2, u3, fun m => ?_⟩, fun m a => ?_⟩
  · rw [← hF]; rfl
  · rw [← hA]; rfl
  · exact law_bc φ Ch.I.G.G t'.G mp.cm.F mp.cart Ch.xT z' hz m Ch.FT (hF ▸ BT.G.const) _ _
      (fun j => by rw [← hF]; rfl) (Ch.chartT.law m)
  · exact act_bc φ Ch.I.G.G t'.G mp.cm.F mp.cart Ch.xT z' hz m (Ch.I.G.act.act a) (t'.act.act a) (mp.act a)
      (Ch.actT a) (hA ▸ BT.A.const a) _ _ (fun j => by rw [← hA]; rfl) (Ch.chartT.act m a)
