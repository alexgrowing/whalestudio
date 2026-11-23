import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermSubstitutionStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf

open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section Jets

variable {R : Type} [CommRing R] {d d' : ℕ}

abbrev sgL (f : Fin d → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) R) p.1 p.2)

abbrev sgR (f : Fin d → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (f j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) R) p.1 p.2)

abbrev sg1 (f : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 1 × Fin d') m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (f p.2)

theorem subst_copy {κ : Type} {n : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial κ R) (i : Fin n) :
    (jetSubstP m φ).comp (jetCopy d m i) = jetSubstP m fun p : Fin 1 × Fin d => φ (i, p.2) := by
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetSubstP, jetMap_mk]

theorem psIn_eq {n : ℕ} (m : ℕ) (i : Fin n) (f : PS R 1 d) :
    psIn d m ![i] f = MvPolynomial.aeval (fun q : Fin 1 × Fin d => (MvPolynomial.X (i, q.2) :
      MvPolynomial (Fin n × Fin d) R)) (psTrunc m f) := by
  have h : (MvPolynomial.rename (fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin n) p.1, p.2)) :
      MvPolynomial (Fin 1 × Fin d) R →ₐ[R] MvPolynomial (Fin n × Fin d) R) =
      MvPolynomial.aeval (fun q : Fin 1 × Fin d => (MvPolynomial.X (i, q.2) : MvPolynomial (Fin n × Fin d) R)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, j⟩
    simp
  exact DFunLike.congr_fun h _

theorem copy_subst {κ : Type} {n : ℕ} (m : ℕ) (i : Fin n) (f : κ → PS R 1 d) :
    (jetCopy d m i).comp (jetSubstP m fun p : κ => psTrunc m (f p)) =
      jetSubstP m fun p : κ => psIn d m ![i] (f p) := by
  apply jet_hom_ext
  intro p
  have hc : MvPolynomial.constantCoeff (psIn d m ![i] (f p)) = MvPolynomial.constantCoeff (psTrunc m (f p)) :=
    MvPolynomial.constantCoeff_rename _ _
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, jetMap_mk, MvPolynomial.aeval_X, map_sub, hc]
  rw [psIn_eq]
  simp [MvPolynomial.algebraMap_eq]

theorem sgL_copy0 (f : Fin d → PS R 1 d) (m : ℕ) :
    (sgL f m).comp (jetCopy d m 0) = (jetCopy d m 0).comp (sg1 f m) :=
  (subst_copy m _ 0).trans (copy_subst m 0 (fun p : Fin 1 × Fin d => f p.2)).symm

theorem sgL_copy1 (f : Fin d → PS R 1 d) (m : ℕ) : (sgL f m).comp (jetCopy d m 1) = jetCopy d m 1 := by
  refine (subst_copy m _ 1).trans ?_
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetSubstP, jetMap_mk]

theorem sgR_copy0 (f : Fin d → PS R 1 d) (m : ℕ) : (sgR f m).comp (jetCopy d m 0) = jetCopy d m 0 := by
  refine (subst_copy m _ 0).trans ?_
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetSubstP, jetMap_mk]

theorem sgR_copy1 (f : Fin d → PS R 1 d) (m : ℕ) :
    (sgR f m).comp (jetCopy d m 1) = (jetCopy d m 1).comp (sg1 f m) :=
  (subst_copy m _ 1).trans (copy_subst m 1 (fun p : Fin 1 × Fin d => f p.2)).symm

theorem double_substitution_jet_inclusion (Qs : Fin d' → PS R 1 d) (m : ℕ) (i : Fin 2) :
    (sub2 Qs m).comp (jetCopy d' m i) = (jetCopy d m i).comp (sub1 Qs m) :=
  (subst_copy m _ i).trans (copy_subst m i (fun p : Fin 1 × Fin d' => Qs p.2)).symm

theorem jet_two_points_alg_hom_ext {B : Type} [CommRing B] [Algebra R B] {m : ℕ} {f g : Jet R (Fin 2 × Fin d) m →ₐ[R] B}
    (h0 : f.comp (jetCopy d m 0) = g.comp (jetCopy d m 0)) (h1 : f.comp (jetCopy d m 1) = g.comp (jetCopy d m 1)) :
    f = g := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  have e : ∀ i : Fin 2, jetCopy (S := R) d m i (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := fun i => by simp [jetCopy, jetMap_mk]
  fin_cases i
  · exact (congrArg f (e 0)).symm.trans ((DFunLike.congr_fun h0 _).trans (congrArg g (e 0)))
  · exact (congrArg f (e 1)).symm.trans ((DFunLike.congr_fun h1 _).trans (congrArg g (e 1)))

theorem left_shift_double_substitution {fA : Fin d → PS R 1 d} {fB : Fin d' → PS R 1 d'} {Qs : Fin d' → PS R 1 d} {m : ℕ}
    (hC : (sg1 fA m).comp (sub1 Qs m) = (sub1 Qs m).comp (sg1 fB m)) :
    (sgL fA m).comp (sub2 Qs m) = (sub2 Qs m).comp (sgL fB m) := by
  apply jet_two_points_alg_hom_ext
  · rw [AlgHom.comp_assoc, double_substitution_jet_inclusion, ← AlgHom.comp_assoc, sgL_copy0, AlgHom.comp_assoc, hC, AlgHom.comp_assoc,
      sgL_copy0, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, double_substitution_jet_inclusion]
  · rw [AlgHom.comp_assoc, double_substitution_jet_inclusion, ← AlgHom.comp_assoc, sgL_copy1, AlgHom.comp_assoc, sgL_copy1, double_substitution_jet_inclusion]

theorem right_shift_double_substitution {fA : Fin d → PS R 1 d} {fB : Fin d' → PS R 1 d'} {Qs : Fin d' → PS R 1 d} {m : ℕ}
    (hC : (sg1 fA m).comp (sub1 Qs m) = (sub1 Qs m).comp (sg1 fB m)) :
    (sgR fA m).comp (sub2 Qs m) = (sub2 Qs m).comp (sgR fB m) := by
  apply jet_two_points_alg_hom_ext
  · rw [AlgHom.comp_assoc, double_substitution_jet_inclusion, ← AlgHom.comp_assoc, sgR_copy0, AlgHom.comp_assoc, sgR_copy0, double_substitution_jet_inclusion]
  · rw [AlgHom.comp_assoc, double_substitution_jet_inclusion, ← AlgHom.comp_assoc, sgR_copy1, AlgHom.comp_assoc, hC, AlgHom.comp_assoc,
      sgR_copy1, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, double_substitution_jet_inclusion]

theorem psJet_subQ (Qs : Fin d' → PS R 1 d) (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) (m : ℕ)
    (f : PS R 2 d') : psJet m (subQ Qs f) = sub2 Qs m (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d', MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d p.1] (Qs p.2)) = 0 := fun p =>
    (TB.LogPf.cc_ev (fun j i => by simp [pt]) _).trans (hQ p.2)
  rw [subQ, FBIdJet.psJet_subst m _ ha f]
  apply DFunLike.congr_fun
  refine jet_hom_ext fun p => ?_
  have hc : MvPolynomial.constantCoeff (psIn d m ![p.1] (Qs p.2)) = 0 := (FBIdPh.cc_psIn d m _ _).trans (hQ p.2)
  simp only [sub2, jetSubstP, jetMap_mk, MvPolynomial.aeval_X, hc, map_zero, sub_zero]
  exact (GlobalTheory.FrameTwistCompare.mk_psIn_psJet m p.1 (Qs p.2)).symm

theorem alg {M : Type} [CommGroup M] (wL wB eσ eτ bσ bτ Wσ Wτ ad adB uσ uτ : M)
    (h1 : wL * eσ = ad * eτ) (h2 : wB * bσ = adB * bτ) (h3 : eσ * Wσ = uσ⁻¹ * bσ) (h3' : eτ * Wτ = uτ⁻¹ * bτ)
    (h4 : wL * (Wτ * Wσ⁻¹) = wB) : adB * uτ = uσ * ad := by
  have hb1 : bσ = uσ * (eσ * Wσ) := by rw [h3, mul_inv_cancel_left]
  have hb2 : bτ = uτ * (eτ * Wτ) := by rw [h3', mul_inv_cancel_left]
  subst hb1 hb2 h4
  have hW : Wσ⁻¹ * Wσ = 1 := inv_mul_cancel _
  have key : (adB * uτ) * (eτ * Wτ) = (uσ * ad) * (eτ * Wτ) :=
    calc (adB * uτ) * (eτ * Wτ) = adB * (uτ * (eτ * Wτ)) := by ac_rfl
      _ = wL * (Wτ * Wσ⁻¹) * (uσ * (eσ * Wσ)) := h2.symm
      _ = (wL * eσ) * (uσ * Wτ) * (Wσ⁻¹ * Wσ) := by ac_rfl
      _ = (ad * eτ) * (uσ * Wτ) := by rw [h1, hW, _root_.mul_one]
      _ = (uσ * ad) * (eτ * Wτ) := by ac_rfl
  exact mul_right_cancel key

end Jets

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X) {d : ℕ}

theorem fib_ext {T : Over (Sp k)} {p p' : T ⟶ GF t x}
    (h : p.left ≫ pullback.fst t.G.hom x = p'.left ≫ pullback.fst t.G.hom x) : p = p' :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w p).trans (Over.w p').symm))

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem homAt_fib {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  refine fib_ext t x ?_
  rw [Over.comp_left, Category.assoc, fibPt_fst, fibPt_fst, Over.comp_left]
  rfl

def jr (xm : ∀ m, jOG x d m 1 ⟶ t.G) (m : ℕ) :
    overAt (𝟙 (Sp k)) (Jet k (Fin 2 × Fin d) m) ⟶ GF t x ⊗ GF t x :=
  lift (fibPt t x (jptG t x d xm m (0 : Fin 2))) (fibPt t x (jptG t x d xm m (1 : Fin 2)))

def jrX (xm : ∀ m, jOG x d m 1 ⟶ t.G) (m : ℕ) :
    jOG x d m 2 ⟶ Over.mk ((GF t x ⊗ GF t x).hom ≫ x) :=
  Over.homMk (jr t x xm m).left (by
    have h := Over.w (jr t x xm m)
    show (jr t x xm m).left ≫ (GF t x ⊗ GF t x).hom ≫ x = _
    rw [← Category.assoc, h]
    simp)

theorem jr_sq (xm : ∀ m, jOG x d m 1 ⟶ t.G) (m : ℕ) :
    (jr t x xm m).left ≫ sqMap t x =
      (lift (jptG t x d xm m (0 : Fin 2)) (jptG t x d xm m (1 : Fin 2))).left := by
  have h : jrX t x xm m ≫ lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _)) =
      lift (jptG t x d xm m (0 : Fin 2)) (jptG t x d xm m (1 : Fin 2)) := by
    rw [comp_lift]
    congr 1
    · apply Over.OverMorphism.ext
      show (jr t x xm m).left ≫ (fst (GF t x) (GF t x)).left ≫ pullback.fst t.G.hom x = _
      rw [← Category.assoc, ← Over.comp_left, jr, lift_fst, fibPt_fst]
    · apply Over.OverMorphism.ext
      show (jr t x xm m).left ≫ (snd (GF t x) (GF t x)).left ≫ pullback.fst t.G.hom x = _
      rw [← Category.assoc, ← Over.comp_left, jr, lift_snd, fibPt_fst]
  exact congrArg (fun f => f.left) h

theorem jr_sqPt (xm : ∀ m, jOG x d m 1 ⟶ t.G) (m : ℕ) (a : t.G ⊗ t.G ⟶ t.G) :
    jr t x xm m ≫ sqPt t x a =
      fibPt t x (lift (jptG t x d xm m (0 : Fin 2)) (jptG t x d xm m (1 : Fin 2)) ≫ a) := by
  refine fib_ext t x ?_
  rw [fibPt_fst, Over.comp_left, Over.comp_left, Category.assoc, ← jr_sq]
  show _ ≫ (toF t x _ _).left ≫ _ = _
  rw [Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

end Pts

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X) {d : ℕ} (xm : ∀ m, jOG x d m 1 ⟶ t.G)

theorem right_shift_first_point (f : Fin d → PS k 1 d) (m : ℕ) :
    homAt x (sgR f m) ≫ jptG t x d xm m (0 : Fin 2) = jptG t x d xm m (0 : Fin 2) := by
  rw [jptG, ← Category.assoc, homAt_comp, sgR_copy0]

theorem left_shift_second_point (f : Fin d → PS k 1 d) (m : ℕ) :
    homAt x (sgL f m) ≫ jptG t x d xm m (1 : Fin 2) = jptG t x d xm m (1 : Fin 2) := by
  rw [jptG, ← Category.assoc, homAt_comp, sgL_copy1]

theorem right_shift_second_point {f : Fin d → PS k 1 d} {m : ℕ} {b : t.G ⟶ t.G} (h : xm m ≫ b = homAt x (sg1 f m) ≫ xm m) :
    homAt x (sgR f m) ≫ jptG t x d xm m (1 : Fin 2) = jptG t x d xm m (1 : Fin 2) ≫ b := by
  rw [jptG, ← Category.assoc, homAt_comp, sgR_copy1, ← homAt_comp, Category.assoc, Category.assoc, h]

theorem left_shift_first_point {f : Fin d → PS k 1 d} {m : ℕ} {b : t.G ⟶ t.G} (h : xm m ≫ b = homAt x (sg1 f m) ≫ xm m) :
    homAt x (sgL f m) ≫ jptG t x d xm m (0 : Fin 2) = jptG t x d xm m (0 : Fin 2) ≫ b := by
  rw [jptG, ← Category.assoc, homAt_comp, sgL_copy0, ← homAt_comp, Category.assoc, Category.assoc, h]

theorem jr_right {f : Fin d → PS k 1 d} {m : ℕ} {b : t.G ⟶ t.G} (h : xm m ≫ b = homAt x (sg1 f m) ≫ xm m)
    (I : Finset (Fin 2)) :
    jr t x xm m ≫ sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ b] I) =
      homAt (𝟙 (Sp k)) (sgR f m) ≫ fibPt t x (psum t.G ![jptG t x d xm m (0 : Fin 2), jptG t x d xm m (1 : Fin 2)] I) := by
  rw [jr_sqPt, homAt_fib]
  congr 1
  refine (psum_hom (preHom _) _ I).trans (Eq.trans ?_ (psum_hom (preHom _) _ I).symm)
  refine congrArg (fun z => psum t.G z I) (funext fun i => ?_)
  fin_cases i
  · exact (lift_fst _ _).trans (right_shift_first_point t x xm f m).symm
  · exact (lift_snd_assoc _ _ _).trans (right_shift_second_point t x xm h).symm

theorem jr_left {f : Fin d → PS k 1 d} {m : ℕ} {b : t.G ⟶ t.G} (h : xm m ≫ b = homAt x (sg1 f m) ≫ xm m)
    (I : Finset (Fin 2)) :
    jr t x xm m ≫ sqPt t x (psum t.G ![fst t.G t.G ≫ b, snd t.G t.G] I) =
      homAt (𝟙 (Sp k)) (sgL f m) ≫ fibPt t x (psum t.G ![jptG t x d xm m (0 : Fin 2), jptG t x d xm m (1 : Fin 2)] I) := by
  rw [jr_sqPt, homAt_fib]
  congr 1
  refine (psum_hom (preHom _) _ I).trans (Eq.trans ?_ (psum_hom (preHom _) _ I).symm)
  refine congrArg (fun z => psum t.G z I) (funext fun i => ?_)
  fin_cases i
  · exact (lift_fst_assoc _ _ _).trans (left_shift_first_point t x xm h).symm
  · exact (lift_snd _ _).trans (left_shift_second_point t x xm f m).symm

end Act

section Quot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {x : Sp k ⟶ X} {d d' : ℕ}

theorem pt_q (Q : AbQuot t x) (xm : ∀ m, jOG x d m 1 ⟶ t.G) (xB : ∀ m, jOG (𝟙 (Sp k)) d' m 1 ⟶ Q.tB.G)
    (Qs : Fin d' → PS k 1 d) (hq : ∀ m, fibPt t x (xm m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ xB m) (m : ℕ)
    (i : Fin 2) : fibPt t x (jptG t x d xm m i) ≫ Q.q =
      homAt (𝟙 (Sp k)) (sub2 Qs m) ≫ jptG Q.tB (𝟙 (Sp k)) d' xB m i := by
  rw [jptG, jptG, ← homAt_fib, Category.assoc, hq, ← Category.assoc, homAt_comp, ← double_substitution_jet_inclusion, ← homAt_comp,
    Category.assoc]

theorem jr_qq (Q : AbQuot t x) (xm : ∀ m, jOG x d m 1 ⟶ t.G) (xB : ∀ m, jOG (𝟙 (Sp k)) d' m 1 ⟶ Q.tB.G)
    (Qs : Fin d' → PS k 1 d) (hq : ∀ m, fibPt t x (xm m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ xB m) (m : ℕ) :
    (jr t x xm m).left ≫ qq Q = (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫
      (lift (jptG Q.tB (𝟙 (Sp k)) d' xB m (0 : Fin 2)) (jptG Q.tB (𝟙 (Sp k)) d' xB m (1 : Fin 2))).left := by
  have h : jr t x xm m ≫ lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q) =
      homAt (𝟙 (Sp k)) (sub2 Qs m) ≫
        lift (jptG Q.tB (𝟙 (Sp k)) d' xB m (0 : Fin 2)) (jptG Q.tB (𝟙 (Sp k)) d' xB m (1 : Fin 2)) := by
    rw [comp_lift, comp_lift, jr, lift_fst_assoc, lift_snd_assoc, pt_q Q xm xB Qs hq, pt_q Q xm xB Qs hq]
  exact congrArg (fun f => f.left) h

end Quot

theorem val_pull1 {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {z : Y'} {J : (Y' ⟶ X) → L.ι}
    (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    val (LB.pullGen L φ ε c h) (𝟙 Y') z J = val c h z J :=
  (val_pull hJ c h (𝟙 Y')).trans (by rw [Category.id_comp])

set_option maxHeartbeats 4000000 in
theorem adRel_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ lam : PS k 2 d, (∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹)) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) 1 → subQ Qs (gB.B.ad a) * ev (n := 2) ![pt k d 0, comp1 (g.B.A.act (H.bar a)) (pt k d 1)] lam = ev (n := 2) ![comp1 (g.B.A.act a) (pt k d 0), pt k d 1] lam * g.B.ad a := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB w hw Qs hQ hq lam hlam a wL wB hwL hwB hAd hAdB h4
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨U, hUl, hTr⟩ := hlam m
  obtain ⟨u, hu, hc⟩ := hAd m
  obtain ⟨uB, huB, hcB⟩ := hAdB m
  have hL := t.PP.isLB
  have hM := Q.tB.PP.isLB
  have hC := GlobalTheory.T.abelian_quotient_germ_substitution E H hstar X t k p x Q d d' g gB Qs hQ hq m
  rw [FBIdJet.psJet_mul, FBIdJet.psJet_mul, psJet_subQ Qs hQ,
    ← GlobalTheory.FrameTwistCompare.jetSubstP_right m (g.B.A.const (H.bar a)) lam,
    ← GlobalTheory.FrameTwistCompare.jetSubstP_left m (g.B.A.const a) lam, ← hUl, ← hu, ← huB]
  have hσ2 := left_shift_double_substitution (fA := g.B.A.act a) (fB := gB.B.A.act a) (Qs := Qs) (m := m) (hC a)
  have hτ2 := right_shift_double_substitution (fA := g.B.A.act (H.bar a)) (fB := gB.B.A.act (H.bar a)) (Qs := Qs) (m := m) (hC (H.bar a))
  have hcσ : (homAt x (sgL (g.B.A.act a) m)).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left =
      (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ (homAt (𝟙 (Sp k)) (sgL (gB.B.A.act a) m)).left :=
    congrArg (fun f => f.left) ((homAt_comp (𝟙 (Sp k)) (sub2 Qs m) (sgL (g.B.A.act a) m)).trans
      ((congrArg (homAt (𝟙 (Sp k))) hσ2).trans (homAt_comp (𝟙 (Sp k)) _ _).symm))
  have hcτ : (homAt x (sgR (g.B.A.act (H.bar a)) m)).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left =
      (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ (homAt (𝟙 (Sp k)) (sgR (gB.B.A.act (H.bar a)) m)).left :=
    congrArg (fun f => f.left) ((homAt_comp (𝟙 (Sp k)) (sub2 Qs m) (sgR (g.B.A.act (H.bar a)) m)).trans
      ((congrArg (homAt (𝟙 (Sp k))) hτ2).trans (homAt_comp (𝟙 (Sp k)) _ _).symm))
  have hkey : unitΓ (Units.map (sub2 Qs m : _ →* _) uB) *
        unitΓ (Units.map (sgR (g.B.A.act (H.bar a)) m : _ →* _) U) =
      unitΓ (Units.map (sgL (g.B.A.act a) m : _ →* _) U) * unitΓ u := by
    refine unit_ext (V := ⊤) fun y _ => ?_
    rw [map_mul, map_mul]
    choose JL hJL using fun χ : Sp (Jet k (Fin 2 × Fin d) m) ⟶ t.G.left => exists_chart hL (χ y)
    choose JM hJM using fun χ : Sp (Jet k (Fin 2 × Fin d) m) ⟶ Q.tB.G.left => exists_chart hM (χ y)
    have gInv : ∀ σ' : Jet k (Fin 2 × Fin d) m →ₐ[k] Jet k (Fin 2 × Fin d) m,
        gm (homAt x σ').left y ⊤ (unitΓ U⁻¹) = (gm (𝟙 _) y ⊤ (unitΓ (Units.map (σ' : _ →* _) U)))⁻¹ := fun σ' => by
      rw [show unitΓ U⁻¹ = (unitΓ U)⁻¹ from map_inv _ U, map_inv]
      exact congrArg _ (FrRatio.gm_map σ' U y)
    have E1 := (val_corr hJL hc (𝟙 _)).trans (GermB.val_scale t _ _ _ _ _ y JL hJL)
    rw [val_mul hJL] at E1
    have h1 : val (Z := Sp (Jet k (Fin 2 × Fin d) m)) wL (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left y JL *
        val (Z := Sp (Jet k (Fin 2 × Fin d) m)) (g.e m) (homAt x (sgL (g.B.A.act a) m)).left y JL =
        gm (𝟙 (Sp (Jet k (Fin 2 × Fin d) m))) y ⊤ (unitΓ u) *
          val (Z := Sp (Jet k (Fin 2 × Fin d) m)) (g.e m) (homAt x (sgR (g.B.A.act (H.bar a)) m)).left y JL :=
      (congrArg₂ (· * ·) (val_pull1 hJL _ _) (val_pull1 hJL _ _)).symm.trans
        (E1.trans (congrArg₂ (· * ·) rfl (val_pull1 hJL _ _)))
    have E2 := (val_corr hJM hcB (homAt (𝟙 (Sp k)) (sub2 Qs m)).left).trans
      (GermB.val_scale Q.tB _ _ _ _ _ y JM hJM)
    rw [val_mul hJM] at E2
    have h2 : val (Z := Sp (Jet k (Fin 2 × Fin d) m)) wB ((homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ (lift (jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2))
          (jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2))).left) y JM *
        val (Z := Sp (Jet k (Fin 2 × Fin d) m)) (gB.e m) ((homAt x (sgL (g.B.A.act a) m)).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) y JM =
        gm (𝟙 (Sp (Jet k (Fin 2 × Fin d) m))) y ⊤ (unitΓ (Units.map (sub2 Qs m : _ →* _) uB)) *
        val (Z := Sp (Jet k (Fin 2 × Fin d) m)) (gB.e m) ((homAt x (sgR (g.B.A.act (H.bar a)) m)).left ≫ (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) y JM :=
      (congrArg₂ (· * ·) (val_pull hJM wB _ _) ((val_pull hJM (gB.e m) _ _).trans
        (congrArg (fun r => val (gB.e m) r y JM) hcσ.symm))).symm.trans
        (E2.trans (congrArg₂ (· * ·) (FrRatio.gm_map (sub2 Qs m) uB y) ((val_pull hJM (gB.e m) _ _).trans
          (congrArg (fun r => val (gB.e m) r y JM) hcτ.symm))))
    have h3 := (hTr _ (homAt x (sgL (g.B.A.act a) m)).left y JL JM hJL hJM).trans
      (congrArg₂ (· * ·) (gInv (sgL (g.B.A.act a) m)) (val_pull hJM (gB.e m) _ _))
    have h3' := (hTr _ (homAt x (sgR (g.B.A.act (H.bar a)) m)).left y JL JM hJL hJM).trans
      (congrArg₂ (· * ·) (gInv (sgR (g.B.A.act (H.bar a)) m)) (val_pull hJM (gB.e m) _ _))
    have E4 := h4 _ (jr t x g.x m).left y JL JM hJL hJM
    have hl : ∀ I, (jr t x g.x m).left ≫ adF t x a (Sum.inl I) = (homAt x (sgR (g.B.A.act (H.bar a)) m)).left ≫
        cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)] I := fun I =>
      congrArg (fun f => f.left) (jr_right t x g.x (g.chart.act m (H.bar a)) I.down)
    have hr : ∀ I, (jr t x g.x m).left ≫ adF t x a (Sum.inr I) = (homAt x (sgL (g.B.A.act a) m)).left ≫
        cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)] I := fun I =>
      congrArg (fun f => f.left) (jr_left t x g.x (g.chart.act m a) I.down)
    rw [Fintype.prod_sum_type, val_pull hJL, jr_sq, val_pull hJM, jr_qq Q g.x gB.x Qs hq] at E4
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, map_one, _root_.one_mul] at E4
    refine alg _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h3' (Eq.trans ?_ E4)
    refine congrArg (fun z => _ * z) (congrArg₂ (fun A B => A * B⁻¹) ?_ ?_)
    · exact Finset.prod_congr rfl fun I _ =>
        congrArg (fun ψ : Sp (Jet k (Fin 2 × Fin d) m) ⟶ (GF t x).left => wv w ψ y JL JM ^ cε 2 I) (hl I).symm
    · exact Finset.prod_congr rfl fun I _ =>
        congrArg (fun ψ : Sp (Jet k (Fin 2 × Fin d) m) ⟶ (GF t x).left => wv w ψ y JL JM ^ cε 2 I) (hr I).symm
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ ((map_mul _ _ _).trans
    ((congrArg Units.val hkey).trans (map_mul _ _ _).symm))

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf
