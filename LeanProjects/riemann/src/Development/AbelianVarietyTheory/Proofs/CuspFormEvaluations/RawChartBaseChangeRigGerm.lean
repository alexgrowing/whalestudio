import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LBPull
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RawChartGermBC

section Alg

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem map_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.map ψ (psTrunc m f) = psTrunc m (MvPowerSeries.map ψ f) := by
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem map_psIn (d : ℕ) {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    MvPolynomial.map ψ (psIn d m r f) = psIn d m r (MvPowerSeries.map ψ f) := by
  unfold psIn
  rw [MvPolynomial.map_rename, map_psTrunc]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem appTop_toΓ_spMap (a : S) : (spMap ψ).appTop.hom (toΓ S a) = toΓ S' (ψ a) := by
  unfold toΓ
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

end Alg

section Pull

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

set_option maxHeartbeats 1000000 in
theorem isPullSec_whisker_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 :=
  (LBPull.isPullSec_congr A L a (MonoidalCategory.comp_whiskerRight h2 h1 A) _ _ s1 s3).2
    (LBPull.isPullSec_comp A L a e1 e2)

end Pull

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem subst_rjBC (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetSubstP m φ')).left ≫ (rjBC ψ x0 d m n).left =
      (rjBC ψ x0 d m n').left ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  have hφ : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  subst hφ
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_rjBC (m n : ℕ) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ (rjBC ψ x0 d m n).left =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ (Fin n × Fin d) m)

theorem base_rjBC (m n : ℕ) :
    rjBase (spMap ψ ≫ x0) d m n ≫ ptBC ψ x0 = rjBC ψ x0 d m n ≫ rjBase x0 d m n := by
  apply Over.OverMorphism.ext
  unfold rjBC ptBC rjBase
  simp only [Over.comp_left, Over.homMk_left]
  refine spMap_comp_eq _ _ _ _ (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply]
  rw [show algebraMap S (Jet S (Fin n × Fin d) m) a = Ideal.Quotient.mk _ (MvPolynomial.C a) from rfl,
    PullbackSections.jetBC_mk, MvPolynomial.map_C]
  rfl

theorem overAt_hom_bc :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  unfold overAt
  simp [spMap]

theorem val_genPow {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z) (J) :
    val (genPow φ ε g k) r z J = val g r z J ^ k := by
  unfold genPow val
  exact map_pow _ _ _

theorem val_reL_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m)
    (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m)
    (he : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
      (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
    (wP : PrimTy H Xo) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m 1).left) (z : Z) {J}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (reL x0 d x act e wP m) (r ≫ (rjBC ψ x0 d m 1).left) z J := by
  have hφ : ∀ p : Fin 2 × Fin d,
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (MvPowerSeries.map ψ (act H.w0 j))] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S') p.1 p.2 =
      MvPolynomial.map ψ ((![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [map_psIn]
  have hxl : (x' m).left = (rjBC ψ x0 d m 1).left ≫ (x m).left := by
    rw [hx m]
    rfl
  unfold reL rpe
  simp only [val_mul hJ, val_pull hJ]
  congr 1
  · rw [hxl, Category.assoc]
  · refine (val_pull hJ _ _ r).trans ?_
    refine (val_corr hJ (he m) _).trans ?_
    refine (val_pull hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    simp only [Category.assoc]
    rw [subst_rjBC ψ x0 d m 2 1 _ _ hφ]

end Geo

end GlobalTheory.RawChartGermBC

namespace GlobalTheory

open RawChartGermBC in

theorem rawChart_baseChange_rig_germ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d _ act x x' hx e e' hge hge' he wP hwP
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx
  refine ⟨fun hrig => ?_, fun k Fs Fs' f hpull hgerm => ?_⟩
  · refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP 0 _ y hJ).trans ?_
    rw [Category.assoc, aug_rjBC ψ x0 d 0 1, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ?_
    refine (val_corr hJ hrig _).trans ?_
    rw [GermB.val_rigT _ _ _ _ _ _ _ hJ, GermB.val_rigT _ _ _ _ _ _ _ hJ, overAt_hom_bc ψ x0]
    simp only [Category.id_comp]
  · intro m
    obtain ⟨F0, τ0, hF0, hτ0, hv0⟩ := hgerm m
    obtain ⟨F1, hF1⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBase (spMap ψ ≫ x0) d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs'
    obtain ⟨F2, hF2⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBC ψ x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F0
    have hA := isPullSec_whisker_comp _ _ (k : ℤ) (rjBase x0 d m 1) (rjBC ψ x0 d m 1) hF0 hF2
    have hB := isPullSec_whisker_comp _ _ (k : ℤ) (ptBC ψ x0) (rjBase (spMap ψ ≫ x0) d m 1) hpull hF1
    have hB' := (LBPull.isPullSec_congr Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (congrArg (· ▷ Xo.univ.t.G) (base_rjBC ψ x0 d m 1)) _ (whiskerRight_snd _ _) Fs F1).1 hB
    have h12 : F1 = F2 := LBPull.isPullSec_unique _ _ _ hB' hA
    subst h12
    have hv := LBPull.isValueAt_pull Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (rjBC ψ x0 d m 1) (x m) hF2 hv0
    have hvb : (rjBC ψ x0 d m 1).left.appTop.hom (toΓ _ (psJet m f)) =
        toΓ _ (psJet m (MvPowerSeries.map ψ f)) := by
      rw [← PullbackSections.jetBC_psJet]
      exact appTop_toΓ_spMap (jetBC ψ (Fin 1 × Fin d) m) (psJet m f)
    rw [hvb] at hv
    refine ⟨F1, LB.pullGen Xo.univ.t.PP.L _ _ τ0 (rjBC ψ x0 d m 1).left, hF1, ?_, hv⟩
    refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_corr hJ hτ0 _).trans ?_
    rw [val_genPow, val_genPow, val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP m _ y hJ]

end GlobalTheory
