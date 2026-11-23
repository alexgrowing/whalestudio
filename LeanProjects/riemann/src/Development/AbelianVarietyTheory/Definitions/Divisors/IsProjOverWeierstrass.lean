import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def tensφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] {r : ℕ} (x : Fin r → (T ⟶ B)) :
    (Fin r × Fin r) × Fin 4 → (T.left ⟶ B.left) := fun k => GlobalTheory.PolDeg.lamPts (x k.1.1) (x k.1.2) k.2

def tensε {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) : (Fin r × Fin r) × Fin 4 → ℤ := fun k => W k.1.1 k.1.2 * Oε k.2

structure Tens (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) where

  pr : Fin r → (D'.P.A ⟶ D.P.A)
  pr_hom : ∀ i, IsMonHom (pr i)

  lim : IsLimit (Fan.mk D'.P.A pr)

  xe : D'.X ≃+ (Fin r → D.X)
  c_pr : ∀ z i, D'.c z ≫ pr i = D.c (xe z i)

  w : LB.Iso D'.P.L (LB.LinComb D.P.L (tensφ pr) (tensε W))
  w_gen : w.IsGen
  psi : ∀ y z J J', Good D.P.L z J → Good D'.P.L z J' →
    val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
      ∏ i, ∏ j, val (D.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def Tens.IsAct {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W) {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Prop :=
  letI := D.P.isAb.comm
  (∀ a z i, T.xe (a • z) i = ∑ j, ρ a i j • T.xe z j) ∧ ∀ a i, o.onB.act a ≫ T.pr i = ∏ j, T.pr j ^ ρ a i j

def GalEqN {D : DegPre R} {A : PolAV (Sp (FractionRing R))} (n : ℕ) (lab : Labels D A) : Prop :=
  ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (j : ℕ) (p p' : QkPt D (Kb R) (n ^ j)), QkExt σ.toRingHom p p' →
    (lab (n ^ j) p').left = spMap σ.toRingHom ≫ (lab (n ^ j) p).left

end

abbrev SecK {X Y : Scheme.{0}} (L : LB X) (h : Y ⟶ X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))

def Agree {X Y Y' : Scheme.{0}} (L : LB X) {h : Y ⟶ X} {h' : Y' ⟶ X} {k : ℕ} (s : SecK L h k) (s' : SecK L h' k) : Prop :=
  ∀ (Z : Scheme.{0}) (p : Z ⟶ Y) (p' : Z ⟶ Y'), p ≫ h = p' ≫ h' → ∀ z J, Good L z J → sval s p z J = sval s' p' z J

def TraitReg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    {Y : Scheme.{0}} {α : Y ⟶ G.left} {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W')
      (σ : SecK L (pullback.fst G.hom (spMap io ≫ ξ)) k), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Agree L σ s

structure UCover (R : Type) [CommRing R] [IsDomain R] extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G'),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β)

attribute [instance] UCover.grp UCover.comm

structure Secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G] (L : LB G.left)
    {A : Scheme.{0}} (α : A ⟶ G.left) where

  N : ℕ

  k : ℕ

  s : Fin (N + 1) → SecK L α k

  θ : SecK L α 1

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j

  O : Y.left.Opens
  O_ne : (O : Set Y.left).Nonempty
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (σ : Fin (N + 1) → SecK L β k) (θ' : SecK L β 1)
      (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧ (∀ i, Agree L (σ i) (s i)) ∧ Agree L θ' θ ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (σ i) p') hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → p' x ∈ nonzeroLocus θ'

attribute [instance] Secs.grp

theorem Agree.symm {X Y Y' : Scheme.{0}} {L : LB X} {h : Y ⟶ X} {h' : Y' ⟶ X} {k : ℕ} {s : SecK L h k} {s' : SecK L h' k}
    (H : Agree L s s') : Agree L s' s := fun Z p p' e z J hJ => (H Z p' p e.symm z J hJ).symm

theorem GalEq.galEqN {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {A : PolAV (Sp (FractionRing R))}
    {lab : Labels D A} (h : GalEq lab) {n : ℕ} (hn : 0 < n) : GalEqN n lab :=
  fun σ j => h σ _ (Nat.one_le_pow _ _ hn)

namespace TraitWit

section Tensor
open GlobalTheory.ToricData InhTate
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

def tq (q : X → (FractionRing K)ˣ) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (z : Fin r → X) : (FractionRing K)ˣ :=
  ∏ i, ∏ j, polar q (z i) (z j) ^ W i j

theorem val_psi {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (q : Y → (FractionRing K)ˣ) (y : Y) (z J)
    (hJ : Good (toricPre K Y q).P.L z J) : val ((toricPre K Y q).psi y) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (q y)) :=
  (congrArg (gm _ z _) (psi_isConst q y _)).trans (gm_res _ z _ (hJ.mem _ _) _)

theorem val_tau {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (q : Y → (FractionRing K)ˣ) (a b : Y) (z J)
    (hJ : Good (toricPre K Y q).P.L z J) : val ((toricPre K Y q).tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (polar q a b)) :=
  (congrArg (gm _ z _) (tau_isConst q a b _)).trans (gm_res _ z _ (hJ.mem _ _) _)

theorem gm_tq (q : X → (FractionRing K)ˣ) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (y : Fin r → X) (z : (TK K).left) :
    gm (𝟙 (TK K).left) z ⊤ (unitOn (tq q W y)) = ∏ i, ∏ j, gm (𝟙 (TK K).left) z ⊤ (unitOn (polar q (y i) (y j))) ^ W i j := by
  let F : (FractionRing K)ˣ →* _ := (gm (𝟙 (TK K).left) z ⊤).comp (MonoidHom.mk' unitOn unitOn_mul)
  change F _ = ∏ i, ∏ j, F _ ^ _
  simp only [tq, map_prod, map_zpow]

def toricTens (q : X → (FractionRing K)ˣ) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) :
    Tens (toricPre K X q) (toricPre K (Fin r → X) (tq q W)) W where
  pr _ := 𝟙 _
  pr_hom _ := inferInstanceAs (IsMonHom (𝟙 _))
  lim := Fan.IsLimit.mk _ (fun s => toUnit _) (fun _ _ => toUnit_unique _ _) (fun _ _ _ => toUnit_unique _ _)
  xe := AddEquiv.refl _
  c_pr _ _ := toUnit_unique _ _
  w := ⟨fun _ => 1⟩
  w_gen := by
    intro p p'
    refine (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (congrArg₂ (· * ·)
      ((congrArg _ (Inh.linComb_triv_g _ _ _ _)).trans (map_one _)) (congrArg (·⁻¹) (map_one _))) (map_one _)).trans
      ((_root_.mul_one _).trans ((_root_.one_mul _).trans inv_one))))
  psi y z J J' hJ hJ' := by
    refine (val_psi (Y := Fin r → X) (tq q W) y z J' hJ').trans ((gm_tq q W y z).trans ?_)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (map_one _) (Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
      congrArg (· ^ W i j) (val_tau q _ _ z J hJ))).symm
    exact (_root_.one_mul _).symm

def rho : GaussianInt →+* Matrix (Fin 2) (Fin 2) ℤ where
  toFun a := !![a.re, -a.im; a.im, a.re]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem polar_tq (u : (FractionRing K)ˣ) (y z : Fin 2 → ℤ) :
    polar (tq (fun n : ℤ => u ^ (n ^ 2)) (1 : Matrix (Fin 2) (Fin 2) ℤ)) y z = u ^ (4 * (y 0 * z 0 + y 1 * z 1)) := by
  have h : ∀ z : Fin 2 → ℤ, tq (fun n : ℤ => u ^ (n ^ 2)) (1 : Matrix (Fin 2) (Fin 2) ℤ) z = u ^ (2 * z 0 * z 0 + 2 * z 1 * z 1) :=
    fun z => by simp [tq, Fin.prod_univ_two, polar_zpow_sq, zpow_add]
  rw [polar, h, h, h, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]
  congr 1
  simp only [Pi.add_apply]
  ring

theorem isAct_gauss (u : (FractionRing K)ˣ) :
    ∃ (_ : Module GaussianInt (toricPre K (Fin 2 → ℤ) (tq (fun n : ℤ => u ^ (n ^ 2)) 1)).X)
      (o : (toricPre K (Fin 2 → ℤ) (tq (fun n : ℤ => u ^ (n ^ 2)) 1)).OAct GaussianInt),
      (toricTens (fun n : ℤ => u ^ (n ^ 2)) 1).IsAct o rho := by
  letI : Module GaussianInt (Fin 2 → ℤ) := Module.compHom (Fin 2 → ℤ) ((Matrix.toLinAlgEquiv' (R := ℤ)).toRingEquiv.toRingHom.comp rho)
  have hs : ∀ (a : GaussianInt) (z : Fin 2 → ℤ), a • z = (rho a).mulVec z := fun _ _ => rfl
  refine ⟨inferInstance, toricOAct _ GaussianInt (fun a y z => ?_), fun a z i => ?_, fun _ _ => toUnit_unique _ _⟩
  · rw [polar_tq, polar_tq, hs, hs]
    congr 1
    simp [rho, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · exact congrFun (hs a z) i

end Tensor

section Cover
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem selfUnif {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (P : PolAV (Sp W)) :
    ∃ (D : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (U : Unif (maximalIdeal W) D A P.A), U.LG.L = P.L := by
  have := hW.1
  have := hW.2.1
  obtain ⟨D, rfl, hX⟩ := GlobalTheory.SelfUnif.exists_degData GlobalTheory.firstFiveLaws.1.cube (maximalIdeal W) P
  let A : PolAV (Spec (CommRingCat.of (FractionRing W))) := GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK W)
  let eA : (Over.pullback (jK W)).obj D.toPre.P.A ≅ A.A := Iso.refl _
  have hA : IsMonHom eA.hom := by
    refine ⟨?_, ?_⟩
    · exact Category.comp_id _
    · show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      rfl
  have hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK W))), w.IsGen :=
    LBIso.chartPull (h := 𝟙 _) (GlobalTheory.chartPullPull _ _) (chartPullId _)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK W))))
  exact ⟨D, A, ⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ =>
    GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds (IsAdicComplete.le_jacobson_bot _) k⟩, rfl⟩

theorem local_or_factor [IsDiscreteValuationRing R] {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W) :
    IsLocalHom φ ∨ ∃ ψ : FractionRing R →+* W, ψ.comp (algebraMap R _) = φ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases h : IsUnit (φ ϖ)
  · refine Or.inr ⟨IsLocalization.lift (M := nonZeroDivisors R) (fun y => ?_), IsLocalization.lift_comp _⟩
    obtain ⟨n, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero y.2) hϖ
    rw [e, map_mul, map_pow]
    exact (u.isUnit.map φ).mul (h.pow n)
  · refine Or.inl ⟨fun a ha => ?_⟩
    by_contra hn
    have hm : a ∈ maximalIdeal R := hn
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul] at ha
    exact h (isUnit_of_mul_isUnit_left ha)

theorem exists_uCover (hR : GlobalTheory.LN.CDvr R) {D : DegData R (maximalIdeal R)} {G : Over (Sp R)} [iG : GrpObj G]
    [cG : IsCommMonObj G] {A : PolAV (Sp (FractionRing R))} (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) :
    ∃ C : UCover R, C.toModif = Modif.self R ∧ C.A = A ∧ C.G.left = G.left := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hR.1
  have hR' : AdmBase R (maximalIdeal R) := ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hlb : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
    LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  refine ⟨{ toModif := Modif.self R
            G := G
            grp := iG
            comm := cG
            semi := hG
            P := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
            A := A
            α := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
            α_cart := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
            α_lb := hlb
            trait := ?_ }, rfl, rfl, rfl⟩
  intro W _ _ _ hW φ ξ hφ hξ
  obtain rfl : ξ = spMap φ := (Category.comp_id ξ).symm.trans hξ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hid : spMap φ = spMap (RingHom.id W) ≫ spMap φ := by
    show spMap φ = Spec.map (𝟙 _) ≫ spMap φ
    rw [Spec.map_id, Category.id_comp]
  rcases local_or_factor φ with hloc | ⟨ψ, hψ⟩
  · obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
      hR' hW' φ hφ (map_maximalIdeal_le φ) hG U
    have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
        pullback.fst G.hom (specOf φ) := Category.id_comp _
    exact ⟨W, _, inferInstance, inferInstance, RingHom.id W, (Over.pullback (specOf φ)).obj G, inferInstance, inferInstance,
      (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ), D', A', U', hW,
      Function.injective_id, RingHom.Finite.id W, (isGrpPullback_pullback G (spMap φ)).congr hid hb.symm,
      ⟨hP.lg.choose, hP.lg.choose_spec.1⟩⟩
  · obtain ⟨D', A', U', hU⟩ := selfUnif hW (GlobalTheory.AmpleSpecialisation.baseChange A (spMap ψ))
    refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, (GlobalTheory.AmpleSpecialisation.baseChange A (spMap ψ)).A,
      inferInstance, inferInstance, pullback.fst A.A.hom (spMap ψ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R), D', A', U', hW,
      Function.injective_id, RingHom.Finite.id W, ?_, ?_⟩
    · refine ((isGrpPullback_pullback A.A (spMap ψ)).comp (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre)).congr ?_ rfl
      refine Eq.trans ?_ hid
      rw [← hψ]
      exact (Spec.map_comp _ _).symm
    · rw [hU]
      exact LBIso.chartPull (h := pullback.fst A.A.hom (spMap ψ)) (GlobalTheory.chartPullPull A.L _)
        (chartPullSame U.LG.L _ (fun _ => U.gen.inv.left ≫ pullback.fst G.hom (jK R)) _ _ fun _ => rfl) hlb

theorem uCover_rank_one : ∃ (C : UCover (PowerSeries ℚ)) (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)))
    (G : Over (Sp (PowerSeries ℚ))) (_ : GrpObj G) (_ : IsCommMonObj G), C.A.g = 1 ∧ C.G.left = G.left ∧
      Module.finrank ℤ D.toPre.X = 1 ∧ Nonempty (Unif (maximalIdeal _) D C.A G) := by
  obtain ⟨A, G, _, _, D, U, hG, hA, hr, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  obtain ⟨C, -, rfl, h⟩ := exists_uCover ⟨inferInstance, base_powerSeries.1.2.2.2, base_powerSeries.2⟩ hG U
  exact ⟨C, D, G, _, _, hA, h, hr, ⟨U⟩⟩

end Cover

section Sections
variable {X Y Y' : Scheme.{0}}

def cpK (L : LB X) (h : Y ⟶ X) : ChartPull (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => ((1 : ℕ) : ℤ))) L h where
  idx J := J 0
  le _ _ hy := Set.mem_iInter.1 hy 0
  g y J J' hJ hJ' := (gm_linComb L (fun _ : Fin 1 => h) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 Y) y J J' hJ hJ').trans (by
    rw [Fin.prod_univ_one, Category.id_comp, Nat.cast_one, zpow_one])

def secK {L : LB X} (t : L.Sec) (h : Y ⟶ X) : SecK L h 1 := GlobalTheory.chartSec (cpK L h) t

theorem nz_secK {L : LB X} (t : L.Sec) (h : Y ⟶ X) : nonzeroLocus (secK t h) = h ⁻¹ᵁ nonzeroLocus t :=
  GlobalTheory.nonzeroLocus_chartSec _ t fun _ j hj => ⟨fun _ => j, Set.mem_iInter.2 fun _ => hj⟩

theorem agree_secK {L : LB X} (t : L.Sec) (h : Y ⟶ X) (h' : Y' ⟶ X) : Agree L (secK t h) (secK t h') := by
  intro Z p p' e z J hJ
  have a := GlobalTheory.gs_chartSec (cpK L h) t p z (fun _ => J (p ≫ h)) (hJ.mem _ p)
  have b := GlobalTheory.gs_chartSec (cpK L h') t p' z (fun _ => J (p' ≫ h')) (hJ.mem _ p')
  refine a.trans (Eq.trans ?_ b.symm)
  change gs (p ≫ h) z (L.U (J (p ≫ h))) (t.f _) = gs (p' ≫ h') z (L.U (J (p' ≫ h'))) (t.f _)
  rw [e]

theorem toProj_secK {R : Type} [CommRing R] {N : ℕ} {L : LB X} (f : X ⟶ Sp R) (t : Fin (N + 1) → L.Sec)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) (h : Y ⟶ X) :
    ∃ hs, GlobalTheory.ProjSpace.toProj (h ≫ f) (fun i => secK (t i) h) hs = h ≫ GlobalTheory.ProjSpace.toProj f t ht := by
  have hs : ⨆ i, nonzeroLocus (secK (t i) h) = ⊤ := by
    simp only [nz_secK]
    rw [← Scheme.Hom.preimage_iSup, ht]; rfl
  refine ⟨hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally ht h hs fun z =>
    (GlobalTheory.ProjSpace.exists_chart_of_iSup_nonzeroLocus ht (h z)).elim fun k hk =>
    ⟨h ⁻¹ᵁ L.U k, hk, k, le_rfl, fun _ => k, fun _ hy => Set.mem_iInter.2 fun _ => hy, 1, fun _ => ?_⟩⟩
  exact (resG_resG _ _ _).trans (_root_.one_mul _).symm

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem traitReg_secK (M : Modif R) (G : Over M.S) {L : LB G.left} (t : L.Sec) (α : Y ⟶ G.left) :
    TraitReg M G L (secK t α) := fun W _ _ _ hW _ _ _ _ _ =>
  ⟨W, _, inferInstance, inferInstance, RingHom.id W, secK t _, hW, Function.injective_id, RingHom.Finite.id W, agree_secK _ _ _⟩

def constSecs (M : Modif R) (G₀ : Over (Sp R)) [GrpObj G₀] [Smooth G₀.hom] {N : ℕ} (i : G₀.left ⟶ PSpace R N)
    [IsImmersion i] (hi : i ≫ PSpace.str R N = G₀.hom) (G : Over M.S) [GrpObj G] (gam : G.left ⟶ G₀.left)
    (hgam : IsGrpPullback G G₀ M.π gam) (α : Y ⟶ G.left) :
    Secs M G ((GlobalTheory.ProjSpace.O1 R N).pull (gam ≫ i)) α := by
  let Y₀ := (Over.pullback (spMap (residue R))).obj G₀
  let j : Y₀.left ⟶ PSpace R N := pullback.fst G₀.hom (spMap (residue R)) ≫ i
  let h₀ := GlobalTheory.ProjSpace.exists_mem_chart R N (j ((η[Y₀]).left (closedPoint (ResidueField R))))
  let i₀ := h₀.choose
  have hi₀ := h₀.choose_spec
  let t : Fin (N + 1) → ((GlobalTheory.ProjSpace.O1 R N).pull (gam ≫ i)).Sec := fun a => GlobalTheory.secPull (GlobalTheory.ProjSpace.coord R N a) (gam ≫ i)
  have ht : ⨆ a, nonzeroLocus (t a) = ⊤ :=
    GlobalTheory.ProjSpace.iSup_nonzeroLocus_secPull (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord R N) _
  have hP : GlobalTheory.ProjSpace.toProj ((gam ≫ i) ≫ PSpace.str R N) t ht = gam ≫ i := GlobalTheory.ProjSpace.toProj_secPull_coord _
  refine { N := N, k := 1, s := fun a => secK (t a) α, θ := secK (t i₀) α, Y := Y₀
           smooth := inferInstanceAs (Smooth (pullback.snd G₀.hom (spMap (residue R))))
           j := j
           j_over := by rw [Category.assoc, hi, pullback.condition]; rfl
           imm := by
             have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
             have : IsClosedImmersion (pullback.fst G₀.hom (spMap (residue R))) := inferInstance
             infer_instance
           O := j ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i₀
           O_ne := ⟨_, hi₀⟩
           trait := ?_ }
  intro W _ _ _ hW φ ξ hφ hloc hξ
  let ξ' := spMap (RingHom.id W) ≫ ξ
  let G' := (Over.pullback ξ').obj G
  let β : G'.left ⟶ G.left := pullback.fst G.hom ξ'
  have hκ : (ResidueField.map φ).comp (residue R) = (residue W).comp ((RingHom.id W).comp φ) := by
    ext x; simp
  have hξ' : ξ' ≫ M.π = spMap ((RingHom.id W).comp φ) := by
    rw [Category.assoc, hξ]; exact (Spec.map_comp _ _).symm
  have h₁ := (isGrpPullback_pullback G' (spMap (residue W))).comp ((isGrpPullback_pullback G ξ').comp hgam)
  have h₂ := (isGrpPullback_pullback Y₀ (spMap (ResidueField.map φ))).comp (isGrpPullback_pullback G₀ (spMap (residue R)))
  have hb : spMap (ResidueField.map φ) ≫ spMap (residue R) = spMap (residue W) ≫ ξ' ≫ M.π := by
    rw [hξ', ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ]
  obtain ⟨e, he, he'⟩ := grpPullback_iso h₁ (h₂.congr hb rfl)
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', inferInstance, β, fun a => secK (t a) β, secK (t i₀) β,
    ResidueField.map φ, e, hW, Function.injective_id, RingHom.Finite.id W, isGrpPullback_pullback G ξ', hκ, he,
    fun a => agree_secK _ _ _, agree_secK _ _ _, ?_⟩
  intro Ω _ p p' y hp hy
  have key : y ≫ j = p' ≫ β ≫ gam ≫ i := by
    have := congrArg (fun q => p ≫ q ≫ i) he'
    rw [hp, hy]
    simpa only [Category.assoc] using this
  obtain ⟨hs, hs'⟩ := toProj_secK ((gam ≫ i) ≫ PSpace.str R N) t ht β
  have hstr : G'.hom ≫ spMap ((RingHom.id W).comp φ) = β ≫ (gam ≫ i) ≫ PSpace.str R N := by
    rw [Category.assoc, hi, hgam.1.w, ← hξ', ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ M.π) pullback.condition.symm
  refine ⟨⟨GlobalTheory.ProjSpace.iSup_nonzeroLocus_secPull hs p', ?_⟩, fun x hx => ?_⟩
  · rw [hstr]
    exact (GlobalTheory.ProjSpace.toProj_secPull hs p').trans (by rw [hs', hP, key])
  · rw [nz_secK, GlobalTheory.nonzeroLocus_secPull, GlobalTheory.ProjSpace.nonzeroLocus_coord]
    have : (y ≫ j) x ∈ GlobalTheory.ProjSpace.chart R N i₀ := hx
    rw [key] at this
    exact this

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isProjOver_weierstrass {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R) :
    IsProjOver (GlobalTheory.WeierstrassCurve.toSpec W) := by
  let g : MvPolynomial.homogeneousSubmodule (Fin 3) R →+*ᵍ GlobalTheory.WeierstrassCurve.grading W :=
    { __ := Ideal.Quotient.mk (GlobalTheory.WeierstrassCurve.cubicIdeal W), map_mem := fun hf => ⟨_, hf, rfl⟩ }
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hi := ProjSpace.irrelevant_le_map_of_surjective g hg
  refine ⟨2, Proj.map g hi, ProjSpace.isClosedImmersion_projMap g hg hi, ?_⟩
  refine (Proj.mapAffineOpenCover g hi).openCover.hom_ext _ _ fun s => ?_
  have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin 3) R)
      (hs : s ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R d),
      Proj.awayι (GlobalTheory.WeierstrassCurve.grading W) (g s) (g.2 hs) hd ≫ Proj.map g hi ≫ PSpace.str R 2 =
        Proj.awayι (GlobalTheory.WeierstrassCurve.grading W) (g s) (g.2 hs) hd ≫ GlobalTheory.WeierstrassCurve.toSpec W := by
    intro d hd s hs
    rw [Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, Proj.awayι_toSpecZero_assoc]
    erw [Proj.awayι_toSpecZero_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  exact key _ s.1.2 _ s.2.2

theorem secs_multiplicative (M : Modif (PowerSeries ℚ)) :
    ∃ (G₀ : Over (Sp (PowerSeries ℚ))) (_ : GrpObj G₀) (_ : IsSemiAbelian G₀)
      (_ : IsProper ((Over.pullback (jK (PowerSeries ℚ))).obj G₀).hom)
      (L : LB ((Over.pullback M.π).obj G₀).left) (_ : L.IsLB)
      (S : Secs M ((Over.pullback M.π).obj G₀) L (pullback.fst ((Over.pullback M.π).obj G₀).hom M.gp))
      (i : splitTorus (Sp (ResidueField (PowerSeries ℚ))) ℤ ≅ S.Y), IsMonHom i.hom ∧
        (∀ a, TraitReg M _ L (S.s a)) ∧ TraitReg M _ L S.θ := by
  obtain ⟨W, hW⟩ : ∃ W : _root_.WeierstrassCurve (PowerSeries ℚ), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := GlobalTheory.WeierstrassCurve.exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, -, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := GlobalTheory.MultiplicativeReduction.isSemiAbelian_and_specialFibre W hW U hU hs hgi hqc hmul
  obtain ⟨N, c, _, hc⟩ := isProjOver_weierstrass W
  let G₀ := Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)
  have : Smooth G₀.hom := hs
  have him : IsImmersion (U.ι ≫ c) := inferInstance
  have hE : (W.map (algebraMap _ (FractionRing (PowerSeries ℚ)))).IsElliptic :=
    hW ▸ GlobalTheory.MultiplicativeReduction.isElliptic_generic
  refine ⟨G₀, inferInstance, hG, GlobalTheory.MultiplicativeReduction.isProper_pullback_snd W U hU _
    (by rw [← _root_.WeierstrassCurve.map_Δ]; exact hE.isUnit.ne_zero), _, LB.isLB_pull (GlobalTheory.ProjSpace.O1_isLB _ N) _,
    @constSecs _ _ _ _ _ M G₀ _ _ N (U.ι ≫ c) him (by rw [Category.assoc, hc]; rfl) _ _ _ (isGrpPullback_pullback _ M.π) _,
    i, hi, fun a => traitReg_secK _ _ _ _, traitReg_secK _ _ _ _⟩

end Sections

end TraitWit

end GlobalTheory.Mum
