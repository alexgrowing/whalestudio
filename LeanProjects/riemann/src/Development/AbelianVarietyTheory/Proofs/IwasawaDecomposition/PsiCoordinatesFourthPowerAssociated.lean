import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (q ⁻¹ᵁ ⊤) z trivial).hom.comp ((q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem cst_eq_cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) :
    cst q z a = cstHom q z a :=
  gs_eq q z ⊤ trivial _

theorem cst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {a b : R}
    (h : cst (p ≫ jK R) z a = cst (p ≫ jK R) z b) : a = b := by
  by_contra hne
  have hu := IntegralExpansionLocal.isUnit_cst_of_ne_zero p z (sub_ne_zero.2 hne)
  rw [cst_eq_cstHom, map_sub, ← cst_eq_cstHom, ← cst_eq_cstHom, h, sub_self] at hu
  exact not_isUnit_zero hu

theorem gm_top {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : ⊤ ≤ V) (g : Γ(Spec (CommRingCat.of R), V)ˣ) : ∃ u : Rˣ, (gm q z V g).val = cst q z (u : R) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom (res hV g), ?_⟩
  rw [← gm_res q z hV trivial g, ← gs_unit q z ⊤ trivial]
  simp only [cst, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom _
  rw [Iso.hom_inv_id]
  rfl

theorem gm_of_top {Z X : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (x : Spec (CommRingCat.of R) ⟶ X)
    {f : Z ⟶ X} (hf : f = q ≫ x) {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) (g : Γ(X, V)ˣ) :
    ∃ u : Rˣ, (gm f z V g).val = cst q z (u : R) := by
  subst hf
  rw [← gm_pull q x z V (hV trivial) g]
  exact gm_top q z hV _

end GlobalTheory.PsiFourthCoord

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem val_psi_of_coord (D : DegPre R) (χ : D.X) {r : R} {j : PUnit → D.P.L.ι}
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
    {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : J (p ≫ D.xK χ) = j PUnit.unit) : (val (D.psi χ) p z J).val = cst (p ≫ jK R) z r := by
  have m₁ : p z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := h trivial
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  rw [val_of (D.psi χ) p z J j (fun _ => hJ)]
  refine (gs_unit p z _ m₁ _).symm.trans ((gs_res p z h trivial _).symm.trans ?_)
  refine (congrArg (gs p z _) e.symm).trans ((gs_pull p (jK R) z ⊤ trivial _).trans ?_)
  rw [hto]; rfl

theorem val_famMult_two {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 2 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul]

theorem val_rigK_of_top (D : DegPre R) {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J)
    (h : ⊤ ≤ (eSec D.P.A) ⁻¹ᵁ D.P.L.U (J ((p ≫ jK R) ≫ eSec D.P.A))) :
    ∃ u : Rˣ, (val D.rigK p z J).val = cst (p ≫ jK R) z u := by
  have e1 : p ≫ (toUnit (TK R)).left = p ≫ jK R := by
    congr 1
  rw [DegPre.rigK, val_pull hJ, e1]
  rw [val_of D.rig (p ≫ jK R) z J (fun _ => J ((p ≫ jK R) ≫ eSec D.P.A)) (fun _ => rfl)]
  exact gm_top _ z (fun y _ => Set.mem_iInter.2 fun _ => h trivial) _

theorem exists_good_pts (P : PolAV (Spec (CommRingCat.of R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {Z : Scheme.{0}} (t : Z ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of F) ⟶ Z) (ha : a ≫ t = DegPre.jFR F)
    (z : Z) (pk : (Spec (CommRingCat.of R) ⟶ P.A.left) → P.L.ι)
    (hpk : ∀ q, q ≫ P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ P.L.U (pk q)) :
    ∃ J, Good P.L z J ∧ ∀ q, q ≫ P.A.hom = 𝟙 _ → J (t ≫ q) = pk q := by
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB z (K := {q : Spec (CommRingCat.of R) ⟶ P.A.left // q ≫ P.A.hom = 𝟙 _})
    (fun q => t ≫ q.1) (fun q => pk q.1) (fun a' b' h => by
      have : a'.1 = b'.1 := GC.vpt_ext F P a'.2 b'.2 (by rw [← ha, Category.assoc, Category.assoc, h])
      rw [this]) (fun q => hpk q.1 q.2 trivial)
  exact ⟨J, hJ, fun q hq => e ⟨q, hq⟩⟩

end GlobalTheory.PsiFourthCoord

open GlobalTheory.PsiFourthCoord ReciprocityTheory.ChartRestriction.G.DVR in

theorem GlobalTheory.psi_coord_fourth_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ D D' Φ w _ nu mu z H r r' hr hr'
  classical
  set π := (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) with hπdef
  have hπ : π ≫ jK R = (DegPre.BF D.toPre (FractionRing R)).hom :=
    (Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A))
  have za : (DegPre.zF D.toPre (FractionRing R)).left ≫ (π ≫ jK R) = DegPre.jFR (FractionRing R) := by
    rw [hπ]; exact Over.w (DegPre.zF D.toPre (FractionRing R))
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨j', hj', h', e'⟩ := hr'
  choose pk hpk using fun q : Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left => GC.exists_chart_top D.toPre.P.L D.toPre.P.isLB q
  choose pk' hpk' using fun q : Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left =>
    GC.exists_chart_top D'.toPre.P.L D'.toPre.P.isLB q
  let pkD : (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun q =>
    if q = (D.toPre.c nu).left then j PUnit.unit else pk q
  let pkD' : (Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun q =>
    if q = (D'.toPre.c mu).left then j' PUnit.unit else pk' q
  have hpkD : ∀ q, q ≫ D.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D.toPre.P.L.U (pkD q) := fun q _ => by
    by_cases hq : q = (D.toPre.c nu).left
    · subst hq; simp only [pkD, if_pos rfl]; exact hj
    · simp only [pkD, if_neg hq]; exact (hpk q).ge
  have hpkD' : ∀ q, q ≫ D'.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D'.toPre.P.L.U (pkD' q) := fun q _ => by
    by_cases hq : q = (D'.toPre.c mu).left
    · subst hq; simp only [pkD', if_pos rfl]; exact hj'
    · simp only [pkD', if_neg hq]; exact (hpk' q).ge
  obtain ⟨J, hJ, eJ⟩ := exists_good_pts D.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD hpkD
  obtain ⟨J', hJ', eJ'⟩ := exists_good_pts D'.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD' hpkD'
  have HH := H J J' hJ hJ'
  have pc : ∀ {X : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X),
      x.left ≫ X.hom = 𝟙 _ := fun x => Over.w x
  have hc : (D.toPre.c nu).left ≫ D.toPre.P.A.hom = 𝟙 _ := pc _
  have hc' : (D'.toPre.c mu).left ≫ D'.toPre.P.A.hom = 𝟙 _ := pc _
  have he : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := pc η[D.toPre.P.A]
  have he' : eSec D'.toPre.P.A ≫ D'.toPre.P.A.hom = 𝟙 _ := pc η[D'.toPre.P.A]
  have hcΦ : ((D'.toPre.c mu).left ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact hc'
  have heΦ : (eSec D'.toPre.P.A ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact he'
  have V1 := val_psi_of_coord D.toPre nu h e π z J (by
    rw [show π ≫ D.toPre.xK nu = (π ≫ jK R) ≫ (D.toPre.c nu).left from (Category.assoc _ _ _).symm, eJ _ hc]
    simp only [pkD, if_pos rfl])
  have V1' := val_psi_of_coord D'.toPre mu h' e' π z J' (by
    rw [show π ≫ D'.toPre.xK mu = (π ≫ jK R) ≫ (D'.toPre.c mu).left from (Category.assoc _ _ _).symm, eJ' _ hc']
    simp only [pkD', if_pos rfl])
  obtain ⟨a, V2⟩ := val_rigK_of_top D.toPre π z J hJ (by rw [eJ _ he]; exact hpkD _ he)
  obtain ⟨a', V2'⟩ := val_rigK_of_top D'.toPre π z J' hJ' (by rw [eJ' _ he']; exact hpkD' _ he')
  have hψ : (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
      (π ≫ jK R) ≫ (D'.toPre.c mu).left := by
    rw [hπ, cP, Over.comp_left]; rfl
  have hψ1 : (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = (π ≫ jK R) ≫ eSec D'.toPre.P.A := by
    rw [hπ]; rfl
  have O1 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left ≫ Φ.hom.left) =
        pkD ((D'.toPre.c mu).left ≫ Φ.hom.left) := by rw [hψ, Category.assoc]; exact eJ _ hcΦ
    have k2 : J' (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
        pkD' (D'.toPre.c mu).left := by rw [hψ]; exact eJ' _ hc'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (D'.toPre.c mu).left hψ (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ hcΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ hc' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  have O2 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left ≫ Φ.hom.left) =
        pkD (eSec D'.toPre.P.A ≫ Φ.hom.left) := by rw [hψ1, Category.assoc]; exact eJ _ heΦ
    have k2 : J' (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = pkD' (eSec D'.toPre.P.A) := by
      rw [hψ1]; exact eJ' _ he'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (eSec D'.toPre.P.A) hψ1 (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ heΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ he' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  obtain ⟨b, O1⟩ := O1
  obtain ⟨b', O2⟩ := O2
  rw [val_famMult_two D'.tau_bimult _ hJ', val_famMult_two D.tau_bimult _ hJ] at HH
  set Ωc := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left
  set Ω1 := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left
  have HH2 : (val (D'.toPre.psi mu) π z J' ^ 2 * val D'.toPre.rigK π z J' ^ 2) ^ 2 * Ω1 ^ 2 =
      Ωc ^ 2 * (val (D.toPre.psi nu) π z J ^ 2 * val D.toPre.rigK π z J ^ 2) ^ 2 := by
    rw [HH, mul_pow, inv_pow, mul_right_comm, inv_mul_cancel_right]
  have V := congrArg Units.val HH2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at V
  rw [V1, V1', V2, V2', O1, O2] at V
  have V' : cst (π ≫ jK R) z (r' ^ 4 * ((a' : R) ^ 4 * (b' : R) ^ 2)) =
      cst (π ≫ jK R) z ((b : R) ^ 2 * (a : R) ^ 4 * r ^ 4) := by
    simp only [cst_eq_cstHom, map_mul, map_pow] at V ⊢
    linear_combination V
  have hR := cst_inj π z V'
  refine ⟨(b ^ 2 * a ^ 4) * (a' ^ 4 * b' ^ 2)⁻¹, ?_⟩
  have k : r ^ 4 * ((b ^ 2 * a ^ 4 : Rˣ) : R) = r' ^ 4 * ((a' ^ 4 * b' ^ 2 : Rˣ) : R) := by
    push_cast
    linear_combination -hR
  rw [Units.val_mul, ← _root_.mul_assoc, k, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
