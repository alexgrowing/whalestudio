import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecThroughUp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteLiftNu

open IsLocalRing ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem coord_eq {K F W W' Ix κ : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module F W'] [Fintype Ix] [Fintype κ] {p : W →ₛₗ[algebraMap K F] W'} (hp : IsExtension p)
    (b : Ix → W) (a : W → Ix → K) (ha : ∀ x, x = ∑ i, a x i • b i) (hu : ∀ x (y : Ix → K), x = ∑ i, y i • b i → y = a x)
    {s : W} {c : κ → F} {τ : κ → W} (e : p s = ∑ l, c l • p (τ l)) (i : Ix) :
    algebraMap K F (a s i) = ∑ l, c l * algebraMap K F (a (τ l) i) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro ℓ
  obtain ⟨Λ, hΛ⟩ := hp.coord ℓ
  have e₁ := congrArg Λ e
  rw [← one_smul F (p s), hΛ, map_sum] at e₁
  simp only [hΛ _ _] at e₁
  have sm : ∀ (d : K) x, d • x = ∑ i, (d * a x i) • b i := fun d x => by
    conv_lhs => rw [ha x]
    simp only [Finset.smul_sum, smul_smul]
  have e₂ : (fun i => ℓ 1 * a s i) = fun i => ∑ l, ℓ (c l) * a (τ l) i := by
    refine (hu (ℓ 1 • s) _ (sm _ _)).trans (hu (ℓ 1 • s) _ ?_).symm
    rw [e₁]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => sm _ _
  have e₃ := congrFun e₂ i
  rw [map_sub, map_sum, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm, e₃, sub_eq_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (c l), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

section Fam

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.toPre.X}

theorem eq_sum_iff {n : ℕ} (s : FamTerm D.toPre F k α) (a : Fin n → F) (b : Fin n → FamTerm D.toPre F k α) :
    (∀ j, LB.Sec.f s j = ∑ i, DegPre.constBF D.toPre F (a i) _ * LB.Sec.f (b i) j) ↔ s = ∑ i, a i • b i := by
  have e : ∀ j, LB.Sec.f (∑ i, a i • b i : FamTerm D.toPre F k α) j =
      ∑ i, DegPre.constBF D.toPre F (a i) _ * LB.Sec.f (b i) j := fun j =>
    map_sum (chartLin (famBase D.toPre F) _ j) _ _
  exact ⟨fun h => SecOver.ext _ _ fun j => (h j).trans (e j).symm, fun h j => by rw [h]; exact e j⟩

theorem secScal_one_iff (σ : IntTerm D k α) (s t : FamTerm D.toPre F k α)
    (ht : ∀ y J, Good D.toPre.P.L y J → sval t (𝟙 _) y J = sval σ (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J) :
    GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s
                      (D.toPre.famφB α) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1 ↔ s = t := by
  refine (secScal_iff_val D.toPre.P.isLB s σ _ _).trans ?_
  have e : ∀ y : (DegPre.BF D.toPre F).left, gs (𝟙 _) y ⊤ 1 = 1 := fun y => by
    rw [gs_eq _ y ⊤ trivial, map_one, map_one]
  simp only [e, _root_.one_mul]
  exact ⟨fun H => sec_ext' D.toPre.P.isLB fun y J hJ => (H y J hJ).symm.trans (ht y J hJ).symm,
    fun H y J hJ => by rw [H, ht y J hJ]⟩

theorem vGe_iff_of (v : AddValuation F (WithTop ℚ)) (p : IntTerm D k α → FamTerm D.toPre F k α)
    (hp : ∀ σ y J, Good D.toPre.P.L y J →
      sval (p σ) (𝟙 _) y J = sval σ (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (s : FamTerm D.toPre F k α) (r : ℚ) :
    VGe D F v k α s r ↔ ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → IntTerm D k α),
      (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i)) ∧ s = ∑ i, a i • p (σ i) := by
  constructor
  · rintro ⟨n, a, σ, σF, h₁, h₂, h₃⟩
    obtain rfl : σF = fun i => p (σ i) := funext fun i => (secScal_one_iff (σ i) _ _ (hp _)).1 (h₁ i)
    exact ⟨n, a, σ, h₂, (eq_sum_iff s a _).1 h₃⟩
  · rintro ⟨n, a, σ, h₂, h₃⟩
    exact ⟨n, a, σ, fun i => p (σ i), fun i => (secScal_one_iff (σ i) _ _ (hp _)).2 rfl, h₂, (eq_sum_iff s a _).2 h₃⟩

theorem vGe_iff_generic (v : AddValuation (FractionRing V) (WithTop ℚ)) (s : FamTerm D.toPre (FractionRing V) k α)
    (r : ℚ) : VGe D (FractionRing V) v k α s r ↔ ∃ (n : ℕ) (a : Fin n → FractionRing V) (σ : Fin n → IntTerm D k α),
      (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i)) ∧ s = ∑ i, a i • genericTerm D k α (σ i) :=
  vGe_iff_of v _ (fun _ _ _ hJ => sval_pullOver _ _ _ _ hJ) s r

theorem vGe_iff_extended (v : AddValuation F (WithTop ℚ)) (s : FamTerm D.toPre F k α)
    (r : ℚ) : VGe D F v k α s r ↔ ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → IntTerm D k α),
      (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • termPull D.toPre (FractionRing V) F k α (genericTerm D k α (σ i)) :=
  vGe_iff_of v (fun σ => termPull D.toPre (FractionRing V) F k α (genericTerm D k α σ)) (fun σ y J hJ =>
    (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
        (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))) s r

variable {ϖ : V} (hϖ : Irreducible ϖ) {vK : AddValuation (FractionRing V) (WithTop ℚ)}
  (hK : ValOver ϖ (FractionRing V) vK) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

include hϖ hK hv

theorem val_algebraMap (c : FractionRing V) : v (algebraMap (FractionRing V) F c) = vK c := by
  by_cases hc : c = 0
  · rw [hc, map_zero, v.map_zero, vK.map_zero]
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hc
  exact (hv c n hn).trans (hK c n hn).symm

theorem vGe_termPull_iff (hk : 1 ≤ k) (s : FamTerm D.toPre (FractionRing V) k α) (r : ℚ) :
    VGe D F v k α (termPull D.toPre (FractionRing V) F k α s) r ↔ VGe D (FractionRing V) vK k α s r := by
  constructor
  · intro h
    obtain ⟨n, c, σ, hc, e⟩ := (vGe_iff_extended v _ r).1 h
    obtain ⟨b, hb, hV⟩ := GlobalTheory.IntegralCoord.main twistBaseChange V ϖ hϖ D (FractionRing V) vK hK k hk α
    choose a ha hu using hb
    have hm : ∀ l i, ((0 : ℚ) : WithTop ℚ) ≤ vK (a (genericTerm D k α (σ l)) i) := fun l =>
      (hV _ _ (ha _) 0).1 ((vGe_iff_generic vK _ 0).2 ⟨1, fun _ => 1, fun _ => σ l,
        fun _ => by rw [vK.map_one]; rfl, by rw [Fin.sum_univ_one, one_smul]⟩)
    refine (hV s _ (ha s) r).2 fun i => ?_
    have key := coord_eq (isExtension_termPull D.toPre (FractionRing V) F k α) b a
      (fun x => (eq_sum_iff x _ _).1 (ha x)) (fun x y h => hu x y ((eq_sum_iff x _ _).2 h)) e i
    rw [← val_algebraMap hϖ hK hv, key]
    refine v.map_le_sum fun l _ => ?_
    rw [v.map_mul, val_algebraMap hϖ hK hv]
    simpa using add_le_add (hc l) (hm l i)
  · intro h
    obtain ⟨n, c, σ, hc, e⟩ := (vGe_iff_generic vK _ r).1 h
    refine (vGe_iff_extended v _ r).2 ⟨n, fun i => algebraMap (FractionRing V) F (c i), σ,
      fun i => by rw [val_algebraMap hϖ hK hv]; exact hc i, ?_⟩
    rw [e, map_sum]
    simp only [map_smulₛₗ]

theorem nuGe_famPull_iff (hG : GlobalFnsSt) (hk : 1 ≤ k) (Q : D.toPre.X → ℤ) (s : Fam D.toPre (FractionRing V) k)
    (r : ℚ) : NuGe D Q F v k (famPull D.toPre (FractionRing V) F hG k s) r ↔ NuGe D Q (FractionRing V) vK k s r :=
  forall_congr' fun χ => vGe_termPull_iff hϖ hK hv hk (s.s χ) _

end Fam

theorem expandsG_extend {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt)
    {k : ℕ} {s : U.SecK k} {x : Fam D.toPre (FractionRing R) k} (h : U.Expands k s x) :
    U.ExpandsG F k (extendSec U F k s) (famPull D.toPre (FractionRing R) F hG k x) := by
  obtain ⟨r, hr, y, hy, e₁, e₂⟩ := (expands_iff U k s x).1 h
  have h0 : algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  refine (expandsG_iff U F k _ _).2 ⟨1, fun _ => (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r))⁻¹,
    fun _ => y, fun _ => hy, ?_, fun α => ?_⟩
  · rw [Fin.sum_univ_one, e₁]
    exact (inv_smul_smul₀ h0 _).symm.trans (congrArg _ (map_smulₛₗ (extendSec U F k) _ s).symm)
  · rw [Fin.sum_univ_one, e₂, map_smulₛₗ, inv_smul_smul₀ h0]
    rfl

theorem exists_isos {X' XG XK XA : Scheme.{0}} {L' : LB X'} {LG : LB XG} {LA : LB XA}
    (h' : L'.IsLB) (hG : LG.IsLB) (hA : LA.IsLB) {m : X' ⟶ XG} {w : LB.Iso L' (LG.pull m)} (gw' : w.IsGen)
    {π : XK ⟶ XG} {a : XK ⟶ XA} {a' : XA ⟶ XK} (ha' : a' ≫ a = 𝟙 _) (ha : a ≫ a' = 𝟙 _) {g : XA ⟶ X'}
    (hg : g ≫ m = a' ≫ π) (ext : LBIso (LA.pull a) (LG.pull π)) :
    ∃ (W : LB.Iso (LA.pull a) (LG.pull π)) (ω : LB.Iso LA (L'.pull g)), W.IsGen ∧ ω.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ XK) (z : Z) j' jG jA, g (a (r z)) ∈ L'.U j' →
        m (g (a (r z))) ∈ LG.U jG → a (r z) ∈ LA.U jA →
        BoxExpansion.pw W r z jA jG = Geo.Tor.gw w ((r ≫ a) ≫ g) z jG j' * Geo.Tor.gw ω (r ≫ a) z j' jA := by
  obtain ⟨ω₂, hω₂⟩ : LBIso LA (LG.pull (g ≫ m)) :=
    LBIso.chartPull (chartPullSec LA a a' ha')
      (chartPullSame LG (fun _ : PUnit => g ≫ m) (fun _ => π) (fun _ => 1) a' fun _ => hg) ext
  obtain rfl : π = a ≫ g ≫ m := by rw [hg, ← Category.assoc, ha, Category.id_comp]
  obtain ⟨W, hW, vW⟩ := IsoValConst.exists_iso_pull hω₂ a
  rw [isGen_iff] at gw' hω₂
  obtain ⟨ω, T⟩ := Geo.Tor.exists_cancel hG w ω₂ gw' hω₂ h' hA
  refine ⟨W, ω, hW, (isGen_iff _).2 (T.pgen_cancel hG gw' hω₂), fun Z r z j' jG jA k' kG kA => ?_⟩
  have e : BoxExpansion.pw W r z jA jG = Geo.Tor.gw ω₂ (r ≫ a) z jG jA := vW Z r z jG jA kG kA
  rw [e, T Z (r ≫ a) z jG j' jA kG k' kA]

def Agree {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) (k : ℕ)
    {π : Y ⟶ X} (u : X' ⟶ Y) {p : Y' ⟶ X'} (x : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (zp : Z ⟶ Y'), zp ≫ p = r →
    ∀ (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
      sval s (r ≫ u) z J = ((gv w r z (fun _ => J (r ≫ m)) (J' (r ≫ 𝟙 _))).val) ^ k * sval x zp z J'

theorem agree_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G} (h : L₁ = L₂)
    {X' Y Y' : Scheme.{0}} {L' : LB X'} {m : X' ⟶ G.left} (w : LB.Iso L' (L₂.L.pull m)) (k : ℕ)
    {π : Y ⟶ G.left} (u : X' ⟶ Y) {p : Y' ⟶ X'}
    (x : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (s : LB.Sec (LB.LinComb L₁.L (K := Fin 1) (fun _ => π) (fun _ => (k : ℤ)))) :
    Agree w k u x (h ▸ s : LB.Sec (LB.LinComb L₂.L (K := Fin 1) (fun _ => π) (fun _ => (k : ℤ)))) ↔
      Agree (PtTie.isoCast (congrArg RigLB.L h).symm m w) k u x s := by
  subst h
  rfl

theorem exists_agree {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {m : X' ⟶ X}
    {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) (k : ℕ) {π : Y ⟶ X} {u : X' ⟶ Y} [IsIso u] (hu : u ≫ π = m)
    {p : Y' ⟶ X'} [IsIso p] (x : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ)))) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (k : ℤ))), Agree w k u x s := by
  have hψ : ∀ _ : Fin 1, p ≫ m = (p ≫ u) ≫ π := fun _ => by rw [Category.assoc, hu]
  obtain ⟨s, hs⟩ := ArcPts.Transfer.exists_secThrough_up (φ' := fun _ : Fin 1 => p) (φ := fun _ => π)
    (ε := fun _ => (k : ℤ)) hw hL hL' hψ x
  refine ⟨s, ?_⟩
  rintro Z _ zp rfl z J J' hJ hJ'
  have := hs.sval hψ zp hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, ← Category.assoc] at this
  rw [Category.comp_id]
  exact this

open scoped CategoryTheory.Obj in

theorem finNu : PullbackSections.FinNuSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hT ϖ hϖ Q hQ vK hK tK m w hw a k ha hk h hh b U ⟨s, x, tie, hx, hν⟩ _hbk hU hUa
  subst ha
  have hL : Laws := abelianSchemeLaws_all.1
  have hTW : TWStatement := (twisting_statements_of_laws hL twistBaseChange).1
  let F := AlgebraicClosure (FractionRing V)
  obtain ⟨v, hv⟩ := exists_valOver_of_isAlgebraic hϖ F
  have := P.U.gen_hom
  have := P.A.isAb.comm
  have gpG : IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he, eφ⟩ := grpPullback_iso gpG m.cart
  have gp := isGrpPullback_of_iso e
  have i₁ : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₂ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have h' := tK.PP.isLB
  have hw' := SymActExpansion.isoCast_isGen (congrArg RigLB.L P.bundle).symm _ hw.1
  obtain ⟨W, ω, hW, hω, rel⟩ := exists_isos h' P.U.LG.isLB P.A.isLB hw' i₁ i₂ eφ P.U.ext
  have hio : PullbackSections.iotaK m ≫ pullback.fst t.G.hom (jK V) = m.φ := pullback.lift_fst _ _ _
  have : IsIso (PullbackSections.iotaK m) := inferInstanceAs (IsIso m.cart.1.isoPullback.hom)
  have : IsIso (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left := by
    have : IsIso (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G) := by rw [← leftUnitor_hom]; infer_instance
    exact inferInstanceAs (IsIso ((Over.forget _).map (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G)))
  have gio : (P.U.gen.hom.left ≫ e.hom.left) ≫ PullbackSections.iotaK m = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hio, Category.assoc, eφ, ← Category.assoc, i₂]
    · rw [Category.assoc, PullbackSections.iotaK, pullback.lift_snd, Category.assoc, Over.w, Over.w, Category.id_comp]
      rfl
  obtain ⟨s', tie'⟩ := exists_agree P.U.LG.isLB h' hw' k hio hh
  obtain ⟨x', hx', -⟩ := (P.U.expand k hk).1 s'
  refine ⟨s', x', (agree_cast P.bundle w k _ hh s').2 tie', hx', ?_⟩
  have tie₀ := (agree_cast P.bundle w k _ h s).1 tie
  have hb : (toUnit (TFK (R := V) F)).left ≫ b.left = (toUnit (TFK (R := V) F) ≫ b ≫ e.inv).left ≫ e.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨Ψ, h₁, h₂⟩ : ∃ Ψ : (TFK (R := V) F ⊗ P.A.A).left ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left,
      Ψ ≫ (fst _ tK.G).left = (fst _ P.A.A).left ≫ (toUnit (TFK (R := V) F)).left ∧
        Ψ ≫ (snd _ tK.G).left = (snd _ P.A.A).left ≫ e.hom.left :=
    ⟨(lift (fst _ P.A.A ≫ toUnit _) (snd _ P.A.A ≫ e.hom)).left, by rw [← Over.comp_left, lift_fst, Over.comp_left],
      by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hθk := fun θ : ThetaGrp P.A.A P.A.L (k : ℤ) (TFK (R := V) F) => TranslMove.pt_pow_eq_one hL.kerPow P.A k rfl θ
  obtain ⟨θ, hθ, mv⟩ := TranslMove.exists_symLift gp h' P.A.isLB hω h₁ h₂ hθk hb hU
  obtain ⟨t₁, R₁⟩ : ∃ t₁ : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F)), TranslMove.SecRel ω Ψ h t₁ := by
    obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => (snd (TFK (R := V) F) P.A.A).left)
      (φ := fun _ => (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) (ε := fun _ => (k : ℤ)) hω h' P.A.isLB
      (fun _ => h₂.symm) h
    refine ⟨s, fun Z r z J J' hJ hJ' => (hs.sval (fun _ => h₂.symm) r hJ hJ').trans ?_⟩
    rw [Fin.prod_univ_one]
    rfl
  obtain ⟨t₂, act, R₂⟩ := mv _ _ _ hUa R₁
  have g₁ : (P.U.genF F).left ≫ (snd (TFK (R := V) F) P.A.A).left =
      (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left ≫ P.U.gen.hom.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have key : ∀ (s : P.U.SecK k) (h : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
      (t₁ : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))),
      Agree (PtTie.isoCast (congrArg RigLB.L P.bundle).symm m.φ w) k (PullbackSections.iotaK m) h s →
      TranslMove.SecRel ω Ψ h t₁ → GeneratorPullback.IsoRelM P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK V)) W
        (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left k
        (snd (TFK (R := V) F) P.A.A).left (P.U.genF F).left t₁
        (UnifPre.gFK (R := V) (G := t.G) F) (𝟙 _) (extendSec P.U.toUnifPre F k s) := by
    intro s h t₁ tie R
    refine BoxExpansion.isoRel_of_val P.A.isLB P.U.LG.isLB g₁ (Category.id_comp _) fun z JA JG hJA hJG => ?_
    obtain ⟨J', hJ'⟩ := TranslMove.exists_good_pt h' z
    refine (sval_pullOver _ _ _ _ hJG).trans ?_
    obtain ⟨n, hn⟩ : ∃ n, n = (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left := ⟨_, rfl⟩
    have c₁ : ((n ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ PullbackSections.iotaK m = n := by
      rw [Category.assoc n, Category.assoc n, gio, Category.comp_id]
    have c₂ : ((n ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ m.φ = n ≫ pullback.fst t.G.hom (jK V) := by
      rw [← hio, ← Category.assoc, c₁]
    have a₁ := tie _ ((n ≫ P.U.gen.hom.left) ≫ e.hom.left) ((P.U.genF F).left ≫ Ψ)
      (by rw [Category.assoc, h₂, ← Category.assoc, g₁, hn]) z JG J' hJG hJ'
    have a₂ := R _ (P.U.genF F).left z J' JA hJ' hJA
    have a₃ := rel _ n z (J' ((n ≫ P.U.gen.hom.left) ≫ e.hom.left))
      (JG (((n ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ m.φ)) (JA (n ≫ P.U.gen.hom.left))
      (hJ' ((n ≫ P.U.gen.hom.left) ≫ e.hom.left)) (hJG (((n ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ m.φ))
      (hJA (n ≫ P.U.gen.hom.left))
    rw [g₁, ← hn, TranslMove.wv, zpow_natCast] at a₂
    rw [c₁, Category.comp_id] at a₁
    rw [← hn, ← c₂, Category.id_comp, a₃, mul_pow, Units.val_mul, _root_.mul_assoc]
    exact a₁.trans (congrArg₂ (· * ·) (Units.val_pow_eq_pow_val _ _).symm a₂)
  exact (nuGe_famPull_iff hϖ hK hv hL.globalFns hk Q x' 0).1
    ((nuGe_iff_of_isActOf_of_pow_eq_one hL hTW V ϖ hϖ E H t P hT
      (expansion_bijective_over_fields hL.globalFns V _ P.D P.A t.G P.U) Q hQ F v hv k hk W hW θ k hk (hθk θ) (hθk θ)
      hθ.pow_eq t₁ t₂ _ _ ⟨_, key s h t₁ tie₀ R₁, expandsG_extend _ F hL.globalFns hx⟩
      ⟨_, key s' hh t₂ tie' R₂, expandsG_extend _ F hL.globalFns hx'⟩ act 0).1
      ((nuGe_famPull_iff hϖ hK hv hL.globalFns hk Q x 0).2 hν))

end GlobalTheory.FiniteLiftNu
