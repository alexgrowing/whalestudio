import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameMove

open GlobalTheory.ConstFam

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left} {x : T ⟶ A} {x' : T' ⟶ A'}

theorem comp_pow {T₀ : Over S} (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem base_comm (gp : IsGrpPullback A' A f φ) (hx : x'.left ≫ φ = h ≫ x.left) : h ≫ T.hom = T'.hom ≫ f := by
  rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, gp.1.w, ← Category.assoc, Over.w x']

theorem pow_comm (gp : IsGrpPullback A' A f φ) (hx : x'.left ≫ φ = h ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = h ≫ (x ^ n).left := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h (base_comm gp hx)
  have e : pushHom gp T' x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e' := map_pow (pushHom gp T') x' n
  rw [e, ← comp_pow] at e'
  exact congrArg (fun q => q.left) e'

theorem pow_eq_one_of (gp : IsGrpPullback A' A f φ) (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} (hn : x ^ n = 1) :
    x' ^ n = 1 := by
  refine Over.OverMorphism.ext (gp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a := pow_comm gp hx n
  have b := pow_comm gp hx 0
  rw [pow_zero, pow_zero] at b
  rw [a, b, hn]

theorem comp_mulA (x : T ⟶ A) (n : ℕ) : x.left ≫ (mulA A n).left = (x ^ n).left := by
  rw [← Over.comp_left, comp_pow, Category.comp_id]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  have := comp_mulA (1 : 𝟙_ (Over S) ⟶ A) n
  rw [one_pow, e₁] at this
  exact this

omit [GrpObj A] in
theorem prod_ext {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ A).left} (h₁ : a ≫ (fst T A).left = b ≫ (fst T A).left)
    (h₂ : a ≫ (snd T A).left = b ≫ (snd T A).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_prodMap (gp : IsGrpPullback A' A f φ) (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ A').left ⟶ (T ⊗ A).left, (snd T' A').left ≫ φ = H ≫ (snd T A).left ∧
      ∀ (x : T ⟶ A) (x' : T' ⟶ A'), x'.left ≫ φ = h ≫ x.left →
        (ptSecT A' x').left ≫ H = h ≫ (ptSecT A x).left := by
  let ρ : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ h) (by
    show ((fst T' A').left ≫ h) ≫ T.hom = (T' ⊗ A').hom ≫ f
    rw [Category.assoc, hh, ← Category.assoc, Over.w])
  have h₁ : (lift ρ (pushHom gp _ (snd T' A'))).left ≫ (fst T A).left = (fst T' A').left ≫ h :=
    congrArg (fun q => q.left) (lift_fst ρ (pushHom gp _ (snd T' A')))
  have h₂ : (lift ρ (pushHom gp _ (snd T' A'))).left ≫ (snd T A).left = (snd T' A').left ≫ φ :=
    congrArg (fun q => q.left) (lift_snd ρ (pushHom gp _ (snd T' A')))
  obtain ⟨H, h₁, h₂⟩ : ∃ H : (T' ⊗ A').left ⟶ (T ⊗ A).left, H ≫ (fst T A).left = (fst T' A').left ≫ h ∧
    H ≫ (snd T A).left = (snd T' A').left ≫ φ := ⟨_, h₁, h₂⟩
  refine ⟨H, h₂.symm, fun x x' hx => prod_ext ?_ ?_⟩
  · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
      lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
      lift_snd, lift_snd, hx]

end Grp

section Val

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem val_powFrame (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ) (r : Z ⟶ T.left)
    (z : Z) (J) : val (powFrame A L x τ k) r z J = val τ r z J ^ k := map_zpow _ _ _

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J =
      gs r z ⊤ v * (val τ r z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J
    (fun _ => J (r ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs r z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull r (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ x.left))) (val_le A L x _ hy) _)).symm

end Val

section Move

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem isTorsFrame_move (gp : IsGrpPullback P'.A P.A f φ) (hw : w.IsGen)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {rig' : LB.Gen (P'.L.pull (eSec P'.A))}
    (hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval rig' r z J')
    {x : T ⟶ P.A} {x' : T' ⟶ P'.A} (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} {τ} (H : IsTorsFrame P rig n x τ)
    {τ' : LB.Gen (LB.LinComb P'.L (Y := T'.left) (K := Fin 1) (fun _ => x'.left) (fun _ => 1))} (hτ' : τ'.IsGen)
    (ht : ∀ (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val τ h z J = wVal w z J J' x'.left * val τ' (𝟙 _) z J') : IsTorsFrame P' rig' n x' τ' := by
  obtain ⟨hn, -, α, hα, hN, hc⟩ := H
  have hn' := pow_eq_one_of gp hx hn
  obtain ⟨α', hα', Hα⟩ := exists_gen_through (φ' := ![𝟙 P'.A.left, (mulA P'.A n).left]) (h := φ) hw P.isLB P'.isLB
    (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact pow_comm gp (x := 𝟙 P.A) (x' := 𝟙 P'.A) (h := φ)
          ((Category.id_comp _).trans (Category.comp_id _).symm) n) α hα
  have Hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      val α (r ≫ φ) z J = wVal w z J J' r ^ ((n : ℤ) ^ 2) * (wVal w z J J' (r ≫ (mulA P'.A n).left))⁻¹ *
        val α' r z J' := fun Z r z J J' hJ hJ' => by
    rw [Hα Z r z J J' hJ hJ', Fin.prod_univ_two]
    simp
  refine ⟨hn', hτ', α', hα', corr_of_val P'.isLB fun y J' hJ' => ?_, corr_of_val P'.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' P.isLB y
    have a : val α (f ≫ eSec P.A) y J = rval rig f y J ^ ((n : ℤ) ^ 2) * (rval rig f y J)⁻¹ :=
      (val_pull hJ α (eSec P.A) f).symm.trans ((val_corr hJ hN f).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
    have b := Hα' _ (eSec P'.A) y J J' hJ hJ'
    have c : rval rig f y J = wVal w y J J' (eSec P'.A) * rval rig' (𝟙 _) y J' := hr _ (𝟙 _) y J J' hJ hJ'
    rw [eSec_mulA] at b
    have b' := (congrArg (fun q => val α q y J) (PolBaseChange.eSec_comm gp)).symm.trans b
    have g : val α' (eSec P'.A) y J' = rval rig' (𝟙 _) y J' ^ ((n : ℤ) ^ 2) * (rval rig' (𝟙 _) y J')⁻¹ := by
      have d := a.symm.trans b'
      rw [c] at d
      apply Additive.ofMul.injective
      replace d := congrArg Additive.ofMul d
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at d ⊢
      linear_combination (norm := module) -d
    exact (val_pull hJ' α' (eSec P'.A) (𝟙 _)).trans (g.trans ((val_mul hJ' _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))).symm)
  · obtain ⟨J, hJ⟩ := exists_good' P.isLB y
    have a : val τ h y J ^ ((n : ℤ) ^ 2) = val α (h ≫ x.left) y J * rval rig (h ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc h).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_rigT _ _ _ hJ))))
    have b := Hα' _ x'.left y J J' hJ hJ'
    have c : rval rig (T'.hom ≫ f) y J = wVal w y J J' (1 : T' ⟶ P'.A).left * rval rig' T'.hom y J' :=
      hr _ T'.hom y J J' hJ hJ'
    rw [comp_mulA, hn', hx] at b
    rw [b, base_comm gp hx, c, ht y J J' hJ hJ'] at a
    have g : val τ' (𝟙 _) y J' ^ ((n : ℤ) ^ 2) = val α' x'.left y J' * rval rig' T'.hom y J' ^ (1 : ℤ) := by
      apply Additive.ofMul.injective
      replace a := congrArg Additive.ofMul a
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at a ⊢
      linear_combination (norm := module) a
    rw [val_powFrame, val_mul hJ', val_pull hJ', val_rigT _ _ _ hJ', Category.id_comp]
    exact g

theorem exists_move (gp : IsGrpPullback P'.A P.A f φ) (lb : LBIso P'.L (P.L.pull φ)) (hh : h ≫ T.hom = T'.hom ≫ f)
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P'.A)}
    (hx : ∀ i, (x' i).left ≫ φ = h ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P'.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      rig'.IsGen ∧ (∀ i, IsTorsFrame P' rig' n (x' i) (τ' i)) ∧ ∀ (k : ℤ) (σ : LB.Sec (LPow P.A P.L k T)),
        ∃ t : LB.Sec (LPow P'.A P'.L k T'), ∀ (i : I) (c : Γ(T.left, ⊤)),
          IsValueAt P.A P.L k σ (x i) (powFrame P.A P.L (x i) (τ i) k) c → ∀ z J, Good P'.L z J →
            sval (L := P'.L) (φ := fun _ : Fin 1 => (snd T' P'.A).left) (ε := fun _ => k) t
                (ptSecT P'.A (x' i)).left z J =
              gs h z ⊤ c * (val (powFrame P'.A P'.L (x' i) (τ' i) k) (𝟙 _) z J).val := by
  obtain ⟨w, hw⟩ := lb
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := h) hw P.isLB P'.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  have ht : ∀ i (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val (τ i) h z J = wVal w z J J' (x' i).left * val (τ' i) (𝟙 _) z J' := fun i z J J' hJ hJ' => by
    have := Hτ i _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', τ', hrig', fun i => isTorsFrame_move gp hw hr (hx i) (H i) (hτ' i) (ht i),
    fun k σ => ?_⟩
  · obtain ⟨Φ, hΦ, hp⟩ := exists_prodMap gp hh
    obtain ⟨t, Ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' P'.A).left)
      (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => k) (h := Φ) hw P.isLB P'.isLB (fun _ => hΦ) σ
    refine ⟨t, fun i c hc z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := exists_good' P.isLB z
    have a := Ht.sval (fun _ => hΦ) (ptSecT P'.A (x' i)).left hJ hJ'
    have b := sval_valueAt hc h hJ
    have p₁ : val (powFrame P.A P.L (x i) (τ i) k) h z J = val (τ i) h z J ^ k := map_zpow _ _ _
    have p₂ : val (powFrame P'.A P'.L (x' i) (τ' i) k) (𝟙 _) z J' = val (τ' i) (𝟙 _) z J' ^ k := map_zpow _ _ _
    rw [hp _ _ (hx i), b, Fin.prod_univ_one, ← Over.comp_left, ptSecT, lift_snd, p₁, ht i z J J' hJ hJ', mul_zpow,
      Units.val_mul, mul_left_comm, Units.mul_right_inj] at a
    rw [p₂]
    exact a.symm

end Move

theorem gs_spMap {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (z : Sp F) (c : R) :
    gs (spMap y) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
      gs (𝟙 (Sp F)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (y c)) := by
  have e := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  exact (gs_pull (𝟙 (Sp F)) (spMap y) z ⊤ trivial _).symm.trans (congrArg (gs (𝟙 (Sp F)) z ⊤) e.symm)

end GlobalTheory.FrameMove

namespace GlobalTheory

open FrameMove

theorem exists_frames_on_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∀ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, LB.Gen (LB.LinComb u.A.L (Y := (TFK (R := u.V) (PadicAlgCl p)).left) (K := Fin 1) (fun _ => (x a).left) (fun _ => 1))), rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧ ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))), ∃ t : SecA u.A (PadicAlgCl p) k, ∀ (a : S.Gam) (c : S.R), IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) → ∀ z J, Good u.A.L z J → sA t (ptSecT u.A.A (x a)).left z J = @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (cst (R := u.V) (PadicAlgCl p) z (y₀ c)) * (val (powFrame u.A.A u.A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  intro o Ω _ _ _ S ρ p _ y₀ u x hx
  have hh : (spMap y₀ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := exists_move (T := baseOver (Sp S.R)) (T' := TFK (R := u.V) (PadicAlgCl p))
    u.cart u.lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (gs_spMap y₀ z c))⟩

end GlobalTheory
