import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

def lamPts {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) : Fin 4 → (T.left ⟶ B.left) :=
  ![(x * y).left, x.left, y.left, (1 : T ⟶ B).left]

def negε : Fin 4 → ℤ := ![-1, 1, 1, -1]

structure Data (R : Type) [CommRing R] [IsDomain R] where

  B : Over (Sp R)
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  g : ℕ
  smoothDim : SmoothOfRelativeDimension g B.hom

  M : RigLB B

  cub : CubicalStr B M
  ample : RelAmple B M.L
  ktriv : KTriv B M.L

  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]

  c : X → (𝟙_ (Over (Sp R)) ⟶ B)
  c_add : ∀ a b, c (a + b) = c a * c b

  tau : ∀ a b : X, LB.Gen (LB.LinComb M.L (lamPts (toUnit (TK R) ≫ c a) (toUnit (TK R) ≫ c b)) negε)
  tau_gen : ∀ a b, (tau a b).IsGen
  tau_symm : ∀ a b z J, Good M.L z J → val (tau a b) (𝟙 _) z J = val (tau b a) (𝟙 _) z J
  tau_add : ∀ a a' b z J, Good M.L z J →
    val (tau (a + a') b) (𝟙 _) z J * cubV cub z J (toUnit (TK R) ≫ c a) (toUnit (TK R) ≫ c a') (toUnit (TK R) ≫ c b) =
      val (tau a b) (𝟙 _) z J * val (tau a' b) (𝟙 _) z J

attribute [instance] Data.grp Data.comm Data.addX Data.freeX Data.finX

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Data.TauCoord (Q : Data R) (a b : Q.X) (k : (FractionRing R)ˣ) : Prop :=
  ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen ∧ ∀ z J, Good Q.M.L z J →
    val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J

def Data.IsMonomialTau (Q : Data R) {m : ℕ} (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, ∃ k : (FractionRing R)ˣ, (k : FractionRing R) = ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b ∧ Q.TauCoord a b k

def Data.IsPos (Q : Data R) (I : Ideal R) : Prop :=
  ∀ y : Q.X, y ≠ 0 → ∃ r ∈ I, ∃ k : (FractionRing R)ˣ, (k : FractionRing R) = algebraMap R (FractionRing R) r ∧ Q.TauCoord y y k

theorem Data.IsMonomialTau.isPos {Q : Data R} {m : ℕ} {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ Q.X}
    (h : Q.IsMonomialTau t β) {I : Ideal R} (ht : ∀ i, t i ∈ I) (h₀ : ∀ i y, 0 ≤ β i y y)
    (h₁ : ∀ y, y ≠ 0 → ∃ i, 0 < β i y y) : Q.IsPos I := fun y hy => by
  obtain ⟨k, hk, hc⟩ := h y y
  obtain ⟨i, hi⟩ := h₁ y hy
  refine ⟨∏ i, t i ^ (β i y y).toNat, Ideal.mem_of_dvd I (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    (I.pow_mem_of_mem (ht i) _ (by omega)), k, ?_, hc⟩
  rw [hk, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (h₀ i y)]

theorem Data.val_tau_zero (Q : Data R) (b : Q.X) (z J) (hJ : Good Q.M.L z J) : val (Q.tau 0 b) (𝟙 _) z J = 1 := by
  have h := Q.tau_add 0 0 b z J hJ
  have c0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have f : cubV Q.cub z J (toUnit (TK R) ≫ Q.c 0) (toUnit (TK R) ≫ Q.c 0) (toUnit (TK R) ≫ Q.c b) = 1 := by
    rw [c0, MonObj.comp_one]; exact (isCub_cubV Q.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

def lamVal {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J' (p ≫ (psum B' (x2 B') I.down).left)))

def Refines (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)
  {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left)

def IsMumfordOf [IsLocalRing R] (ξ : Sp R ⟶ S) (Q : Data R) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifOf F j e (spMap ρ ≫ ξ) π U

variable {F j e} in

theorem IsMumfordOf.isCN [IsLocalRing R] {ξ : Sp R ⟶ S} {Q : Data R} (h : IsMumfordOf F j e ξ Q) : IsCN R := h.1

variable {F j e} in

theorem IsMumfordOf.isPos [IsLocalRing R] {ξ : Sp R ⟶ S} {Q : Data R} (h : IsMumfordOf F j e ξ Q) :
    Q.IsPos (maximalIdeal R) := h.2.1

variable {F j e} in

theorem IsMumfordOf.unif [IsLocalRing R] {ξ : Sp R ⟶ S} {Q : Data R} (h : IsMumfordOf F j e ξ Q) :
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifOf F j e (spMap ρ ≫ ξ) π U := h.2.2

def HasPolChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ)
    (t : Fin m → R) (Q : Data R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ),
    (IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (IsMumfordOf F j e ξ Q ∧ Module.finrank ℤ Q.X ≤ g ∧ IsCone id φ δ ∧ (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) ∧
      Q.IsMonomialTau t fun i => (n : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

end Charts

namespace Wit

theorem exists_tau (D : DegPre R) (a b : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val t r z J = val (D.tau a b) r z J := by
  refine exists_gen D.P.isLB (fun U _ h => ?_) (D.tau a b) (DVR.tau_isGen D a b)
  have e₁ : ptK (D.c (a + b)) = ((toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b)).left := by
    rw [D.c_add]; exact congrArg (fun q : TK R ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TK R)) (D.c a) (D.c b))
  have e₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
  simp [lamPts, negε, ptK]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R where
  B := D.P.A
  comm := D.P.isAb.comm
  isAb := D.P.isAb
  g := D.P.g
  smoothDim := D.P.smoothDim
  M := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
  cub := D.cub
  ample := D.P.ample
  ktriv := D.P.ktriv
  X := D.X
  c := D.c
  c_add := D.c_add
  tau a b := (exists_tau D a b).choose
  tau_gen a b := (exists_tau D a b).choose_spec.1
  tau_symm a b z J hJ := ((exists_tau D a b).choose_spec.2 _ _ z J hJ).trans
    ((GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a b).trans ((exists_tau D b a).choose_spec.2 _ _ z J hJ).symm)
  tau_add a a' b z J hJ := (congrArg (· * _) ((exists_tau D (a + a') b).choose_spec.2 _ _ z J hJ)).trans
    ((GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB a a' b).trans (congrArg₂ (· * ·)
      ((exists_tau D a b).choose_spec.2 _ _ z J hJ).symm ((exists_tau D a' b).choose_spec.2 _ _ z J hJ).symm))

def idPull {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (inf_le_inf_right _ (fun _ hx => mem_pull.1 hx) :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_idPull {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idPull L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem idPull_isGen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : (idPull L).IsGen := by
  refine (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_
  rw [gw_idPull L f y j k hj hk, gw_idPull L f y j' k' hj' hk', Category.comp_id, mul_right_comm,
    gm_cocycle hL f y hj hj' hk', ← gm_cocycle hL f y hj hk hk', mul_inv_cancel_right]

theorem grpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem mono_jK : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem prod_neg_lamPts {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) {U : Type} [CommGroup U]
    (h : (T.left ⟶ B.left) → U) : ∏ k, (h (𝟙 _ ≫ lamPts x y k))⁻¹ ^ negε k =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left := by
  simp only [Category.id_comp, Fin.prod_univ_four]
  simp [lamPts, negε]

theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) : Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  refine ⟨𝟙 _, 𝟙 _, idPull _, ?_, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm⟩, idPull_isGen (DVR.linComb_isLB _ D.P.isLB _ _), fun a => ?_,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  · rw [hs]
    exact grpPullback_id D.P.A
  · rw [hs]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · obtain rfl : κ = 𝟙 _ := by
      rw [hs, Category.comp_id] at hκ
      have : Mono (jK R) := mono_jK
      exact (cancel_mono (jK R)).1 (hκ.trans (Category.id_comp _).symm)
    refine ((exists_tau D a b).choose_spec.2 _ _ z J' hJ').symm.trans ?_
    refine (gen_trans (exists_tau D a b).choose_spec.1 (𝟙 _) z (hJ'.mem _ _) (hJ.mem _ _)).trans (congrArg (· * _) ?_)
    have hm : ∀ {J}, Good D.P.L z J → (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := fun hJ => hJ.mem _ _
    refine Eq.trans ?_ (gw_idPull (abelian₂ D.P.A D.P.L) _ z _ _ (hm hJ) (hm hJ')).symm
    refine Eq.trans ?_ (gm_linComb D.P.L _ _ _ z _ _ (hm hJ) (hm hJ')).symm
    refine Eq.trans ?_ (GlobalTheory.PrimCocycle.prod_lam (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (fun q => gm q z _ (D.P.L.g (J q) (J' q)))).symm
    have inv : ∀ q, gm q z _ (D.P.L.g (J' q) (J q)) = (gm q z _ (D.P.L.g (J q) (J' q)))⁻¹ := fun q =>
      eq_inv_of_mul_eq_one_left ((gm_cocycle D.P.isLB q z (hJ' q) (hJ q) (hJ' q)).trans (gm_self D.P.isLB q z (hJ' q)))
    refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (𝟙 _ ≫ _))).trans ?_
    exact prod_neg_lamPts _ _ (fun q => gm q z _ (D.P.L.g (J q) (J' q)))

open InhTate in

def tate (k : ℤ) : Data InhTate.R where
  B := P0.A
  comm := P0.isAb.comm
  isAb := P0.isAb
  g := P0.g
  smoothDim := P0.smoothDim
  M := ⟨P0.L, tatePre.rig, P0.isLB, tatePre.rig_gen⟩
  cub := tatePre.cub
  ample := P0.ample
  ktriv := P0.ktriv
  X := ℤ
  c := tatePre.c
  c_add := tatePre.c_add
  tau a b := cg _ _ (pi0 ^ (k * a * b))
  tau_gen a b := cg_isGen _ _ _
  tau_symm a b z J hJ := (gm_res _ z _ (hJ.mem _ _) _).trans
    ((congrArg (fun l : ℤ => gm (𝟙 _) z ⊤ (pi0 ^ l)) (mul_right_comm k a b)).trans (gm_res _ z _ (hJ.mem _ _) _).symm)
  tau_add a a' b z J hJ := by
    refine (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) (gm_res _ z _ (hJ.mem _ _) _)).symm)
    rw [_root_.mul_one, ← map_mul, ← zpow_add, mul_add, add_mul]

instance (k : ℤ) : Nontrivial (tate k).X := inferInstanceAs (Nontrivial ℤ)

open InhTate in

theorem tate_isMonomialTau (k : ℤ) : (tate k).IsMonomialTau ![PowerSeries.X] ![k • mulForm] := fun (a b : ℤ) => by
  refine ⟨piK ^ (k * a * b), ?_, cg _ _ 1, cg_isGen _ _ _, fun z J hJ => ?_⟩
  · rw [Fin.prod_univ_one, _root_.mul_assoc]; exact Units.val_zpow_eq_zpow_val _ _
  refine (gm_res _ z _ (hJ.mem _ _) _).trans (Eq.trans ?_
    (congrArg (_ * ·) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).symm)
  rw [_root_.mul_one]
  exact congrArg (gm (𝟙 _) z ⊤) (map_zpow _ _ _).symm

theorem tate_isPos {k : ℤ} (hk : 0 < k) : (tate k).IsPos (maximalIdeal (PowerSeries ℚ)) :=
  (tate_isMonomialTau k).isPos
    (fun i => by
      rw [Subsingleton.elim i 0, PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _)
    (fun i (y : ℤ) => by
      rw [Subsingleton.elim i 0]; exact (mul_nonneg hk.le (mul_self_nonneg y) : 0 ≤ k * (y * y)))
    (fun (y : ℤ) hy => ⟨0, (mul_pos hk (mul_self_pos.2 hy) : 0 < k * (y * y))⟩)

open InhTate in

theorem not_isPos_tate_zero : ¬ (tate 0).IsPos (maximalIdeal (PowerSeries ℚ)) := fun h => by
  obtain ⟨r, hr, k, hk, u, -, hu⟩ := h (1 : ℤ) (one_ne_zero (α := ℤ))
  let J : ((TK InhTate.R).left ⟶ (tate 0).B.left) → (tate 0).M.L.ι := fun _ => PUnit.unit
  have hJ : ∀ z, Good (tate 0).M.L z J := fun _ _ => trivial
  have hle : (⊤ : (Sp InhTate.R).Opens) ≤ (LB.LinComb (tate 0).M.L (lamPts ((tate 0).c (1 : ℤ)) ((tate 0).c (1 : ℤ))) negε).U
      (fun _ => PUnit.unit) := fun _ _ => Set.mem_iInter.2 fun _ => trivial
  let a : Γ(Sp InhTate.R, ⊤)ˣ := res hle (u.s fun _ => PUnit.unit)
  have key : (1 : Γ((TK InhTate.R).left, ⊤)ˣ) = unitOn k * pullTop (jK InhTate.R) a := unit_ext fun z _ => by
    have h₁ := hu z J (hJ z)
    have h₂ : val ((tate 0).tau (1 : ℤ) (1 : ℤ)) (𝟙 _) z J = gm (𝟙 _) z ⊤ 1 := gm_res _ z _ ((hJ z).mem _ _) _
    have h₃ : val u (toUnit (TK InhTate.R)).left z J = gm (𝟙 _) z ⊤ (pullTop (jK InhTate.R) a) := by
      refine (gm_res _ z hle trivial _).symm.trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK InhTate.R) z ⊤ trivial a).symm)
      rfl
    rw [map_mul, ← h₂, h₁, h₃]
  let x : InhTate.R := (Scheme.ΓSpecIso (CommRingCat.of InhTate.R)).hom.hom a.val
  have hx : IsUnit x := a.isUnit.map _
  have nat := congrArg (fun g => g.hom a.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap InhTate.R (FractionRing InhTate.R))))
  have e := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).hom.hom v.val) key
  have e' : algebraMap InhTate.R (FractionRing InhTate.R) 1 = algebraMap InhTate.R (FractionRing InhTate.R) (r * x) := by
    rw [map_one, map_mul, ← hk]
    refine (map_one _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ nat)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).inv_hom_id_apply k.val
  exact (mem_maximalIdeal r).1 hr (IsUnit.of_mul_eq_one x (IsFractionRing.injective _ _ e').symm)

open InhTate in

theorem refines_tate : Refines (tate 2) (RingHom.id _) tatePre (AddEquiv.refl _) := by
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅⟩ := refines_ofDeg tatePre tauBimult
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun κ hκ a b z J J' hJ hJ' => (h₅ κ hκ a b z J J' hJ hJ').trans (congrArg (_ * ·) ?_)⟩
  refine ((exists_tau tatePre a b).choose_spec.2 _ κ z J hJ).trans ?_
  refine Eq.trans ?_ (gm_res κ z _ (hJ.mem _ _) _).symm
  unfold val
  erw [tau_isConst a b]
  exact gm_res _ z _ (hJ.mem _ _) _

theorem isCN_powerSeries : IsCN (PowerSeries ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance, algebraRat.charZero _⟩

theorem exists_pos_refined : ∃ (Q : Data (PowerSeries ℚ)) (D : DegData (PowerSeries ℚ) (maximalIdeal _))
    (ε : D.toPre.X ≃+ Q.X), Nontrivial Q.X ∧ IsCN (PowerSeries ℚ) ∧ Q.IsPos (maximalIdeal _) ∧
      Refines Q (RingHom.id _) D.toPre ε :=
  ⟨tate 2, ⟨InhTate.tatePre, InhTate.psiEven, InhTate.tauBimult,
    by rw [PowerSeries.maximalIdeal_eq_span_X]; exact InhTate.tateData.psi_pos,
    by rw [PowerSeries.maximalIdeal_eq_span_X]; exact InhTate.tateData.psi_tendsto⟩, AddEquiv.refl _,
    inferInstance, isCN_powerSeries, tate_isPos two_pos, refines_tate⟩

theorem exists_unif_of_isMumfordOf {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S)
    {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) [IsLocalRing R] (ξ : Sp R ⟶ S)
    (D : DegData R (maximalIdeal R)) (h : IsMumfordOf F j e ξ (ofDeg D.toPre D.tau_bimult)) :
    ∃ (G' : Over (Sp R)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (A : PolAV (Sp (FractionRing R)))
      (U : Unif (maximalIdeal R) D A G'), IsUnifOf F j e (spMap (RingHom.id R) ≫ ξ) π U :=
  h.unif R (RingHom.id R) h.isCN Function.injective_id (RingHom.Finite.id R) D _ (refines_ofDeg _ _)

end Wit

end GlobalTheory.PolDeg
