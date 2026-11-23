import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.FieldBaseChange
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenBasis

section Expansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

abbrev SecKM (U : UnifPre I D A G) (N : ℕ) : Type :=
  SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (N : ℤ)))

def resK (U : UnifPre I D A G) (N : ℕ) : SecG U N →ₛₗ[algebraMap R (FractionRing R)] SecKM U N :=
  pullOver U.LG.L _ (pullback.condition (f := G.hom) (g := jK R)) (fun _ => (Category.comp_id _).symm)

theorem sval_resK (U : UnifPre I D A G) (N : ℕ) (σ : SecG U N) {Z : Scheme.{0}} (r : Z ⟶ pullback G.hom (jK R))
    {z : Z} {J} (hJ : Good U.LG.L z J) : sval (resK U N σ) r z J = sval σ (r ≫ pullback.fst G.hom (jK R)) z J :=
  sval_pullOver _ _ σ r hJ

theorem comb_f (U : UnifPre I D A G) (N : ℕ) {n : ℕ} (c : Fin n → FractionRing R) (b : Fin n → SecKM U N) (j) :
    (∑ i, c i • b i : SecKM U N).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j := by
  show chartLin _ _ j (∑ i, c i • b i : SecKM U N) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem expands_resK (U : Unif I D A G) {N : ℕ} (σ : H0 U.LG.L N) (Φ : Fam D.toPre (FractionRing R) N)
    (f : ∀ α, SecAb D.toPre N α) (hE : ∀ e, U.ExpandsAt e N σ f)
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε N) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε N) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) :
    U.Expands N (resK U.toUnifPre N σ) Φ := by
  refine ⟨1, one_ne_zero, σ, f, ?_, fun α => ?_, hE⟩
  · exact (secScal_iff pullback.condition (fun _ => (Category.comp_id _).symm) U.LG.isLB _ _ _ (algebraMap R (FractionRing R)) rfl 1).2
      (by rw [map_one, one_smul]; rfl)
  · have e : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by simp [scal]
    rw [e]
    exact hf α

end Expansion

section Basis

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] [GeometricallyConnected G.hom] (hR : AdmBase R I) (U : Unif I D A G) {N : ℕ} (hN : 1 ≤ N)
  {n : ℕ} (b : Fin n → SecKM U.toUnifPre N) (Φ : Fin n → Fam D.toPre (FractionRing R) N)
  (hb : ∀ i, U.Expands N (b i) (Φ i))
include hR hN hb

theorem expands_comb (c : Fin n → FractionRing R) : U.Expands N (∑ i, c i • b i : SecKM U.toUnifPre N) (∑ i, c i • Φ i) :=
  GlobalTheory.expands_linear R I hR D A G U.toUnifPre N n b Φ c _ hb (comb_f U.toUnifPre N c b)

theorem exists_comb (hsp : Submodule.span (FractionRing R) (Set.range Φ) = ⊤) (t : SecKM U.toUnifPre N) :
    ∃ c : Fin n → FractionRing R, t = ∑ i, c i • b i := by
  obtain ⟨F, hF, -⟩ := (U.expand N hN).1 t
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : F ∈ ⊤))
  refine ⟨c, ((U.expand N hN).2 F).unique hF ?_⟩
  rw [← hc]
  exact expands_comb hR U hN b Φ hb c

theorem comb_inj (hli : LinearIndependent (FractionRing R) Φ) (c c' : Fin n → FractionRing R)
    (h : (∑ i, c i • b i : SecKM U.toUnifPre N) = ∑ i, c' i • b i) : c = c' := by
  have e₁ := expands_comb hR U hN b Φ hb c
  rw [h] at e₁
  have e := ((U.expand N hN).1 _).unique e₁ (expands_comb hR U hN b Φ hb c')
  exact funext (Fintype.linearIndependent_iffₛ.1 hli c c' e)

end Basis

section Transfer

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genO : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

abbrev baseK (R : Type) [CommRing R] [IsDomain R] : Over (Sp R) := Over.mk (spMap (algebraMap R (FractionRing R)))

def toGen : pullback G.hom (jK R) ⟶ (baseK R ⊗ G).left :=
  (lift (Over.homMk (pullback.snd G.hom (jK R)) rfl : genO G ⟶ baseK R)
    (Over.homMk (pullback.fst G.hom (jK R)) pullback.condition : genO G ⟶ G)).left

def fromGen : (baseK R ⊗ G).left ⟶ pullback G.hom (jK R) :=
  pullback.lift (snd (baseK R) G).left (fst (baseK R) G).left
    ((Over.w (snd (baseK R) G)).trans (Over.w (fst (baseK R) G)).symm)

theorem toGen_snd : toGen G ≫ (snd (baseK R) G).left = pullback.fst G.hom (jK R) := by
  rw [toGen, ← Over.comp_left, lift_snd]; rfl

theorem toGen_fst : toGen G ≫ (fst (baseK R) G).left = pullback.snd G.hom (jK R) := by
  rw [toGen, ← Over.comp_left, lift_fst]; rfl

theorem fromGen_fst : fromGen G ≫ pullback.fst G.hom (jK R) = (snd (baseK R) G).left := pullback.lift_fst _ _ _

theorem fromGen_snd : fromGen G ≫ pullback.snd G.hom (jK R) = (fst (baseK R) G).left := pullback.lift_snd _ _ _

theorem toGen_fromGen : toGen G ≫ fromGen G = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fromGen_fst, toGen_snd, Category.id_comp]
  · rw [Category.assoc, fromGen_snd, toGen_fst, Category.id_comp]

theorem fromGen_toGen : fromGen G ≫ toGen G = 𝟙 _ := by
  let fO : baseK R ⊗ G ⟶ genO G := Over.homMk (fromGen G) (by
    show fromGen G ≫ pullback.snd G.hom (jK R) ≫ jK R = _
    rw [← Category.assoc, fromGen_snd]
    exact Over.w (fst (baseK R) G))
  have e : fO ≫ lift (Over.homMk (pullback.snd G.hom (jK R)) rfl : genO G ⟶ baseK R)
      (Over.homMk (pullback.fst G.hom (jK R)) pullback.condition : genO G ⟶ G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, Category.id_comp]
      exact Over.OverMorphism.ext (fromGen_snd G)
    · rw [Category.assoc, lift_snd, Category.id_comp]
      exact Over.OverMorphism.ext (fromGen_fst G)
  exact congrArg CommaMorphism.left e

theorem Γ_inv_hom (K : Type) [CommRing K] (x : Γ(Sp K, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl

theorem Γ_hom_inv (K : Type) [CommRing K] (x : K) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} [GrpObj G]
  [IsCommMonObj G] (U : Unif I D A G) {N n : ℕ} (σ : Fin n → H0 U.LG.L N)

theorem sval_comb (c : Fin n → FractionRing R) (q : (baseK R ⊗ G).left ⟶ pullback G.hom (jK R)) (hq : q = fromGen G)
    {y : (baseK R ⊗ G).left} {J} (hJ : Good U.LG.L y J) :
    sval (∑ i, c i • resK U.toUnifPre N (σ i) : SecKM U.toUnifPre N) q y J =
      ∑ i, gs (fst (baseK R) G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i)) *
        sval (upSec G (σ i)) (toBase (algebraMap R (FractionRing R)) ▷ G).left y J := by
  subst hq
  refine (sval_sum' hJ _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  refine (sval_smul' hJ _ _ _).trans (congrArg₂ (· * ·) ?_ ((sval_resK U.toUnifPre N (σ i) _ hJ).trans ?_))
  · show gs (fromGen G ≫ pullback.snd G.hom (jK R)) y ⊤ _ = _
    rw [fromGen_snd]
  · refine Eq.trans ?_ (sval_upSec G (σ i) _ y hJ).symm
    exact congrArg (fun r => sval (σ i) r y J) ((fromGen_fst G).trans (VVRank.whisker_snd_left G _).symm)

abbrev toK (s : LB.Sec (LPow G U.LG.L (N : ℤ) (baseK R))) : SecKM U.toUnifPre N :=
  VVRank.pullTo (φ := fun _ : Fin 1 => (snd (baseK R) G).left) (ε := fun _ => (N : ℤ)) s (toGen G)
    (fun _ => toGen_snd G)

theorem lin_of_eq (s : LB.Sec (LPow G U.LG.L (N : ℤ) (baseK R))) (c : Fin n → FractionRing R)
    (h : toK G U s = ∑ i, c i • resK U.toUnifPre N (σ i)) :
    Lin G U.LG.L N (toBase (algebraMap R (FractionRing R))) (fun i => upSec G (σ i))
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i)) s := by
  intro y J hJ
  refine Eq.trans ?_ (sval_comb G U σ c _ rfl hJ)
  refine Eq.trans ?_ (congrArg (fun t : SecKM U.toUnifPre N => sval t (fromGen G) y J) h)
  refine Eq.trans ?_ (VVRank.sval_pullTo (φ := fun _ : Fin 1 => (snd (baseK R) G).left) (ε := fun _ => (N : ℤ))
    s (toGen G) (fun _ => toGen_snd G) (fromGen G) y hJ).symm
  exact congrArg (fun r => sval (φ := fun _ : Fin 1 => (snd (baseK R) G).left) (ε := fun _ => (N : ℤ)) s r y J)
    (fromGen_toGen G).symm

theorem eq_of_lin (s : LB.Sec (LPow G U.LG.L (N : ℤ) (baseK R))) (c : Fin n → Γ(Sp (FractionRing R), ⊤))
    (h : Lin G U.LG.L N (toBase (algebraMap R (FractionRing R))) (fun i => upSec G (σ i)) c s) :
    toK G U s = ∑ i, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c i) •
      resK U.toUnifPre N (σ i) := by
  set t : SecKM U.toUnifPre N := ∑ i, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c i) •
      resK U.toUnifPre N (σ i) with ht
  have hs : s = VVRank.pullTo (φ := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε := fun _ => (N : ℤ))
      t (fromGen G) (fun _ => fromGen_fst G) := by
    refine sec_ext' U.LG.isLB fun y J hJ => (h y J hJ).trans ?_
    refine Eq.trans ?_ (VVRank.sval_pullTo _ _ _ (𝟙 _) y hJ).symm
    refine Eq.trans ?_ (sval_comb G U σ _ _ (Category.id_comp _) hJ).symm
    exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (congrArg _ (Γ_inv_hom _ (c i)).symm)
  subst hs
  refine sec_ext' U.LG.isLB fun x J hJ => ?_
  refine (VVRank.sval_pullTo _ (toGen G) _ (𝟙 _) x hJ).trans ((VVRank.sval_pullTo _ (fromGen G) _ _ x hJ).trans ?_)
  exact congrArg (fun r => sval t r x J) (by rw [Category.id_comp, toGen_fromGen])

end Transfer

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (N : ℕ), 1 ≤ N →
    ∀ (n : ℕ) (σ : Fin n → H0 U.LG.L N) (Φ : Fin n → Fam D.toPre (FractionRing R) N)
      (f : Fin n → ∀ α, SecAb D.toPre N α), (∀ i e, U.ExpandsAt e N (σ i) (f i)) →
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε N) ((Φ i).s α)
        (D.toPre.famφB α) (DegPre.famε N) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) →
      LinearIndependent (FractionRing R) Φ → Submodule.span (FractionRing R) (Set.range Φ) = ⊤ →
      BasisAlong G U.LG.L N (toBase (algebraMap R (FractionRing R))) (fun i => upSec G (σ i)) := by
  intro R _ _ _ hR D A G _ _ hG U N hN n σ Φ f hE hf hli hsp
  have hadm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hb : ∀ i, U.Expands N (resK U.toUnifPre N (σ i)) (Φ i) := fun i =>
    expands_resK U (σ i) (Φ i) (f i) (hE i) (hf i)
  intro s
  obtain ⟨c, hc⟩ := exists_comb hadm U hN _ Φ hb hsp (toK G U s)
  refine ⟨_, lin_of_eq G U σ s c hc, fun c' hc' => ?_⟩
  have e := comb_inj hadm U hN _ Φ hb hli _ _ ((eq_of_lin G U σ s c' hc').symm.trans hc)
  subst e
  funext i
  exact (Γ_inv_hom _ (c' i)).symm

end GlobalTheory.GenBasis
