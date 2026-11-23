import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.EmbSpan

open ReciprocityTheory.ChartRestriction.G.Out

theorem pt_pow_and_surjective (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (P : PolAV S) (f : S' ⟶ S)
    (n : ℕ) (hn : 1 ≤ n) : (∀ θ : ThetaGrp P.A P.L n (Over.mk f), θ.pt ^ n = 1) ∧
      Surjective (mulT P.A (Over.mk f) n).left := by
  obtain ⟨P', g, hg, -, hmul, hiso⟩ := hL.polBaseChange S S' f P
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨h, k, hk, -, hs, hf, -⟩ := GeomPointSections.exists_totalIso hg hmul
  let Φ : ∀ T : Over S', (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := fun T =>
    MonoidHom.mk' (toBase hg.w) (hmul T)
  have c' : (fst (baseOver S') P'.A).left = (baseOver S' ⊗ P'.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst (baseOver S') P'.A))
  let H : Over.mk ((baseOver S' ⊗ P'.A).hom ≫ f) ⟶ Over.mk f ⊗ P.A := Over.homMk h (by
    have e := Over.w (fst (Over.mk f) P.A)
    exact (congrArg (h ≫ ·) e.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ f) (hf.trans c'))))
  have Hs : H ≫ snd (Over.mk f) P.A = Φ _ (snd (baseOver S') P'.A) := Over.OverMorphism.ext hs.symm
  constructor
  · intro θ
    have sq : θ.pt.left ≫ P.A.hom = 𝟙 S' ≫ f := (Over.w θ.pt).trans (Category.id_comp f).symm
    let x' : baseOver S' ⟶ P'.A := Over.homMk (hg.lift _ _ sq) (hg.lift_snd _ _ _)
    have ex : x'.left ≫ g = θ.pt.left := hg.lift_fst _ _ _
    have e₀ : H ≫ fst (Over.mk f) P.A ≫ θ.pt = Φ _ (fst (baseOver S') P'.A ≫ x') :=
      Over.OverMorphism.ext ((Category.assoc h _ _).symm.trans ((congrArg₂ (· ≫ ·) hf ex.symm).trans
        (Category.assoc _ _ _).symm))
    have e₁ : H ≫ translPt P.A θ.pt = Φ _ (translPt P'.A x') := by
      refine (MonObj.comp_mul H (fst (Over.mk f) P.A ≫ θ.pt) (snd (Over.mk f) P.A)).trans
        (Eq.trans ?_ (map_mul (Φ _) (fst (baseOver S') P'.A ≫ x') (snd (baseOver S') P'.A)).symm)
      rw [e₀, Hs]
    have e₂ : h ≫ (translPt P.A θ.pt).left = (translPt P'.A x').left ≫ g := congrArg (fun q => q.left) e₁
    obtain ⟨t₁, h₁⟩ := KerPow.HasGen.pull (L := P.L)
      (φ := ![(snd (Over.mk f) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(n : ℤ), -n]) ⟨θ.φ, θ.isGen⟩ h
      (φ' := fun i => ![(snd (baseOver S') P'.A).left, (translPt P'.A x').left] i ≫ g)
      (fun i => by fin_cases i; exacts [hs.symm, e₂])
    obtain ⟨t₂, h₂⟩ := exists_down hw' P.isLB P'.isLB t₁ h₁
    have hx : x' ^ n = 1 := (hL.kerPow S' P' n hn _ x').1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ t₂ h₂ _⟩
    let j : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') rfl
    have ej : j ≫ θ.pt = Φ _ x' := Over.OverMorphism.ext ((Category.id_comp _).trans ex.symm)
    have : j ≫ θ.pt ^ n = j ≫ 1 := by
      rw [MonObj.comp_pow, ej, ← map_pow, hx, map_one, MonObj.comp_one]
    exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
      ((congrArg (fun q => q.left) this).trans (Category.id_comp _)))
  · have s₁ := VVRank.surjective_mulT P'.A n (hL.mulN S' P' n hn).2.2.1 (baseOver S')
    have s₂ : Surjective h := by
      have : Surjective (k ≫ h) := by rw [hk]; infer_instance
      exact Surjective.of_comp k h
    have t₁ : (mulT P.A (Over.mk f) n).left ≫ (fst (Over.mk f) P.A).left = (fst (Over.mk f) P.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₂ : (mulT P.A (Over.mk f) n).left ≫ (snd (Over.mk f) P.A).left = (snd (Over.mk f) P.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₁' : (mulT P'.A (baseOver S') n).left ≫ (fst (baseOver S') P'.A).left = (fst (baseOver S') P'.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have t₂' : (mulT P'.A (baseOver S') n).left ≫ (snd (baseOver S') P'.A).left =
        (snd (baseOver S') P'.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have e₁ : H ≫ snd (Over.mk f) P.A ^ n = Φ _ (snd (baseOver S') P'.A ^ n) := by
      rw [MonObj.comp_pow, Hs, map_pow]
    have e₂ : h ≫ (snd (Over.mk f) P.A ^ n).left = (snd (baseOver S') P'.A ^ n).left ≫ g :=
      congrArg (fun q => q.left) e₁
    have ext₁ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (Over.mk f ⊗ P.A).left},
        r ≫ (fst (Over.mk f) P.A).left = r' ≫ (fst (Over.mk f) P.A).left →
        r ≫ (snd (Over.mk f) P.A).left = r' ≫ (snd (Over.mk f) P.A).left → r = r' :=
      fun e e' => pullback.hom_ext e e'
    have e : (mulT P'.A (baseOver S') n).left ≫ h = h ≫ (mulT P.A (Over.mk f) n).left := ext₁
      (by rw [Category.assoc, Category.assoc, t₁, hf, t₁'])
      (by rw [Category.assoc, Category.assoc, t₂, ← hs, ← Category.assoc, t₂', e₂])
    have : Surjective (h ≫ (mulT P.A (Over.mk f) n).left) := by rw [← e]; infer_instance
    exact Surjective.of_comp h _

theorem exists_pow_eq {G : Type} [CommGroup G] {r N u v : ℕ} (hN : N = u * v) (hN0 : N ≠ 0) (p : Fin r → G)
    (hp : ∀ i, p i ^ N = 1) (hb : ∀ y : G, y ^ N = 1 → ∃! c : Fin r → ZMod N, ∏ i, p i ^ (c i).val = y)
    (y : G) (hy : y ^ u = 1) : ∃ a : Fin r → ZMod N, (∏ i, p i ^ (a i).val) ^ v = y := by
  have : NeZero N := ⟨hN0⟩
  have hu : u ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  obtain ⟨c, hc, -⟩ := hb y (by rw [hN, pow_mul, hy, one_pow])
  have h0 : (fun i => (((c i).val * u : ℕ) : ZMod N)) = 0 := by
    refine (hb 1 (one_pow _)).unique ?_ (by simp)
    rw [← hy, ← hc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), pow_mul]
  have hd : ∀ i, v ∣ (c i).val := fun i => by
    have := (ZMod.natCast_eq_zero_iff _ _).1 (congrFun h0 i)
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hu)
      ((dvd_of_eq (hN.trans (mul_comm u v)).symm).trans this)
  refine ⟨fun i => (((c i).val / v : ℕ) : ZMod N), ?_⟩
  rw [← hc, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), ← pow_mul, Nat.div_mul_cancel (hd i)]

theorem span_eq_top (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k : ℤ} {n : ℕ} (hk : k = n) (h4 : 4 ≤ n) (hn : (n : K) ≠ 0) {I : Type} [Nonempty I]
    (U : I → ThetaGrp P.A P.L k (Over.mk x)) (hU : ∀ y : Over.mk x ⟶ P.A, y ^ n = 1 → ∃ c, (U c).pt = y)
    (s₁ : LB.Sec (LPow P.A P.L k (Over.mk x))) (σ : I → LB.Sec (LPow P.A P.L k (Over.mk x)))
    (hσ : ∀ c, IsActOf P.A P.L k (U c) s₁ (σ c)) (h0 : (SecM.ofSec P.A s₁ : SecM P.A P.L k (Over.mk x)) ≠ 0) :
    Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L k (Over.mk x))) = ⊤ := by
  subst hk
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P n (Over.mk x)
  have e : (fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L n (Over.mk x))) =
      fun c => ρ (U c) (SecM.ofSec P.A s₁) := funext fun c => ((k₁ _ _ _).1 (hσ c)).symm
  rw [e]
  exact VVRank.span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K x n (Or.inr h4) hn) ρ k₁ k₃ k₄ U
    (fun θ => hU _ ((pt_pow_and_surjective hL P x n (by omega)).1 θ)) _ h0

theorem ne_zero_of_isGenSec (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) (th : LB.Sec (LPow P.A P.L 1 (Over.mk x))) (h : IsGenSec P.A P.L 1 th) :
    (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) ≠ 0 := by
  intro h0
  have hnt : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  have hr : Module.finrank Γ((Over.mk x).left, ⊤) (SecM P.A P.L 1 (Over.mk x)) = 1 ^ P.g :=
    (secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).1 hL.globalSectionsRank S P K x 1 le_rfl
  have z : ∀ v : SecM P.A P.L 1 (Over.mk x), v = 0 := fun v => by
    obtain ⟨r, hr⟩ := h (SecM.toSec P.A v)
    have : v = r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) := Subtype.ext (funext hr)
    rw [this, h0, smul_zero]
  have : Subsingleton (SecM P.A P.L 1 (Over.mk x)) := ⟨fun a b => (z a).trans (z b).symm⟩
  rw [Module.finrank_zero_of_subsingleton, one_pow] at hr
  exact zero_ne_one hr

theorem emb_span_eq_top : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤ := by
  rintro hL - o _ g N' J b S s t m K _ _ x σ hodd ⟨d, hd⟩ hm ⟨th, s₁, α, U, hth, -, htw, hU, hσ⟩
  have := t.ab.comm
  have hN0 : N' ≠ 0 := hodd.pos.ne'
  have hdiv : N' / m = d := by rw [hd, Nat.mul_div_cancel_left _ (by omega)]
  have hK : ((N' ^ 2 : ℕ) : K) ≠ 0 := VVRank.natCast_ne_zero (x ≫ s) (by
    simpa using b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  have hN : N' ^ 2 = m ^ 2 * d ^ 2 := by rw [hd, mul_pow]
  refine span_eq_top hL t.pol x (n := m ^ 2) (Nat.cast_pow m 2).symm (by nlinarith)
    (fun h => hK (by rw [hN, Nat.cast_mul, h, zero_mul])) U (fun y hy => ?_) s₁ σ hσ fun h0 => ?_
  · obtain ⟨a, ha⟩ := exists_pow_eq (G := (Over.mk x ⟶ t.A)) hN (pow_ne_zero _ hN0)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i)
      (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
      (fun z hz => by simpa only [linComb, List.prod_ofFn] using t.bij K x z hz) y hy
    refine ⟨a, (hU a).pt_eq.trans (Eq.trans ?_ ha)⟩
    rw [hdiv, TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
    rfl
  · have hint : IsIntegral (Over.mk x ⊗ t.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ t.A.hom t.ab.smooth
        t.ab.geomConnected).geometrically_isIntegral x _ _ (IsPullback.of_hasPullback x t.A.hom).flip
    exact ne_zero_of_isGenSec hL t.pol x th hth (VVRank.ofSec_eq_zero_of_twist t.A t.isLB
      (pt_pow_and_surjective hL t.pol x m (by omega)).2 htw h0)

end GlobalTheory.EmbSpan
