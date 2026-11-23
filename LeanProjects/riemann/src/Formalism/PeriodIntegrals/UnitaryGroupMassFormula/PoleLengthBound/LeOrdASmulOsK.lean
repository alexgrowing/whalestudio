import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.RestrictedDerivativeLinear
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

section

variable (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

theorem rD_eq (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF))
    (h : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF) :
    rD G la β x = toA0K X la G.w wF ⟨_, h⟩ := by
  unfold rD
  rw [dif_pos h]

theorem rD_add (β : Idx D j G.N →₀ ℕ) (x y : ↥(HK X la G.w wF)) :
    rD G la β (x + y) = rD G la β x + rD G la β y := by
  have hP := hasse_preserves_kernel G la
  rw [rD_eq G la β _ (hP β _ (x + y).2), rD_eq G la β _ (hP β _ x.2), rD_eq G la β _ (hP β _ y.2), ← map_add]
  congr 1
  apply Subtype.ext
  exact (hasse X la G.w β).map_add _ _

def rDh (β : Idx D j G.N →₀ ℕ) : ↥(HK X la G.w wF) →+ SectionSheafQuotient X la G.w wF :=
  AddMonoidHom.mk' (rD G la β) (rD_add G la β)

theorem rD_sum (β : Idx D j G.N →₀ ℕ) {ι : Type*} (s : Finset ι) (f : ι → ↥(HK X la G.w wF)) :
    rD G la β (∑ i ∈ s, f i) = ∑ i ∈ s, rD G la β (f i) :=
  map_sum (rDh G la β) f s

theorem rD_zero (β : Idx D j G.N →₀ ℕ) : rD G la β 0 = 0 := (rDh G la β).map_zero

theorem hasse_smul_Op (β : Idx D j G.N →₀ ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF)) :
    hasse X la G.w β ((algebraMap (Op X la G.N) (Kp X la G.N) r • x : ↥(HK X la G.w wF)) : Lw X la G.w) =
      ∑ q ∈ antidiagonal β, algebraMap (Op X la G.N) (Kp X la G.N) (hasseOp X la G.N q.1 r) •
        hasse X la G.w q.2 (x : Lw X la G.w) := by
  have hA : ∀ (q : Idx D j G.N →₀ ℕ) (a : Op X la G.N), PI.HJP.H X la G.w q
      (algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) a)) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) (hasseOp X la G.N q a)) :=
    fun q a => hasse_algebraMap_Op X la G.w q a
  have e0 : ((algebraMap (Op X la G.N) (Kp X la G.N) r • x : ↥(HK X la G.w wF)) : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) r) * (x : Lw X la G.w) :=
    (algebraMap_Op_mul la G.w r x).symm
  show PI.HJP.H X la G.w β _ = ∑ q ∈ antidiagonal β, algebraMap (Op X la G.N) (Kp X la G.N)
    (hasseOp X la G.N q.1 r) • PI.HJP.H X la G.w q.2 (x : Lw X la G.w)
  rw [e0, PI.HJP.H_mul]
  simp only [hA, algebraMap_Op_mul la G.w]

theorem rD_smul (β : Idx D j G.N →₀ ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF)) :
    rD G la β (algebraMap (Op X la G.N) (Kp X la G.N) r • x) =
      ∑ q ∈ antidiagonal β, hasseOp X la G.N q.1 r • rD G la q.2 x := by
  have hP := hasse_preserves_kernel G la
  rw [rD_eq G la β _ (hP β _ (algebraMap (Op X la G.N) (Kp X la G.N) r • x).2)]
  have e : (⟨_, hP β _ (algebraMap (Op X la G.N) (Kp X la G.N) r • x).2⟩ : ↥(HK X la G.w wF)) =
      ∑ q ∈ antidiagonal β, algebraMap (Op X la G.N) (Kp X la G.N) (hasseOp X la G.N q.1 r) •
        (⟨_, hP q.2 _ x.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hasse_smul_Op G la β r x
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.map_smul_of_tower, rD_eq G la q.2 x (hP q.2 _ x.2)]
  rfl

end

section

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la)

theorem le_ordA_sum (hC : Q.InCurve) (ζ : PtsG G la) {ι : Type*} (s : Finset ι) (f : ι → SectionSheafQuotient X la G.w wF)
    (t : WithTop ℤ) (h : ∀ i ∈ s, t ≤ Q.ordA ζ (f i)) : t ≤ Q.ordA ζ (∑ i ∈ s, f i) := by
  classical
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    show t ≤ ordV _ ζ Q.e Q.c 0
    rw [ordV_zero Q.c ζ hU hC.2.2]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (ordV_add Q.c ζ hU hC.2.2 _ _)

theorem le_ordA_smul_OsK (hC : Q.InCurve) (ζ : PtsG G la) (a : OsK X la G.w) (ha : 0 ≤ ord (unifO X la G.N) ζ a)
    (v : SectionSheafQuotient X la G.w wF) (t : WithTop ℤ) (h : t ≤ Q.ordA ζ v) : t ≤ Q.ordA ζ (a • v) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  show t ≤ ordV _ ζ Q.e Q.c _
  rw [ordV_smul Q.c ζ hU hC.2.2]
  calc t = 0 + t := (zero_add t).symm
    _ ≤ _ := add_le_add ha h

theorem le_ordA_smul_Op (hC : Q.InCurve) (ζ : PtsG G la) (r : Op X la G.N) (v : SectionSheafQuotient X la G.w wF) (t : WithTop ℤ)
    (h : t ≤ Q.ordA ζ v) : t ≤ Q.ordA ζ (r • v) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [← algebraMap_smul (OsK X la G.w) r v]
  exact le_ordA_smul_OsK Q hC ζ _ (ord_nonneg ζ hU (Subalgebra.algebraMap_mem _ r)) v t h

def GoodP (T : ℕ) (m : PtsG G la → ℕ) (x : ↥(HK X la G.w wF)) : Prop :=
  ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
    ∀ ζ, ((-(m ζ : ℤ) : ℤ) : WithTop ℤ) ≤ Q.ordA ζ (rD G la β x)

variable {Q}

theorem good_add (hC : Q.InCurve) {T : ℕ} {m : PtsG G la → ℕ} {x y : ↥(HK X la G.w wF)}
    (hx : GoodP Q T m x) (hy : GoodP Q T m y) : GoodP Q T m (x + y) := fun β hβ ζ => by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [rD_add]
  exact (le_min (hx β hβ ζ) (hy β hβ ζ)).trans (ordV_add Q.c ζ hU hC.2.2 _ _)

theorem good_of_mem (hC : Q.InCurve) {T : ℕ} {m : PtsG G la → ℕ} (ha : 0 < a0 D j T) {x : ↥(HK X la G.w wF)}
    (hx : x ∈ Jid X la G.w ^ a0 D j T • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) :
    GoodP Q T m x := fun β hβ ζ => by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [vanishingOnQuadric G la (a0 D j T) β x hx (by omega)]
  show _ ≤ ordV _ ζ Q.e Q.c 0
  rw [ordV_zero Q.c ζ hU hC.2.2]
  exact le_top

theorem good_smul (hC : Q.InCurve) {T : ℕ} {m : PtsG G la → ℕ} {x : ↥(HK X la G.w wF)} (hx : GoodP Q T m x)
    (r : Op X la G.N) : GoodP Q T m (algebraMap (Op X la G.N) (Kp X la G.N) r • x) := fun β hβ ζ => by
  rw [rD_smul]
  refine le_ordA_sum Q hC ζ _ _ _ fun q hq => le_ordA_smul_Op Q hC ζ _ _ _ (hx q.2 ?_ ζ)
  rw [mem_antidiagonal] at hq
  rw [PI.HJP.sum_eq_degree] at hβ ⊢
  have : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by rw [← hq, map_add]
  omega

theorem good_of_mem_AAp (hC : Q.InCurve) {T : ℕ} {m : PtsG G la → ℕ} (ha : 0 < a0 D j T)
    {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Q.AAp T m) :
    ∀ x : ↥(HK X la G.w wF), toWK X la G.w wF (a0 D j T) x = z → GoodP Q T m x := by
  unfold LocalPointData.AAp at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, ⟨hg1, hg2⟩, rfl⟩ := hz
    intro x hx
    have hgood : GoodP Q T m g := fun β hβ ζ => by rw [rD_eq G la β g (hg1 β hβ)]; exact hg2 β hβ ζ
    have hd : x - g ∈ Jid X la G.w ^ a0 D j T • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
      rw [← toWK_eq_zero_iff, map_sub, hx, sub_self]
    have := good_add hC hgood (good_of_mem hC ha hd)
    convert this using 1
    abel
  | zero =>
    intro x hx
    exact good_of_mem hC ha ((toWK_eq_zero_iff X la G.w wF _ x).1 hx)
  | add z1 z2 _ _ h1 h2 =>
    intro x hx
    obtain ⟨x1, rfl⟩ := toWK_surjective X la G.w wF _ z1
    have hx2 : toWK X la G.w wF (a0 D j T) (x - x1) = z2 := by rw [map_sub, hx, add_sub_cancel_left]
    have := good_add hC (h1 x1 rfl) (h2 _ hx2)
    convert this using 1
    abel
  | smul r z _ h =>
    intro x hx
    obtain ⟨x1, rfl⟩ := toWK_surjective X la G.w wF _ z
    have e : toWK X la G.w wF (a0 D j T) (algebraMap (Op X la G.N) (Kp X la G.N) r • x1) =
        r • toWK X la G.w wF (a0 D j T) x1 := by
      rw [LinearMap.map_smul_of_tower]
      rfl
    have hd : x - algebraMap (Op X la G.N) (Kp X la G.N) r • x1 ∈
        Jid X la G.w ^ a0 D j T • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
      rw [← toWK_eq_zero_iff, map_sub, hx, e, sub_self]
    have := good_add hC (good_smul hC (h x1 rfl) r) (good_of_mem hC ha hd)
    convert this using 1
    abel

end

end PI.PoleLengthCount
