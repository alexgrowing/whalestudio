import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoLevels

open ReciprocityTheory.ChartRestriction.G.Out ThetaCoord CommPairing GlobalLift VVRank

theorem labelSymp_eq {g M : ℕ} (a b : Fin (2 * g) → ZMod M) :
    labelSymp a b = Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : ZMod M)) a b := by
  rw [labelSymp, Matrix.toBilin'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply]; ring

theorem labelSymp_swap {g M : ℕ} (a b : Fin (2 * g) → ZMod M) : labelSymp a b = -labelSymp b a := by
  have h : ∀ i j, stdSymp g i j = -stdSymp g j i := fun i j => by
    unfold stdSymp
    split_ifs <;> omega
  rw [labelSymp, labelSymp, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j i]; push_cast; ring

theorem eq_of_proportional {R : Type} [CommRing R] [IsDomain R] {g n j N' : ℕ} (hn : Odd n) (hN : N' = n ^ j)
    {ζ : Rˣ} (hζ : IsPrimitiveRoot ζ (N' ^ 2))
    (σ : (Fin (2 * g) → ZMod (N' ^ 2)) →ₗ[ZMod (N' ^ 2)] (Fin (2 * g) → ZMod (N' ^ 2)))
    (hσ : ∀ a b, labelSymp (σ a) (σ b) = labelSymp a b) (hm : ∀ a, N' • σ a = N' • a)
    (v : (Fin (2 * g) → ZMod (N' ^ 2)) → R) (u u' : Rˣ) (hu : ∀ a, u * v (σ a) = u' * v a)
    (hr : ∀ a b, v a = (ζ ^ thetaRelExp N' 1 a b : Rˣ) * v (a + N' • b))
    (hs : ∀ c, ∃ d, v (c + n • d) ≠ 0) (a : Fin (2 * g) → ZMod (N' ^ 2)) : σ a = a := by
  have ho : Odd N' := hN ▸ hn.pow
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  let ω := Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : ZMod (N' ^ 2)))
  let S := σ - LinearMap.id
  have hb : ∀ a, ∃ b, S a = N' • b := fun a => by
    have h : N' • S a = 0 := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, smul_sub, hm, sub_self]
    choose b hb using fun i => exists_eq_nsmul_of_nsmul_eq_zero_zmod ho.pos.ne' le_rfl (S a i) (congrFun h i)
    exact ⟨b, funext hb⟩
  have e : ∀ a, σ a = a + S a := fun a => by simp [S]
  have sw : ∀ a b, ω a b = -ω b a := fun a b => by
    rw [← labelSymp_eq, ← labelSymp_eq, labelSymp_swap]
  have hS : ∀ a b, ω (S a) b = ω (S b) a := fun a b => by
    have h := hσ a b
    rw [labelSymp_eq, labelSymp_eq, e, e] at h
    have h₀ : ω (S a) (S b) = 0 := by
      obtain ⟨x, hx⟩ := hb a
      obtain ⟨y, hy⟩ := hb b
      rw [hx, hy, map_nsmul, map_nsmul, LinearMap.smul_apply, ← mul_smul, ← sq, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul]
    change ω _ _ = ω _ _ at h
    simp only [map_add, LinearMap.add_apply] at h
    rw [sw (S b)]
    linear_combination h - h₀
  let q : (Fin (2 * g) → ZMod (N' ^ 2)) → ZMod (N' ^ 2) := fun a => (((N' ^ 2 + 1) / 2 : ℕ) : ZMod (N' ^ 2)) * ω a (S a)
  have h₁ : ∀ a, v a ≠ 0 → ζ ^ (q a).val * u' = u := fun a ha => by
    obtain ⟨b, hb⟩ := hb a
    have h := hr a b
    rw [thetaRelExp, one_pow, Nat.one_mul, ← hb, ← e, labelSymp_eq] at h
    refine Units.ext (mul_right_cancel₀ ha ?_)
    rw [Units.val_mul, _root_.mul_assoc, ← hu, mul_left_comm]
    exact congrArg _ h.symm
  obtain ⟨d₀, hd₀⟩ := hs 0
  have h0 : S = 0 := end_eq_zero_of_quad_const_on_cosets (isUnit_two_zmod_pow ho 2) (r := (n : ZMod (N' ^ 2)))
    ⟨j * 2, by rw [← Nat.cast_pow, pow_mul, ← hN, ZMod.natCast_self]⟩ ω (injective_toBilin'_stdSymp g) S hS (-1) q
    (fun x => by
      have : (2 : ZMod (N' ^ 2)) * (((N' ^ 2 + 1) / 2 : ℕ) : ZMod (N' ^ 2)) = 1 := by
        rw [show (2 : ZMod (N' ^ 2)) = ((2 : ℕ) : ZMod (N' ^ 2)) from Nat.cast_ofNat.symm, ← Nat.cast_mul,
          Nat.mul_div_cancel' ho.pow.add_one.two_dvd, Nat.cast_add,
          ZMod.natCast_self, zero_add, Nat.cast_one]
      rw [← _root_.mul_assoc, this, sw x]; simp)
    {t | v t ≠ 0}
    (fun x => by
      obtain ⟨d, hd⟩ := hs x
      exact ⟨_, hd, -d, by rw [Nat.cast_smul_eq_nsmul, smul_neg, add_neg_cancel_right]⟩)
    (q (0 + n • d₀))
    (fun t ht => ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      (mul_right_cancel ((h₁ t ht).trans (h₁ _ hd₀).symm))))
  rw [e, h0, LinearMap.zero_apply, add_zero]

theorem value_eq_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} {k : ℤ}
    {s s' : LB.Sec (LPow A L k T)} {r x y : Γ(T.left, ⊤)} (h : SecM.ofSec A s = r • SecM.ofSec A s') {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))}
    (H : IsValueAt A L k s w τ x) (H' : IsValueAt A L k s' w τ y) : x = r * y := by
  refine fn_ext fun z _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
  have a := sv_of_isValueAt H (𝟙 T) hJ
  have b := sv_of_isValueAt H' (𝟙 T) hJ
  have c : sv A s (lift (𝟙 T) (𝟙 T ≫ w)).left z J =
      gs (𝟙 T.left) z ⊤ r * sv A s' (lift (𝟙 T) (𝟙 T ≫ w)).left z J := by
    have := ThetaAct.sv_smul r (SecM.ofSec A s') (lift (𝟙 T) (𝟙 T ≫ w)).left z hJ
    rw [← h, lift_fst_left] at this
    exact this
  rw [a, b, ← _root_.mul_assoc] at c
  rw [gs_mul _ _ ⊤ trivial]
  exact (Units.mul_left_inj _).1 c

theorem levelPoint_injective {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Spec (CommRingCat.of K))} {M : ℕ}
    [NeZero M] {ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g) :
    Function.Injective (levelPoint lev hg) := by
  subst hg
  have E : ∀ c : Fin (2 * P.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  intro a b h
  have h₀ := lev.indep K (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
    ((E _).trans (h.trans (E _).symm))
  exact funext fun i => ZMod.val_injective M (congrArg Fin.val (congrFun h₀ i))

end GlobalTheory.TwoLevels

namespace GlobalTheory

open TwoLevels ThetaCoord in

theorem levelBasis_eq_of_isThetaPt : Out.Laws → ∀ (g n j N' : ℕ), Odd n → N' = n ^ j → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev lev' : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → Out.IsThetaPt P N' (levelPoint lev' hg) v → (∀ i, levelBasis lev hg i ^ N' = levelBasis lev' hg i ^ N') → (∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0) → ∀ i, levelBasis lev hg i = levelBasis lev' hg i := by
  intro hLaw g n j N' hn hN K _ _ P hg ze lev lev' v hv hv' hm hs
  have hG := hLaw.globalFns
  have := P.isAb.comm
  have ho : Odd N' := hv.1
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hp := levelBasis_pow lev hg
  have hp' := levelBasis_pow lev' hg
  have inj := levelPoint_injective lev hg
  choose s hs' using fun i => (pow_eq_one_iff (Nat.mul_one (N' ^ 2)).symm lev hg _).1 (hp' i)
  let σ := Fintype.linearCombination (ZMod (N' ^ 2)) s
  have e : ∀ a, levelPoint lev' hg a = levelPoint lev hg (σ a) := fun a => by
    rw [levelPoint_eq_lab, levelPoint_eq_lab]
    refine char_ext (lab (levelBasis lev' hg)) (fun a => lab (levelBasis lev hg) (σ a)) (lab_add hp')
      (fun a b => by rw [map_add, lab_add hp]) (fun i => ?_) a
    rw [lab_single hp', ← hs' i, pow_one, levelPoint_eq_lab, Fintype.linearCombination_apply_single, one_smul]
  have hw : ∀ (l : Out.Level P (N' ^ 2) ze) a b, Out.WeilIs P.A P.L (N' ^ 2 : ℕ) (levelPoint l hg a) (levelPoint l hg b)
      (ze ^ (labelSymp a b).val) := fun l a b => by
    rw [levelPoint_eq_lab]
    exact weilIs_lab hG P (levelBasis_pow l hg) (ze := ze) l.prim.pow_eq_one (weilIs_levelBasis l hg)
      (fun a b => ((hLaw.weil _ P _ _).1 _ _ (lab_pow (levelBasis_pow l hg) a)
        (lab_pow (levelBasis_pow l hg) b)).exists) a b
  have hσ : ∀ a b, labelSymp (σ a) (σ b) = labelSymp a b := fun a b => by
    have h := hw lev' a b
    rw [e, e] at h
    exact ZMod.val_injective _ (lev.prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      (CommutatorPairing.weilIs_unique hG P.isAb P.isLB (hw lev _ _) h))
  have hN' : ∀ a, N' • σ a = N' • a := fun a => inj (by
    have h := e a
    rw [levelPoint_eq_lab, levelPoint_eq_lab] at h
    rw [levelPoint_eq_lab, lab_nsmul hp, lab_nsmul hp, ← h]
    exact char_ext (fun a => lab (levelBasis lev' hg) a ^ N') (fun a => lab (levelBasis lev hg) a ^ N')
      (fun a b => by rw [lab_add hp', mul_pow]) (fun a b => by rw [lab_add hp, mul_pow])
      (fun i => by rw [lab_single hp', lab_single hp, hm]) a)
  have C := (theta_coordinates hLaw g N' 1 (N' ^ 2) N' rfl (Nat.one_mul _).symm).1 (Sp K) P hg ze
  obtain ⟨⟨th, t, hth, ht⟩, H⟩ := C lev v hv
  obtain ⟨H, hr⟩ := H th t hth ht
  have H' := ((C lev' v hv').2 th (fun a => t (σ a)) hth (by
    obtain ⟨s₁, α, U, hα, h₁, hU, h₂⟩ := ht
    exact ⟨s₁, α, fun a => U (σ a), hα, h₁, fun a => by beta_reduce; rw [e]; exact hU _, fun a => h₂ _⟩)).1 0
  replace H := H 0
  have z : ∀ l : Out.Level P (N' ^ 2) ze, levelPoint l hg 0 ^ N' = 1 := fun l => by
    rw [levelPoint_eq_lab, lab_zero, one_pow]
  rw [z] at H H'
  obtain ⟨τ, hτ⟩ := DVR.exists_gen_of_local P.L P.isLB (K := Fin 1)
    (fun _ => (1 : Out.baseOver (Sp K) ⟶ P.A).left) (fun _ => ((N' ^ 2 : ℕ) : ℤ))
  obtain ⟨u, hu⟩ := H τ hτ
  obtain ⟨u', hu'⟩ := H' τ hτ
  have z₁ : ∀ a : Fin (2 * g) → ZMod (N' ^ 2), thetaCoordExp N' 1 a 0 = 0 := fun a => by
    simp [thetaCoordExp, labelSymp]
  have z₂ : ∀ a : Fin (2 * g) → ZMod (N' ^ 2), thetaCoordIdx N' 1 a 0 = a := fun a => by
    simp [thetaCoordIdx]
  simp only [z₁, z₂, pow_zero, _root_.mul_one] at hu hu'
  have : IsDomain Γ((Out.baseOver (Sp K)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := eq_of_proportional (R := Γ((Out.baseOver (Sp K)).left, ⊤)) hn hN (ζ := ze) lev.prim σ hσ hN' v u u'
    (fun a => (value_eq_mul P.isLB (one_smul _ _).symm (hu (σ a)) (hu' a)).trans (_root_.one_mul _))
    (fun a b => (Units.mul_right_inj u).1
      ((value_eq_mul P.isLB (hr a b) (hu a) (hu _)).trans (mul_left_comm _ _ _))) hs
  intro i
  have h := e (Pi.single i 1)
  rw [key, levelPoint_eq_lab, levelPoint_eq_lab, lab_single hp', lab_single hp] at h
  exact h.symm

end GlobalTheory
