import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

open GlobalTheory.PullPair LBGerm GlobalTheory.AbLaw

def chartPullTwJ {X₁ X₂ : Scheme.{0}} (M₁ : LB X₁) (M₂ : LB X₂) (f : X₁ ⟶ X₂) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t) (𝟙 X₁) where
  idx J := (fun _ => J 0, fun _ => (J 1).1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0,
    Set.mem_iInter.2 fun _ => ((isPart_inl M₁ M₂).mem _ _).1 (Set.mem_iInter.1 hy 1)⟩
  g y J J' hJ hJ' := by
    have P := isPart_inl M₁ M₂
    have a₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ 1)
    have b₀ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ LB.wchart (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X₁ : X₁ ⟶ X₁) y ∈ powChart M₁ (fun _ => (J' 1).1) :=
      Set.mem_iInter.2 fun _ => (P.mem _ _).1 (Set.mem_iInter.1 hJ' 1)
    have hg := P.g _ (𝟙 X₁) y (J 1) (J' 1) ((P.mem _ _).1 (Set.mem_iInter.1 hJ 1)) ((P.mem _ _).1 (Set.mem_iInter.1 hJ' 1))
    refine (gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e)) (lbPow M₁ n) t y
      (fun _ => J 0, fun _ => (J 1).1) (fun _ => J' 0, fun _ => (J' 1).1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X₁) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb _ _ _ (𝟙 X₁) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp] at hg ⊢
    rw [hg]

theorem exists_sec_twist_join {X₁ X₂ : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} (h : IsAmpleLB M₁) (h₂ : M₂.IsLB)
    [Nonempty X₁] [Nonempty X₂] (f : X₁ ⟶ X₂) (e : ℤ) (k : ℕ) (hk : 1 ≤ k) (y : X₁) :
    ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb (join M₁ M₂) (K := Fin 2) ![f ≫ coprod.inr, coprod.inl] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  have hN := join_isLB hL h₂
  obtain ⟨m, hm, s, hs, -, ha⟩ := h.exists_affine_le (x := y) (U := ⊤) trivial
  obtain ⟨V, N, hV, H⟩ := TwistGen.exists_nhds
    (M := LB.LinComb (join M₁ M₂) (fun _ : PUnit => f ≫ coprod.inr) (fun _ => e))
    (LB.isLB_linComb hN _ _) (isLB_lbPow hL m) s ha y hs
  obtain ⟨d, hd⟩ : ∃ d, k * (N + 1) = N + d := Nat.exists_eq_add_of_le (by nlinarith)
  obtain ⟨u, hu⟩ := H d
  refine ⟨m * (N + 1), Nat.mul_pos hm (Nat.succ_pos N), ?_⟩
  rw [show k * (m * (N + 1)) = m * (N + d) by rw [← hd]; ring]
  refine ⟨chartSec (chartPullTwJ M₁ M₂ f e m (N + d)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id _ u fun x _ _ => exists_chart (LB.isLB_linComb hN _ _) x]
  exact hu hV

theorem exists_crossH : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧
      ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧
        ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) →
          (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  intro R _ _ A₁ A₂ F _ _ c hc j k hk
  have hL₁ := A₁.isLB
  have hL₂ := A₂.isLB
  let T : Over (Sp (FractionRing R)) := TFK (R := R) F
  have hsub : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let z₀ : T.left := (⊥ : PrimeSpectrum F)
  have P₁ := isPart_inl A₁.L A₂.L
  have P₂ := isPart_inr A₁.L A₂.L
  have hN := join_isLB hL₁ hL₂
  obtain ⟨n, hn, u, hu⟩ := exists_sec_twist_join (isAmpleLB_of_relAmple_of_isAffine A₁.A hL₁ A₁.ample) hL₂ c.left
    (-(j : ℤ)) k hk (((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀)
  have key : ∀ t : SecA A₂ F j, ∃ t' : SecA A₁ F (k * n), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A₁.A).left) (z : Z) (J),
      Good (join A₁.L A₂.L) z J →
        sA t' r z (rl J) = sA t (r ≫ (T ◁ c).left) z (rr J) * sval u (r ≫ (snd T A₁.A).left) z J := by
    intro t
    have e : (T ◁ c).left ≫ (snd T A₂.A).left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) =
        (snd T A₁.A).left ≫ c.left ≫ (coprod.inr : A₂.A.left ⟶ A₁.A.left ⨿ A₂.A.left) := by
      rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    let tN := P₂.sec (φ := fun _ : Fin 1 => (snd T A₂.A).left) (ε := fun _ => (j : ℤ)) t
    obtain ⟨s, hs⟩ := exists_sec hN (φ' := fun _ : Fin 1 => (snd T A₁.A).left ≫ coprod.inl)
      (ε' := fun _ => ((k * n : ℕ) : ℤ))
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
          Matrix.cons_val_zero, Matrix.cons_val_one, e, zpow_neg, mul_inv_cancel_left])
      (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec tN (T ◁ c).left) (H1.SectionArithmetic.pullSec u (snd T A₁.A).left))
    obtain ⟨t', ht'⟩ := P₁.exists_sec (φ := fun _ : Fin 1 => (snd T A₁.A).left) (ε := fun _ => ((k * n : ℕ) : ℤ)) hL₁
      (fst_surjective hL₂) s
    refine ⟨t', fun Z r z J hJ => (ht' Z r z J hJ).trans ((hs Z r z J hJ).trans ?_)⟩
    refine (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) ?_ (H1.SectionArithmetic.sval_pullSec _ _ r z hJ))
    exact (H1.SectionArithmetic.sval_pullSec _ _ r z hJ).trans (P₂.sval_sec _ _ z hJ)
  refine ⟨n, hn, fun t₁ t₂ => ?_⟩
  obtain ⟨t₁', h₁⟩ := key t₁
  obtain ⟨t₂', h₂⟩ := key t₂
  refine ⟨t₁', t₂', fun z J₁ J₂ g₁ g₂ => ?_, fun h z J₁ g₁ => ?_⟩
  · obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join hL₁ hL₂ g₁ g₂
    rw [h₁ _ _ z J hJ, h₂ _ _ z J hJ, Category.id_comp]
    ring
  · choose d hd using fun ψ : T.left ⟶ A₂.A.left => exists_chart hL₂ (ψ z)
    obtain ⟨J, hJ, rfl, hr⟩ := exists_good_join hL₁ hL₂ g₁ (J₂ := d) hd
    have e : (ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (T ◁ c).left = (ptSecT A₂.A (1 : T ⟶ A₂.A)).left := by
      rw [← Over.comp_left, ptSecT, ptSecT, lift_whiskerLeft, MonObj.one_comp]
    rw [h₂ _ _ z J hJ, e]
    obtain rfl : z₀ = z := Subsingleton.elim _ _
    have hU : IsUnit (sval u ((ptSecT A₁.A (1 : T ⟶ A₁.A)).left ≫ (snd T A₁.A).left) z₀ J) :=
      (mem_nonzeroLocus_iff_pull u _ z₀ (hJ.mem _ _)).1 hu
    have g₂ : Good A₂.L z₀ (rr J) := hr ▸ hd
    exact fun h0 => h z₀ (rr J) g₂ (hU.mul_left_eq_zero.1 h0)

end GlobalTheory.Mum.Two
