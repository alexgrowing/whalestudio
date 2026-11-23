import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordWeak
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacterStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TorsionValueNormEqThetaNormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionEvenBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Sup

section Pts
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem pow_iff_of_left {S' : Scheme.{0}} {b b' : S' ⟶ S} (h : b = b') (y : Over.mk b ⟶ G) (y' : Over.mk b' ⟶ G)
    (hl : y.left = y'.left) (m : ℕ) : y ^ m = 1 ↔ y' ^ m = 1 := by
  subst h
  have : y = y' := by ext1; exact hl
  rw [this]

variable (a : ArchFrame P z g)

theorem pt_over (w : Fin g → ℂ) : a.pt w ≫ G.hom = z := by
  have h1 := a.cart.1.w
  have h2 : (a.u.ex w).left ≫ a.A.hom = 𝟙 _ := Over.w (a.u.ex w)
  simp only [ArchFrame.pt, Category.assoc, h1]
  rw [reassoc_of% h2]

def lift (q : 𝟙_ (Over (Sp ℂ)) ⟶ a.A) : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ z) ⟶ G :=
  Over.homMk (q.left ≫ a.φ) (by
    have h1 := a.cart.1.w
    have h2 : q.left ≫ a.A.hom = 𝟙 _ := Over.w q
    simp only [Over.mk_left, Over.mk_hom, Category.assoc, h1]
    rw [reassoc_of% h2]
    rfl)

theorem lift_mul (q q' : 𝟙_ (Over (Sp ℂ)) ⟶ a.A) : lift a (q * q') = lift a q * lift a q' := by
  ext1
  exact (a.cart.2 _ q q' (lift a q) (lift a q') rfl rfl).symm

theorem lift_one : lift a 1 = 1 := by
  have h := lift_mul a 1 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem lift_pow (q : 𝟙_ (Over (Sp ℂ)) ⟶ a.A) (m : ℕ) : lift a (q ^ m) = lift a q ^ m := by
  induction m with
  | zero => simpa using lift_one a
  | succ n ih => rw [pow_succ, pow_succ, lift_mul, ih]

theorem lift_inj {q q' : 𝟙_ (Over (Sp ℂ)) ⟶ a.A} (h : (lift a q).left = (lift a q').left) : q = q' := by
  ext1
  refine a.cart.1.hom_ext h ?_
  have h2 : q.left ≫ a.A.hom = 𝟙 _ := Over.w q
  have h3 : q'.left ≫ a.A.hom = 𝟙 _ := Over.w q'
  rw [h2, h3]

theorem ex_nsmul (w : Fin g → ℂ) (m : ℕ) : a.u.ex ((m : ℂ) • w) = a.u.ex w ^ m := by
  have h0 : a.u.ex 0 = 1 := by
    have := a.u.ex_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  induction m with
  | zero => simpa using h0
  | succ n ih =>
    have : (((n + 1 : ℕ) : ℂ)) • w = (n : ℂ) • w + w := by
      push_cast; rw [add_smul, one_smul]
    rw [this, a.u.ex_add, ih, pow_succ]

theorem exists_pt (y : Over.mk z ⟶ G) : ∃ w, y.left = a.pt w := by
  have hw : y.left ≫ G.hom = 𝟙 _ ≫ z := by
    have : y.left ≫ G.hom = z := Over.w y
    simpa using this
  let q₀ := a.cart.1.lift y.left (𝟙 _) hw
  have h1 : q₀ ≫ a.φ = y.left := a.cart.1.lift_fst _ _ _
  have h2 : q₀ ≫ a.A.hom = 𝟙 _ := a.cart.1.lift_snd _ _ _
  let q : 𝟙_ (Over (Sp ℂ)) ⟶ a.A := Over.homMk q₀ h2
  obtain ⟨w, hw⟩ := a.u.ex_onto q
  exact ⟨w, by simp only [ArchFrame.pt, hw]; exact h1.symm⟩

theorem pt_eq_iff (w w' : Fin g → ℂ) : a.pt w = a.pt w' ↔ w - w' ∈ a.u.Λ := by
  have hadd : a.u.ex w = a.u.ex (w - w') * a.u.ex w' := by
    rw [← a.u.ex_add, sub_add_cancel]
  constructor
  · intro h
    have : a.u.ex w = a.u.ex w' := lift_inj a h
    rw [← a.u.ker]
    rw [this] at hadd
    exact (mul_eq_right.mp hadd.symm)
  · intro h
    have : a.u.ex (w - w') = 1 := (a.u.ker _).2 h
    rw [this, _root_.one_mul] at hadd
    simp only [ArchFrame.pt, hadd]

theorem pow_eq_one_iff (y : Over.mk z ⟶ G) (w : Fin g → ℂ) (h : y.left = a.pt w) (m : ℕ) :
    y ^ m = 1 ↔ (m : ℂ) • w ∈ a.u.Λ := by
  have hz : (𝟙_ (Over (Sp ℂ))).hom ≫ z = z := Category.id_comp z
  rw [pow_iff_of_left hz.symm y (lift a (a.u.ex w)) h m, ← lift_pow, ← a.u.ker, ex_nsmul]
  constructor
  · intro h1
    rw [← lift_one a] at h1
    exact lift_inj a (congrArg (fun t => t.left) h1)
  · intro h1
    rw [h1, lift_one]

end Pts

section Numbers

theorem sum_log_norm_nonneg (K : Type) [Field K] [NumberField K] (T : K) (hT : IsIntegral ℤ T) (h0 : T ≠ 0) :
    0 ≤ ∑ τ : K →+* ℂ, Real.log ‖τ T‖ := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ T) := Algebra.isIntegral_norm ℚ hT
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hn0 : Algebra.norm ℚ T ≠ 0 := Algebra.norm_ne_zero_iff.mpr h0
  have hnz : n ≠ 0 := by
    rintro rfl
    apply hn0
    rw [← hn]; simp
  have hp : ((n : ℤ) : ℂ) = ∏ τ : K →+* ℂ, τ T := by
    have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ T
    rw [← hn] at h1
    have h2 : ∏ σ : K →ₐ[ℚ] ℂ, σ T = ∏ τ : K →+* ℂ, τ T :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ (fun _ => rfl)
    rw [← h2, ← h1]
    simp
  rw [← Real.log_prod (fun τ _ => by simpa using h0), ← norm_prod, ← hp]
  apply Real.log_nonneg
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hnz

open Classical in
theorem card_ext (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K] (σ : L →+* ℂ) :
    Fintype.card {τ : K →+* ℂ // τ.comp (algebraMap L K) = σ} = Module.finrank L K := by
  letI : Algebra L ℂ := σ.toAlgebra
  haveI : FiniteDimensional L K := Module.Finite.of_restrictScalars_finite ℚ L K
  rw [← AlgHom.card_of_splits L K ℂ (fun x => IsAlgClosed.splits _)]
  refine Fintype.card_congr
    { toFun := fun t => { t.1 with commutes' := fun r => congrArg (fun f : L →+* ℂ => f r) t.2 }
      invFun := fun φ => ⟨φ.toRingHom, φ.comp_algebraMap⟩
      left_inv := fun t => by ext; rfl
      right_inv := fun φ => by ext; rfl }

open Classical in
theorem sum_comp_algebraMap (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
    (F : (L →+* ℂ) → ℝ) :
    ∑ τ : K →+* ℂ, F (τ.comp (algebraMap L K)) = Module.finrank L K * ∑ σ, F σ := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : K →+* ℂ => τ.comp (algebraMap L K)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ τ ∈ Finset.univ.filter (fun τ : K →+* ℂ => τ.comp (algebraMap L K) = σ),
      F (τ.comp (algebraMap L K)) = F σ := by
    intro τ hτ
    rw [(Finset.mem_filter.mp hτ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← card_ext L K σ, Fintype.card_subtype]

end Numbers

section Mean

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem tors_transport {P : RigLB G} {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b b' : Sp F ⟶ S} (h : b = b')
    (y : Over.mk b ⟶ G) : ∃ y' : Over.mk b' ⟶ G, y'.left = y.left ∧
      (∀ N T, TorsVal P s y N T → TorsVal P s y' N T) ∧ ∀ m : ℕ, y ^ m = 1 → y' ^ m = 1 := by
  subst h
  exact ⟨y, rfl, fun _ _ h => h, fun _ h => h⟩

theorem nrm_pos_iff {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : 0 < a.nrm n θ w ↔ θ w ≠ 0 := by
  unfold ArchFrame.nrm
  constructor
  · intro h h0
    rw [h0] at h
    simp at h
  · intro h
    exact mul_pos (norm_pos_iff.mpr h) (Real.exp_pos _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem tors_mean (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (f : ∀ σ, D.Frame σ)
    (θ : (L →+* ℂ) → (Fin D.g → ℂ) → ℂ) (hθ : ∀ σ, (f σ).IsFn th (θ σ)) (b c : (L →+* ℂ) → ℝ)
    (hb : ∀ σ, 0 < b σ)
    (h : ∀ σ, ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin D.g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ (f σ).u.Λ ∧ θ σ (r i) ≠ 0) →
      (∀ w : Fin D.g → ℂ, (m : ℂ) • w ∈ (f σ).u.Λ → θ σ w ≠ 0 → ∃! i, w - r i ∈ (f σ).u.Λ) →
      Nonempty Ix ∧ (Fintype.card Ix : ℝ) * c σ ≤ ∑ i, -Real.log ((f σ).nrm 1 (θ σ) (r i) / b σ)) :
    ∑ σ, c σ ≤ ∑ σ, Real.log (b σ) := by
  obtain ⟨m, hmall, hm1⟩ := ((Filter.eventually_all.2 h).and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨K, _, _, _, x, hx, hu⟩ := GlobalTheory.T.exists_full_torsion_number_field E H L D m hm1
  have hT0 := fun i => (GlobalTheory.T.torsion_value_unique_base_change E H L D 1 th K _ (x i) m hm1 (hx i))
  choose T hT using fun i => (hT0 i).1.exists
  have hTint := fun i => GlobalTheory.T.torsion_value_integral E H L D th K _ (x i) m (T i) (hT i)
  let res : (K →+* ℂ) → (L →+* ℂ) := fun τ => τ.comp (algebraMap L K)
  have hemb : ∀ τ : K →+* ℂ, spMap τ ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) = emb (res τ) := by
    intro τ
    simp only [emb, res, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hpt : ∀ (τ : K →+* ℂ) i, ∃ y : Over.mk (emb (res τ)) ⟶ D.t.G, y.left = spMap τ ≫ (x i).left ∧ y ^ m = 1 ∧
      TorsVal D.t.PP th y m (τ (T i)) := by
    intro τ i
    let p : Over.mk (spMap τ ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶
        Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) := Over.homMk (spMap τ) rfl
    have h1 : TorsVal D.t.PP th (p ≫ x i) m (τ (T i)) := (hT0 i).2 ℂ τ _ (T i) rfl (hT i)
    have h2 : (p ≫ x i) ^ m = 1 := by
      rw [← comp_pow, hx i, comp_one]
    obtain ⟨y, hl, hv, hp⟩ := tors_transport th (hemb τ) (p ≫ x i)
    exact ⟨y, hl, hp m h2, hv _ _ h1⟩
  choose y hyl hy1 hyT using hpt
  have hex := fun τ i => exists_pt (f (res τ)) (y τ i)
  choose r hr using hex
  have hnorm : ∀ (τ : K →+* ℂ) (i) (w : Fin D.g → ℂ), (y τ i).left = (f (res τ)).pt w →
      ‖τ (T i)‖ = (f (res τ)).nrm 1 (θ (res τ)) w ^ (m ^ 2) := fun τ i w hw =>
    GlobalTheory.T.torsion_value_norm_eq_theta_norm E H L D (res τ) (f _) 1 th (θ _) (y τ i) w m (τ (T i)) (hθ _) hw (hyT τ i)
  have hm2 : m ^ 2 ≠ 0 := by positivity
  have hne : ∀ (τ : K →+* ℂ) (i) (w : Fin D.g → ℂ), (y τ i).left = (f (res τ)).pt w →
      (T i ≠ 0 ↔ θ (res τ) w ≠ 0) := by
    intro τ i w hw
    have h1 := hnorm τ i w hw
    rw [← nrm_pos_iff (f (res τ)) 1]
    have h0 : 0 ≤ (f (res τ)).nrm 1 (θ (res τ)) w :=
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    constructor
    · intro hT
      have : 0 < ‖τ (T i)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hT)
      rw [h1] at this
      rcases h0.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_pow hm2] at this
        exact absurd this (lt_irrefl _)
    · intro hp hT
      rw [hT, map_zero, norm_zero] at h1
      exact absurd h1.symm (pow_pos hp _).ne'
  classical
  let Ix : Type := {i // T i ≠ 0}
  letI : Fintype Ix := (inferInstance : Fintype {i // T i ≠ 0})
  have hkey : ∀ τ : K →+* ℂ, Nonempty Ix ∧ (Fintype.card Ix : ℝ) * c (res τ) ≤
      ∑ i : Ix, -Real.log ((f (res τ)).nrm 1 (θ (res τ)) (r τ i.1) / b (res τ)) := by
    intro τ
    refine hmall (res τ) Ix (fun i => r τ i.1) (fun i => ⟨?_, ?_⟩) ?_
    · exact (pow_eq_one_iff (f (res τ)) (y τ i.1) (r τ i.1) (hr τ i.1) m).1 (hy1 τ i.1)
    · exact (hne τ i.1 _ (hr τ i.1)).1 i.2
    · intro w hw hθw
      let yw : Over.mk (emb (res τ)) ⟶ D.t.G := Over.homMk ((f (res τ)).pt w) (pt_over (f (res τ)) w)
      have hyw : yw ^ m = 1 := (pow_eq_one_iff (f (res τ)) yw w rfl m).2 hw
      obtain ⟨i, hi, huniq⟩ := hu ℂ τ (emb (res τ)) yw (hemb τ).symm hyw
      have hi' : (y τ i).left = (f (res τ)).pt w := by rw [hyl]; exact hi.symm
      refine ⟨⟨i, (hne τ i w hi').2 hθw⟩, ?_, ?_⟩
      · exact (pt_eq_iff (f (res τ)) w (r τ i)).1 (hi'.symm.trans (hr τ i))
      · intro j hj
        have h3 := (pt_eq_iff (f (res τ)) w (r τ j.1)).2 hj
        apply Subtype.ext
        apply huniq
        change (f (res τ)).pt w = _
        rw [h3, ← hr τ j.1, hyl]
  have hτ : Nonempty (K →+* ℂ) := Fintype.card_pos_iff.1 (by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
  obtain ⟨τ₀⟩ := hτ
  haveI hIx : Nonempty Ix := (hkey τ₀).1
  have hcard : (0 : ℝ) < Fintype.card Ix := by exact_mod_cast Fintype.card_pos
  have hmr : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm1
    positivity

  have hlog : ∀ (τ : K →+* ℂ) (i : Ix),
      (m : ℝ) ^ 2 * -Real.log ((f (res τ)).nrm 1 (θ (res τ)) (r τ i.1) / b (res τ)) =
        -Real.log ‖τ (T i.1)‖ + (m : ℝ) ^ 2 * Real.log (b (res τ)) := by
    intro τ i
    have hp : 0 < (f (res τ)).nrm 1 (θ (res τ)) (r τ i.1) :=
      (nrm_pos_iff _ 1 _ _).2 ((hne τ i.1 _ (hr τ i.1)).1 i.2)
    rw [hnorm τ i.1 _ (hr τ i.1), Real.log_div hp.ne' (hb _).ne', Real.log_pow]
    push_cast
    ring
  have hsum : ∑ τ : K →+* ℂ, (Fintype.card Ix : ℝ) * ((m : ℝ) ^ 2 * c (res τ)) ≤
      ∑ τ : K →+* ℂ, ∑ i : Ix, (-Real.log ‖τ (T i.1)‖ + (m : ℝ) ^ 2 * Real.log (b (res τ))) := by
    refine Finset.sum_le_sum fun τ _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hkey τ).2 hmr.le
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hlog τ i)] at h1
    calc _ = (m : ℝ) ^ 2 * ((Fintype.card Ix : ℝ) * c (res τ)) := by ring
      _ ≤ _ := h1
  have hprod : ∑ τ : K →+* ℂ, ∑ i : Ix, (-Real.log ‖τ (T i.1)‖ + (m : ℝ) ^ 2 * Real.log (b (res τ))) ≤
      ∑ τ : K →+* ℂ, (Fintype.card Ix : ℝ) * ((m : ℝ) ^ 2 * Real.log (b (res τ))) := by
    have h1 : ∑ τ : K →+* ℂ, ∑ i : Ix, (-Real.log ‖τ (T i.1)‖ + (m : ℝ) ^ 2 * Real.log (b (res τ))) =
        -∑ i : Ix, ∑ τ : K →+* ℂ, Real.log ‖τ (T i.1)‖ +
          ∑ τ : K →+* ℂ, (Fintype.card Ix : ℝ) * ((m : ℝ) ^ 2 * Real.log (b (res τ))) := by
      rw [Finset.sum_comm (f := fun (i : Ix) (τ : K →+* ℂ) => Real.log ‖τ (T i.1)‖), ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [h1]
    have h2 : 0 ≤ ∑ i : Ix, ∑ τ : K →+* ℂ, Real.log ‖τ (T i.1)‖ :=
      Finset.sum_nonneg fun i _ => sum_log_norm_nonneg K (T i.1) (hTint i.1) i.2
    linarith
  have hfin := hsum.trans hprod
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hfin
  have hfin2 := le_of_mul_le_mul_left (le_of_mul_le_mul_left hfin hcard) hmr
  have e1 := sum_comp_algebraMap L K c
  have e2 := sum_comp_algebraMap L K (fun σ => Real.log (b σ))
  have hfin3 : (Module.finrank L K : ℝ) * ∑ σ, c σ ≤ (Module.finrank L K : ℝ) * ∑ σ, Real.log (b σ) := by
    rw [← e1, ← e2]; exact hfin2
  haveI : FiniteDimensional L K := Module.Finite.of_restrictScalars_finite ℚ L K
  have hd : (0 : ℝ) < Module.finrank L K := by exact_mod_cast Module.finrank_pos
  exact le_of_mul_le_mul_left hfin3 hd

end Mean

section Real

def Ef (g : ℕ) (C₀ ρ : ℝ) : ℝ := g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g)

theorem Ef_nonneg {g : ℕ} (hg : 1 ≤ g) {C₀ ρ : ℝ} (hC₀ : 0 ≤ C₀) (hρ : 0 < ρ) : 0 ≤ Ef g C₀ ρ := by
  have h1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h2 : 0 ≤ Real.log (1 + 1 / ρ) := Real.log_nonneg (by
    have : 0 < 1 / ρ := by positivity
    linarith)
  have h3 : 0 ≤ Real.log (2 * g) := Real.log_nonneg (by linarith)
  unfold Ef
  positivity

theorem Ef_le {g : ℕ} (C₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Ef g C₀ ρ ≤ (Real.pi / 96 * (ρ ^ 2)⁻¹ - Ef g C₀ ρ) +
      (2 * (C₀ * g * Real.log (2 * g)) + 96 / Real.pi * (g : ℝ) ^ 2) := by
  have hpi := Real.pi_pos
  set t : ℝ := 1 / ρ with ht
  have ht0 : 0 < t := by positivity
  have hl : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
    linarith
  have hsq : (ρ ^ 2)⁻¹ = t ^ 2 := by rw [ht]; field_simp
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have key : 2 * (g : ℝ) * t ≤ Real.pi / 96 * t ^ 2 + 96 / Real.pi * (g : ℝ) ^ 2 := by
    have h : 0 ≤ (Real.pi / 96 * t - g) ^ 2 * (96 / Real.pi) := by positivity
    have e : (Real.pi / 96 * t - g) ^ 2 * (96 / Real.pi) =
        Real.pi / 96 * t ^ 2 + 96 / Real.pi * (g : ℝ) ^ 2 - 2 * g * t := by
      field_simp
      ring
    linarith
  have h2 : 2 * (g : ℝ) * Real.log (1 + t) ≤ 2 * g * t := by
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  rw [hsq]
  unfold Ef
  rw [← ht]
  linarith

theorem final_bound (C₀ C : ℝ) (hC₀ : 0 ≤ C₀) (hC : 0 < C) : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (g : ℕ) (Φ : ℝ), 1 ≤ g → 0 ≤ Φ →
    (g : ℝ) * (Real.log 2 + 1 / 2 * Real.log (1 + C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)))) +
      C₀ * g * Real.log (2 * g) + 1 ≤ C' * g * Real.log (2 + g + Φ) := by
  have hB : 0 ≤ Real.log (1 + 3 * C) := Real.log_nonneg (by linarith)
  refine ⟨1 + 1 / 2 * (Real.log (1 + 3 * C) + 3) + 2 * C₀ + 1, by positivity, ?_⟩
  intro g Φ hg hΦ
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  set x : ℝ := 2 + g + Φ with hx
  have hx3 : 3 ≤ x := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  set Λ : ℝ := Real.log x with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : Real.log 2 ≤ Λ := Real.log_le_log (by norm_num) (by linarith)
  have h2g0 : 0 ≤ Real.log (2 * g) := Real.log_nonneg (by linarith)
  have h2g : Real.log (2 * g) ≤ 2 * Λ := by
    have : Real.log (2 * g) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) (by
      have : (g : ℝ) ≤ x := by rw [hx]; linarith
      nlinarith)
    rwa [Real.log_pow] at this
  have h2g' : Real.log (2 * g) ≤ 2 * x := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * g by linarith)
    have h : (g : ℝ) ≤ x := by rw [hx]; linarith
    linarith
  have hgx : (g : ℝ) ≤ x := by rw [hx]; linarith
  have hΦx : Φ ≤ x := by rw [hx]; linarith
  have hx1 : x ≤ x ^ 3 := by nlinarith [mul_self_nonneg (x - 1), sq_nonneg x]
  have hx3' : 1 ≤ x ^ 3 := by linarith
  have hgg : (g : ℝ) ^ 2 * Real.log (2 * g) ≤ 2 * x ^ 3 := by
    have h1 : (g : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
    calc (g : ℝ) ^ 2 * Real.log (2 * g) ≤ x ^ 2 * (2 * x) := by gcongr
      _ = 2 * x ^ 3 := by ring
  have hin : 1 + C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ≤ (1 + 3 * C) * x ^ 3 := by
    have : C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ≤ C * (3 * x ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    nlinarith
  have hpos : 0 < 1 + C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) := by positivity
  have hlog : Real.log (1 + C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g))) ≤ (Real.log (1 + 3 * C) + 3) * Λ := by
    have h1 := Real.log_le_log hpos hin
    have e : Real.log ((1 + 3 * C) * x ^ 3) = Real.log (1 + 3 * C) + 3 * Λ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      rfl
    rw [e] at h1
    nlinarith
  have hgΛ : 1 ≤ (g : ℝ) * Λ := by nlinarith
  have e1 : (g : ℝ) * (Real.log 2 + 1 / 2 * Real.log (1 + C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)))) ≤
      (g : ℝ) * (Λ + 1 / 2 * ((Real.log (1 + 3 * C) + 3) * Λ)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have e2 : C₀ * g * Real.log (2 * g) ≤ C₀ * g * (2 * Λ) := by
    apply mul_le_mul_of_nonneg_left h2g (by positivity)
  have : (1 + 1 / 2 * (Real.log (1 + 3 * C) + 3) + 2 * C₀ + 1) * g * Λ =
      (g : ℝ) * (Λ + 1 / 2 * ((Real.log (1 + 3 * C) + 3) * Λ)) + C₀ * g * (2 * Λ) + (g : ℝ) * Λ := by ring
  rw [this]
  linarith

theorem log_one_add_le (t : ℝ) (ht : 0 < t) : Real.log (1 + t) ≤ Real.log 2 + Real.posLog t := by
  have h1 : Real.log (1 + t) ≤ Real.posLog (1 + t) := by
    rw [Real.posLog]; exact le_max_right _ _
  have h2 := Real.posLog_add (x := 1) (y := t)
  simp only [Real.posLog_one, add_zero] at h2
  linarith

end Real

section Main

variable {L : Type} [Field L] [NumberField L]

theorem card_emb : (Fintype.card (L →+* ℂ) : ℝ) = Module.finrank ℚ L := by
  rw [NumberField.Embeddings.card]

theorem mean_eq (f : (L →+* ℂ) → ℝ) : mean L f = finMean f := by
  rw [mean, finMean, card_emb]

theorem finrank_pos' : (0 : ℝ) < Module.finrank ℚ L := by
  exact_mod_cast Module.finrank_pos

theorem mean_add (f h : (L →+* ℂ) → ℝ) : mean L (fun σ => f σ + h σ) = mean L f + mean L h := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul (c : ℝ) (f : (L →+* ℂ) → ℝ) : mean L (fun σ => c * f σ) = c * mean L f := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_const (c : ℝ) : mean L (fun _ => c) = c := by
  have h := finrank_pos' (L := L)
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_emb]
  field_simp

theorem mean_mono {f h : (L →+* ℂ) → ℝ} (hfh : ∀ σ, f σ ≤ h σ) : mean L f ≤ mean L h := by
  have hp := finrank_pos' (L := L)
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => hfh σ) hp.le

end Main

theorem mean_log_sup : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ), 1 ≤ D.g → 0 ≤ Φ → D.HasTheta th Φ →
    ∃ M : (L →+* ℂ) → ℝ, (∀ σ, 0 < M σ) ∧ D.SupLe th M ∧
      mean L (fun σ => Real.log (M σ)) ≤ Φ + C * D.g * Real.log (2 + D.g + Φ) := by
  obtain ⟨C₀, hC₀, hN⟩ := GlobalTheory.T.theta_function_even_bound
  obtain ⟨C, hC, hW⟩ := WeakMatrixArithmetic.intersectionNumber_baseChange C₀ hC₀
  obtain ⟨C', hC', hF⟩ := final_bound C₀ C hC₀ hC
  refine ⟨C', hC', ?_⟩
  intro E _ _ _ H L _ _ D th Φ hg hΦ hth
  obtain ⟨b, hb, hmean⟩ := hth
  have hfr := GlobalTheory.T.theta_function_archimedean_frame E H L D
  have hun := GlobalTheory.T.theta_multiplier_quadratic_character E H L D
  have hdata : ∀ (σ : L →+* ℂ) (a : D.Frame σ), ∃ (θ : (Fin D.g → ℂ) → ℂ) (ρ : ℝ), a.IsFn th θ ∧ 0 < ρ ∧
      ρ ≤ √(2 * D.g) ∧ 0 < b σ ∧ (∀ w, a.nrm 1 θ w ≤ b σ * Real.exp (Ef D.g C₀ ρ)) ∧
      ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin D.g → ℂ),
        (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) →
        (∀ w : Fin D.g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) →
        Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - Ef D.g C₀ ρ) ≤
          ∑ i, -Real.log (a.nrm 1 θ (r i) / b σ) := by
    intro σ a
    obtain ⟨θ, hθ, -⟩ := ((hfr σ).2 a).1 1 th
    have hT := ((hfr σ).2 a).2.1 1 th θ hθ
    have hL := hb σ a θ hθ
    obtain ⟨u1, u2, u3, u4⟩ := hun σ a
    obtain ⟨ρ, h0, h1, h2, h3⟩ := hN a hg u1 u2 u3 u4 θ (b σ) hT hL
    exact ⟨θ, ρ, hθ, h0, h1, hL.1, h2, h3⟩
  choose θ ρ hfn hρ0 hρ1 hbp hsup hev using hdata
  have hfr0 : ∀ σ, Nonempty (D.Frame σ) := fun σ => (hfr σ).1
  let f₀ : ∀ σ, D.Frame σ := fun σ => (hfr0 σ).some
  have hbpos : ∀ σ, 0 < b σ := fun σ => hbp σ (f₀ σ)
  let φ : ℝ → ℝ := fun r => Real.pi / 96 * (r ^ 2)⁻¹ - Ef D.g C₀ r
  have hQ : ∀ f : ∀ σ, D.Frame σ, ∑ σ, φ (ρ σ (f σ)) ≤ ∑ σ, Real.log (b σ) := fun f =>
    tors_mean D th f (fun σ => θ σ (f σ)) (fun σ => hfn σ (f σ)) b (fun σ => φ (ρ σ (f σ))) hbpos
      (fun σ => hev σ (f σ))
  let K₁ : ℝ := 2 * (C₀ * D.g * Real.log (2 * D.g)) + 96 / Real.pi * (D.g : ℝ) ^ 2
  have hφ : ∀ r, 0 < r → Ef D.g C₀ r ≤ φ r + K₁ := fun r hr => Ef_le C₀ hr
  have hφ0 : ∀ r, 0 < r → 0 ≤ φ r + K₁ := fun r hr => (Ef_nonneg hg hC₀ hr).trans (hφ r hr)
  have hbdd : ∀ σ₀, BddAbove (Set.range fun a : D.Frame σ₀ => Ef D.g C₀ (ρ σ₀ a)) := by
    intro σ₀
    classical
    refine ⟨∑ σ, Real.log (b σ) + ∑ _σ : L →+* ℂ, K₁, ?_⟩
    rintro _ ⟨a, rfl⟩
    let f : ∀ σ, D.Frame σ := Function.update f₀ σ₀ a
    have h1 := hQ f
    have h2 : φ (ρ σ₀ (f σ₀)) + K₁ ≤ ∑ σ, (φ (ρ σ (f σ)) + K₁) :=
      Finset.single_le_sum (f := fun σ => φ (ρ σ (f σ)) + K₁) (fun σ _ => hφ0 _ (hρ0 σ (f σ))) (Finset.mem_univ σ₀)
    rw [Finset.sum_add_distrib] at h2
    have h3 : f σ₀ = a := Function.update_self ..
    rw [h3] at h2
    have h4 := hφ _ (hρ0 σ₀ a)
    simp only at h4 ⊢
    linarith
  let e : (L →+* ℂ) → ℝ := fun σ => sSup (Set.range fun a : D.Frame σ => Ef D.g C₀ (ρ σ a))
  have hle : ∀ σ (a : D.Frame σ), Ef D.g C₀ (ρ σ a) ≤ e σ := fun σ a => le_csSup (hbdd σ) ⟨a, rfl⟩
  have hnear : ∀ σ, ∃ a : D.Frame σ, e σ - 1 < Ef D.g C₀ (ρ σ a) := by
    intro σ
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) (show e σ - 1 < e σ by linarith)
    exact ⟨a, h⟩
  choose f hf using hnear
  let r : (L →+* ℂ) → ℝ := fun σ => ρ σ (f σ)
  have hr0 : ∀ σ, 0 < r σ := fun σ => hρ0 σ (f σ)
  refine ⟨fun σ => b σ * Real.exp (e σ), fun σ => mul_pos (hbpos σ) (Real.exp_pos _), ?_, ?_⟩
  · intro σ a θ' hθ' w
    obtain ⟨_, -, hu⟩ := ((hfr σ).2 a).1 1 th
    have hth' : θ' = θ σ a := by
      rw [hu θ' hθ', hu _ (hfn σ a)]
    rw [hth']
    refine (hsup σ a w).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hle σ a)) (hbpos σ).le
  · haveI : NeZero D.g := ⟨by omega⟩
    haveI : Nonempty (L →+* ℂ) := Fintype.card_pos_iff.1 (by
      rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
    have hm1 : finMean (fun σ => Real.pi / 96 * (r σ ^ 2)⁻¹ -
        ((D.g : ℝ) * Real.log (1 + 1 / r σ) + C₀ * D.g * Real.log (2 * D.g))) ≤ Φ := by
      rw [← mean_eq]
      refine le_trans ?_ hmean
      exact div_le_div_of_nonneg_right (hQ f) (finrank_pos' (L := L)).le
    obtain ⟨w1, -, w3⟩ := hW D.g (L →+* ℂ) r Φ (fun σ => ⟨hr0 σ, hρ1 σ (f σ)⟩) hΦ hm1
    have hnn : 0 ≤ finMean (fun σ => (r σ ^ 2)⁻¹) := by
      rw [← mean_eq]
      exact div_nonneg (Finset.sum_nonneg fun σ _ => by have := hr0 σ; positivity) (finrank_pos' (L := L)).le
    have hA : mean L (fun σ => Real.log (1 + 1 / r σ)) ≤
        Real.log 2 + 1 / 2 * Real.log (1 + C * (Φ + (D.g : ℝ) ^ 2 * Real.log (2 * D.g))) := by
      have h1 : mean L (fun σ => Real.log (1 + 1 / r σ)) ≤ mean L (fun σ => Real.log 2 + Real.posLog (1 / r σ)) :=
        mean_mono fun σ => log_one_add_le _ (by have := hr0 σ; positivity)
      rw [mean_add, mean_const, mean_eq (fun σ => Real.posLog (1 / r σ))] at h1
      have h2 : Real.log (1 + finMean (fun σ => (r σ ^ 2)⁻¹)) ≤
          Real.log (1 + C * (Φ + (D.g : ℝ) ^ 2 * Real.log (2 * D.g))) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hlogM : ∀ σ, Real.log (b σ * Real.exp (e σ)) ≤ Real.log (b σ) +
        ((D.g : ℝ) * Real.log (1 + 1 / r σ) + (C₀ * D.g * Real.log (2 * D.g) + 1)) := by
      intro σ
      rw [Real.log_mul (hbpos σ).ne' (Real.exp_pos _).ne', Real.log_exp]
      have := hf σ
      simp only [Ef] at this
      change _ < (D.g : ℝ) * Real.log (1 + 1 / r σ) + _ at this
      linarith
    have hfin := mean_mono hlogM
    rw [mean_add, mean_add, mean_const, mean_mul] at hfin
    have hg0 : (0 : ℝ) ≤ D.g := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hA hg0
    have hbm : mean L (fun σ => Real.log (b σ)) ≤ Φ := hmean
    have := hF D.g Φ hg hΦ
    linarith

end GlobalTheory.CompanionTheory.Ar.Sl.Sup
