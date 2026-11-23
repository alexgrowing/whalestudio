import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis

noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.Rep
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf invF zOfX tw mAt rank_eq kapOf kapOf_injective subst_lin hasSubst_invF)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.KerInert.Loc (resFam resFam_apply hasSubst_resFam resV_eq_subst)

section Gen

variable {σ τ : Type} {K : Type} [Field K]

theorem hasSubst_linFam [Finite σ] [Fintype τ] (A : σ → τ → K) :
    MvPowerSeries.HasSubst (fun x => ∑ y, MvPowerSeries.C (A x y) * MvPowerSeries.X y : σ → MvPowerSeries τ K) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp

theorem hasSubst_hypLin (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] {r : ℕ} (f f' : ι → Fin r → MaximalUnramifiedExtension l) :
    MvPowerSeries.HasSubst (hypLin l f f') :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp [hypLin]

end Gen

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

theorem kapOf_kapInv (j : ℕ) (y : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    kapOf X pos j (kapInv X pos j y) = y := by
  obtain ⟨t, b, a⟩ := y
  simp [kapOf, kapInv]

theorem thA_thFOf_linSub {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (S : ∀ j, X.Lt j → X.Lt (j + 1) → (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := Formalism.L2.G.Pend.algKfC E.toCEmb
    thA ℂ_[p] φ (thFOf X pos (fun j La La' => linSub (S j La La') (F j La La')) j L0 La') =
      MvPowerSeries.subst (linFrame X E pos φ (S j L0 La')) (F j L0 La') := by
  let _ := wittFractionAlgebraCp p
  let _ := Formalism.L2.G.Pend.algKfC E.toCEmb
  show MvPowerSeries.subst (invF ℂ_[p] φ) (Formalism.MainNotions.FormalGroupSystem.resV (kapOf X pos j) (linSub (S j L0 La') (F j L0 La'))) = _
  have hfam : (fun s => MvPowerSeries.subst (resFam (kapOf X pos j))
      (∑ y, MvPowerSeries.C (S j L0 La' s y) * MvPowerSeries.X y : MvPowerSeries _ ℂ_[p])) =
      fun s => ∑ y, MvPowerSeries.C (S j L0 La' s y) * (MvPowerSeries.X (kapInv X pos j y) : MvPowerSeries (X.ZA j) ℂ_[p]) := by
    funext s
    rw [subst_lin (hasSubst_resFam _)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h := resFam_apply (R := ℂ_[p]) (kapOf_injective X pos j) (kapInv X pos j y)
    rw [kapOf_kapInv] at h
    rw [MvPowerSeries.subst_X (hasSubst_resFam _), h]
  have hs2 : MvPowerSeries.HasSubst (fun s => ∑ y, MvPowerSeries.C (S j L0 La' s y) *
      (MvPowerSeries.X (kapInv X pos j y) : MvPowerSeries (X.ZA j) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  rw [resV_eq_subst (kapOf_injective X pos j), linSub,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_linFam _) (hasSubst_resFam _), hfam,
    MvPowerSeries.subst_comp_subst_apply hs2 (hasSubst_invF ℂ_[p] φ)]
  congr 1
  funext k
  rw [subst_lin (hasSubst_invF ℂ_[p] φ), linFrame]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MvPowerSeries.subst_X (hasSubst_invF ℂ_[p] φ)]

theorem subst_hypLin_thOrth (D : D7) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) {ι : Type} [Fintype ι] (f f' : ι → Fin r → MaximalUnramifiedExtension p)
    (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries.subst (hypLin p f f') (thOrth D lam c b G) =
      MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
        ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hypLin p f f' i) G := by
  rw [thOrth, MvPowerSeries.subst_comp_subst_apply (hasSubst_linFam _) (hasSubst_hypLin p f f')]
  congr 1
  funext k
  rw [subst_lin (hasSubst_hypLin p f f')]
  simp only [MvPowerSeries.subst_X (hasSubst_hypLin p f f')]

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameHyp_of_lin (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameLin X E hfin D pos' large₂ Lg' S lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHyp X E hfin D pos' large₂ Lg' F S lam c := by
  intro j L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j L0 hL0 La' hLa' φ
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, ?_⟩
  rw [thA_thFOf_linSub X E pos' φ S F, subst_hypLin_thOrth]
  congr 1
  funext k
  exact hk k

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi)

section Sums

variable {S : Type} [CommSemiring S] {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem sum4 (A : α → S) (B : β → S) (P : α → γ → S) (Q : β → δ → S) (z : γ → δ → S) :
    ∑ b, ∑ a, A a * B b * ∑ c, ∑ d, P a c * Q b d * z c d =
      ∑ c, ∑ d, (∑ a, A a * P a c) * (∑ b, Q b d * B b) * z c d := by
  calc ∑ b, ∑ a, A a * B b * ∑ c, ∑ d, P a c * Q b d * z c d
        = ∑ b, ∑ a, ∑ c, ∑ d, A a * B b * (P a c * Q b d * z c d) := by
          simp only [Finset.mul_sum]
    _ = ∑ b, ∑ c, ∑ d, ∑ a, A a * B b * (P a c * Q b d * z c d) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ b, ∑ a, A a * B b * (P a c * Q b d * z c d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, (∑ a, A a * P a c) * (∑ b, Q b d * B b) * z c d := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring

theorem sum4' (A : α → S) (B : β → S) (P : α → γ → S) (Q : β → δ → S) (z : γ → δ → S) :
    ∑ b, ∑ a, B b * A a * ∑ c, ∑ d, P a c * Q b d * z c d =
      ∑ c, ∑ d, (∑ b, B b * Q b d) * (∑ a, P a c * A a) * z c d := by
  have h := sum4 A B P Q z
  calc _ = ∑ b, ∑ a, A a * B b * ∑ c, ∑ d, P a c * Q b d * z c d :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm (B b)]
    _ = _ := h
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
        rw [mul_comm (∑ a, A a * P a c)]
        congr 2
        · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        · exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem sum_cast {n m : ℕ} (h : n = m) (g : Fin m → S) : ∑ a : Fin n, g (Fin.cast h a) = ∑ x, g x :=
  Fintype.sum_equiv (finCongr h) _ _ fun _ => rfl

end Sums

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

theorem mAt_cast (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ) (v : X.Pl)
    (s : Fin (X.G.P.n' v)) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (a a' : Fin ((X.Pj j).m + 1)) :
    mAt X Kc j v s A (Fin.cast (rank_eq X j) a) (Fin.cast (rank_eq X j) a') = A.map (tw X Kc v s) a a' := by
  simp [mAt]

theorem mAt_mul_left (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ) (v : X.Pl)
    (s : Fin (X.G.P.n' v)) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (a : Fin ((X.Pj j).m + 1)) (c : Fin (NN X.G.P.m X.t j)) :
    ∑ a', A.map (tw X Kc v s) a a' * mAt X Kc j v s B (Fin.cast (rank_eq X j) a') c =
      mAt X Kc j v s (A * B) (Fin.cast (rank_eq X j) a) c := by
  rw [← mAt_mul, Matrix.mul_apply, ← sum_cast (rank_eq X j)]
  simp only [mAt_cast]

theorem mAt_mul_right (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ) (v : X.Pl)
    (s : Fin (X.G.P.n' v)) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (a : Fin ((X.Pj j).m + 1)) (c : Fin (NN X.G.P.m X.t j)) :
    ∑ a', mAt X Kc j v s A c (Fin.cast (rank_eq X j) a') * B.map (tw X Kc v s) a' a =
      mAt X Kc j v s (A * B) c (Fin.cast (rank_eq X j) a) := by
  rw [← mAt_mul, Matrix.mul_apply, ← sum_cast (rank_eq X j)]
  simp only [mAt_cast]

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

theorem linFrame_subGen (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    linFrame X E pos φ (subGen X E pos M j L0 La') k = stdLin X E pos M φ k := by
  let _ := wittFractionAlgebraCp p
  let _ := Formalism.L2.G.Pend.algKfC E.toCEmb
  obtain ⟨t, bb, aa⟩ := k
  simp only [linFrame, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single t]
  rotate_left
  · intro t' _ ht'
    refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun a' _ => ?_
    simp [subGen, Ne.symm ht']
  · intro h
    exact absurd (Finset.mem_univ t) h
  simp only [subGen, if_true, kapInv, invF, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, map_mul]
  by_cases hodd : IsOddPos (pos.symm t).2
  · simp only [if_pos hodd, stdLin, Pi, Qi, Matrix.transpose_apply]
    refine Eq.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [map_mul])
      (Eq.trans (sum4 _ _ _ _ _) ?_)
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, ← mAt_mul_left, ← mAt_mul_right]
    simp only [map_sum, map_mul]
  · simp only [if_neg hodd, stdLin, Pi, Qi, Matrix.transpose_apply]
    refine Eq.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [map_mul])
      (Eq.trans (sum4' _ _ _ _ _) ?_)
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, ← mAt_mul_left, ← mAt_mul_right]
    simp only [map_sum, map_mul]

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.Rep
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameLin_of_std (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameStd X E hfin D pos large₂ Lg' M lam c) :
    FrameLin X E hfin D pos large₂ Lg' (fun j La La' => subGen X E pos M j La La') lam c := by
  intro j L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j L0 hL0 La' hLa' φ
  exact ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => (linFrame_subGen X E pos M φ k).trans (hk k)⟩

theorem frameHyp_of_std (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameStd X E hfin D pos large₂ Lg' M lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHyp X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam c :=
  frameHyp_of_lin X E hfin D pos large₂ Lg' _ lam c (frameLin_of_std X E hfin D pos large₂ Lg' M lam c h) F

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm zOfX lin_repr)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Lin

variable {σ : Type} [Fintype σ] {K : Type} [Field K]

def IsLin (L : MvPowerSeries σ K) : Prop := ∃ w : σ → K, L = ∑ y, MvPowerSeries.C (w y) * MvPowerSeries.X y

theorem isLin_X (y : σ) : IsLin (MvPowerSeries.X y : MvPowerSeries σ K) := by
  classical
  refine ⟨fun z => if z = y then 1 else 0, ?_⟩
  simp [ite_mul]

theorem isLin_C_mul (a : K) {L : MvPowerSeries σ K} (h : IsLin L) : IsLin (MvPowerSeries.C a * L) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨fun y => a * w y, by simp [Finset.mul_sum, mul_assoc]⟩

theorem isLin_sum {ι : Type} [Fintype ι] (L : ι → MvPowerSeries σ K) (h : ∀ i, IsLin (L i)) :
    IsLin (∑ i, L i) := by
  choose w hw using h
  refine ⟨fun y => ∑ i, w i y, ?_⟩
  simp only [hw, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem IsLin.repr {L : MvPowerSeries σ K} (h : IsLin L) :
    L = ∑ y, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single y 1) L) * MvPowerSeries.X y := by
  obtain ⟨w, rfl⟩ := h
  exact (lin_repr w id).symm

end Lin

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

theorem isLin_stdLin (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : IsLin (stdLin X E pos M φ k) := by
  let _ := Formalism.L2.G.Pend.wittFractionAlgebraCp p
  let _ := Formalism.L2.G.Pend.algKfC E.toCEmb
  have hz : ∀ z, IsLin (zOfX X ℂ_[p] j z) := by
    rintro ⟨v, s, a, b⟩
    simp only [zOfX]
    split_ifs
    · exact isLin_sum _ fun r => isLin_C_mul _ (isLin_X _)
    · exact isLin_sum _ fun r => isLin_C_mul _ (isLin_X _)
  unfold stdLin
  split_ifs
  · exact isLin_sum _ fun a => isLin_sum _ fun b => isLin_C_mul _ (hz _)
  · exact isLin_sum _ fun a => isLin_sum _ fun b => isLin_C_mul _ (hz _)

theorem coord_recon (D : D7) (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hL : LamONB D lam b) {c : ℂ_[p]} (hc0 : c ≠ 0) (V : D.what₂.Tau × Fin N' × Fin N → ℂ_[p])
    (k : D.what₂.Tau × Fin N' × Fin N) :
    ∑ i, c * lamB D lam b k i * (c⁻¹ * ∑ k', lamBc D lam b k' i * V k') = V k := by
  classical
  calc ∑ i, c * lamB D lam b k i * (c⁻¹ * ∑ k', lamBc D lam b k' i * V k')
        = ∑ i, lamB D lam b k i * ∑ k', lamBc D lam b k' i * V k' :=
          Finset.sum_congr rfl fun i _ => by
            rw [mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul]
    _ = ∑ k', (∑ i, lamB D lam b k i * lamBc D lam b k' i) * V k' := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = V k := by
          have hL' := hL k
          simp only [hL']
          simp [ite_mul]

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameStd_of (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (hc0 : c ≠ 0) (h1 : OnbEx X hfin D large₂ Lg')
    (h2 : LamTrace X hfin D large₂ Lg' lam) (h3 : HypCoord X E hfin D pos' large₂ Lg' M lam c) :
    FrameStd X E hfin D pos' large₂ Lg' M lam c := by
  intro j L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho⟩ := h1 j L0 hL0 La' hLa'
  obtain ⟨σ, f, f', hσ, hH, hf, hf'⟩ := h3 j L0 hL0 La' hLa' r b hb ho φ
  have hL := h2 j L0 hL0 La' hLa' r b hb ho
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => ?_⟩
  rw [(isLin_stdLin X E pos' M φ k).repr, Fintype.sum_sum_type]
  simp only [hypLin, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f e i : ℂ_[p]) * MvPowerSeries.X (Sum.inl e))),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f' e i : ℂ_[p]) * MvPowerSeries.X (Sum.inr e)))]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf]
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos' M φ (Sum.inl e) k') k).symm
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf']
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos' M φ (Sum.inr e) k') k).symm

theorem frameHyp_of_coord (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (hc0 : c ≠ 0) (h1 : OnbEx X hfin D large₂ Lg')
    (h2 : LamTrace X hfin D large₂ Lg' lam) (h3 : HypCoord X E hfin D pos' large₂ Lg' M lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.L2.KerInert.Rep.FrameHyp X E hfin D pos' large₂ Lg' F (fun j La La' => subGen X E pos' M j La La') lam c :=
  frameHyp_of_std X E hfin D pos' large₂ Lg' M lam c (frameStd_of X E hfin D pos' large₂ Lg' M lam c hc0 h1 h2 h3) F

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem onbEx_of (hO : Formalism.L2.KerInert.OrthBasisExists) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (hadm : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    OnbEx X hfin D large₂ Lg' :=
  fun j L0 hL0 La' hLa' => hO D p h5 hin _ _ _ _ (hadm j L0 hL0 La' hLa')

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem lamONB_of_cols (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hr : r = Fintype.card (D.what₂.Tau × Fin N' × Fin N))
    (hcol : ∀ i i', ∑ k, lamBc D lam b k i * lamB D lam b k i' = if i = i' then 1 else 0) :
    LamONB D lam b := by
  classical
  let e : Fin r ≃ (D.what₂.Tau × Fin N' × Fin N) := (Fintype.equivFinOfCardEq hr.symm).symm
  let B : Matrix (D.what₂.Tau × Fin N' × Fin N) (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
    fun k l => lamB D lam b k (e.symm l)
  let C : Matrix (D.what₂.Tau × Fin N' × Fin N) (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
    fun l k => lamBc D lam b k (e.symm l)
  have h1 : C * B = 1 := by
    ext l l'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hcol (e.symm l) (e.symm l')
    rw [this]
    simp only [Equiv.apply_eq_iff_eq]
  have h2 : B * C = 1 := mul_eq_one_comm.1 h1
  intro k k'
  have h3 := congrFun (congrFun h2 k) k'
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  rw [← h3]
  exact Fintype.sum_equiv e _ _ fun i => by simp [B, C]

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem lamTrace_of (lam : Qbar →+* ℂ_[p]) (h1 : RankTie X hfin D large₂ Lg') (h2 : ColTie X hfin D large₂ Lg' lam) :
    LamTrace X hfin D large₂ Lg' lam :=
  fun j L0 hL0 La' hLa' r b hb ho => lamONB_of_cols D lam b (h1 j L0 hL0 La' hLa' r b hb) (h2 j L0 hL0 La' hLa' r b hb ho)

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.KerInert.IntegralOrthonormalChange (embQ lamC_embT)

theorem cols_of_trace (D : D7) (hT : TraceTau D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ho : Orthonormal D b) (i i' : Fin r) :
    ∑ k, lamBc D lam b k i * lamB D lam b k i' = if i = i' then 1 else 0 := by
  classical
  set Y : D.host.E := ∑ ba : Fin N' × Fin N, b i' ba.1 ba.2 * D.host.conj (b i ba.1 ba.2) with hY
  have htr : Algebra.trace D.host.K D.host.E Y = if i' = i then 1 else 0 := by
    rw [← ho i' i, hYY, hY, Fintype.sum_prod_type]
  have hq : ∑ τ : D.what₂.Tau, embQ D τ Y = if i = i' then 1 else 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [embQ, RingHom.codRestrict_apply]
    rw [hT Y, htr]
    by_cases h : i = i'
    · rw [if_pos h.symm, if_pos h]
      simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
      simp
  calc ∑ k, lamBc D lam b k i * lamB D lam b k i'
      = ∑ τ : D.what₂.Tau, lam (embQ D τ Y) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [lamB, lamBc, lamC_embT, hY, map_sum, map_mul]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = lam (∑ τ : D.what₂.Tau, embQ D τ Y) := (map_sum lam _ _).symm
    _ = if i = i' then 1 else 0 := by
        rw [hq]
        split_ifs
        · exact map_one lam
        · exact map_zero lam

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem colTie_of (hT : TraceTau D) (lam : Qbar →+* ℂ_[p]) : ColTie X hfin D large₂ Lg' lam :=
  fun _ _ _ _ _ _ b _ ho i i' => cols_of_trace D hT lam b ho i i'

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Coef

variable {σ : Type} {K : Type} [Field K]

theorem coeff_CC_mul_X [DecidableEq σ] (a c : K) (z y : σ) :
    MvPowerSeries.coeff (Finsupp.single y 1)
      (MvPowerSeries.C a * MvPowerSeries.C c * MvPowerSeries.X z : MvPowerSeries σ K) = if z = y then a * c else 0 := by
  rw [← map_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases h : z = y
  · subst h; simp
  · have : Finsupp.single y 1 ≠ Finsupp.single z (1 : ℕ) := fun e => h ((Finsupp.single_left_inj one_ne_zero).1 e).symm
    simp [h, this]

end Coef

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem frVec_inl_same {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') (e : X.EA j)
    (s : Fin (X.G.P.n' e.1)) (B : Fin ((X.Pj (j + 1)).m + 1)) (A : Fin ((X.Pj j).m + 1)) :
    letI := wittFractionAlgebraCp p
    letI := Formalism.L2.G.Pend.algKfC E.toCEmb
    frVec X E pos M φ (Sum.inl e) (pos ⟨e.1, s⟩, B, A) =
      if IsOddPos s then 0 else
        mAt X ℂ_[p] (j + 1) e.1 s (M (j + 1) La' e.1 * (φ.g' e.1 : Matrix _ _ _)) (Fin.cast (rank_eq X (j + 1)) B) e.2.2.2 *
          mAt X ℂ_[p] j e.1 s ((((φ.g e.1)⁻¹ : GL _ _) : Matrix _ _ _) * (M j L0 e.1)⁻¹) e.2.2.1 (Fin.cast (rank_eq X j) A) *
          algebraMap (K0 p) ℂ_[p] (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om e.1).om e.2.1))) := by
  classical
  simp only [frVec, stdLin]
  rw [Equiv.symm_apply_apply]
  by_cases hs : IsOddPos s
  · simp only [if_pos hs, zOfX, Finset.mul_sum, ← mul_assoc, map_sum, coeff_CC_mul_X]
    simp
  · simp only [if_neg hs, zOfX, Finset.mul_sum, ← mul_assoc, map_sum, coeff_CC_mul_X]
    obtain ⟨v, r, a, b⟩ := e
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_neg hs, if_false, Finset.sum_const_zero,
      Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single r (fun x _ hx => by simp [hx]) (by simp)]
    simp

theorem frVec_inr_same {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') (e : X.EA j)
    (s : Fin (X.G.P.n' e.1)) (B : Fin ((X.Pj (j + 1)).m + 1)) (A : Fin ((X.Pj j).m + 1)) :
    letI := wittFractionAlgebraCp p
    letI := Formalism.L2.G.Pend.algKfC E.toCEmb
    frVec X E pos M φ (Sum.inr e) (pos ⟨e.1, s⟩, B, A) =
      if IsOddPos s then
        mAt X ℂ_[p] j e.1 s (M j L0 e.1 * (φ.g e.1 : Matrix _ _ _)) (Fin.cast (rank_eq X j) A) e.2.2.1 *
          mAt X ℂ_[p] (j + 1) e.1 s ((((φ.g' e.1)⁻¹ : GL _ _) : Matrix _ _ _) * (M (j + 1) La' e.1)⁻¹) e.2.2.2
            (Fin.cast (rank_eq X (j + 1)) B) *
          algebraMap (K0 p) ℂ_[p] (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om e.1).omS e.2.1)))
      else 0 := by
  classical
  simp only [frVec, stdLin]
  rw [Equiv.symm_apply_apply]
  by_cases hs : IsOddPos s
  · simp only [if_pos hs, zOfX, Finset.mul_sum, ← mul_assoc, map_sum, coeff_CC_mul_X]
    obtain ⟨v, r, a, b⟩ := e
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_pos hs, if_false, Finset.sum_const_zero,
      Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single r (fun x _ hx => by simp [hx]) (by simp)]
    simp
  · simp only [if_neg hs, zOfX, Finset.mul_sum, ← mul_assoc, map_sum, coeff_CC_mul_X]
    simp

theorem frVec_ne {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') (y : X.EA j ⊕ X.EA j)
    (v : X.Pl) (hv : v ≠ (Sum.elim id id y).1) (s : Fin (X.G.P.n' v))
    (B : Fin ((X.Pj (j + 1)).m + 1)) (A : Fin ((X.Pj j).m + 1)) :
    frVec X E pos M φ y (pos ⟨v, s⟩, B, A) = 0 := by
  classical
  simp only [frVec, stdLin]
  rw [Equiv.symm_apply_apply]
  dsimp only
  rcases y with ⟨v', r, a, b⟩ | ⟨v', r, a, b⟩ <;>
  · simp only [Sum.elim_inl, Sum.elim_inr, id] at hv
    by_cases hs : IsOddPos s <;>
    · simp only [hs, if_true, if_false, zOfX, Finset.mul_sum, ← mul_assoc, map_sum, coeff_CC_mul_X]
      simp [hv]

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)

theorem mAt_apply_cast (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (Q : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (a : Fin ((X.Pj j).m + 1))
    (y : Fin (NN X.G.P.m X.t j)) :
    (letI := wittFractionAlgebraCp p
     letI := Formalism.L2.G.Pend.algKfC E.toCEmb
     mAt X ℂ_[p] j v s Q (Fin.cast (rank_eq X j) a) y) = twE X E v s (Q a (Fin.cast (rank_eq X j).symm y)) := by
  simp [mAt, twE]

theorem mAt_apply_cast' (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (Q : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (a : Fin ((X.Pj j).m + 1))
    (y : Fin (NN X.G.P.m X.t j)) :
    (letI := wittFractionAlgebraCp p
     letI := Formalism.L2.G.Pend.algKfC E.toCEmb
     mAt X ℂ_[p] j v s Q y (Fin.cast (rank_eq X j) a)) = twE X E v s (Q (Fin.cast (rank_eq X j).symm y) a) := by
  simp [mAt, twE]

theorem val_finRotate {n : ℕ} (s : Fin n) : (finRotate n s).val = if s.val + 1 = n then 0 else s.val + 1 := by
  cases n with
  | zero => exact s.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : s = Fin.last n
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro e
      apply h
      ext
      simp
      omega

theorem odd_finRotate {n : ℕ} (hn : Even n) (s : Fin n) : IsOddPos (finRotate n s) ↔ ¬ IsOddPos s := by
  obtain ⟨h, hh⟩ := hn
  show (finRotate n s).val % 2 = 1 ↔ ¬ s.val % 2 = 1
  rw [val_finRotate]
  have hs := s.isLt
  by_cases h1 : s.val + 1 = n
  · rw [if_pos h1]
    constructor
    · intro h2; exact absurd h2 (by decide)
    · intro h2; exfalso; apply h2; omega
  · rw [if_neg h1]
    constructor
    · intro h2 h3; omega
    · intro h2; omega

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi dualT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Sum3

variable {R : Type} [CommRing R] {ι κ κ' : Type} [Fintype ι] [Fintype κ] [Fintype κ']

theorem sum3 (F : ι → κ → R) (G : ι → κ' → R) (Z : κ → R) (W : κ' → R) :
    ∑ i, (∑ k, F i k * Z k) * (∑ k', G i k' * W k') = ∑ k, ∑ k', (∑ i, F i k * G i k') * Z k * W k' := by
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Sum3

theorem iter_rot {R : Type} (f : R → R) {n : ℕ} (w : R) (hfix : f^[n] w = w) (s : Fin n) :
    f^[s.val + 1] w = f^[(finRotate n s).val] w := by
  rw [val_finRotate]
  split_ifs with h
  · rw [h, hfix]; rfl
  · rfl

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : Qbar →+* ℂ_[p])
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') {r : ℕ}
  (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
  (twK : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), X.G.P.Qq v →+* MaximalUnramifiedExtension p) (wK : WW p →+* MaximalUnramifiedExtension p)

abbrev PIx (v : X.Pl) : Type := Fin (X.G.P.n' v) × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)

def LBc (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) : MaximalUnramifiedExtension p :=
  twK v k.1 (ρ v (if IsOddPos k.1 then D.host.conj (D.host.conj (b i k.2.1 k.2.2)) else D.host.conj (b i k.2.1 k.2.2)))

def LB (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) : MaximalUnramifiedExtension p :=
  twK v k.1 (ρ v (if IsOddPos k.1 then D.host.conj (b i k.2.1 k.2.2) else b i k.2.1 k.2.2))

def YX (e : X.EA j) (k : PIx X (j := j) e.1) : MaximalUnramifiedExtension p :=
  if IsOddPos k.1 then 0 else
    twK e.1 k.1 (Gp X M φ e.1 k.2.1 (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2)) *
    twK e.1 k.1 (Gmi X M φ e.1 (Fin.cast (rank_eq X j).symm e.2.2.1) k.2.2) *
    wK ((sigW p)^[k.1.val] ((X.om e.1).om e.2.1))

def ZX (e : X.EA j) (k : PIx X (j := j) e.1) : MaximalUnramifiedExtension p :=
  if IsOddPos k.1 then
    twK e.1 k.1 (Gp X M φ e.1 k.2.1 (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2)) *
    twK e.1 k.1 (Gmi X M φ e.1 (Fin.cast (rank_eq X j).symm e.2.2.1) k.2.2) *
    wK ((sigW p)^[k.1.val] ((X.om e.1).om e.2.1))
  else 0

def YX' (e : X.EA j) (k : PIx X (j := j) e.1) : MaximalUnramifiedExtension p :=
  if IsOddPos k.1 then
    twK e.1 k.1 (Gm X M φ e.1 k.2.2 (Fin.cast (rank_eq X j).symm e.2.2.1)) *
    twK e.1 k.1 (Gpi X M φ e.1 (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2) k.2.1) *
    wK ((sigW p)^[k.1.val] ((X.om e.1).omS e.2.1))
  else 0

def ZX' (e : X.EA j) (k : PIx X (j := j) e.1) : MaximalUnramifiedExtension p :=
  if IsOddPos k.1 then 0 else
    twK e.1 k.1 (Gm X M φ e.1 k.2.2 (Fin.cast (rank_eq X j).symm e.2.2.1)) *
    twK e.1 k.1 (Gpi X M φ e.1 (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2) k.2.1) *
    wK ((sigW p)^[k.1.val] ((X.om e.1).omS e.2.1))

def fK (e : X.EA j) (i : Fin r) : MaximalUnramifiedExtension p := ∑ k, LBc X D b ρ twK e.1 k i * YX X M φ twK wK e k

def fK' (e : X.EA j) (i : Fin r) : MaximalUnramifiedExtension p := ∑ k, LBc X D b ρ twK e.1 k i * YX' X M φ twK wK e k

def rotP (v : X.Pl) : PIx X (j := j) v ≃ PIx X (j := j) v :=
  (finRotate (X.G.P.n' v)).prodCongr (Equiv.refl _)

section Sigma

variable (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
  (hσtw : ∀ v s x, σ (twK v s x) = twK v (finRotate _ s) x) (hσw : ∀ w, σ (wK w) = wK (sigW p w))
  (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x)

include hσtw hev hconj in
theorem sigma_LBc (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) :
    σ (LBc X D b ρ twK v k i) = LB X D b ρ twK v (rotP X v k) i := by
  simp only [LBc, LB, rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, hσtw]
  congr 2
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev v)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2, hconj]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev v) _).2 hs
    rw [if_neg hs, if_pos h2]

include hσtw hev hconj in
theorem sigma_LB (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) :
    σ (LB X D b ρ twK v k i) = LBc X D b ρ twK v (rotP X v k) i := by
  simp only [LBc, LB, rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, hσtw]
  congr 2
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev v)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev v) _).2 hs
    rw [if_neg hs, if_pos h2, hconj]

include hσtw hσw hev in
theorem sigma_YX (e : X.EA j) (k : PIx X (j := j) e.1) :
    σ (YX X M φ twK wK e k) = ZX X M φ twK wK e (rotP X e.1 k) := by
  simp only [YX, ZX, rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id]
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev e.1)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2, map_zero]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev e.1) _).2 hs
    rw [if_neg hs, if_pos h2, map_mul, map_mul, hσtw, hσtw, hσw, ← Function.iterate_succ_apply' (sigW p),
      iter_rot (sigW p) _ ((X.om e.1).fix e.2.1) k.1]

include hσtw hσw hev in
theorem sigma_ZX (e : X.EA j) (k : PIx X (j := j) e.1) :
    σ (ZX X M φ twK wK e k) = YX X M φ twK wK e (rotP X e.1 k) := by
  simp only [YX, ZX, rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id]
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev e.1)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2, map_mul, map_mul, hσtw, hσtw, hσw, ← Function.iterate_succ_apply' (sigW p),
      iter_rot (sigW p) _ ((X.om e.1).fix e.2.1) k.1]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev e.1) _).2 hs
    rw [if_neg hs, if_pos h2, map_zero]

include hσtw hσw hev in
theorem sigma_YX' (e : X.EA j) (k : PIx X (j := j) e.1) :
    σ (YX' X M φ twK wK e k) = ZX' X M φ twK wK e (rotP X e.1 k) := by
  simp only [YX', ZX', rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id]
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev e.1)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2, map_mul, map_mul, hσtw, hσtw, hσw, ← Function.iterate_succ_apply' (sigW p),
      iter_rot (sigW p) _ ((X.om e.1).fixS e.2.1) k.1]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev e.1) _).2 hs
    rw [if_neg hs, if_pos h2, map_zero]

include hσtw hσw hev in
theorem sigma_ZX' (e : X.EA j) (k : PIx X (j := j) e.1) :
    σ (ZX' X M φ twK wK e k) = YX' X M φ twK wK e (rotP X e.1 k) := by
  simp only [YX', ZX', rotP, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id]
  by_cases hs : IsOddPos k.1
  · have h2 : ¬ IsOddPos (finRotate _ k.1) := by rw [odd_finRotate (hev e.1)]; exact not_not.2 hs
    rw [if_pos hs, if_neg h2, map_zero]
  · have h2 : IsOddPos (finRotate _ k.1) := (odd_finRotate (hev e.1) _).2 hs
    rw [if_neg hs, if_pos h2, map_mul, map_mul, hσtw, hσtw, hσw, ← Function.iterate_succ_apply' (sigW p),
      iter_rot (sigW p) _ ((X.om e.1).fixS e.2.1) k.1]

end Sigma

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi dualT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem sum2x {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β] (x u : β → R) (y z : α → R) (w1 w2 : R) :
    ∑ B, ∑ A, (x B * y A * w1) * (z A * u B * w2) = (∑ A, y A * z A) * (∑ B, u B * x B) * (w1 * w2) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun B _ => ?_
  ring

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : Qbar →+* ℂ_[p])
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') {r : ℕ}
  (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
  (twK : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), X.G.P.Qq v →+* MaximalUnramifiedExtension p) (wK : WW p →+* MaximalUnramifiedExtension p)
  (hρ : ∀ v s x, lamC lam (embT D (pos ⟨v, s⟩) x) = twE X E v s (ρ v (if IsOddPos s then D.host.conj x else x)))
  (htwK : ∀ v s x, ((twK v s x : MaximalUnramifiedExtension p) : ℂ_[p]) = twE X E v s x)

include hρ htwK in
theorem coe_LB (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) :
    ((LB X D b ρ twK v k i : MaximalUnramifiedExtension p) : ℂ_[p]) = lamB D lam b (pos ⟨v, k.1⟩, k.2.1, k.2.2) i := by
  rw [LB, htwK, lamB, hρ]

include hρ htwK in
theorem coe_LBc (v : X.Pl) (k : PIx X (j := j) v) (i : Fin r) :
    ((LBc X D b ρ twK v k i : MaximalUnramifiedExtension p) : ℂ_[p]) = lamBc D lam b (pos ⟨v, k.1⟩, k.2.1, k.2.2) i := by
  rw [LBc, htwK, lamBc, hρ]

open Classical in
include hρ htwK in

theorem kurONB (hL : LamONB D lam b) (v v' : X.Pl) (k : PIx X (j := j) v) (k' : PIx X (j := j) v') :
    ∑ i, LB X D b ρ twK v k i * LBc X D b ρ twK v' k' i =
      if ((pos ⟨v, k.1⟩, k.2.1, k.2.2) : D.what₂.Tau × _ × _) = (pos ⟨v', k'.1⟩, k'.2.1, k'.2.2) then 1 else 0 := by
  classical
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [MulMemClass.coe_mul, coe_LB X E D pos lam b ρ twK hρ htwK, coe_LBc X E D pos lam b ρ twK hρ htwK]
  rw [hL (pos ⟨v, k.1⟩, k.2.1, k.2.2) (pos ⟨v', k'.1⟩, k'.2.1, k'.2.2)]
  split_ifs <;> simp

section Hyp

variable (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
  (hσtw : ∀ v s x, σ (twK v s x) = twK v (finRotate _ s) x) (hσw : ∀ w, σ (wK w) = wK (sigW p w))
  (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x)

include hσtw hσw hev hconj in
theorem sigma_fK (e : X.EA j) (i : Fin r) :
    σ (fK X D M φ b ρ twK wK e i) = ∑ k, LB X D b ρ twK e.1 k i * ZX X M φ twK wK e k := by
  simp only [fK, map_sum, map_mul, sigma_LBc X D b ρ twK σ hσtw hev hconj, sigma_YX X M φ twK wK σ hσtw hσw hev]
  exact Equiv.sum_comp (rotP X e.1) (fun k => LB X D b ρ twK e.1 k i * ZX X M φ twK wK e k)

include hσtw hσw hev hconj in
theorem sigma_fK' (e : X.EA j) (i : Fin r) :
    σ (fK' X D M φ b ρ twK wK e i) = ∑ k, LB X D b ρ twK e.1 k i * ZX' X M φ twK wK e k := by
  simp only [fK', map_sum, map_mul, sigma_LBc X D b ρ twK σ hσtw hev hconj, sigma_YX' X M φ twK wK σ hσtw hσw hev]
  exact Equiv.sum_comp (rotP X e.1) (fun k => LB X D b ρ twK e.1 k i * ZX' X M φ twK wK e k)

include hσtw hσw hev hconj in
theorem sigma2_fK (e : X.EA j) (i : Fin r) : σ (σ (fK X D M φ b ρ twK wK e i)) = fK X D M φ b ρ twK wK e i := by
  rw [sigma_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj]
  simp only [map_sum, map_mul, sigma_LB X D b ρ twK σ hσtw hev hconj, sigma_ZX X M φ twK wK σ hσtw hσw hev]
  exact Equiv.sum_comp (rotP X e.1) (fun k => LBc X D b ρ twK e.1 k i * YX X M φ twK wK e k)

include hσtw hσw hev hconj in
theorem sigma2_fK' (e : X.EA j) (i : Fin r) : σ (σ (fK' X D M φ b ρ twK wK e i)) = fK' X D M φ b ρ twK wK e i := by
  rw [sigma_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj]
  simp only [map_sum, map_mul, sigma_LB X D b ρ twK σ hσtw hev hconj, sigma_ZX' X M φ twK wK σ hσtw hσw hev]
  exact Equiv.sum_comp (rotP X e.1) (fun k => LBc X D b ρ twK e.1 k i * YX' X M φ twK wK e k)

theorem pos_delta_same (v : X.Pl) (k k' : PIx X (j := j) v) :
    ((pos ⟨v, k.1⟩, k.2.1, k.2.2) : D.what₂.Tau × _ × _) = (pos ⟨v, k'.1⟩, k'.2.1, k'.2.2) ↔ k = k' := by
  obtain ⟨s, B, A⟩ := k
  obtain ⟨s', B', A'⟩ := k'
  simp [Prod.ext_iff, pos.injective.eq_iff]

theorem pos_delta_ne {v v' : X.Pl} (hv : v ≠ v') (k : PIx X (j := j) v) (k' : PIx X (j := j) v') :
    ¬ (((pos ⟨v, k.1⟩, k.2.1, k.2.2) : D.what₂.Tau × _ × _) = (pos ⟨v', k'.1⟩, k'.2.1, k'.2.2)) := by
  intro h
  have := pos.injective (congrArg Prod.fst h)
  exact hv (congrArg Sigma.fst this)

include hρ htwK hσtw hσw hev hconj in
theorem iso_fK (hL : LamONB D lam b) (e e' : X.EA j) :
    ∑ i, σ (fK X D M φ b ρ twK wK e i) * fK X D M φ b ρ twK wK e' i = 0 := by
  classical
  simp only [sigma_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj]
  simp only [fK]
  rw [sum3]
  simp only [kurONB X E D pos lam b ρ twK hρ htwK hL]
  obtain ⟨v, x⟩ := e
  obtain ⟨v', x'⟩ := e'
  by_cases hv : v = v'
  · subst hv
    simp only [pos_delta_same X D pos, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [ZX, YX]
    by_cases hs : IsOddPos k.1 <;> simp [hs]
  · simp [pos_delta_ne X D pos hv]

include hρ htwK hσtw hσw hev hconj in
theorem iso_fK' (hL : LamONB D lam b) (e e' : X.EA j) :
    ∑ i, σ (fK' X D M φ b ρ twK wK e i) * fK' X D M φ b ρ twK wK e' i = 0 := by
  classical
  simp only [sigma_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj]
  simp only [fK']
  rw [sum3]
  simp only [kurONB X E D pos lam b ρ twK hρ htwK hL]
  obtain ⟨v, x⟩ := e
  obtain ⟨v', x'⟩ := e'
  by_cases hv : v = v'
  · subst hv
    simp only [pos_delta_same X D pos, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [ZX', YX']
    by_cases hs : IsOddPos k.1 <;> simp [hs]
  · simp [pos_delta_ne X D pos hv]

end Hyp

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi dualT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : Qbar →+* ℂ_[p])
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') {r : ℕ}
  (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
  (twK : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), X.G.P.Qq v →+* MaximalUnramifiedExtension p) (wK : WW p →+* MaximalUnramifiedExtension p)
  (hρ : ∀ v s x, lamC lam (embT D (pos ⟨v, s⟩) x) = twE X E v s (ρ v (if IsOddPos s then D.host.conj x else x)))
  (htwK : ∀ v s x, ((twK v s x : MaximalUnramifiedExtension p) : ℂ_[p]) = twE X E v s x)

theorem Gmi_mul_Gm (hM : ∀ v, IsUnit (M j L0 v).det) (v : X.Pl) : Gmi X M φ v * Gm X M φ v = 1 := by
  simp only [Gmi, Gm]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((M j L0 v)⁻¹), Matrix.nonsing_inv_mul _ (hM v), Matrix.one_mul]
  exact Units.inv_mul (φ.g v)

theorem Gpi_mul_Gp (hM : ∀ v, IsUnit (M (j + 1) La' v).det) (v : X.Pl) : Gpi X M φ v * Gp X M φ v = 1 := by
  simp only [Gpi, Gp]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((M (j + 1) La' v)⁻¹), Matrix.nonsing_inv_mul _ (hM v), Matrix.one_mul]
  exact Units.inv_mul (φ.g' v)

section Hyp

variable (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
  (hσtw : ∀ v s x, σ (twK v s x) = twK v (finRotate _ s) x) (hσw : ∀ w, σ (wK w) = wK (sigW p w))
  (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x)

open Classical in
include hρ htwK hσtw hσw hev hconj in
theorem dual_fK (hL : LamONB D lam b) (hM : ∀ v, IsUnit (M j L0 v).det) (hM' : ∀ v, IsUnit (M (j + 1) La' v).det)
    (e e' : X.EA j) :
    ∑ i, σ (fK X D M φ b ρ twK wK e i) * fK' X D M φ b ρ twK wK e' i = if e = e' then 1 else 0 := by
  simp only [sigma_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj]
  simp only [fK']
  rw [sum3]
  simp only [kurONB X E D pos lam b ρ twK hρ htwK hL]
  obtain ⟨v, r0, a0, b0⟩ := e
  obtain ⟨v', r1, a1, b1⟩ := e'
  by_cases hv : v = v'
  · subst hv
    simp only [pos_delta_same X D pos, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Fintype.sum_prod_type]
    have key : ∀ s : Fin (X.G.P.n' v), ∑ x : Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1),
        ZX X M φ twK wK ⟨v, (r0, a0, b0)⟩ (s, x) * YX' X M φ twK wK ⟨v, (r1, a1, b1)⟩ (s, x) =
          if IsOddPos s then
            twK v s ((Gmi X M φ v * Gm X M φ v) (Fin.cast (rank_eq X j).symm a0) (Fin.cast (rank_eq X j).symm a1) *
              (Gpi X M φ v * Gp X M φ v) (Fin.cast (rank_eq X (j + 1)).symm b1) (Fin.cast (rank_eq X (j + 1)).symm b0)) *
            (wK ((sigW p)^[s.val] ((X.om v).om r0)) * wK ((sigW p)^[s.val] ((X.om v).omS r1)))
          else 0 := by
      intro s
      by_cases hs : IsOddPos s
      · simp only [ZX, YX', if_pos hs]
        rw [Fintype.sum_prod_type]
        dsimp only
        rw [sum2x, map_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
        simp only [map_mul]
      · simp [ZX, hs]
    simp only [key, Gmi_mul_Gm X M φ hM, Gpi_mul_Gp X M φ hM', Matrix.one_apply, Fin.cast_inj]
    by_cases ha : a0 = a1
    · by_cases hb : b1 = b0
      · subst ha
        subst hb
        simp only [if_true, mul_one, map_one, one_mul]
        rw [← Finset.sum_filter]
        simp only [← map_mul, ← map_sum]
        rw [dualT (X.om v) (hev v) 1 (by norm_num) IsOddPos (fun s => Iff.rfl) r0 r1]
        by_cases hr : r0 = r1
        · subst hr; simp
        · rw [if_neg hr, map_zero, if_neg]
          intro h
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
          exact hr h.1
      · simp only [if_neg hb, mul_zero, map_zero, zero_mul, ite_self, Finset.sum_const_zero]
        rw [if_neg]
        intro h
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
        exact hb h.2.2.symm
    · simp only [if_neg ha, zero_mul, map_zero, ite_self, Finset.sum_const_zero]
      rw [if_neg]
      intro h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
      exact ha h.2.1
  · rw [if_neg]
    · refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun k' _ => ?_
      rw [if_neg (pos_delta_ne X D pos hv k k')]
      simp
    · intro h
      exact hv (congrArg Sigma.fst h)

end Hyp

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp Frm invF zOfX tw mAt rank_eq mAt_mul Pi Qi dualT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : Qbar →+* ℂ_[p])
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') {r : ℕ}
  (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
  (twK : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), X.G.P.Qq v →+* MaximalUnramifiedExtension p) (wK : WW p →+* MaximalUnramifiedExtension p)
  (hρ : ∀ v s x, lamC lam (embT D (pos ⟨v, s⟩) x) = twE X E v s (ρ v (if IsOddPos s then D.host.conj x else x)))
  (htwK : ∀ v s x, ((twK v s x : MaximalUnramifiedExtension p) : ℂ_[p]) = twE X E v s x)
  (hwK : ∀ w, ((wK w : MaximalUnramifiedExtension p) : ℂ_[p]) = wE p w)

include hρ htwK hwK in
theorem coe_fK (e : X.EA j) (i : Fin r) :
    ((fK X D M φ b ρ twK wK e i : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ k, lamBc D lam b k i * frVec X E pos M φ (Sum.inl e) k := by
  classical
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp pos, Fintype.sum_sigma, Finset.sum_eq_single e.1]
  · rw [fK, AddSubmonoidClass.coe_finsetSum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
    rw [MulMemClass.coe_mul, coe_LBc X E D pos lam b ρ twK hρ htwK]
    congr 1
    rw [frVec_inl_same]
    by_cases hs : IsOddPos s
    · simp [YX, hs]
    · simp only [YX, if_neg hs, MulMemClass.coe_mul, htwK, hwK, wE, mAt_apply_cast, mAt_apply_cast', Gp, Gmi]
  · intro v _ hv
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun x _ => ?_
    rw [frVec_ne X E pos M φ (Sum.inl e) v hv s x.1 x.2, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

include hρ htwK hwK in
theorem coe_fK' (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (e : X.EA j) (i : Fin r) :
    ((fK' X D M φ b ρ twK wK e i : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ k, lamBc D lam b k i * frVec X E pos M φ (Sum.inr e) k := by
  classical
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp pos, Fintype.sum_sigma, Finset.sum_eq_single e.1]
  · rw [fK', AddSubmonoidClass.coe_finsetSum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
    rw [MulMemClass.coe_mul, coe_LBc X E D pos lam b ρ twK hρ htwK]
    congr 1
    rw [frVec_inr_same]
    by_cases hs : IsOddPos s
    · simp only [YX', if_pos hs, MulMemClass.coe_mul, htwK, hwK, wE, mAt_apply_cast, mAt_apply_cast', Gm, Gpi]
    · simp [YX', hs]
  · intro v _ hv
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun x _ => ?_
    rw [frVec_ne X E pos M φ (Sum.inr e) v hv s x.1 x.2, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fK_pos (e : X.EA j) (i : Fin r) (s : Fin (X.G.P.n' e.1)) :
    ∑ x : Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1),
        LBc X D b ρ twK e.1 (s, x) i * YX X M φ twK wK e (s, x) =
      if IsOddPos s then 0 else
        twK e.1 s (∑ B, ∑ A, ρ e.1 (D.host.conj (b i B A)) * Gp X M φ e.1 B (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2) *
          Gmi X M φ e.1 (Fin.cast (rank_eq X j).symm e.2.2.1) A) * wK ((sigW p)^[s.val] ((X.om e.1).om e.2.1)) := by
  by_cases hs : IsOddPos s
  · simp [YX, hs]
  · simp only [LBc, YX, if_neg hs, Fintype.sum_prod_type, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
    ring

theorem fK'_pos (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (e : X.EA j) (i : Fin r) (s : Fin (X.G.P.n' e.1)) :
    ∑ x : Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1),
        LBc X D b ρ twK e.1 (s, x) i * YX' X M φ twK wK e (s, x) =
      if IsOddPos s then
        twK e.1 s (∑ B, ∑ A, ρ e.1 (b i B A) * Gm X M φ e.1 A (Fin.cast (rank_eq X j).symm e.2.2.1) *
          Gpi X M φ e.1 (Fin.cast (rank_eq X (j + 1)).symm e.2.2.2) B) * wK ((sigW p)^[s.val] ((X.om e.1).omS e.2.1))
      else 0 := by
  by_cases hs : IsOddPos s
  · simp only [LBc, YX', if_pos hs, hconj, Fintype.sum_prod_type, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
    ring
  · simp [YX', hs]

include htwK in
theorem norm_fK (hwn : ∀ w, ‖((wK w : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1)
    (hint : ∀ (i : Fin r) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b0 : Fin ((X.Pj (j + 1)).m + 1)) (a0 : Fin ((X.Pj j).m + 1)),
      ‖twE X E v s (∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A)‖ ≤ 1)
    (e : X.EA j) (i : Fin r) : ‖fK X D M φ b ρ twK wK e i‖ ≤ 1 := by
  show ‖((fK X D M φ b ρ twK wK e i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [fK, Fintype.sum_prod_type]
  simp only [fK_pos X D M φ b ρ twK wK e i, AddSubmonoidClass.coe_finsetSum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
  split_ifs
  · simp
  · rw [MulMemClass.coe_mul, norm_mul, htwK]
    exact mul_le_one₀ (hint i e.1 s _ _) (norm_nonneg _) (hwn _)

include htwK in
theorem norm_fK' (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (hwn : ∀ w, ‖((wK w : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1)
    (hint' : ∀ (i : Fin r) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b1 : Fin ((X.Pj (j + 1)).m + 1)) (a1 : Fin ((X.Pj j).m + 1)),
      ‖twE X E v s (∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a1 * Gpi X M φ v b1 B)‖ ≤ 1)
    (e : X.EA j) (i : Fin r) : ‖fK' X D M φ b ρ twK wK e i‖ ≤ 1 := by
  show ‖((fK' X D M φ b ρ twK wK e i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [fK', Fintype.sum_prod_type]
  simp only [fK'_pos X D M φ b ρ twK wK hconj e i, AddSubmonoidClass.coe_finsetSum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
  split_ifs
  · rw [MulMemClass.coe_mul, norm_mul, htwK]
    exact mul_le_one₀ (hint' i e.1 s _ _) (norm_nonneg _) (hwn _)
  · simp

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.G.Pend (Frm)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem hypCoord_of (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : LamTrace X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ) (hF : FrobTw X E)
    (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (hM : MInv X M)
    (hI : FrameInt X E M hfin D large₂ Lg' ρ) :
    HypCoord X E hfin D pos large₂ Lg' M lam 1 := by
  intro j L0 hL0 La' hLa' r b hb ho φ
  obtain ⟨σ, twK, wK, hσ, htwK, hσtw, hwK, hσw, hwn⟩ := hF
  have hL := hT j L0 hL0 La' hLa' r b hb ho
  have hH : IsHypPair σ (fK X D M φ b ρ twK wK) (fK' X D M φ b ρ twK wK) := by
    unfold IsHypPair
    refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩, fun e e' => ?_, fun e e' => ?_, fun e e' => ?_⟩
    · exact norm_fK X E D M φ b ρ twK wK htwK hwn (fun i v s b0 a0 => (hI j L0 hL0 La' hLa' φ r b hb ho i v s b0 a0).1) e i
    · exact sigma2_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact norm_fK' X E D M φ b ρ twK wK htwK hconj hwn
        (fun i v s b1 a1 => (hI j L0 hL0 La' hLa' φ r b hb ho i v s b1 a1).2) e i
    · exact sigma2_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact iso_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · exact iso_fK' X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · rw [dual_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL (hM j L0) (hM (j + 1) La') e e']
  refine ⟨σ, fK X D M φ b ρ twK wK, fK' X D M φ b ρ twK wK, hσ, hH, fun e i => ?_, fun e i => ?_⟩
  · rw [inv_one, one_mul]
    exact coe_fK X E D pos lam M φ b ρ twK wK hρ htwK hwK e i
  · rw [inv_one, one_mul]
    exact coe_fK' X E D pos lam M φ b ρ twK wK hρ htwK hwK hconj e i

theorem frameHyp_of_local (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbEx X hfin D large₂ Lg') (hT : LamTrace X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x)
    (hM : MInv X M) (hI : FrameInt X E M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.L2.KerInert.Rep.FrameHyp X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHyp_of_coord X E hfin D pos large₂ Lg' M lam 1 one_ne_zero h1 hT
    (hypCoord_of X E hfin D pos large₂ Lg' M lam ρ hT hρ hF hev hconj hM hI) F

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  show D.host.φ₀ (D.host.conj (D.host.conj x)) = D.host.φ₀ x
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem frameHyp_of_local' (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbEx X hfin D large₂ Lg') (hT : LamTrace X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hM : MInv X M) (hI : FrameInt X E M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.L2.KerInert.Rep.FrameHyp X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHyp_of_local X E hfin D pos large₂ Lg' M lam ρ h1 hT hρ hF (fun v => (X.G.P.setting v).even) (conj_conj D) hM hI F

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open scoped Matrix

theorem entry_int {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k l : ℕ} (Gt Gti : Matrix (Fin k) (Fin k) Qq)
    (hG : Gti * Gt = 1) (A : Matrix (Fin k) (Fin l) Qq) (Gs : Matrix (Fin l) (Fin l) Qq)
    (hmap : ∀ c, A.mulVec (fun x => Gs x c) ∈ Formalism.MainNotions.G.colSpan W Gt) (x : Fin k) (c : Fin l) :
    ∃ w : W, (Gti * A * Gs) x c = algebraMap W Qq w := by
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun W).1 (hmap c)
  refine ⟨w x, ?_⟩
  have h1 : (Gti * A * Gs) x c = (Gti.mulVec (A.mulVec (fun y => Gs y c))) x := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h2 : A.mulVec (fun y => Gs y c) = Gt.mulVec (fun d => algebraMap W Qq (w d)) := by
    rw [← hw]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [h1, h2, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameInt_of (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (hM : MInv X M) (hT : TwInt X E)
    (hL : FrameLatMap X M hfin D large₂ Lg' ρ) : FrameInt X E M hfin D large₂ Lg' ρ := by
  intro j L0 hL0 La' hLa' φ r b hb ho i v s b0 a0
  obtain ⟨h1, h2⟩ := hL j L0 hL0 La' hLa' φ r b hb ho i v
  constructor
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gm X M φ v) (Gmi X M φ v) (Gmi_mul_Gm X M φ (hM j L0) v)
      ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ (Gp X M φ v) h2 a0 b0
    have e1 : ∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A =
        (Gmi X M φ v * ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ * Gp X M φ v) a0 b0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gp X M φ v) (Gpi X M φ v) (Gpi_mul_Gp X M φ (hM (j + 1) La') v)
      ((b i).map (ρ v)) (Gm X M φ v) h1 b0 a0
    have e1 : ∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a0 * Gpi X M φ v b0 B =
        (Gpi X M φ v * (b i).map (ρ v) * Gm X M φ v) b0 a0 := by
      rw [Matrix.mul_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem frameHyp_of_lat (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbEx X hfin D large₂ Lg') (hT : LamTrace X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hM : MInv X M) (hTw : TwInt X E) (hL : FrameLatMap X M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.L2.KerInert.Rep.FrameHyp X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHyp_of_local' X E hfin D pos large₂ Lg' M lam ρ h1 hT hρ hF hM (frameInt_of X E M hfin D large₂ Lg' ρ hM hTw hL) F

end Formalism.L2.KerInert.RepFrame
