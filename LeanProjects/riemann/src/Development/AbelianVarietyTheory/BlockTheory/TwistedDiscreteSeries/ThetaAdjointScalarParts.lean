import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badPlaces (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun P : HeightOneSpectrum (𝓞 D.host.E) => P.under (𝓞 D.host.F)

def goodPartOff (R : RealDat D A Ks) (i : Fin D.R.m) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) :
    Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S c ⊓
    R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def IsScalarOnParts (R : RealDat D A Ks) (lam : Fin D.R.m → T → EigSys D → ℝ) : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (goodPartOff R i (badPlaces R t)) (lam i t)

def ScalarAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP →
    ∃ lam : Fin D.R.m → T → EigSys D → ℝ, IsScalarOnParts R lam

def ThetaThetaAdjScalar : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ScalarAt R F

theorem gap {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) {n : ℕ} (hn : n < Rk.r) :
    ((Rk.t : ℚ) + 3) / 2 ≤ |Formalism.L2.NTheta.lamAt h n + h.e j| := by
  have hk := Rk.m_add_three_le_k
  have hj := j.2
  have mono : ∀ a d : ℕ, a + d < Rk.r → Formalism.L2.NTheta.lamAt h (a + d) ≤ Formalism.L2.NTheta.lamAt h a := by
    intro a d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (a + d) hd).le.trans (ih (by omega))
  have val : ∀ (c : ℕ) (hc : c < Rk.m), Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
    intro c hc
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    simp
  unfold Ranks.r at hn mono
  by_cases hle : n ≤ Rk.k - 1 + j
  · have h1 := mono n (Rk.k - 1 + j - n) (by omega)
    rw [show n + (Rk.k - 1 + j - n) = Rk.k - 1 + j by omega, val j hj] at h1
    have h2 := h.gap_be j
    exact le_trans (by simp only [Fin.eta] at h1; linarith) (le_abs_self _)
  · have hj1 : (j : ℕ) + 1 < Rk.m := by omega
    have h1 := mono (Rk.k - 1 + (j + 1)) (n - (Rk.k - 1 + (j + 1))) (by omega)
    rw [show Rk.k - 1 + (j + 1) + (n - (Rk.k - 1 + (j + 1))) = n by omega, val _ hj1] at h1
    have h2 := h.gap_eb j hj1
    exact le_trans (by linarith) (neg_le_abs _)

theorem IsScalarOnParts.mem {R : RealDat D A Ks} {lam : Fin D.R.m → T → EigSys D → ℝ} (h : IsScalarOnParts R lam)
    (i : Fin D.R.m) (t : T) (c : EigSys D) {x} (hx : x ∈ goodPartOff R i (badPlaces R t) c) :
    R.thG i t (LinearMap.adjoint (R.thG i t) x) ∈ goodPartOff R i (badPlaces R t) c := by
  rw [h i t c x hx]; exact Submodule.smul_mem _ _ hx

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push_neg at hc
    apply h
    have hle : v.asIdeal ≤ (P.under (𝓞 D.host.F)).asIdeal := by
      intro x hx
      obtain ⟨y, hy, hyP⟩ := hc x hx
      have : y = algebraMap _ _ x := RingOfIntegers.ext hy
      subst this
      exact hyP
    have := v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top hle
    rwa [show P.under (𝓞 D.host.F) = v from HeightOneSpectrum.ext this.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

end
