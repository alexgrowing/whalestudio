import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
open GlobalTheory.CompanionTheory.WaveAll

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Swap

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (X : Mat n) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro x hx
  have h1 : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h3 : fderiv ℝ (c • f) x = c • fderiv ℝ f x := (h1.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, Pi.smul_apply, h3]
  rfl

theorem Eu_csmul {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_csmul hf c _ hx]
  rw [smul_comm c (1 / 2 : ℂ), smul_add c, smul_comm c]

theorem Epow_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (c • f)) (c • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Eu_congr isOpen_GLs (ih d b) s a d hx]
    exact Eu_csmul (Epow_smooth hR hf s m d b) c s a d hx

theorem gel_csmul (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (c • f)) (c • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_csmul hR hf c s m a a hx

theorem gel_add (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  have e : f + f' = f - (-1 : ℂ) • f' := by
    ext y
    simp
  have hm : ContDiffOn ℝ ∞ ((-1 : ℂ) • f') (GLs n) := hf'.const_smul (-1 : ℂ)
  have h := gel_sub hR hf hm s m hx
  rw [e, h]
  simp only [Pi.sub_apply, Pi.add_apply, gel_csmul hR hf' (-1) s m hx, Pi.smul_apply]
  simp

theorem gel_zero (hR : RCalc) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (0 : Mat n → V)) 0 (GLs n) := by
  intro x hx
  have h := gel_csmul hR (contDiffOn_const (c := (0 : V)) : ContDiffOn ℝ ∞ (0 : Mat n → V) (GLs n)) 0 s m hx
  simpa using h

theorem gel_sum (hR : RCalc) {ι : Type} (S : Finset ι) {F : ι → Mat n → V}
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (∑ i ∈ S, F i)) (∑ i ∈ S, gel s m (F i)) (GLs n) := by
  classical
  intro x hx
  induction S using Finset.induction_on with
  | empty => simpa using gel_zero hR s m hx
  | insert i S hi ih =>
    have hS : ContDiffOn ℝ ∞ (∑ j ∈ S, F j) (GLs n) := by
      have e : (∑ j ∈ S, F j) = fun y => ∑ j ∈ S, F j y := by
        ext y
        simp only [Finset.sum_apply]
      rw [e]
      exact ContDiffOn.sum fun j _ => hF j
    rw [Finset.sum_insert hi, Finset.sum_insert hi, gel_add hR (hF i) hS s m hx, Pi.add_apply, Pi.add_apply, ih]

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ContDiffOn ℝ ∞ (gel s m f) (GLs n) := by
  have e : gel s m f = fun x => ∑ a, Epow s m a a f x := by
    ext x
    simp only [gel, Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => Epow_smooth hR hf s m a a

theorem zOp_smooth (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact gel_smooth hR ih p.1 p.2

theorem Eu_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (a b : Fin n)
    (s : Bool) (m : ℕ) : Set.EqOn (Eu s' a b (gel s m f)) (gel s m (Eu s' a b f)) (GLs n) := by
  intro x hx
  have hc := (hR n).1 V f hf
  have hS := hc.1
  have hG := hc.2.2.1
  set d : ℂ := if s' then -Complex.I else Complex.I with hd
  have hdB : ContDiffOn ℝ ∞ (d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).const_smul d
  have hsum : ContDiffOn ℝ ∞ (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) (GLs n) :=
    (hS _).add hdB
  have e : Eu s' a b f = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) f + d • Rd (Matrix.single a b Complex.I) f) := rfl
  rw [e, gel_csmul hR hsum _ s m hx, Pi.smul_apply, gel_add hR (hS _) hdB s m hx, Pi.add_apply,
    gel_csmul hR (hS _) d s m hx, Pi.smul_apply, ← hG s m _ x hx, ← hG s m _ x hx]
  rfl

theorem Epow_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s' m' a b (gel s m f)) (gel s m (Epow s' m' a b f)) (GLs n) := by
  induction m' with
  | zero =>
    intro a b x hx
    by_cases hab : a = b
    · simp [Epow, hab]
    · simp only [Epow, if_neg hab]
      exact (gel_zero hR s m hx).symm
  | succ m' ih =>
    intro a b x hx
    have e : Epow s' (m' + 1) a b f = ∑ c, Eu s' a c (Epow s' m' c b f) := rfl
    rw [e, gel_sum hR _ (fun c => Eu_smooth hR (Epow_smooth hR hf s' m' c b) s' a c) s m hx]
    simp only [Epow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr isOpen_GLs (ih c b) s' a c hx]
    exact Eu_gel hR (Epow_smooth hR hf s' m' c b) s' a c s m hx

theorem gel_gel (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s' : Bool) (m' : ℕ)
    (s : Bool) (m : ℕ) : Set.EqOn (gel s' m' (gel s m f)) (gel s m (gel s' m' f)) (GLs n) := by
  intro x hx
  have e : gel s' m' f = ∑ a, Epow s' m' a a f := rfl
  rw [e, gel_sum hR _ (fun a => Epow_smooth hR hf s' m' a a) s m hx]
  simp only [gel, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Epow_gel hR hf s' m' s m a a hx
  simpa only [gel, Finset.sum_apply] using h

theorem zOp_append (w w' : List (Bool × ℕ)) (f : Mat n → V) : zOp (w ++ w') f = zOp w (zOp w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change gel p.1 p.2 (zOp (w ++ w') f) = gel p.1 p.2 (zOp w (zOp w' f))
    rw [ih]

theorem gel_zOp (hR : RCalc) (s : Bool) (m : ℕ) (w : List (Bool × ℕ)) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (gel s m (zOp w f)) (zOp w (gel s m f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel s m (gel p.1 p.2 (zOp w f)) x = gel p.1 p.2 (zOp w (gel s m f)) x
    rw [gel_gel hR (zOp_smooth hR w hf) s m p.1 p.2 hx]
    exact gel_congr isOpen_GLs ih p.1 p.2 hx

theorem zOp_zOp (hR : RCalc) (w w' : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (zOp w (zOp w' f)) (zOp w' (zOp w f)) (GLs n) := by
  induction w with
  | nil => exact fun _ _ => rfl
  | cons p w ih =>
    intro x hx
    change gel p.1 p.2 (zOp w (zOp w' f)) x = zOp w' (gel p.1 p.2 (zOp w f)) x
    rw [gel_congr isOpen_GLs ih p.1 p.2 hx]
    exact gel_zOp hR p.1 p.2 w' (zOp_smooth hR w hf) hx

theorem zOp_swap : RCalc → ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w w' : List (Bool × ℕ)) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ∀ x ∈ GLs n, zOp (w ++ w') f x = zOp (w' ++ w) f x := by
  intro hR n V _ _ w w' f hf x hx
  rw [zOp_append, zOp_append]
  exact zOp_zOp hR w w' hf hx

end GlobalTheory.CompanionTheory.WaveMult.Swap
