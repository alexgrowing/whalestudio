import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

section Block

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def blkV (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) : (Σ k, J₀ k) → Σ k, J k :=
  fun p => ⟨bk p.1, bx p.1 p.2⟩

theorem isBlockMap_blkV {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (h : Function.Injective bk) :
    IsBlockMap bk (blkV bk bx) := by
  refine ⟨h, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, a⟩ ⟨k', a'⟩ e
    have e1 : bk k = bk k' := congrArg Sigma.fst e
    obtain rfl := h e1
    have e2 : bx k a = bx k a' := by simpa [blkV] using e
    rw [(bx k).injective e2]
  · rintro ⟨_, a⟩ ⟨k, rfl⟩
    exact ⟨⟨k, (bx k).symm a⟩, by simp [blkV]⟩

variable {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}

def restr (v : (Σ k, J₀ k) → Σ k, J k) : ((Σ k, J k) → ℂ) →L[ℝ] ((Σ k, J₀ k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Σ k, J k => ℂ) (v p)

theorem restr_ne (hv : IsBlockMap κ v) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K₀) :
    ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem isSmoothHerm_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsSmoothHerm A) :
    IsSmoothHerm (pullHerm hv A) := by
  have h := ContDiffOn.comp (s := {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA
    (restr v).contDiff.contDiffOn (fun z hz => restr_ne hv hz)
  exact h

theorem isConj_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsConjInvariantH A) :
    IsConjInvariantH (pullHerm hv A) := fun z => hA fun p => z (v p)

theorem isConj_tensor {A B : HermLine J} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) :
    IsConjInvariantH (A.tensor B) := fun z => by
  show A.h _ * B.h _ = A.h _ * B.h _
  rw [hA, hB]

theorem mCoordIdeal_le_imageZ {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    mCoordIdeal y₀ ≤ imageZ (blkV bk bx) (mCoordIdeal y) := by
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp i) fun k => MvPolynomial.X (bk k)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have hf' : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename (blkV bk bx) f) = 0
  rw [key, hf', map_zero]

theorem mem_mcPts_restr (hv : IsBlockMap κ v) {P₀ : Ideal (MRing J₀)} {P : Ideal (MRing J)}
    (hP : P₀ ≤ imageZ v P) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) : (fun p => z (v p)) ∈ mcPts P₀ := by
  refine ⟨restr_ne hv hz.1, fun f hf => ?_⟩
  have := hz.2 _ (hP hf)
  have e : (rename v : MRing J₀ →ₐ[ℤ] MRing J).toRingHom f = rename v f := rfl
  rw [e, map_rename, eval_rename] at this
  exact this

end Block

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have h1 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)) (A.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (h1 k)), add_comm]
  simp only [Real.log_zpow]

theorem prod_zpow_sum {R : Type} [Field R] {X : Type} (s : Finset X) {r : R} (hr : r ≠ 0) (a : X → ℤ) :
    ∏ x ∈ s, r ^ a x = r ^ ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, zpow_add₀ hr, ih]

def stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) : HermLine J where
  a := fun k => -∑ x ∈ Finset.Iic i, (T x).a k
  h z := ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹
  pos z hz := Finset.prod_pos fun x _ => inv_pos.2 ((T x).pos z hz)
  smul c z hc := by
    have h1 : ∀ k, (‖c k‖ : ℝ) ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    simp only [(T _).smul c z hc, mul_inv, Finset.prod_mul_distrib]
    congr 1
    simp only [← Finset.prod_inv_distrib]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg, ← prod_zpow_sum _ (h1 k), Finset.prod_inv_distrib]

theorem log_stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) :
    Real.log ((stepLine T i).h z) = -∑ x ∈ Finset.Iic i, Real.log ((T x).h z) := by
  show Real.log (∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) = _
  rw [Real.log_prod fun x _ => inv_ne_zero ((T x).pos z hz).ne']
  simp only [Real.log_inv, Finset.sum_neg_distrib]

theorem isSmoothHerm_stepLine {N : ℕ} {T : Fin N → HermLine J} (hT : ∀ x, IsSmoothHerm (T x)) (i : Fin N) :
    IsSmoothHerm (stepLine T i) := by
  show ContDiffOn ℝ _ (fun z => ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) _
  exact contDiffOn_prod fun x _ => (hT x).inv fun z hz => ((T x).pos z hz).ne'

def corr {Ψ : Type} {N : ℕ} (T : Ψ × Fin N → HermLine J) : Option (Ψ × Fin N) → HermLine J
  | none => Top.trivLine J
  | some r => stepLine (fun k => T (r.1, k)) r.2

theorem isSmoothHerm_trivLine : IsSmoothHerm (Top.trivLine J) := contDiffOn_const

theorem isSmoothHerm_corr {Ψ : Type} {N : ℕ} {T : Ψ × Fin N → HermLine J} (hT : ∀ r, IsSmoothHerm (T r))
    (a : Option (Ψ × Fin N)) : IsSmoothHerm (corr T a) := by
  cases a with
  | none => exact isSmoothHerm_trivLine
  | some r => exact isSmoothHerm_stepLine (fun k => hT (r.1, k)) r.2

def IsFlatOn {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (T : HermLine J) : Prop :=
  PB.SamePot R.A Set.univ (potOf R T) (ReciprocityTheory.AnForm.M.LocPot.ofFun 0)

def withTop {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (hP : ¬ (⊤ : Ideal (MRing J)) ≤ P)
    (hE : Cmp.IsEmbedded R.A P R.U R.lift) : AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hP
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj z hz _ := hE.surj z hz
  inj x x' _ h := hE.inj x x' h
  immersion x _ p hp j hj := hE.immersion x p hp j hj
  snc f a hf hh hz := R.snc f a hf hh fun z hz' h0 => by
    have h1 := (hz z hz' h0).2 1 trivial
    simp at h1
  null j := by
    have : {x | R.lift x x ∈ mcPts (⊤ : Ideal (MRing J))} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 := h.2 1 trivial
      simp at h1
    rw [this]
    simp

end Lines

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

def pushCpt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀} {i : Ω₀ →+* Ω}
    (hd : Dominates ξ ξ₀ h i) (p : Cpt ξ) : Cpt ξ₀ := ⟨h p.1, hd.specializes p⟩

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def IsRatio (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (bk : K₀ → K)
    (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (φ : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
    ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u ∧
        φ w * ∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

end Points

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

def IsCovOf (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i ∧ 𝔐.f = h ≫ 𝔐₀.f ∧ 𝔐.cst = i.comp 𝔐₀.cst

def FlagsOver {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) : Prop :=
  ∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ

def GenPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) {h : 𝔐.X ⟶ 𝔐₀.X}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) : Prop :=
  ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s (a : Fin (labelRk D s)) (t₀ : Ω₀),
    ((𝔐₀.V s).gr (Fl₀.b s) a).IsGenAt (pushCpt hd q) t₀ → ((𝔐.V s).gr (Fl.b s) a).IsGenAt q (i t₀)

def NormPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω)
    (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) s (a : Fin (labelRk D s)) (t₀ : Ω₀) (ν : ℝ),
    𝔐₀.M.IsGrNorm 𝔐₀.t.PP.L (𝔐₀.V s) (Fl₀.b s) a (z ≫ h) t₀ ν →
      𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) a z (i t₀) ν

end Cover

end GlobalTheory.CompanionTheory.Ar.Chg
