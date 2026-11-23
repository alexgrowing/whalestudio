import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {fc : DefSub A → DefFace Bs}

structure RefInputs (X : CxData A) (cr : Crd A fc) : Prop where

  M_lat : ∀ j, Submodule.IsLattice K (X.M false j)

  T_lat : ∀ j, Submodule.IsLattice K ((lv (fc X.zs) false).Tl j Bs.μ0)

  form_nondeg : ∀ j, ((lv (fc X.zs) false).HT j Bs.μ0).det ≠ 0

  w_inj : ∀ j, Function.Injective (X.w0C false j)

  theta_inj : ∀ j, Function.Injective (X.tC cr false j Bs.μ0)

  theta_range : ∀ j, LinearMap.range (X.tC cr false j Bs.μ0) = LinearMap.range (X.w0C false j)

  theta_rat : ∀ j, IsRat Bs.v0.embedding (X.liftMatC cr false j Bs.μ0)

def ContentSupport (N : IndefNum Bs) (X'' : ℝ) (d g₁ g₂ : ℕ) : Prop :=
  ∀ w j, N.F0 w j ≠ 0 → (plc w : ℝ) ≤ X'' ∨ plc w = d ∨ plc w = g₁ ∨ plc w = g₂

def retuple (X : CxData A) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (Tw : Finset (HeightOneSpectrum (𝓞 K))) : CxData A :=
  { X with μ := μ, Tw := Tw }

def TwistChoice (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (tw : HeightOneSpectrum (𝓞 K) → Bs.Tup) : Prop :=
  (∀ w, X.W1 cr N w → tw w ≠ Bs.μ0) ∧ ∀ w, X.W1 cr N w → tw (conjPl w) = tw w

def FinAt (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) : Prop :=
  {w | X.W1 cr N w}.Finite ∧ (∀ w, X.W1 cr N (conjPl w) ↔ X.W1 cr N w) ∧
    ∀ tw, TwistChoice X cr N tw →
      ∃ (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (Tw : Finset (HeightOneSpectrum (𝓞 K))), (retuple X μ Tw).MuDef cr N tw

def FinLemma : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (fc : DefSub A → DefFace Bs)
    (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (X'' : ℝ) (d g₁ g₂ : ℕ),
    RefInputs X cr → ContentSupport N X'' d g₁ g₂ → FinAt X cr N

theorem W1_retuple (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup)
    (Tw : Finset (HeightOneSpectrum (𝓞 K))) (w : HeightOneSpectrum (𝓞 K)) :
    (retuple X μ Tw).W1 cr N w ↔ X.W1 cr N w := Iff.rfl

def FiveSet (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ j, (X.data cr false).Iw j Bs.μ0 w ≠ 0 ∨ (X.data cr false).Iw j Bs.μ0 (conjPl w) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT j Bs.μ0) w ((lv (fc X.zs) false).Tl j Bs.μ0) ≠ 0 ∨ N.F0 w j ≠ 0 ∨ N.F0 (conjPl w) j ≠ 0

theorem W1_iff_fiveSet_or_fiveSet_conjPl (X : CxData A) (cr : Crd A fc) (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) :
    X.W1 cr N w ↔ FiveSet X cr N w ∨ FiveSet X cr N (conjPl w) := by
  unfold CxData.W1 FiveSet
  rw [ValuationRepresentative.conjPl_conjPl]
  constructor
  · rintro ⟨j, h | h | h | h | h | h⟩
    · exact Or.inl ⟨j, Or.inl h⟩
    · exact Or.inl ⟨j, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inr ⟨j, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact Or.inl ⟨j, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩
  · rintro (⟨j, h⟩ | ⟨j, h⟩) <;> exact ⟨j, by tauto⟩

theorem refInputs_of_links (X : CxData A) (cr : Crd A fc) (wf : (lv (fc X.zs) false).WF) (hM : X.MLat false)
    (hK : X.KForm false) (hE : X.EWnorm false) (hp : X.H4pos) (h5 : X.H5 cr false) (hr : X.RATth cr false) :
    RefInputs X cr where
  M_lat := hM
  T_lat j := wf.Tl_lat j _
  form_nondeg j := by
    obtain ⟨hu, he⟩ := wf.XT_herm j Bs.μ0
    intro h0
    have h1 : (((lv (fc X.zs) false).HT j Bs.μ0).map Bs.v0.embedding).det = 0 := by
      have := (Bs.v0.embedding).map_det ((lv (fc X.zs) false).HT j Bs.μ0)
      rw [h0, map_zero] at this
      exact this.symm
    rw [← he, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    have h2 : (((lv (fc X.zs) false).XT j Bs.μ0 Bs.v0)⁻¹).det ≠ 0 :=
      (Matrix.isUnit_nonsing_inv_det _ (hu Bs.v0)).ne_zero
    exact mul_ne_zero (star_ne_zero.2 h2) h2 h1
  w_inj j := by
    have hw : Function.Injective (X.wC false j Bs.v0) :=
      by
        rw [injective_iff_map_eq_zero]
        intro c hc
        have hc' : ∑ i, c i • X.bW false j Bs.v0 i = 0 := by
          simpa [CxData.wC, lin, Fintype.linearCombination_apply] using hc
        funext i
        exact Fintype.linearIndependent_iff.1 (hK j Bs.v0).1 c hc' i
    have he : Function.Injective (X.eW false j) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h := hE j x x
      rw [hx, inner_zero_left] at h
      have hn : ((X.nP false : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp.2.2 false).ne'
      exact inner_self_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left hn)
    exact he.comp hw
  theta_inj j := (h5 j _).1
  theta_range j := (h5 j _).2
  theta_rat j := hr j _

namespace Examples₂

variable (K) (v0 : InfinitePlace K)

def base : DefBase K := ⟨⊤, v0, Bool, false, Unit, inferInstance, Unit, inferInstance⟩

def stdLat : Submodule (𝓞 K) (Fin 1 → K) := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin 1)))

omit [StarRing K] in
theorem stdLat_isLattice : Submodule.IsLattice K (stdLat K) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin 1)).span_eq]
    exact Submodule.span_mono Submodule.subset_span

def amb : DefAmb (base K v0) :=
  ⟨fun _ => K, fun _ => inferInstance, fun _ => inferInstance, fun _ => Unit, fun _ _ => 1, fun _ => ⊤,
    fun _ _ => K, fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ => Unit, fun _ _ _ => 1, fun _ _ => ⊤⟩

def side : DefSide (base K v0) :=
  ⟨fun _ => 1, fun _ => 1, fun _ => stdLat K, fun _ => 1, fun _ => 1, fun _ _ => 1, fun _ _ => ⊤,
    fun _ _ => 1, fun _ _ => 2, fun _ _ _ => 1, fun _ _ => stdLat K, fun _ _ _ => ⊤⟩

def face : DefSub (amb K v0) → DefFace (base K v0) := fun _ =>
  ⟨side K v0, side K v0, ⟨Empty, fun _ => 0, fun u => u.elim, fun u => u.elim⟩,
    ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊤⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

def crd : Crd (amb K v0) (face K v0) where
  toR _ b _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
  toL _ b _ _ := match b with
    | false => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)
    | true => (LinearMap.proj 0 : (Fin 1 → K) →ₗ[K] K)

def cx : CxData (amb K v0) where
  FC _ := ℂ
  jR _ := v0.embedding.toSemilinearMap
  EE := ℂ
  Θ _ := LinearMap.id
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := ℂ
  jL _ _ := v0.embedding.toSemilinearMap
  W _ := ℂ
  θ' _ _ := LinearMap.id
  Wp _ _ := ⊤
  dW _ _ := 1
  WC _ _ _ := ℂ
  bW _ _ _ _ := 1
  eW _ _ := LinearMap.id
  M _ _ := stdLat K
  nP _ := 1
  μ _ := false
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0

theorem lin_one_inj : Function.Injective (lin (fun _ : Fin 1 => (1 : ℂ))) := by
  intro x y h
  funext i
  fin_cases i
  simpa [lin, Fintype.linearCombination_apply] using h

theorem exampleTwistChoice_w0C (j : Unit) : (cx K v0).w0C false j = lin (fun _ : Fin 1 => (1 : ℂ)) := rfl

theorem tC_eq (j : Unit) : (cx K v0).tC (crd K v0) false j false = lin (fun _ : Fin 1 => (1 : ℂ)) := by
  change lin (fun k : Fin 1 => v0.embedding ((Pi.single k (1 : K) : Fin 1 → K) 0)) = _
  congr 1
  funext k
  fin_cases k
  simp

theorem refInputs : RefInputs (cx K v0) (crd K v0) where
  M_lat _ := stdLat_isLattice K
  T_lat _ := stdLat_isLattice K
  form_nondeg _ := by
    change (2 : Matrix (Fin 1) (Fin 1) K).det ≠ 0
    rw [Matrix.det_unique]
    change ((2 : ℕ) : Matrix (Fin 1) (Fin 1) K) default default ≠ 0
    simp [Matrix.natCast_apply, Matrix.ofNat_apply]
  w_inj j := lin_one_inj
  theta_inj j := (tC_eq K v0 j).symm ▸ lin_one_inj
  theta_range j := congrArg LinearMap.range (tC_eq K v0 j)
  theta_rat j := by
    intro i k
    have h : (cx K v0).liftMatC (crd K v0) false j false =
        relMat (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ))) :=
      congrArg (relMat (lin (fun _ : Fin 1 => (1 : ℂ)))) (tC_eq K v0 j)
    have h1 : ∀ y, solve (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ)) y) = y := by
      intro y
      have he : ∃ z, lin (fun _ : Fin 1 => (1 : ℂ)) z = lin (fun _ : Fin 1 => (1 : ℂ)) y := ⟨y, rfl⟩
      unfold solve
      rw [dif_pos he]
      exact lin_one_inj he.choose_spec
    have h2 : ∀ i k : Fin 1, relMat (lin (fun _ : Fin 1 => (1 : ℂ))) (lin (fun _ : Fin 1 => (1 : ℂ))) i k = 1 := by
      intro i k
      rw [relMat, Matrix.of_apply, h1, Subsingleton.elim i k, Pi.single_eq_same]
    exact ⟨1, (map_one _).trans ((h2 i k).symm.trans (congrFun (congrFun h i) k).symm)⟩

end Examples₂

end GlobalTheory.IndefiniteRowSideFullHecke.TwistChoiceExample
