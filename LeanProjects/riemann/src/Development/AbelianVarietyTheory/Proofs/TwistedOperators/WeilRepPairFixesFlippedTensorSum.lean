import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix.Tens

def sumFun {ι κ : Type} {X : ι → Type} {Y : κ → Type} (A : ∀ i, (X i → ℂ) →ₗ[ℂ] ℂ) (B : ∀ k, (Y k → ℂ) →ₗ[ℂ] ℂ) :
    ∀ a : ι ⊕ κ, (Sum.elim X Y a → ℂ) →ₗ[ℂ] ℂ
  | .inl i => A i
  | .inr k => B k

theorem sum_prod_functional_eq {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] ℂ) (B : ∀ k, (Y k → ℂ) →ₗ[ℂ] ℂ) {α : Type} (τ : α →₀ ℂ)
    (f f' : α → ∀ i, X i → ℂ) (g g' : α → ∀ k, Y k → ℂ)
    (h : ∀ (x : ∀ i, X i) (y : ∀ k, Y k), (τ.sum fun d c => c * ((∏ i, f d i (x i)) * ∏ k, g d k (y k))) =
      τ.sum fun d c => c * ((∏ i, f' d i (x i)) * ∏ k, g' d k (y k))) :
    (τ.sum fun d c => c * ((∏ i, A i (f d i)) * ∏ k, B k (g d k))) =
      τ.sum fun d c => c * ((∏ i, A i (f' d i)) * ∏ k, B k (g' d k)) := by
  classical
  let Z : ι ⊕ κ → Type := Sum.elim X Y
  let C : ∀ a : ι ⊕ κ, (Z a → ℂ) →ₗ[ℂ] ℂ := sumFun A B
  let J : (α → ∀ i, X i → ℂ) → (α → ∀ k, Y k → ℂ) → α → ∀ a, Z a → ℂ := fun f g d a =>
    Sum.rec (motive := fun a => Z a → ℂ) (f d) (g d) a
  let M : MultilinearMap ℂ (fun a => ↥(⊤ : Submodule ℂ (Z a → ℂ))) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (ι ⊕ κ) ℂ).compLinearMap fun a => C a ∘ₗ (⊤ : Submodule ℂ (Z a → ℂ)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := Z) (fun _ => ⊤) M τ τ
    (fun d a => ⟨J f g d a, trivial⟩) (fun d a => ⟨J f' g' d a, trivial⟩) (fun z => by
      simp only [Fintype.prod_sum_type]
      exact h (fun i => z (.inl i)) (fun k => z (.inr k)))
  simp only [smul_eq_mul, M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fintype.prod_sum_type] at key
  exact key

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem selfDual_last {i : ℕ} (hi : i ≤ D.R.m) : IsSelfDualC (G.V (.grid D.R.m i)) (G.Λ (.grid D.R.m i)) :=
  (G.isV (X := .grid D.R.m i) ⟨le_rfl, hi⟩ (fun k hk => by
    have := D.R.two_le_m
    simp only [Node.grid.injEq] at hk; omega)).sd

theorem keep_pair {i : ℕ} (hi : i < D.R.m) (a : GA D (G.V (.grid D.R.m i))) (b : GA D (G.V (.grid D.R.m (i + 1))))
    (ha : Lev.finE (G.V (.grid D.R.m i)) a ∈ G.levMax (.grid D.R.m i)) (hb : Lev.finE (G.V (.grid D.R.m (i + 1))) b ∈ G.levMax (.grid D.R.m (i + 1)))
    (u : WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) :
    u ∈ latO _ _ (G.Λ (.grid D.R.m i) : Set _) (G.Λ (.grid D.R.m (i + 1)) : Set _) (fun _ => True) ↔
      actO _ _ a b u ∈ latO _ _ (G.Λ (.grid D.R.m i) : Set _) (G.Λ (.grid D.R.m (i + 1)) : Set _) (fun _ => True) := by
  have sdS := selfDual_last (G := G) hi.le
  have sdT := selfDual_last (G := G) (i := i + 1) hi
  obtain ⟨βT, hβT⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdT.1.fg sdT.1.span_eq_top
  obtain ⟨βS, hβS⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdS.1.fg sdS.1.span_eq_top
  have keep : ∀ {V : HSp D} (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
      Formalism.L2.DIV.IsFrame β Λ → ∀ X : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      X ∈ congLev D.sp.cm V.gram Λ ⊤ → X ∈ Formalism.L2.DIV.St β := by
    intro V Λ β hβ X hX
    rw [congLev_top] at hX
    have hst := (Subgroup.mem_inf.1 hX).2
    have hst' := (Subgroup.mem_inf.1 (inv_mem hX)).2
    exact (GlobalTheory.LevSplit.mem_St_iff β Λ hβ X).2 ⟨fun v hv => (hst v).1 hv, fun v hv => (hst' v).1 hv⟩
  exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ _ _ _ βS βT sdS sdT hβS hβT a b (keep _ βS hβS _ ha) (keep _ βT hβT _ hb) u

theorem vT_ne_zero {W : G.Weil} (ρ : RealMatch W) (t : T) {i : ℕ} (hi : i < D.R.m) : ρ.vT D.R.m i ≠ 0 := by
  intro h0
  obtain ⟨⟨p, hp⟩, hn⟩ := (ρ.vT_is t D.R.m i le_rfl hi).2.norm
  have := hn p hp
  simp [nrm2, h0] at this

theorem sum_om_eq {W : G.Weil} (ρ : RealMatch W) (t : T) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (τ : SchRow G × SchDown G t →₀ ℂ) (φ : SchRow G × SchDown G t → SchRow G × SchDown G t)
    (hloc : ∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) ((φ d).2 j) (d.2 j))
    (h : Pts G) (hh : ∀ i, Lev.finE (G.V (.grid D.R.m i)) (h i) ∈ G.levMax (.grid D.R.m i)) (c : Fin D.R.m → ℂ)
    (hc : ∀ i : Fin D.R.m, W.om (.mu t D.R.m i) (h i, h (i + 1)) (ρ.vT D.R.m i) = c i • ρ.vT D.R.m i)
    (hsum : ∀ (x : RowPt G) (y : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))),
      (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i : Fin D.R.m, c i * (φ d).2 i (actO _ _ (h i)⁻¹ (h (i + 1))⁻¹ (y i)))) =
        τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (y i)))
    (y : RowPt G) (v : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) :
    (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, W.om (.mu t D.R.m i) (h i, h (i + 1)) (d.2 i) (v i))) =
      τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i)) := by
  classical
  let P : ∀ (p : Pair T) (f₀ : WO (G.pS p) (G.pT p) → ℂ), ((WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ)) → Prop :=
    fun p f₀ => IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀
  have hP : ∀ (p : Pair T) (f₀ f₁ f : WO (G.pS p) (G.pT p) → ℂ), IsLocVec W p e f₀ f₁ f →
      P p f₀ (Classical.epsilon (P p f₀)) ∧ f = Classical.epsilon (P p f₀) f₁ := fun p f₀ f₁ f hf =>
    have hs := Classical.epsilon_spec hf.2.1
    ⟨hs, hf.2.2 _ hs⟩
  have key := sum_prod_functional_eq
    (X := fun n : Fin D.R.m => WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T)))
    (Y := fun i : Fin D.R.m => WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1))))
    (fun n => LinearMap.proj (y n) ∘ₗ Classical.epsilon (P (.chi n D.R.m) (ρ.vX n D.R.m)))
    (fun i => LinearMap.proj (v i) ∘ₗ Classical.epsilon (P (.mu t D.R.m i) (ρ.vT D.R.m i))) τ
    (fun d => (φ d).1) (fun d => (φ d).1)
    (fun d i => c i • fun u => (φ d).2 i (actO _ _ (h i)⁻¹ (h (i + 1))⁻¹ u)) (fun d => (φ d).2) hsum
  have hrow : ∀ d ∈ τ.support, ∀ n : Fin D.R.m, d.1 n (y n) =
      (LinearMap.proj (y n) ∘ₗ Classical.epsilon (P (.chi n D.R.m) (ρ.vX n D.R.m))) ((φ d).1 n) := fun d hd n =>
    congrFun (hP _ _ _ _ ((hloc d hd).1 n)).2 _
  refine Eq.trans (Finsupp.sum_congr fun d hd => ?_) (key.trans (Finsupp.sum_congr fun d hd => ?_))
  · refine congrArg _ (congrArg₂ _ (Finset.prod_congr rfl fun n _ => hrow d hd n) (Finset.prod_congr rfl fun i _ => ?_))
    have hl := (hloc d hd).2 i
    exact congrFun (GlobalTheory.RowVertexInv.FactorTheta.om_theta_eq (W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩) hee hinf
      (selfDual_last i.2.le) (selfDual_last (i := i + 1) i.2) (ρ.vT_is t D.R.m i le_rfl i.2).2.theta (h i, h (i + 1))
      (keep_pair i.2 _ _ (hh _) (hh _))
      (GlobalTheory.RowVertexInv.FactorTheta.scalar_ne_zero (p := .mu t D.R.m i) _ (vT_ne_zero ρ t i.2) (hc i)) (hc i)
      (hP _ _ _ _ hl).1 hl.2) (v i)
  · refine congrArg _ (congrArg₂ _ (Finset.prod_congr rfl fun n _ => (hrow d hd n).symm) (Finset.prod_congr rfl fun i _ => ?_))
    exact (congrFun (hP _ _ _ _ ((hloc d hd).2 i)).2 (v i)).symm

theorem actO_one_one (S T' : HSp D) (u : WO S T') : actO S T' 1 1 u = u := by
  unfold actO
  rw [inv_one]
  exact (Matrix.mul_one _).trans (Matrix.one_mul _)

theorem movY_eq (j : ℕ) (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1)))) (i : Fin D.R.m) :
    GlobalTheory.RowKFix.movY G j hj k y i =
      actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) i)⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (i + 1))⁻¹ (y i) := by
  let B : Fin D.R.m → Type := fun i => Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank
  by_cases h2 : i = ⟨j + 1, by omega⟩
  · subst h2
    refine (Function.update_self (β := B) _ _ _).trans ?_
    have e1 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1) = k := Pi.mulSingle_eq_same _ _
    have e2 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1 + 1) = 1 := Pi.mulSingle_eq_of_ne (by omega) _
    change _ = actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1))⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1 + 1))⁻¹ _
    rw [e1, e2, inv_one]
  refine (Function.update_of_ne (β := B) h2 _ _).trans ?_
  by_cases h1 : i = ⟨j, by omega⟩
  · subst h1
    refine (Function.update_self (β := B) _ _ _).trans ?_
    have e1 : (Pi.mulSingle (j + 1) k : Pts G) (j + 1) = k := Pi.mulSingle_eq_same _ _
    have e2 : (Pi.mulSingle (j + 1) k : Pts G) j = 1 := Pi.mulSingle_eq_of_ne (by omega) _
    change _ = actO _ _ ((Pi.mulSingle (j + 1) k : Pts G) j)⁻¹ ((Pi.mulSingle (j + 1) k : Pts G) (j + 1))⁻¹ _
    rw [e1, e2, inv_one]
  refine (Function.update_of_ne (β := B) h1 _ _).trans ?_
  have e1 : (Pi.mulSingle (j + 1) k : Pts G) i = 1 := Pi.mulSingle_eq_of_ne (fun h => h2 (Fin.ext h)) _
  have e2 : (Pi.mulSingle (j + 1) k : Pts G) (i + 1) = 1 :=
    Pi.mulSingle_eq_of_ne (fun h => h1 (Fin.ext (Nat.succ_injective h))) _
  rw [e1, e2, inv_one, inv_one, actO_one_one]

theorem sum_om_single_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∀ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j → ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) → (∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (y : RowPt ch.G) (v : ∀ i : Fin D.R.m, WO (ch.G.V (.grid D.R.m i)) (ch.G.V (.grid D.R.m (i + 1)))), (τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i : Fin D.R.m, ch.W.om (.mu t D.R.m i) ((Pi.mulSingle (j + 1) k : Pts ch.G) i, (Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1)) (d.2 i) (v i))) = τ.sum fun d x => x * ((∏ n, d.1 n (y n)) * ∏ i, d.2 i (v i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ t Φ τ hτ j hj k hk c₁ c₂ h₁ h₂ hT y v
  classical
  obtain ⟨e, he, φ, hloc, hid⟩ := hτ
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, by omega⟩ := by simp
  let c : Fin D.R.m → ℂ := fun i => (Pi.mulSingle (⟨j, by omega⟩ : Fin D.R.m) c₁ : Fin D.R.m → ℂ) i *
    (Pi.mulSingle (⟨j + 1, by omega⟩ : Fin D.R.m) c₂ : Fin D.R.m → ℂ) i
  have hprod : ∏ i, c i = c₁ * c₂ := by
    simp only [c]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']
  have e1 : (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1) = k := Pi.mulSingle_eq_same _ _
  refine sum_om_eq ch.rm t (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) τ φ hloc
    (Pi.mulSingle (j + 1) k) (fun i => ?_) c (fun i => ?_) (fun x z => ?_) y v
  · by_cases hi : i = j + 1
    · subst hi
      rw [e1]
      exact (Subgroup.mem_inf.1 hk).2
    · rw [Pi.mulSingle_eq_of_ne hi, MonoidHom.map_one]
      exact one_mem _
  · by_cases h2 : i = ⟨j + 1, by omega⟩
    · subst h2
      have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1 + 1) = 1 := Pi.mulSingle_eq_of_ne (by omega) _
      have e3 : c ⟨j + 1, by omega⟩ = c₂ := by simp [c, Pi.mulSingle_apply]
      rw [e3]
      change ch.W.om (.mu t D.R.m (j + 1)) ((Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1),
        (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1 + 1)) _ = _
      rw [e1, e2]
      exact h₂
    by_cases h1 : i = ⟨j, by omega⟩
    · subst h1
      have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) j = 1 := Pi.mulSingle_eq_of_ne (by omega) _
      have e3 : c ⟨j, by omega⟩ = c₁ := by simp [c, Pi.mulSingle_apply]
      rw [e3]
      change ch.W.om (.mu t D.R.m j) ((Pi.mulSingle (j + 1) k : Pts ch.G) j,
        (Pi.mulSingle (j + 1) k : Pts ch.G) (j + 1)) _ = _
      rw [e1, e2]
      exact h₁
    have e2 : (Pi.mulSingle (j + 1) k : Pts ch.G) i = 1 := Pi.mulSingle_eq_of_ne (fun h => h2 (Fin.ext h)) _
    have e3 : (Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1) = 1 :=
      Pi.mulSingle_eq_of_ne (fun h => h1 (Fin.ext (Nat.succ_injective h))) _
    have e4 : c i = 1 := by simp [c, Pi.mulSingle_apply, h1, h2]
    have e5 : ch.W.om (.mu t D.R.m i) (1, 1) = 1 := map_one _
    rw [e2, e3, e4, e5, one_smul]
    rfl
  · have hL : (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i : Fin D.R.m, c i * (φ d).2 i
        (actO _ _ ((Pi.mulSingle (j + 1) k : Pts ch.G) i)⁻¹ ((Pi.mulSingle (j + 1) k : Pts ch.G) (i + 1))⁻¹ (z i)))) =
        c₁ * c₂ * τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (GlobalTheory.RowKFix.movY ch.G j hj k z i) := by
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun d _ => ?_
      rw [Finset.prod_mul_distrib, hprod, Finset.prod_congr rfl fun i _ => congrArg ((φ d).2 i) (movY_eq j hj k z i)]
      ring
    have hR : (τ.sum fun d a => a * ((∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z i))) =
        τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z i) :=
      Finsupp.sum_congr fun d _ => (mul_assoc _ _ _).symm
    have hmov : ∀ i, IsHalf e (GlobalTheory.RowKFix.movY ch.G j hj k z i) ↔ IsHalf e (z i) := fun i => by
      rw [movY_eq]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    have hzero : ∀ z' : ∀ i : Fin D.R.m, WO (ch.G.V (.grid D.R.m i)) (ch.G.V (.grid D.R.m (i + 1))),
        ¬ ((∀ n, IsHalf e (x n)) ∧ ∀ i, IsHalf e (z' i)) →
        (τ.sum fun d a => a * (∏ n, (φ d).1 n (x n)) * ∏ i, (φ d).2 i (z' i)) = 0 := by
      intro z' hz'
      refine Finset.sum_eq_zero fun d hd => ?_
      by_contra h0
      obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 h0
      exact hz' ⟨fun n => ((hloc d hd).1 n).1.1 _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul ha) n (Finset.mem_univ _)),
        fun i => ((hloc d hd).2 i).1.1 _ (Finset.prod_ne_zero_iff.1 hb i (Finset.mem_univ _))⟩
    refine hL.trans (Eq.trans ?_ hR.symm)
    by_cases hall : (∀ n, IsHalf e (x n)) ∧ ∀ i, IsHalf e (z i)
    · rw [hid x z hall.1 hall.2, hid x _ hall.1 fun i => (hmov i).2 (hall.2 i)]
      exact hT x z
    · rw [hzero z hall, hzero _ fun h => hall ⟨h.1, fun i => (hmov i).1 (h.2 i)⟩, mul_zero]

end GlobalTheory.RowKFix.Tens

end
