import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

theorem map_actP (B : I → GL (Fin n) K) (F : Pol K I n) :
    MvPolynomial.map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) := by
  have h1 : (MvPolynomial.map φ).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc φ (B τ))).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map φ (trAct B F) = trAct (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) :=
    congrArg (fun ψ : Pol K I n →+* Pol K' I n => ψ F) h1
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

def up (v : VV K lam) : VV K' lam := ⟨MvPolynomial.map φ (v : Pol K I n), GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ v.2⟩

theorem up_sum (a : VVIdx lam → K) (v : VVIdx lam → VV K lam) :
    up φ lam (∑ j, a j • v j) = ∑ j, φ (a j) • up φ lam (v j) := by
  apply Subtype.ext
  simp only [up, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul, map_C]

theorem exists_coord (v : VV K' lam) : ∃ a : VVIdx lam → K', v = ∑ j, a j • up φ lam (bVV K lam j) := by
  have hv : v ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam j
    refine ⟨fun k => φ ((bVV K lam).repr ⟨F, hF⟩ k), ?_⟩
    rw [← up_sum, (bVV K lam).sum_repr]
    exact Subtype.ext ((bVV_coe _ _ _).trans hj)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩

theorem up_rhoVr {E : Type} [Field E] [NumberField E] [NumberField K] [NumberField K'] (emb : I → E →+* K)
    (g : GL (Fin n) E) (v : VV K lam) :
    up φ lam (rhoVr emb lam g v) = rhoVr (fun τ => φ.comp (emb τ)) lam g (up φ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map φ (actP lam (invTrK (embGL emb g)) (v : Pol K I n)) =
    actP lam (invTrK (embGL (fun τ => φ.comp (emb τ)) g)) (MvPolynomial.map φ (v : Pol K I n))
  rw [map_actP]
  rfl

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem equivariant (hE : ∀ v, c' (up φ lam v) = c₀ v) (T : W →ₗ[ℂ] W) (S : VV K lam →ₗ[K] VV K lam)
    (S' : VV K' lam →ₗ[K'] VV K' lam) (hS : ∀ v, up φ lam (S v) = S' (up φ lam v)) (hT : ∀ v, c₀ (S v) = T (c₀ v))
    (v : VV K' lam) : c' (S' v) = T (c' v) := by
  obtain ⟨a, rfl⟩ := exists_coord φ lam v
  simp only [map_sum, map_smul, map_smulₛₗ, ← hS, hE, hT, RingHom.id_apply]

theorem span_top (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hs : Submodule.span ℂ (Set.range fun j => c₀ (bVV K lam j)) = ⊤) : Submodule.span ℂ (Set.range c') = ⊤ := by
  refine top_le_iff.1 (hs ▸ Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨_, hE _⟩

theorem linearIndependent (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {m : ℕ} (b : Fin m → VV K' lam) (hb : LinearIndependent K' b) :
    LinearIndependent ℂ fun j => c' (b j) := by
  classical
  letI : Algebra K' ℂ := σ'.toAlgebra
  choose a ha using fun j => exists_coord φ lam (b j)
  have h1 : LinearIndependent K' a := by
    refine LinearIndependent.of_comp (Fintype.linearCombination K' fun k => up φ lam (bVV K lam k)) ?_
    convert hb using 1
    funext j
    rw [ha j]
    simp [Fintype.linearCombination_apply]
  have h2 : LinearIndependent ℂ fun j => algebraMap K' ℂ ∘ a j := linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k))
    (LinearMap.ker_eq_bot'.2 fun g hg => funext (Fintype.linearIndependent_iff.1 hli g (by simpa [Fintype.linearCombination_apply] using hg)))
  have e : (fun j => c' (b j)) = ⇑(Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k)) ∘ fun j => algebraMap K' ℂ ∘ a j := by
    funext j
    rw [ha j]
    simp only [map_sum, map_smulₛₗ, hE, Function.comp_apply, Fintype.linearCombination_apply]
    rfl
  rw [e]
  exact h3

theorem pairVr_extremal {E : Type} [Field E] [NumberField E] [NumberField K] [StarRing K] (emb : I → E →+* K)
    (v : VV K lam) (hv : (v : Pol K I n) = ten fun τ => extremal K n (lam τ)) : pairVr emb lam 1 v v = 1 := by
  have hG : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have h := pairingExtremal_holds K I n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [polyAction_one₂] at h
  rw [pairVr, pairK_apply, hG, hv, h]

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem inner_of_coefTie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : Formalism.L2.DIV.CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : Formalism.L2.DIV.VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (v w : Formalism.L2.DIV.VV D.what₂.LL lam) :
    inner ℂ (c0 v) (c0 w) = D.what₂.embLL (pair v w) := by
  obtain ⟨e, -, he, hp, -⟩ := h
  have hi := P.coef_pair (e.symm v) (e.symm w)
  rwa [he, he, ← hp, e.apply_symm_apply, e.apply_symm_apply] at hi

set_option maxHeartbeats 800000 in

theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dif_pos hu, hγE, hemb]
    exact CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh

end
