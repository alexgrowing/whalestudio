import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCmComplexOfPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeRational

open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open scoped TensorProduct

theorem repr_mem_of_basis_rational {K V ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (F : Subfield K) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) (h : ∀ i j, b'.repr (b i) j ∈ F)
    (v : V) (hv : ∀ j, b'.repr v j ∈ F) (i : ι) : b.repr v i ∈ F := by
  obtain ⟨φ, h1, h2⟩ := FormsDescent.exists_retraction F
  have e2 : FormsDescent.coordMap F b' φ v = v := by
    apply b'.repr.injective
    ext j
    rw [FormsDescent.repr_coordMap, h2 _ (hv j)]
  have key : v = ∑ a, φ (b.repr v a) • b a := by
    rw [← FormsDescent.coordMap_sum F b' φ _ _ h, b.sum_repr, e2]
  have : b.repr v i = φ (b.repr v i) := by
    conv_lhs => rw [key]
    rw [b.repr_sum_self]
  rw [this]
  exact h1 _

theorem repr_map_mem {K V κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype κ]
    (F : Subfield K) (b : Module.Basis κ K V) (g : V →ₗ[K] V) (hg : ∀ i j, b.repr (g (b j)) i ∈ F)
    (v : V) (hv : ∀ j, b.repr v j ∈ F) (i : κ) : b.repr (g v) i ∈ F := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [h1]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hv j) (hg i j)

theorem levFn_isOfFinOrder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    IsOfFinOrder (levFn β L x) := by
  have hfin : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hone : IsOfFinOrder (1 : ℂˣ) := IsOfFinOrder.one
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact hone
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun c _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

variable {D : D7}

theorem levEnv_chi_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).χ k ^ n = 1 :=
  isOfFinOrder_iff_pow_eq_one.1 (levFn_isOfFinOrder β (Lev.flag1L L) _)

theorem embE_mem_cmMax (x : D.host.E) : D.embE x ∈ cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

theorem labLL_mem_cmMax (τ : D.what₂.Tau) (x : D.host.E) : labLL D τ x ∈ cmMax D.what₂.LL := embE_mem_cmMax _

theorem action_rational (V : TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL) (γ : GQ V) (j : S.ιV) :
    ∃ c : S.ιV → D.what₂.LL, (∀ i, c i ∈ cmMax D.what₂.LL) ∧
      C.ρ γ (P.coef (S.bV j)) = ∑ i, D.what₂.embLL (c i) • P.coef (S.bV i) := by
  obtain ⟨e, hr, he, -⟩ := hP
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  refine ⟨fun i => (S.bV.map e).repr (rho γE (e (S.bV j))) i, fun i => ?_, ?_⟩
  · exact repr_mem_of_basis_rational _ (S.bV.map e) (bVV D.what₂.LL lam) hr _
      (repr_map_mem _ _ _ (hrho γE) _ (hr j)) i
  · rw [he, ← hM.1 γ γE hγ]
    conv_lhs => rw [← (S.bV.map e).sum_repr (rho γE (e (S.bV j)))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, LinearMap.map_smulₛₗ, Module.Basis.map_apply]

theorem dcOp_matrix_mem_cmMax (V : TH.HSp D) (C : CoefDat D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {S : CSD D.what₂.LL}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ (levEnv V β L).J (levEnv V β L).χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL)
    (B : Finset (Gf V)) (T : Module.End D.what₂.LL S.Forms)
    (hT : ∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) :
    S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax D.what₂.LL :=
  GlobalTheory.classPres_dcOp_rat (ratF V) S D.what₂.embLL C.ρ _ _ P B T D.starLL_cx (levEnv_chi_pow V β L)
    (action_rational V C P hP hM hrho) hT

theorem toMatrix_one_mem {K M ι : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι] (F : Subfield K)
    (b : Module.Basis ι K M) (i j : ι) : LinearMap.toMatrix b b (1 : Module.End K M) i j ∈ F := by
  rw [LinearMap.toMatrix_one, Matrix.one_apply]
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (t : T) (B : Finset (Gf D.sp.X'))
    (U : Module.End D.what₂.LL (A.MtildeCSD t).Forms)
    (hU : ∀ f : (A.MtildeCSD t).Forms, (R.B.R t).pres.ext (U f).1 = dcOp B ((R.B.R t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres (hT.coefR t) hT.mapR
    (fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i j).1) B U hU).2 a b

theorem lifts_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (j : Fin D.R.m) (t : T) (B : Finset (Gf (Vc D j)))
    (U : Module.End D.what₂.LL (A.MtCSD j t).Forms)
    (hU : ∀ f : (A.MtCSD j t).Forms, (R.B.L j t).pres.ext (U f).1 = dcOp B ((R.B.L j t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres (hT.coefL j t) (hT.mapL j)
    (fun g i k => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i k).2) B U hU).2 a b

theorem hecke_opMat_mem_cmMax : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → (∀ t i a b, (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL) ∧ ∀ j t i a b, (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC
  refine ⟨fun t i a b => ?_, fun j t i a b => ?_⟩
  · obtain ⟨P, k⟩ := i
    show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(hC.fam.degR t P).1]
      exact toMatrix_one_mem _ _ _ _
    rcases le_or_gt k D.sp.X'.rank with hk' | hk'
    · exact rows_dcOp_mem_cmMax R hC.fam.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
    · rw [(hC.fam.degR t P).2 k hk', map_zero]
      exact Subfield.zero_mem _
  · obtain ⟨P, k⟩ := i
    show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(hC.fam.degL j t P).1]
      exact toMatrix_one_mem _ _ _ _
    rcases le_or_gt k (Vc D j).rank with hk' | hk'
    · exact lifts_dcOp_mem_cmMax R hC.fam.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
    · rw [(hC.fam.degL j t P).2 k hk', map_zero]
      exact Subfield.zero_mem _

end GlobalTheory.HeckeRational

end
