import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EgEqStep

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g k : G') :
    RealDat.eC (A := A) D.what₂.embLL (g * k * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL k := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  rw [e, e, show σ.symm (g * k * g⁻¹) = σ.symm g * σ.symm k * (σ.symm g)⁻¹ by simp, GlobalTheory.ProjComm.goodProjector_coeff_classFunction]

theorem eC_conv_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g : G') :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  simp only [e]
  rw [← GlobalTheory.ProjectedLift.conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (σ.symm g), star_sum]
  refine Fintype.sum_equiv σ.symm.toEquiv _ _ fun a => ?_
  show _ = star (D.ntypes.e0.coeff (σ.symm a) * D.ntypes.e0.coeff ((σ.symm a)⁻¹ * σ.symm g))
  rw [star_mul', map_mul, map_inv]

theorem goodProjector_maps_rows_into_goodRows {R : RealDat D A Ks} {F : Face D A} (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf)
    {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) {S : MMap (MP R)} (hS : S ∈ MultR R F) :
    postOn (MP R) R.e0 S ∈ EP R F := by
  have hX : S ∈ GlobalTheory.Mem.Th.multAt R (R.levR F true) A.μ0 0 := by
    rw [GlobalTheory.Mem.Th.multAt_zero]; exact hS
  have h0 := GlobalTheory.Mem.Th.multAt_le R _ A.μ0 0 hX
  rw [GlobalTheory.Mem.Th.multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 S ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (eC_conv_of_match hC) h0
  refine ⟨GlobalTheory.KeepLevel.mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (S v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 h0).lev v
  refine GlobalTheory.KeepLevel.hasType_of_comm (L := R.dat0 R.triv) (P := R.levR F true) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hX).lev v)
    fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact GlobalTheory.ProjComm.gaL_comm (L := R.dat0 R.triv) R.eG _ (eC_conj_of_match hC) g a0

set_option maxHeartbeats 1000000 in

theorem evalOn_good : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c hl hi hv hsee hJe
  obtain ⟨σ, red, hA, hB, hC⟩ := hsee.mat
  obtain ⟨J, hJ⟩ := hJe
  have hle : EP R F ≤ MultR R F := inf_le_left
  have hmult : ∀ S ∈ MultR R F, IsMultMap R.θ (MP R) (JR R F) (chiR R F) S := fun S hS =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hS
  have hGQ : ∀ S ∈ MultR R F, ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := fun S hS =>
    ((hmult S hS).aut v₀).left
  choose s0 hs0 using hB.1.2.2.1
  have hs0' : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ := hs0

  have hinv : ∀ S : MultR R F, ∀ k ∈ X.B.I.Kg X.B.g,
      X.B.R (1, k) (star ((J S : conjRows X) : L2X X)) = star ((J S : conjRows X) : L2X X) := by
    intro S k hk
    classical
    have hkK : k ∈ X.B.I.Kset := hk.1
    have hrk : red k = 1 := (hB.1.2.2.2 k hkK).2 hk
    let a : G0g D.nd → ℂ := fun γ => if γ = 1 then 1 else 0
    let s : G0g D.nd → X.B.I.Gf := fun γ => if γ = 1 then k else s0 γ
    have hs : ∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ := by
      intro γ
      by_cases hγ : γ = 1
      · subst hγ
        simp only [s, if_pos rfl]
        exact ⟨hkK, hrk⟩
      · simp only [s, if_neg hγ]
        exact hs0' γ
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) a s hs
    have e1 : (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star ((J S : conjRows X) : L2X X))) : L2X X) =
        star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) := by
      rw [Finset.sum_eq_single (1 : G0g D.nd)]
      · simp [a, s]
      · intro b _ hb
        simp [a, hb]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have hsum : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) =
        actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) := by
      unfold gaL
      rw [Finset.sum_eq_single (1 : G')]
      · have ha1 : a (σ.symm 1) = 1 := by simp [a]
        simp only [ha1, star_one, one_smul]
        rfl
      · intro b _ hb
        have hb' : σ.symm b ≠ 1 := by
          intro h1
          apply hb
          simpa using congrArg σ h1
        have ha0 : a (σ.symm b) = 0 := by simp [a, hb']
        simp only [ha0, star_zero, zero_smul]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have e2 : ∀ y : GA D (D.sp.Y 0),
        (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) ((S : MMap (MP R)) v₀) y =
          (S : MMap (MP R)) v₀ y := by
      intro y
      rw [hsum]
      have hB2 := hB.2 k hkK (S : MMap (MP R)) S.2 v₀ y
      rw [hrk, map_one σ] at hB2
      refine hB2.symm.trans ?_
      have hK2 := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
      obtain ⟨hkJ, hkχ⟩ := hA k hK2.1
      have hχ1 : chiR R F (kap X h t k) = 1 := hkχ.trans (by rw [hK2.2, star_one])
      refine ((hmult _ S.2).lev v₀ _ hkJ y).trans ?_
      rw [hχ1, one_mul]
    have e3 : ((star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
        (((J S : conjRows X) : L2X X) : X.B.I.GA → ℂ) := by
      rw [← e1]
      exact hI.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => e2 _) (hJ S).1.symm)
    have e4 := congrArg star (Lp.ext e3)
    rwa [star_star] at e4

  have key : ∀ S : MultR R F,
      ((J ⟨postOn (MP R) R.e0 S, hle (goodProjector_maps_rows_into_goodRows hl hi hC S.2)⟩ : conjRows X) : L2X X) =
        star (G.Rg (star ((J S : conjRows X) : L2X X))) := by
    intro S
    have hexp := GlobalTheory.Mem.GoodExpand.rg_expand D X G red s0 hB.1 hs0' _ (hinv S)
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) (fun γ => D.ntypes.e0.coeff γ) s0 hs0'
    have e1 : star (G.Rg (star ((J S : conjRows X) : L2X X))) = ∑ γ, star (D.ntypes.e0.coeff γ) •
        star (X.B.R (1, s0 γ) (star ((J S : conjRows X) : L2X X))) := by
      rw [hexp]
      change conjL (muX X) _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, starRingEnd_apply]
    have e2 : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (D.ntypes.e0.coeff (σ.symm g))) = R.e0 := by
      unfold RealDat.e0
      congr 1
      funext g
      rw [hC, MulEquiv.apply_symm_apply]
    rw [e1]
    apply Lp.ext
    refine (hJ _).1.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) hI.symm)
    rw [e2]
    rfl
  have hEPS : ∀ S : MultR R F, (S : MMap (MP R)) ∈ EP R F ↔ postOn (MP R) R.e0 S = S := by
    intro S
    constructor
    · intro hS
      exact sub_eq_zero.1 (LinearMap.mem_ker.1 hS.2)
    · intro e
      exact ⟨S.2, LinearMap.mem_ker.2 (sub_eq_zero.2 e)⟩
  have hconj : ∀ Fx : L2X X, Fx ∈ EEC X G → Fx ∈ conjRows X := fun Fx hF => (Submodule.mem_inf.1 hF).1
  let L0 : EP R F →ₗ[ℂ] L2X X :=
    (conjRows X).subtype ∘ₗ (J : MultR R F →ₗ[ℂ] conjRows X) ∘ₗ Submodule.inclusion hle
  have hL0 : ∀ S : EP R F, L0 S ∈ EEC X G := by
    intro S
    have hS1 : postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F) = (Submodule.inclusion hle S : MultR R F) :=
      (hEPS _).1 S.2
    have k1 := key (Submodule.inclusion hle S)
    have e : (⟨postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F),
        hle (goodProjector_maps_rows_into_goodRows hl hi hC (Submodule.inclusion hle S).2)⟩ : MultR R F) = Submodule.inclusion hle S :=
      Subtype.ext hS1
    rw [e] at k1
    have k2 : G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) =
        star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) := by
      have k3 := congrArg star k1
      rw [star_star] at k3
      exact k3.symm
    refine Submodule.mem_inf.2 ⟨(J (Submodule.inclusion hle S)).2, LinearMap.mem_ker.2 ?_⟩
    change G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) -
      star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) = 0
    rw [k2, sub_self]
  let L : EP R F →ₗ[ℂ] EEC X G := L0.codRestrict (EEC X G) hL0
  have hLv : ∀ S : EP R F, ((L S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  have hinj : Function.Injective L := by
    intro x y hxy
    have e1 : ((L x : EEC X G) : L2X X) = ((L y : EEC X G) : L2X X) := by rw [hxy]
    rw [hLv, hLv] at e1
    exact Submodule.inclusion_injective hle (J.injective (Subtype.ext e1))
  have hsurj : Function.Surjective L := by
    intro Fx
    let F' : conjRows X := ⟨(Fx : L2X X), hconj _ Fx.2⟩
    let S : MultR R F := J.symm F'
    have hJS : ((J S : conjRows X) : L2X X) = (Fx : L2X X) := by
      show ((J (J.symm F') : conjRows X) : L2X X) = _
      rw [LinearEquiv.apply_symm_apply]
    have hRg : G.Rg (star (Fx : L2X X)) = star (Fx : L2X X) := by
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 Fx.2).2
      exact sub_eq_zero.1 this
    have k1 := key S
    rw [hJS, hRg, star_star, ← hJS] at k1
    have hfix : postOn (MP R) R.e0 S = S := congrArg Subtype.val (J.injective (Subtype.ext k1))
    refine ⟨⟨(S : MMap (MP R)), (hEPS S).2 hfix⟩, Subtype.ext ?_⟩
    rw [hLv]
    exact hJS
  let j : EP R F ≃ₗ[ℂ] EEC X G := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hj : ∀ S : EP R F, ((j S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  refine ⟨⟨j, fun S => ?_⟩, ⟨v₀, hv, j, fun S => ?_⟩⟩
  · rw [hj]
    exact hJ _
  · rw [hj]
    exact hJ _

end GlobalTheory.Mem.SRe
