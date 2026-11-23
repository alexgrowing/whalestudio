import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Topology

namespace GlobalTheory.FinCharInt

theorem tensInt_le {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
    (S₁ : Subring E) (S₂ : Subring R) (K : AddSubgroup (E ⊗[F] R))
    (hK : ∀ b ∈ S₁, ∀ α ∈ S₂, b ⊗ₜ[F] α ∈ K) {x : E ⊗[F] R} (hx : x ∈ Formalism.UG.tensInt R S₁ S₂) : x ∈ K := by
  let C : AddSubgroup (E ⊗[F] R) := AddSubgroup.closure {z | ∃ b ∈ S₁, ∃ α ∈ S₂, z = b ⊗ₜ[F] α}
  have hC : C ≤ K := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, α, hα, rfl⟩
    exact hK b hb α hα
  have hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy =>
      obtain ⟨b, hb, α, hα, rfl⟩ := hx
      obtain ⟨c, hc, β, hβ, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, S₁.mul_mem hb hc, _, S₂.mul_mem hα hβ, rfl⟩
    | zero_left x _ => rw [zero_mul]; exact C.zero_mem
    | zero_right x _ => rw [mul_zero]; exact C.zero_mem
    | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact C.add_mem h1 h2
    | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact C.add_mem h1 h2
    | neg_left x y _ _ h => rw [neg_mul]; exact C.neg_mem h
    | neg_right x y _ _ h => rw [mul_neg]; exact C.neg_mem h
  refine hC ?_
  unfold Formalism.UG.tensInt at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, c.2, _, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, c.2, rfl⟩
  | zero => exact C.zero_mem
  | one => exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, S₂.one_mem, Algebra.TensorProduct.one_def⟩
  | add x y _ _ ihx ihy => exact C.add_mem ihx ihy
  | neg x _ ihx => exact C.neg_mem ihx
  | mul x y _ _ ihx ihy => exact hmul _ ihx _ ihy

theorem exists_nsmul_kill {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Finite ι] (c : ι → AF F) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ α ∈ Formalism.UG.intAd F, ψ (N • (pairA F 0 α * c i)) = 1 := by
  have hU : (⋂ i, {α : Af F | ψ (pairA F 0 (α * (c i).2)) = 1}) ∈ 𝓝 (0 : Af F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : Continuous fun α : Af F => α * (c i).2 := continuous_id.mul continuous_const
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA F 0 a) = 1})
      (by rw [zero_mul]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  refine ⟨N, hN, fun i α hα => ?_⟩
  have h1 : ψ (pairA F 0 ((N • α) * (c i).2)) = 1 := Set.mem_iInter.1 (h α hα) i
  have e : N • (pairA F 0 α * c i) = pairA F 0 ((N • α) * (c i).2) :=
    Prod.ext (show N • ((0 : Ainf F) * (c i).1) = 0 by rw [zero_mul, smul_zero])
      (show N • (α * (c i).2) = (N • α) * (c i).2 from (smul_mul_assoc N α _).symm)
  rw [e, h1]

def kerSub {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) : AddSubgroup A where
  carrier := {a | ψ a = 1}
  zero_mem' := ψ.map_zero_eq_one
  add_mem' {a b} ha hb := by
    have ha' : ψ a = 1 := ha
    have hb' : ψ b = 1 := hb
    show ψ (a + b) = 1
    rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
  neg_mem' {a} ha := by
    have ha' : ψ a = 1 := ha
    show ψ (-a) = 1
    have := AddChar.map_add_eq_mul ψ a (-a)
    rw [add_neg_cancel, ψ.map_zero_eq_one, ha', one_mul] at this
    exact this.symm

variable {D : D7}

noncomputable def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_finPart {a : AE D} (h : infPart D a = 0) : finIncl D (finPart D a) = a := by
  have key : ∀ a : AE D, (1 - GlobalTheory.FinTranslate.eInf D) • a = finIncl D (finPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : (1 - GlobalTheory.FinTranslate.eInf D) • a =
          LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F a) :=
        Prod.ext (show (1 - 1) * a.1 = 0 by rw [sub_self, zero_mul]) (show (1 - 0) * a.2 = a.2 by rw [sub_zero, one_mul])
      rw [this]
      rfl
  rw [← key, sub_smul, one_smul, GlobalTheory.FinTranslate.smul_eq_zero_of_inf h, sub_zero]

theorem exists_nsmul_kill_forms {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {ι : Type} [Finite ι] (lam : ι → (AE D →ₗ[AF D.host.F] AF D.host.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ a : AE D, infPart D a = 0 → GlobalTheory.BotClassDict.finQ D a ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D →
      ψ (N • lam i a) = 1 := by
  let w := RingOfIntegers.basis D.host.E
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill hc hn
    (fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      lam p.1 ((1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E (w p.2))))
  refine ⟨N, hN, fun i a ha hint => ?_⟩
  let g : D.host.E ⊗[D.host.F] Af D.host.F →+ AF D.host.F :=
    N • ((lam i).toAddMonoidHom.comp ((finIncl D).toAddMonoidHom.comp
      (TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toLinearMap.toAddMonoidHom))
  have hg : ∀ y, g (Lev.swapAE D y) = N • lam i (finIncl D y) := by
    intro y
    have : TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y) = y :=
      (TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply y
    show N • lam i (finIncl D (TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y))) = _
    rw [this]
  have h1 : Lev.swapAE D (finPart D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (GlobalTheory.BotClassDict.toAfE_int_iff _).2 hint
    rwa [GlobalTheory.BotClassDict.toAfE_finQ] at this
  have h2 : Lev.swapAE D (finPart D a) ∈ (kerSub ψ).comap g := by
    refine tensInt_le _ _ _ ?_ h1
    rintro _ ⟨b, rfl⟩ α hα
    let φ : 𝓞 D.host.E →+ D.host.E ⊗[D.host.F] Af D.host.F :=
      ((TensorProduct.mk D.host.F D.host.E (Af D.host.F)).flip α).toAddMonoidHom.comp
        (algebraMap (𝓞 D.host.E) D.host.E).toAddMonoidHom
    have hb : b ∈ (((kerSub ψ).comap g).comap φ).toIntSubmodule := by
      have hsp : b ∈ Submodule.span ℤ (Set.range w) := by rw [w.span_eq]; trivial
      refine Submodule.span_le.2 ?_ hsp
      rintro _ ⟨k, rfl⟩
      have h3 := h (i, k) α hα
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h3
      exact h3
    exact hb
  have h3 : ψ (g (Lev.swapAE D (finPart D a))) = 1 := h2
  rwa [hg, finIncl_finPart ha] at h3

noncomputable def symplR (S T : HSp D) (x : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun := symplOH S T x
  map_add' := GlobalTheory.FinTranslate.symplOH_add_right S T x
  map_smul' c y := GlobalTheory.FinTranslate.symplOH_smul_right S T c x y

theorem char_sympl_nsmul_int : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
    ∀ (S T : HSp D) (A0 : WO S T), ∃ N : ℕ, 0 < N ∧ ∀ v : WO S T, (∀ i j, infPart D (v i j) = 0) →
      (∀ i j, GlobalTheory.BotClassDict.finQ D (v i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) → ψ (symplOH S T A0 (N • v)) = 1 := by
  intro D ψ hc hn S T A0
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill_forms hc hn
    (fun p : Fin T.rank × Fin S.rank => (symplR S T A0).comp (Matrix.singleLinearMap (AF D.host.F) p.1 p.2))
  refine ⟨N, hN, fun v hv hint => ?_⟩
  show symplR S T A0 (N • v) ∈ kerSub ψ
  rw [map_nsmul, Matrix.matrix_eq_sum_single v, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [map_sum, Finset.smul_sum]
  exact sum_mem fun j _ => h (i, j) (v i j) (hv i j) (hint i j)

end GlobalTheory.FinCharInt
