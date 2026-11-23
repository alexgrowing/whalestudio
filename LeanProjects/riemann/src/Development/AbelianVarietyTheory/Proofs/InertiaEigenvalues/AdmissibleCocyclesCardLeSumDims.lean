import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelSenWeightCountStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargestModelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapAevalNab

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.AdmBound

theorem inZZ_mono {k : Type} [Field k] {l n m r : ℕ} {R : RingPG k l} (D : ModPG R n (Vc k m)) (Dt : TopData n r)
    {N N' : Lats k n m} (h : ∀ i, N i ≤ N' i) {b g : ZMod n → Vc k m} (hz : InZZ D Dt N b g) :
    InZZ D Dt N' b g := by
  intro i
  obtain ⟨h0, h1, h2, h3⟩ := hz i
  refine ⟨h0, sh_le_sh 1 (h i) h1, fun hG => sh_le_sh _ (h i) (h2 hG), fun hB => ?_⟩
  obtain ⟨hb, x, hx, hx'⟩ := h3 hB
  exact ⟨sh_le_sh _ (pull_le_pull _ (h (i - 1))) hb, x, h i hx, sh_le_sh _ (h i) hx'⟩

theorem repr_sum {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {ι : Type} (z : ι → G → Fin A.m → k)
    (b g : ι → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a)) (a₀ : ι) (c : ι → k) (t : Finset ι) :
    Repr F A (∑ a ∈ t, c a • z a) (∑ a ∈ t, c a • b a) (∑ a ∈ t, c a • g a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := GlobalTheory.T.repr_smul_add F A (-1) (z a₀) (z a₀) (b a₀) (g a₀) (b a₀) (g a₀) (h a₀) (h a₀)
    simpa only [neg_one_smul, neg_add_cancel, Finset.sum_empty] using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.repr_smul_add F A (c a) (z a) _ (b a) (g a) _ _ (h a) ih

theorem indep_pairs {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {s : ℕ} (z : Fin s → G → Fin A.m → k)
    (b g : Fin s → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a))
    (hz : LinearIndependent k (fun a => (cob A).mkQ (z a))) :
    LinearIndependent k (fun a => (herrB (F.D A)).mkQ (b a, g a)) := by
  classical
  rw [linearIndependent_iff'] at hz ⊢
  intro t c hc a ha
  have e1 : ∑ a ∈ t, c a • (herrB (F.D A)).mkQ (b a, g a) =
      (herrB (F.D A)).mkQ (∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) := by
    rw [show ((∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) : (ZMod n → Vc k A.m) × (ZMod n → Vc k A.m)) =
        ∑ a ∈ t, c a • (b a, g a) by ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
    simp only [map_sum, map_smul]
  rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hcob := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F A _ _ _ (repr_sum F A z b g h a c t) hc
  refine hz t c ?_ a ha
  have e2 : ∑ a ∈ t, c a • (cob A).mkQ (z a) = (cob A).mkQ (∑ a ∈ t, c a • z a) := by
    simp only [map_sum, map_smul]
  rw [e2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcob

private theorem exists_ne_zero_smul_mem_of_mem_span' (hψ : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi) {k : Type} [Field k] {l n m r : ℕ} [Fact l.Prime]
    [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n r)
    (N : Lats k n m) (hr : m = r) (hc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (habc : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧
      (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧
      (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = r ∧
        EPoly (D.γ i) (N i) (Dt.wst i + 1)))
    (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : ∀ a, InZZ D Dt N (z a).1 (z a).2)
    (hind : LinearIndependent k (fun a => (herrB D).mkQ (z a))) : s ≤ Dt.dsum := by
  subst hr
  exact GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le hψ D ι Dt N hc h1 h2 h3 habc hsen s z hz hind

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hψ k G _ _ l n _ _ _ R F r Dt M ι hc h1 h2 h3 s z hz hind
  choose N b g hN hR hZ using fun a => GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 M.T (z a) (hz a)
  obtain ⟨Nm, hNm, hmax⟩ := GlobalTheory.T.exists_largest_model' F M M.T M.Nstd M.std_model
  have hS := GlobalTheory.T.twistedPhiGammaModel_sen_weight_count F M h1 h2 h3 Nm hNm (hmax _ M.std_model)
  refine exists_ne_zero_smul_mem_of_mem_span' hψ (F.D M.T) ι Dt Nm M.T_m hc h1 h2 h3 (GlobalTheory.T.obj_and_abc_of_model F M M.T Nm hNm).2
    (fun i => ⟨(hS i).1, (hS i).2.1, fun hB => ⟨(hS i).2.2 hB,
      GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 M.T Nm hNm i hB⟩⟩)
    s (fun a => (b a, g a)) (fun a => inZZ_mono _ _ (hmax _ (hN a)) (hZ a)) (indep_pairs F M.T z b g hR hind)

end GlobalTheory.Models.AdmBound
