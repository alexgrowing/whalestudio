import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfAMemAdjoinLow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.ZFin

open Polynomial in

theorem commute_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {T S : Module.End ℂ M} (h : Commute S T) (q : ℂ[X]) :
    Commute S (aeval T q) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

open Polynomial in

theorem aeval_modByMonic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} {w : M}
    (hw : aeval T p w = 0) (q : ℂ[X]) : aeval T q w = aeval T (q %ₘ p) w := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div q p]
  rw [map_add, LinearMap.add_apply, mul_comm, map_mul, Module.End.mul_apply, hw, map_zero, add_zero]

open Polynomial in

theorem exists_step {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {p : ℂ[X]} (hp : p.Monic)
    {W : Submodule ℂ M} (hF : W.FG) (hW : ∀ w ∈ W, aeval T p w = 0) :
    ∃ W' : Submodule ℂ M, W'.FG ∧ W ≤ W' ∧ (∀ w ∈ W', T w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w ∈ W) → ∀ w ∈ W', S w ∈ W') ∧
      (∀ S : Module.End ℂ M, Commute S T → (∀ w ∈ W, S w = 0) → ∀ w ∈ W', S w = 0) := by
  let B : ℂ[X] →ₗ[ℂ] M →ₗ[ℂ] M := (aeval T).toLinearMap
  have hB : ∀ q w, B q w = aeval T q w := fun _ _ => rfl
  have hdeg : ∀ q : ℂ[X], q %ₘ p ∈ degreeLT ℂ p.natDegree := fun q => by
    rw [Polynomial.mem_degreeLT, ← Polynomial.degree_eq_natDegree hp.ne_zero]
    exact Polynomial.degree_modByMonic_lt q hp
  have hmem : ∀ q, ∀ w ∈ W, aeval T q w ∈ Submodule.map₂ B (degreeLT ℂ p.natDegree) W := fun q w hw => by
    rw [aeval_modByMonic T (hW w hw) q]
    exact Submodule.apply_mem_map₂ B (hdeg q) hw
  have hfg : (degreeLT ℂ p.natDegree).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ p.natDegree).symm
  refine ⟨Submodule.map₂ B (degreeLT ℂ p.natDegree) W, Submodule.FG.map₂ _ hfg hF, fun w hw => ?_, ?_, ?_, ?_⟩
  · simpa using hmem 1 w hw
  · have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap T :=
      Submodule.map₂_le.2 fun q _ w hw => by
        have e : T * aeval T q = aeval T (X * q) := by rw [map_mul, Polynomial.aeval_X]
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, e]
        exact hmem _ w hw
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤
        (Submodule.map₂ B (degreeLT ℂ p.natDegree) W).comap S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [Submodule.mem_comap, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply]
        exact hmem _ _ (hSW w hw)
    exact fun w hw => this hw
  · intro S hS hSW
    have : Submodule.map₂ B (degreeLT ℂ p.natDegree) W ≤ LinearMap.ker S :=
      Submodule.map₂_le.2 fun q _ w hw => by
        rw [LinearMap.mem_ker, hB, ← Module.End.mul_apply, (commute_aeval hS q).eq, Module.End.mul_apply,
          hSW w hw, map_zero]
    exact fun w hw => this hw

open Polynomial in

theorem exists_fg_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Fintype ι] (T : ι → Module.End ℂ M)
    (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) (hc : ∀ i j, Commute (T i) (T j)) (v : M)
    (hv : ∀ i, aeval (T i) (p i) v = 0) :
    ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ ∀ i, ∀ w ∈ W, T i w ∈ W := by
  classical
  have key : ∀ s : Finset ι, ∃ W : Submodule ℂ M, W.FG ∧ v ∈ W ∧ (∀ i ∈ s, ∀ w ∈ W, T i w ∈ W) ∧
      ∀ i, ∀ w ∈ W, aeval (T i) (p i) w = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {v}, Submodule.fg_span_singleton v, Submodule.mem_span_singleton_self v,
        by simp, fun i w hw => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hv, smul_zero]
    | insert j s _ ih =>
      obtain ⟨W, hF, hvW, hs, hk⟩ := ih
      obtain ⟨W', hF', hle, hT, hS, hZ⟩ := exists_step (T j) (hp j) hF (hk j)
      refine ⟨W', hF', hle hvW, fun i hi => ?_, fun i => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hT
        · exact hS _ (hc i j) (hs i hi)
      · exact hZ _ ((commute_aeval (hc j i) (p i)).symm) (hk i)
  obtain ⟨W, hF, hvW, hs, _⟩ := key Finset.univ
  exact ⟨W, hF, hvW, fun i => hs i (Finset.mem_univ i)⟩

section Main

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

abbrev unitOp (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Fin V.rank → Fin V.rank → Module.End ℂ (SmFun θ V) :=
  fun a b => derEnd hθ τ (Matrix.single a b 1)

theorem commute_derEnd_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ℕ) :
    Commute (derEnd hθ τ Z) (gelfA (unitOp hθ V τ') k) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have e1 : ∀ g : SmFun θ V, (gelfA (unitOp hθ V τ') k g).1 = gelf θ V τ' k g.1 := fun g => (gelf_eq hθ τ' k g).symm
  have L := linOnSm_gelf (θ := θ) (V := V) τ' k
  refine LinearMap.ext fun f => Subtype.ext ?_
  change RderC θ V τ Z (gelfA (unitOp hθ V τ') k f).1 = (gelfA (unitOp hθ V τ') k (derEnd hθ τ Z f)).1
  rw [e1, e1]
  change _ = gelf θ V τ' k (RderC θ V τ Z f.1)
  simp only [RderC]
  rw [L.add _ (Rder_mem f.2 h1) _ (Submodule.smul_mem _ _ (Rder_mem f.2 h2)), L.smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 f.2, GlobalTheory.CuspLie.gelf_Rder hθ h2 f.2]

theorem commute_gelfA (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k k' : ℕ) :
    Commute (gelfA (unitOp hθ V τ) k) (gelfA (unitOp hθ V τ') k') := by
  refine Commute.sum_left _ _ _ fun idx _ => Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact commute_derEnd_gelfA hθ τ τ' _ k'

open Polynomial in

theorem foldr_gelf_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) (L : List ℂ) :
    L.foldr (fun a f => gelf θ V τ k f - a • f) φ.1 =
      (aeval (gelfA (unitOp hθ V τ) k) ((L.map fun a => (X - C a : ℂ[X])).prod) φ).1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, gelf_eq hθ τ k, map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    rfl

open Polynomial in
theorem monic_prod_roots (L : List ℂ) : ((L.map fun a => (X - C a : ℂ[X])).prod).Monic := by
  induction L with
  | nil => simp
  | cons a L ih => simpa using (monic_X_sub_C a).mul ih

end Main

end GlobalTheory.CompanionTheory.ZFin

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.SmoothForms GlobalTheory.CompanionTheory.ZFin in
open Polynomial in

theorem GlobalTheory.CompanionTheory.ZFin.isAutFunSm_of_gelf_roots : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) → (∀ τ k, ∃ L : List ℂ, L.foldr (fun a f => gelf θ V τ k f - a • f) φ = 0) → IsAutFunSm θ V φ := by
  intro D θ hθ V φ hA hs hg hz
  choose L hL using hz
  have hsm : φ ∈ SmFun θ V := hs
  obtain ⟨W, hF, hv, hS⟩ := exists_fg_stable (ι := D.what₂.Tau × Fin V.rank)
    (fun i => gelfA (unitOp hθ V i.1) i.2.val)
    (fun i => ((L i.1 i.2.val).map fun a => (X - C a : ℂ[X])).prod)
    (fun i => monic_prod_roots _) (fun i j => commute_gelfA hθ _ _ _ _) ⟨φ, hsm⟩
    (fun i => Subtype.ext ((foldr_gelf_eq hθ i.1 i.2.val ⟨φ, hsm⟩ _).symm.trans (hL _ _)))
  refine { toIsAutFun := hA, smooth := hs, growth := hg,
           zfin := ⟨W.map (SmFun θ V).subtype, Module.Finite.iff_fg.2 (hF.map _), ⟨⟨φ, hsm⟩, hv, rfl⟩, ?_⟩ }
  rintro τ k _ ⟨f, hf, rfl⟩
  have hstab : ∀ x ∈ Algebra.adjoin ℂ (Set.range fun k : Fin V.rank => gelfA (unitOp hθ V τ) k.val),
      ∀ w ∈ W, x w ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hS (τ, j)
    | algebraMap r =>
      intro w hw
      simpa using W.smul_mem r hw
    | add x y _ _ hx hy => exact fun w hw => add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => exact fun w hw => hx _ (hy w hw)
  exact ⟨_, hstab _ (gelfA_mem_adjoin_low _ _ _ (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) k) f hf, (gelf_eq hθ τ k f).symm⟩

end
