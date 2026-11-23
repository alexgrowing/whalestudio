import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg
    simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]
    rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]
      simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2
      simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
