import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartitionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem two_le_jhMult {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    {B : Representation ℂ (GL (Fin N) k) V} (hB : IsSmooth B) (S : Subrepresentation B)
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h1 : IsSubquotient τ (jac e S.toRepresentation)) (h2 : IsSubquotient τ (jac e (subQuot ⊤ S))) :
    2 ≤ jhMult τ (jac e B) := by
  let ι : S.toRepresentation.IntertwiningMap B := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let p : B.IntertwiningMap (subQuot ⊤ S) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation B).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := fun x => by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩
  let P := jacMap e p
  let K : Subrepresentation (jac e B) := ⟨LinearMap.ker P.toLinearMap, fun g x hx => by
    show P (jac e B g x) = 0
    rw [P.isIntertwining]
    have hx' : P x = 0 := hx
    rw [hx', map_zero]⟩
  let κ : K.toRepresentation.IntertwiningMap (jac e B) := ⟨K.toSubmodule.subtype, fun _ => rfl⟩
  have hadd := jhMult_exact κ P hτ Subtype.val_injective (GlobalTheory.JacquetExact.jacMap_surjective e p hps)
    (fun u => u.2) fun v hv => ⟨⟨v, hv⟩, rfl⟩
  have hz : ∀ x, P (jacMap e ι x) = 0 := fun x => by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : p (ι v) = 0 := (hp _).2 v.2
    show Submodule.Quotient.mk (p (ι v)) = 0
    rw [this]
    rfl
  let ψ : (jac e S.toRepresentation).IntertwiningMap K.toRepresentation :=
    ⟨LinearMap.codRestrict K.toSubmodule (jacMap e ι).toLinearMap hz, fun g => LinearMap.ext fun x =>
      Subtype.ext ((jacMap e ι).isIntertwining _ _ g x)⟩
  have hψ : Function.Injective ψ := fun x y h =>
    GlobalTheory.JacquetExact.jacMap_injective e hB ι Subtype.val_injective (congrArg Subtype.val h)
  have h3 : jhMult τ K.toRepresentation ≠ 0 := jhMult_ne_zero_iff.2 (h1.trans (.of_injective ψ hψ))
  have h4 : jhMult τ (jac e (subQuot ⊤ S)) ≠ 0 := jhMult_ne_zero_iff.2 h2
  rw [hadd]
  have h5 := ENat.one_le_iff_ne_zero.2 h3
  have h6 := ENat.one_le_iff_ne_zero.2 h4
  exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add h5 h6)

theorem isIrreducible_of_jhMult_eq_one {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    {B : Representation ℂ (GL (Fin N) k) V} (hB : IsSmooth B)
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hτ : τ.IsIrreducible)
    (h1 : jhMult τ (jac e B) = 1)
    (occ : ∀ {U : Type} [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin N) k) U),
      Nontrivial U → IsSubquotient ρ B → IsSubquotient τ (jac e ρ)) : B.IsIrreducible := by
  have hsub : IsSubquotient τ (jac e B) := jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hnt : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨S, f, hf⟩ := hsub
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
    haveI : Subsingleton (Jacquet B (unipRad k e)) := (Submodule.mkQ_surjective _).subsingleton
    haveI : Subsingleton S.toSubmodule := inferInstance
    exact not_subsingleton _ (Function.Surjective.subsingleton hf)
  show IsSimpleOrder (Subrepresentation B)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation B).toSubmodule := trivial
    rw [← h] at this
    exact hx this
  by_contra hS
  push_neg at hS
  obtain ⟨hS0, hS1⟩ := hS
  have n1 : Nontrivial S.toSubmodule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hS0 (le_antisymm (fun v hv => ?_) bot_le)
    have : (⟨v, hv⟩ : S.toSubmodule) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have n2 : Nontrivial ((⊤ : Subrepresentation B).toSubmodule ⧸
      S.toSubmodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hS1 (le_antisymm le_top fun v _ => ?_)
    have h0 : (Submodule.Quotient.mk (⟨v, trivial⟩ : (⊤ : Subrepresentation B).toSubmodule) :
      _ ⧸ S.toSubmodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype) = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (S.toSubmodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype)).1 h0
  let ι : S.toRepresentation.IntertwiningMap B := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let q : B.IntertwiningMap (subQuot ⊤ S) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation B).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hq : Function.Surjective q := fun x => by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩
  have h2 := two_le_jhMult e hB S hτ (occ _ n1 (.of_injective ι Subtype.val_injective))
    (occ _ n2 (.of_surjective q hq))
  rw [h1] at h2
  exact absurd h2 (by norm_num)

theorem isIrreducible_of_occurs (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {N : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin N)
    (hOcc : ∀ Q : Irr k N, IsSubquotient Q.π (multiProd e fun i => (p i).π) →
      IsSubquotient (piTensor fun i => (p i).π) (jac e Q.π)) :
    (multiProd e fun i => (p i).π).IsIrreducible := by
  have hτ : (piTensor fun i => (p i).π).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun i => (p i).toIrrRep
  have hτs : IsSmooth (piTensor fun i => (p i).π) := isSmooth_piTensor fun i => (p i).smooth
  have hB : IsSmooth (multiProd e fun i => (p i).π) := isSmooth_parInd _ _
  refine isIrreducible_of_jhMult_eq_one e hB hτ ?_ ?_
  · rw [jhMult_jac_multiProd hG hBZ p hA hAB e e hτ hτs (fun i => (p i).toIrrRep)
      (fun i => isSubquotient_comp_mulSingle _ (fun i => (p i).irr) i) hA, jhMult_self hτ]
  · intro U _ _ ρ hn hρ
    have hρs : IsSmooth ρ := hρ.isSmooth hB
    obtain ⟨Z, _, _, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ ρ hn
    exact (hOcc ⟨Z, υ, hs.isSmooth hρs, hυ⟩ (hs.trans hρ)).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac e hρs hs)

theorem occurs_of_embedding (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {N : ℕ} (e : (Σ i, Fin (d i)) ≃ Fin N) (Q : Irr k N)
    (hQ : IsSubquotient Q.π (multiProd e fun i => (p i).π))
    {X : Fin 2 → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (F : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (hFs : ∀ i, IsSmooth (F i))
    (hF : ∀ i (y : IrrRep (GL (Fin (d i)) k)), IsSubquotient y.ρ (F i) → HasSupport y.ρ (A i))
    (φ : Q.π.IntertwiningMap (multiProd e F)) (hφ : Function.Injective φ) :
    IsSubquotient (piTensor fun i => (p i).π) (jac e Q.π) := by
  have hirr : (piTensor fun i => (p i).π).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun i => (p i).toIrrRep
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible Q.irr

  let ψ := Model.evalOne e φ
  have hψ : ∃ x, ψ x ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Q.V)
    have h1 : φ v ≠ 0 := fun h => hv (hφ (by rw [h, map_zero]))
    obtain ⟨g, hg⟩ : ∃ g, (φ v).1.1 g ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (Subtype.ext (Subtype.ext (funext hn)))
    refine ⟨Submodule.Quotient.mk (Q.π g v), fun h => hg ?_⟩
    have h2 : (φ (Q.π g v)).1.1 1 = 0 := h
    rw [φ.isIntertwining] at h2
    have h3 : (φ v).1.1 (1 * g) = 0 := h2
    rwa [one_mul] at h3
  obtain ⟨x₀, hx₀⟩ := hψ
  let R : Subrepresentation (piTensor F) := ⟨LinearMap.range ψ.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨jac e Q.π g x, ψ.isIntertwining _ _ g x⟩⟩
  have hRn : Nontrivial R.toSubmodule :=
    ⟨⟨⟨ψ x₀, ⟨x₀, rfl⟩⟩, 0, fun h => hx₀ (congrArg Subtype.val h)⟩⟩
  have hRF : IsSubquotient R.toRepresentation (piTensor F) :=
    .of_injective ⟨R.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective
  have hRJ : IsSubquotient R.toRepresentation (jac e Q.π) :=
    .of_surjective ⟨LinearMap.codRestrict R.toSubmodule ψ.toLinearMap (fun x => ⟨x, rfl⟩), fun g =>
      LinearMap.ext fun x => Subtype.ext (ψ.isIntertwining _ _ g x)⟩ (by
        rintro ⟨_, x, rfl⟩
        exact ⟨x, rfl⟩)
  obtain ⟨Z, _, _, τ, hτ, hτR⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ R.toRepresentation hRn
  have hτJ := hτR.trans hRJ
  have hτF := hτR.trans hRF
  have hτs : IsSmooth τ := hτJ.isSmooth (isSmooth_jac e Q.smooth)
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Z) := by
    intro j
    obtain ⟨X', _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X', υ, hυs.isSmooth (isSmooth_comp hτs _
      (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
  choose y hy using hy
  have hys : ∀ j, HasSupport (y j).ρ (A j) := fun j =>
    hF j (y j) (isSubquotient_factor F j (y j).irr ((hy j).trans (isSubquotient_comp hτF _)))
  have h1 := jhMult_jac_multiProd hG hBZ p hA hAB e e hτ hτs y hy hys
  have h2 : jhMult τ (jac e (multiProd e fun i => (p i).π)) ≠ 0 :=
    jhMult_ne_zero_iff.2 (hτJ.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _) hQ))
  rw [h1] at h2
  obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hτ hirr (jhMult_ne_zero_iff.1 h2)
  exact (IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans hτJ

theorem occurs_of_prod₂ (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) (e : (Σ i, Fin (d i)) ≃ Fin (d 0 + d 1)) (Q : Irr k (d 0 + d 1))
    (hQ : IsSubquotient Q.π (multiProd e fun i => (p i).π))
    (F₀ : SmRep (GL (Fin (d 0)) k)) (F₁ : SmRep (GL (Fin (d 1)) k))
    (hF₀ : ∀ y : IrrRep (GL (Fin (d 0)) k), IsSubquotient y.ρ F₀.ρ → HasSupport y.ρ (A 0))
    (hF₁ : ∀ y : IrrRep (GL (Fin (d 1)) k), IsSubquotient y.ρ F₁.ρ → HasSupport y.ρ (A 1))
    (φ : Q.π.IntertwiningMap (prod₂ F₀.ρ F₁.ρ)) (hφ : Function.Injective φ) :
    IsSubquotient (piTensor fun i => (p i).π) (jac e Q.π) := by
  let R : ∀ i : Fin 2, SmRep (GL (Fin (d i)) k) := fun i =>
    Fin.cases (motive := fun i => SmRep (GL (Fin (d i)) k)) F₀
      (fun j => Fin.cases (motive := fun j : Fin 1 => SmRep (GL (Fin (d j.succ)) k)) F₁ (fun l => l.elim0) j) i
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (R i).ρ
  obtain ⟨E₂⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (stdBlocks d hd) e _).1 (piTensor fun i => (R i).ρ)
  let E := E₁.trans E₂
  refine occurs_of_embedding hG hBZ p hA hAB e Q hQ (fun i => (R i).ρ) (fun i => (R i).smooth) ?_
    (E.toIntertwiningMap.comp φ) (E.toLinearEquiv.injective.comp hφ)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hF₀
  · refine Fin.cases ?_ (fun l => l.elim0) j
    exact hF₁

theorem isIrreducible_multiProd_of_prod₂ {n : Type} [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ)
    (σ : ∀ i, Irr k (d i)) (h2 : (prod₂ (σ 0).π (σ 1).π).IsIrreducible) (e : (Σ i, Fin (d i)) ≃ n) :
    (multiProd e fun i => (σ i).π).IsIrreducible := by
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (σ i).π
  have h3 := GlobalTheory.Parabolic.isIrreducible_of_equiv E₁ h2
  have hc : Fintype.card (Fin (d 0 + d 1)) = Fintype.card n := by
    rw [Fintype.card_fin, ← hd, ← Fintype.card_congr e]; simp
  let ψ : Fin (d 0 + d 1) ≃ n := Fintype.equivOfCardEq hc
  obtain ⟨E₂⟩ := GlobalTheory.T.normalisedParabolicInduction_reindex_equiv k (Fin 2) (fun i => Fin (d i)) _ _ (stdBlocks d hd) ψ _ (piTensor fun i => (σ i).π)
  have h4 := GlobalTheory.SwapTwo.isIrreducible_of_comp _ (GlobalTheory.Parabolic.isIrreducible_of_equiv E₂ h3)
  obtain ⟨E₃⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin 2) n (fun i => Fin (d i)) ((stdBlocks d hd).trans ψ) e _).1
    (piTensor fun i => (σ i).π)
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E₃ h4

theorem unlinked_symm {x y : IrrGL k} (h : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) (j : ℤ) (hj : |j| ≤ 1) :
    y ≠ x.nu (j : ℂ) := by
  intro e
  refine h (-j) (by rwa [abs_neg]) ?_
  rw [e, IrrGL.nu_nu]
  simp

theorem map_orderEmb {s : ℕ} {β : Type*} (T : Finset (Fin s)) (g : Fin s → β) :
    Finset.univ.val.map (fun a : Fin T.card => g (T.orderEmbOfFin rfl a)) = T.val.map g := by
  rw [map_univ_eq_sum]
  have h : ∑ a : Fin T.card, ({g (T.orderEmbOfFin rfl a)} : Multiset β) = ∑ t : T, ({g t} : Multiset β) :=
    Fintype.sum_equiv (T.orderIsoOfFin rfl).toEquiv _ _ (fun a => by simp)
  rw [h, Finset.sum_coe_sort T (fun a => ({g a} : Multiset β)), Finset.sum,
    ← Multiset.sum_map_singleton (T.val.map g), Multiset.map_map]
  rfl

theorem exists_equiv_of_eq_nu {p q : ℕ} (x : Irr k p) (y : Irr k q) (c : ℂ)
    (h : IrrGL.of x.π x.smooth x.irr = (IrrGL.of y.π y.smooth y.irr).nu c) :
    ∃ hpq : p = q, Nonempty ((hpq ▸ x : Irr k q).π.Equiv (twist y.π (detChar (Fin q) (absPow k c)))) := by
  rw [IrrGL.nu, IrrGL.tw_of] at h
  have hpq : p = q := congrArg Sigma.fst h
  subst hpq
  exact ⟨rfl, IrrGL.of_eq_of.1 h⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.TD

end
