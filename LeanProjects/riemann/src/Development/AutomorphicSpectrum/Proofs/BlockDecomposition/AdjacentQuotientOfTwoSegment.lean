import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.ProdReorder
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdjQuot

section Linear

theorem nontrivial_piTensorProduct {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push_neg at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

theorem nontrivial_tensorProduct {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    [Nontrivial V] [Nontrivial U] : Nontrivial (V ⊗[ℂ] U) := inferInstance

theorem ofFn_split {α : Type*} {h : ℕ} (x : Fin h → α) (j : ℕ) (hj : j ≤ h) :
    List.ofFn x = List.ofFn (fun i : Fin j => x ⟨i, by omega⟩) ++
      List.ofFn (fun i : Fin (h - j) => x ⟨j + i, by omega⟩) := by
  refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_append]
  split_ifs with hc
  · simp
  · simp only [List.length_ofFn] at hc
    simp only [List.getElem_ofFn, List.length_ofFn]
    exact congrArg x (Fin.ext (by simp; omega))

end Linear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Induction

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W W' : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem parIndMap_surjective (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {ρ' : Representation ℂ (Levi k m) W'} (hρ : IsSmooth ρ) (f : ρ.IntertwiningMap ρ')
    (hf : Function.Surjective f) : Function.Surjective (parIndMap e f) := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let σ₀ : Representation ℂ (parab k e) W := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
    hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont)
    (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    [Nontrivial W] : Nontrivial (IndSp e ρ) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

end Induction

theorem nontrivial_prodIrr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := by
  haveI : ∀ a, Nontrivial (x a).2.rep.V := fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (x a).2.rep.irr
  haveI := nontrivial_piTensorProduct (X := fun a => (x a).2.rep.V)
  exact nontrivial_indSp _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)

section Two

variable {V U W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  {r t N : ℕ}

theorem isSmooth_levi (A : Representation ℂ (GL (Fin r) k) V) (C : Representation ℂ (GL (Fin t) k) U)
    (hA : IsSmooth A) (hC : IsSmooth C) :
    IsSmooth ((extTensor A C).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  isSmooth_comp (isSmooth_extTensor hA hC) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))

theorem nontrivial_ind₂ (e : r + t = N) (A : Representation ℂ (GL (Fin r) k) V)
    (C : Representation ℂ (GL (Fin t) k) U) (hA : IsSmooth A) (hC : IsSmooth C) [Nontrivial V] [Nontrivial U] :
    Nontrivial (IndSp (two (stdSum e)) ((extTensor A C).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)) := by
  haveI : Nontrivial (V ⊗[ℂ] U) := nontrivial_tensorProduct
  exact nontrivial_indSp _ (isSmooth_levi A C hA hC)

def deg2 (r t : ℕ) : Fin 2 → ℕ := Fin.cases r fun _ => t

def fam2 (A : GlobalTheory.ProdFlatten.BR k r) (C : GlobalTheory.ProdFlatten.BR k t) : ∀ i, GlobalTheory.ProdFlatten.BR k (deg2 r t i) :=
  Fin.cases A fun _ => C

theorem nonempty_multiProd_fin_one {d : Fin 1 → ℕ} {X : Fin 1 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : IsSmooth (π 0))
    (e : (Σ a, Fin (d a)) ≃ Fin (d 0)) : Nonempty ((multiProd e π).Equiv (π 0)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = fun _ => n := ⟨d 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, X = fun _ => Y := ⟨X 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨i, rfl⟩ : ∃ i, iX = fun _ => i := ⟨iX 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨j, rfl⟩ : ∃ j, mX = fun _ => j := ⟨mX 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ, π = fun _ => ρ := ⟨π 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  let f : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  exact eqv_trans (multiProd_placing e f _) (eqv_symm (nonempty_equiv_multiProd_one hs f fun _ _ => rfl))

theorem nonempty_multiProd_two {d : Fin 2 → ℕ} {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : IsSmooth (π 1))
    (hd : ∑ a, d a = N) (e : d 0 + d 1 = N) :
    Nonempty ((multiProd (stdBlocks d hd) π).Equiv (ind₂ (stdSum e) (extTensor (π 0) (π 1)))) := by
  let f : (Σ a : Fin 1, Fin (d a.succ)) ≃ Fin (d 1) :=
    { toFun := fun p => Fin.cast (by rw [Subsingleton.elim p.1 0]; rfl) p.2
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  have B := multiProd_head (k := k) (d := d) (X := X) π (stdBlocks _ hd) e f
  have D := nonempty_multiProd_fin_one (d := fun a : Fin 1 => d a.succ) (X := fun a => X a.succ)
    (fun a => π a.succ) hs f
  exact eqv_trans B (ind₂_congr e (eqv_refl (π 0)) D)

theorem isGeneric_fam_iff (hG : GlobalTheory.BZSeg.GenericProdIff k) {d : Fin 2 → ℕ} {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (hs : ∀ a, IsSmooth (π a)) (e : d 0 + d 1 = N) :
    IsGeneric (ind₂ (stdSum e) (extTensor (π 0) (π 1))) ↔ IsGeneric (π 0) ∧ IsGeneric (π 1) := by
  have hd : ∑ a, d a = N := (Fin.sum_univ_two d).trans e
  obtain ⟨φ⟩ := nonempty_multiProd_two π (hs 1) hd e
  exact (isGeneric_congr φ).symm.trans ((hG 2 N d hd X π hs).trans Fin.forall_fin_two)

theorem isGeneric_ind₂_iff (hG : GlobalTheory.BZSeg.GenericProdIff k) (e : r + t = N)
    (A : Representation ℂ (GL (Fin r) k) V) (C : Representation ℂ (GL (Fin t) k) U) (hA : IsSmooth A)
    (hC : IsSmooth C) : IsGeneric (ind₂ (stdSum e) (extTensor A C)) ↔ IsGeneric A ∧ IsGeneric C :=
  isGeneric_fam_iff hG (d := deg2 r t) (X := fun a => (fam2 ⟨V, A⟩ ⟨U, C⟩ a).V)
    (fun a => (fam2 ⟨V, A⟩ ⟨U, C⟩ a).ρ) (Fin.forall_fin_two.2 ⟨hA, hC⟩) e

def HasNGQuot (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W)
    (f : π.IntertwiningMap τ), Function.Surjective f ∧ Nontrivial W ∧ ¬ IsGeneric τ

theorem HasNGQuot.of_equiv {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) U}
    (h : HasNGQuot π) (φ : σ.Equiv π) : HasNGQuot σ := by
  obtain ⟨W, _, _, τ, f, hf, hW, hτ⟩ := h
  exact ⟨W, _, _, τ, f.comp φ.toIntertwiningMap, hf.comp φ.toLinearEquiv.surjective, hW, hτ⟩

theorem HasNGQuot.ind₂_left (hG : GlobalTheory.BZSeg.GenericProdIff k) (e : r + t = N)
    {π : Representation ℂ (GL (Fin r) k) V} (C : Representation ℂ (GL (Fin t) k) U) (hπ : IsSmooth π)
    (hC : IsSmooth C) [Nontrivial U] (h : HasNGQuot π) : HasNGQuot (ind₂ (stdSum e) (extTensor π C)) := by
  obtain ⟨W, _, _, τ, f, hf, hW, hτ⟩ := h
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  refine ⟨_, _, _, ind₂ (stdSum e) (extTensor τ C),
    parIndMap (two (stdSum e)) (compMap (GlobalTheory.ParIndExact.extTensorMapLeft C f) _),
    parIndMap_surjective _ (isSmooth_levi π C hπ hC) _ (LinearMap.rTensor_surjective U hf),
    nontrivial_ind₂ e τ C hτs hC, fun hg => hτ ((isGeneric_ind₂_iff hG e τ C hτs hC).1 hg).1⟩

theorem HasNGQuot.ind₂_right (hG : GlobalTheory.BZSeg.GenericProdIff k) (e : r + t = N)
    {π : Representation ℂ (GL (Fin t) k) V} (A : Representation ℂ (GL (Fin r) k) U) (hπ : IsSmooth π)
    (hA : IsSmooth A) [Nontrivial U] (h : HasNGQuot π) : HasNGQuot (ind₂ (stdSum e) (extTensor A π)) := by
  obtain ⟨W, _, _, τ, f, hf, hW, hτ⟩ := h
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  refine ⟨_, _, _, ind₂ (stdSum e) (extTensor A τ),
    parIndMap (two (stdSum e)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight A f) _),
    parIndMap_surjective _ (isSmooth_levi A π hA hπ) _ (LinearMap.lTensor_surjective U hf),
    nontrivial_ind₂ e A τ hA hτs, fun hg => hτ ((isGeneric_ind₂_iff hG e A τ hA hτs).1 hg).2⟩

theorem HasNGQuot.of_ind₂_left {Y : Type} [AddCommGroup Y] [Module ℂ Y] (hG : GlobalTheory.BZSeg.GenericProdIff k)
    (e : r + t = N) {π : Representation ℂ (GL (Fin r) k) V} {C : Representation ℂ (GL (Fin t) k) U}
    {σ : Representation ℂ (GL (Fin N) k) Y} (hπ : IsSmooth π) (hC : IsSmooth C) (hU : Nontrivial U)
    (h : HasNGQuot π) (φ : Nonempty (σ.Equiv (ind₂ (stdSum e) (extTensor π C)))) : HasNGQuot σ :=
  φ.elim fun φ => (h.ind₂_left hG e C hπ hC).of_equiv φ

theorem HasNGQuot.of_ind₂_right {Y : Type} [AddCommGroup Y] [Module ℂ Y] (hG : GlobalTheory.BZSeg.GenericProdIff k)
    (e : r + t = N) {π : Representation ℂ (GL (Fin t) k) V} {A : Representation ℂ (GL (Fin r) k) U}
    {σ : Representation ℂ (GL (Fin N) k) Y} (hπ : IsSmooth π) (hA : IsSmooth A) (hU : Nontrivial U)
    (h : HasNGQuot π) (φ : Nonempty (σ.Equiv (ind₂ (stdSum e) (extTensor A π)))) : HasNGQuot σ :=
  φ.elim fun φ => (h.ind₂_right hG e A hπ hA).of_equiv φ

end Two

section Concat

theorem deg_sum_append {a b c : ℕ} {x : Fin a → IrrGL k} {y : Fin b → IrrGL k} {z : Fin c → IrrGL k}
    (h : List.ofFn z = List.ofFn x ++ List.ofFn y) : ∑ i, (x i).1 + ∑ i, (y i).1 = ∑ i, (z i).1 := by
  have := congrArg (fun l : List (IrrGL k) => (l.map Sigma.fst).sum) h
  simp only [List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
  exact this.symm

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in

theorem nonempty_prodIrr_append {a b c r t N : ℕ} (x : Fin a → IrrGL k) (y : Fin b → IrrGL k) (z : Fin c → IrrGL k)
    (h : List.ofFn z = List.ofFn x ++ List.ofFn y) (hab : a ≠ 0 ∨ b = 0) (hx : ∑ i, (x i).1 = r)
    (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (e : r + t = N) :
    Nonempty ((prodIrr z hz).Equiv (ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy)))) :=
  GlobalTheory.ProdFlatten.pr_append x y z h hab hx hy hz e

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in

theorem nonempty_prodIrr_congr {a b N : ℕ} {x : Fin a → IrrGL k} {z : Fin b → IrrGL k}
    (h : List.ofFn x = List.ofFn z) (hx : ∑ i, (x i).1 = N) (hz : ∑ i, (z i).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr z hz)) :=
  GlobalTheory.ProdFlatten.pr_congr h hx hz

end Concat

theorem hasNGQuot_left (hG : GlobalTheory.BZSeg.GenericProdIff k) {a b c r t N : ℕ} (x : Fin a → IrrGL k)
    (y : Fin b → IrrGL k) (z : Fin c → IrrGL k) (h : List.ofFn z = List.ofFn x ++ List.ofFn y) (ha : a ≠ 0)
    (hx : ∑ i, (x i).1 = r) (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (H : HasNGQuot (prodIrr x hx)) :
    HasNGQuot (prodIrr z hz) := by
  have e : r + t = N := by rw [← hx, ← hy, ← hz]; exact deg_sum_append h
  exact H.of_ind₂_left hG e (isSmooth_prodIrr _ _) (isSmooth_prodIrr y hy) (nontrivial_prodIrr y hy)
    (nonempty_prodIrr_append x y z h (Or.inl ha) hx hy hz e)

theorem hasNGQuot_right (hG : GlobalTheory.BZSeg.GenericProdIff k) {a b c r t N : ℕ} (x : Fin a → IrrGL k)
    (y : Fin b → IrrGL k) (z : Fin c → IrrGL k) (h : List.ofFn z = List.ofFn x ++ List.ofFn y) (ha : a ≠ 0)
    (hx : ∑ i, (x i).1 = r) (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (H : HasNGQuot (prodIrr y hy)) :
    HasNGQuot (prodIrr z hz) := by
  have e : r + t = N := by rw [← hx, ← hy, ← hz]; exact deg_sum_append h
  exact H.of_ind₂_right hG e (isSmooth_prodIrr _ _) (isSmooth_prodIrr x hx) (nontrivial_prodIrr x hx)
    (nonempty_prodIrr_append x y z h (Or.inl ha) hx hy hz e)

theorem hasNGQuot_of_pair (hG : GlobalTheory.BZSeg.GenericProdIff k) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (P : Fin 2 → IrrGL k) (hP0 : P 0 = x ⟨j, by omega⟩)
    (hP1 : P 1 = x ⟨j + 1, hj⟩) (hM : HasNGQuot (prodIrr P rfl)) : HasNGQuot (prodIrr x hd) := by
  have hS := ofFn_split x j (by omega)
  generalize hxR : (fun i : Fin (h - j) => x ⟨j + i, by omega⟩) = xR at hS
  have hLR : ∃ xB : Fin (h - j - 2) → IrrGL k, List.ofFn xR = List.ofFn P ++ List.ofFn xB := by
    refine ⟨fun i => xR ⟨2 + i, by omega⟩, ?_⟩
    have h2 := ofFn_split xR 2 (by omega)
    have key : ∀ i : Fin 2, x ⟨j + i, by omega⟩ = P i := Fin.forall_fin_two.2 ⟨hP0.symm, hP1.symm⟩
    have h3 : (fun i : Fin 2 => xR ⟨i, by omega⟩) = P := by
      funext i
      subst hxR
      exact key i
    rw [h3] at h2
    exact h2
  obtain ⟨xB, hLR⟩ := hLR
  have hR : ∀ {M : ℕ} (hM' : ∑ i, (xR i).1 = M), HasNGQuot (prodIrr xR hM') := fun hM' =>
    hasNGQuot_left hG P xB xR hLR two_ne_zero rfl rfl hM' hM
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hS' : List.ofFn x = List.ofFn xR := by simpa using hS
    have hN : ∑ i, (xR i).1 = N := by
      have := congrArg (fun l : List (IrrGL k) => (l.map Sigma.fst).sum) hS'
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
      exact this.symm.trans hd
    obtain ⟨φ⟩ := nonempty_prodIrr_congr hS' hd hN
    exact (hR hN).of_equiv φ
  · exact hasNGQuot_right hG (fun i : Fin j => x ⟨i, by omega⟩) xR x hS hj0.ne' rfl rfl hd (hR rfl)

theorem adjQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.TwoSegNonGenQuot k → GlobalTheory.BZSeg.GenericProdIff k → GlobalTheory.BZSeg.AdjQuot k := by
  intro k _ _ _ _ hT hG h N Δ x hd j hj hL hP
  have hM := hT (Δ ⟨j, by omega⟩) (Δ ⟨j + 1, hj⟩) (x ⟨j, by omega⟩) (x ⟨j + 1, hj⟩) _ rfl hP (hL _) (hL _)
  exact hasNGQuot_of_pair hG x hd j hj _ rfl rfl hM

end GlobalTheory.CompanionTheory.AdjQuot
end
