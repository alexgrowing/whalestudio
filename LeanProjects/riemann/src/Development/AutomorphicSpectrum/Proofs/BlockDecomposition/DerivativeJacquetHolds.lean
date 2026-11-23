import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BZDerivJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def embM (n j : ℕ) : Mir k n →* Mir k (n + j) :=
  Nat.rec (motive := fun j => Mir k n →* Mir k (n + j)) (MonoidHom.id _)
    (fun j f => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp f) j

theorem exists_proj (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ p : τ.V →ₗ[ℂ] (iterPhi k ψ j τ).V, Function.Surjective p ∧
      (∀ (m : Mir k n) (v : τ.V), p (τ.ρ (embM k n j m) v) = (iterPhi k ψ j τ).ρ m (p v)) ∧
      (twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)).map p ≤
        twKer (iterPhi k ψ j τ).ρ (MirUin k n) 1
  | 0, τ => ⟨LinearMap.id, Function.surjective_id, fun _ _ => rfl, by
      rintro _ ⟨y, hy, rfl⟩
      exact (GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ).ge hy⟩
  | j + 1, τ => by
    obtain ⟨p, hp, hq, hk⟩ := exists_proj ψ n j (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    obtain ⟨e, -⟩ := GlobalTheory.CompanionTheory.BZMirStep.twKer_twAct_eq_map τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j)) _
      (levi_stab ψ (n + j)) (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) (derUnipM k (n + j + 1) n)
      (derCharM k ψ (n + j + 1) n) (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
      (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
    refine ⟨p ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ,
      hp.comp (Submodule.mkQ_surjective _), fun m v => hq m (Submodule.Quotient.mk v), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hk (Submodule.mem_map_of_mem (e.ge (Submodule.mem_map_of_mem hy)))

theorem glEmbMat_apply (N : ℕ) (A : Matrix (Fin N) (Fin N) k) (a b : Fin (N + 1)) :
    glEmbMat k N A a b = if h : (a : ℕ) < N ∧ (b : ℕ) < N then A ⟨a, h.1⟩ ⟨b, h.2⟩
      else if (a : ℕ) = b then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b =>
      have := b.2
      simp [glEmbMat]
      omega
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      have := a.2
      simp [glEmbMat]
      omega
    | cast b => simp [glEmbMat]

theorem embM_levi_apply (n : ℕ) : ∀ (j : ℕ) (g : GL (Fin n) k) (a b : Fin (n + j + 1)),
    (((embM k n j (levi k n g) : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b =
      if h : (a : ℕ) < n ∧ (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, h.1⟩ ⟨b, h.2⟩
      else if (a : ℕ) = b then 1 else 0
  | 0, g, a, b => glEmbMat_apply n _ a b
  | j + 1, g, a, b => by
    refine (glEmbMat_apply (n + j + 1) _ a b).trans ?_
    by_cases h : (a : ℕ) < n + j + 1 ∧ (b : ℕ) < n + j + 1
    · rw [dif_pos h]
      exact embM_levi_apply n j g ⟨a, h.1⟩ ⟨b, h.2⟩
    · have h2 : ¬ ((a : ℕ) < n ∧ (b : ℕ) < n) := by omega
      rw [dif_neg h, dif_neg h2]

abbrev dd (n t : ℕ) : Fin 2 → ℕ := ![n, t]

theorem dd_sum (n j : ℕ) : ∑ a, dd n (j + 1) a = n + j + 1 := by
  simp [dd, Fin.sum_univ_two]
  omega

theorem std_val0 (n t N : ℕ) (h : ∑ a, dd n t a = N) (i : Fin n) :
    (stdBlocks (dd n t) h ⟨0, i⟩ : ℕ) = i := by
  simpa using stdBlocks_val (dd n t) h 0 i

theorem std_val1 (n t N : ℕ) (h : ∑ a, dd n t a = N) (i : Fin t) :
    (stdBlocks (dd n t) h ⟨1, i⟩ : ℕ) = n + i := by
  simpa using stdBlocks_val (dd n t) h 1 i

theorem embM_eq_leviEmb (n j : ℕ) (g : GL (Fin n) k) :
    ((embM k n j (levi k n g) : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g) := by
  set e := stdBlocks (dd n (j + 1)) (dd_sum n j) with he
  apply Units.ext
  ext a b
  rw [embM_levi_apply]
  obtain ⟨⟨x, i⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨y, l⟩, rfl⟩ := e.surjective b
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · have hi : (e ⟨0, i⟩ : ℕ) = i := std_val0 n (j + 1) _ (dd_sum n j) i
    have hin : (i : ℕ) < n := i.2
    obtain rfl | rfl : y = 0 ∨ y = 1 := by omega
    · have hl : (e ⟨0, l⟩ : ℕ) = l := std_val0 n (j + 1) _ (dd_sum n j) l
      have hln : (l : ℕ) < n := l.2
      have hs : Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 0 = g :=
        Pi.mulSingle_eq_same _ _
      rw [leviEmb_apply_same, dif_pos (by omega)]
      refine Eq.trans ?_ (congrArg (fun X : GL (Fin n) k => (X : Matrix (Fin n) (Fin n) k) i l) hs).symm
      exact congrArg₂ (fun a b => (g : Matrix (Fin n) (Fin n) k) a b) (Fin.ext hi) (Fin.ext hl)
    · have hl : (e ⟨1, l⟩ : ℕ) = n + l := std_val1 n (j + 1) _ (dd_sum n j) l
      rw [leviEmb_apply_ne k e _ (by decide), dif_neg (by omega), if_neg (by omega)]
  · have hi : (e ⟨1, i⟩ : ℕ) = n + i := std_val1 n (j + 1) _ (dd_sum n j) i
    obtain rfl | rfl : y = 0 ∨ y = 1 := by omega
    · have hl : (e ⟨0, l⟩ : ℕ) = l := std_val0 n (j + 1) _ (dd_sum n j) l
      have hln : (l : ℕ) < n := l.2
      rw [leviEmb_apply_ne k e _ (by decide), dif_neg (by omega), if_neg (by omega)]
    · have hl : (e ⟨1, l⟩ : ℕ) = n + l := std_val1 n (j + 1) _ (dd_sum n j) l
      have hs : Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 1 = 1 :=
        Pi.mulSingle_eq_of_ne (by decide) _
      rw [leviEmb_apply_same, dif_neg (by omega)]
      refine Eq.trans ?_ (congrArg (fun X : GL (Fin (dd n (j + 1) 1)) k =>
        (X : Matrix (Fin (dd n (j + 1) 1)) (Fin (dd n (j + 1) 1)) k) i l) hs).symm
      show _ = (1 : Matrix (Fin (dd n (j + 1) 1)) (Fin (dd n (j + 1) 1)) k) i l
      rw [Matrix.one_apply]
      by_cases h : i = l
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · have h' : (i : ℕ) ≠ l := fun e' => h (Fin.ext e')
        rw [if_neg h, if_neg (by omega)]

theorem unipRad_apply {n t N : ℕ} (h : ∑ a, dd n t a = N) {u : GL (Fin N) k}
    (hu : u ∈ unipRad k (stdBlocks (dd n t) h)) (a b : Fin N) (hab : (b : ℕ) < n ∨ n ≤ (a : ℕ)) :
    (u : Matrix (Fin N) (Fin N) k) a b = (1 : Matrix (Fin N) (Fin N) k) a b := by
  set e := stdBlocks (dd n t) h with he
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  obtain ⟨⟨x, i⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨y, l⟩, rfl⟩ := e.surjective b
  by_cases hxy : x = y
  · subst hxy
    rw [hD, Matrix.one_apply, Matrix.one_apply]
    simp
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by omega
    · have hi : (e ⟨0, i⟩ : ℕ) = i := std_val0 n t _ h i
      have hl : (e ⟨1, l⟩ : ℕ) = n + l := std_val1 n t _ h l
      have hin : (i : ℕ) < n := i.2
      omega
    · rw [mem_parab_iff.1 hP 1 0 i l (by decide)]
      exact (Matrix.one_apply_ne fun e' => hxy (by simpa using congrArg Sigma.fst (e.injective e'))).symm

theorem unipRad_le_derUnip {n t N : ℕ} (h : ∑ a, dd n t a = N) :
    unipRad k (stdBlocks (dd n t) h) ≤ derUnip k N n := by
  intro u hu
  have H := unipRad_apply h hu
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => H i j (Or.inl hj)⟩
  · rw [H i j (by have : (j : ℕ) < i := hji; omega)]
    exact Matrix.one_apply_ne (fun e => by rw [e] at hji; exact lt_irrefl _ hji)
  · rw [H i i (by omega)]
    exact Matrix.one_apply_eq i

theorem derChar_eq_one {n t N : ℕ} (h : ∑ a, dd n t a = N) (ψ : AddChar k Circle) (u : derUnip k N n)
    (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks (dd n t) h)) : derChar k ψ N n u = 1 := by
  have H := unipRad_apply h hu
  show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ),
    ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  rw [H _ _ (Or.inr h2)]
  exact Matrix.one_apply_ne fun e => by rw [e] at h1; omega

theorem isSubquotient_twist' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (χ : G →* ℂˣ) :
    IsSubquotient (twist σ χ) (twist ρ χ) := by
  obtain ⟨R, f, hf⟩ := h
  refine ⟨⟨R.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩, hf⟩
  · rw [twist_apply]
    exact R.toSubmodule.smul_mem _ (R.apply_mem_toSubmodule g hv)
  · show f.toLinearMap ((χ g : ℂ) • R.toRepresentation g v) = (χ g : ℂ) • σ g (f v)
    rw [map_smul]
    exact congrArg _ (f.isIntertwining _ _ g v)

theorem exists_jac_deriv (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    ∃ L : Jacquet π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) →ₗ[ℂ]
        TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1,
      Function.Surjective L ∧ ∀ (g : GL (Fin n) k) (v : V),
        L (Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
          (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v)) =
        GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v)) := by
  obtain ⟨p, hp, hq, hk⟩ := exists_proj ψ n j (resM k π)
  let q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1 :=
    (twKer (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1).mkQ ∘ₗ p
  have hker : twKer π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) 1 ≤ LinearMap.ker q := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have hmem : (u : GL (Fin (n + j + 1)) k) ∈ derUnip k (n + j + 1) n := unipRad_le_derUnip _ u.2
    have h1 : π (u : GL (Fin (n + j + 1)) k) v - (((1 : (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) →* ℂˣ) u : ℂˣ) : ℂ) • v ∈
        twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
      Submodule.subset_span ⟨⟨u, hmem⟩, v, by rw [derChar_eq_one (dd_sum n j) ψ ⟨u, hmem⟩ u.2]; rfl⟩
    rw [← GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + j) n V π] at h1
    exact (Submodule.Quotient.mk_eq_zero _).2 (hk (Submodule.mem_map_of_mem h1))
  refine ⟨(twKer π (unipRad k (stdBlocks (dd n (j + 1)) (dd_sum n j))) 1).liftQ q hker, ?_, fun g v => ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp y
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · rw [← embM_eq_leviEmb]
    exact congrArg (twKer (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1).mkQ (hq (levi k n g) v)

theorem delta_mulSingle (n j : ℕ) (g : GL (Fin n) k) :
    (deltaHalf k (fun a => Fin (dd n (j + 1) a))
      (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ =
      detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2))) g := by
  have h0 : Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 0 = g :=
    Pi.mulSingle_eq_same _ _
  have h1 : Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 1 = 1 :=
    Pi.mulSingle_eq_of_ne (by decide) _
  have hm : modExp (fun a => Fin (dd n (j + 1) a)) (0 : Fin 2) = (j : ℤ) + 1 := by
    simp [modExp, Fin.sum_univ_two, Finset.sum_filter]
  rw [deltaHalf_apply, Fin.prod_univ_two]
  have e0 : absPow k (((modExp (fun a => Fin (dd n (j + 1) a)) (0 : Fin 2) : ℤ) : ℂ) / 2)
      (GeneralLinearGroup.det (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 0)) =
      absPow k (((j : ℂ) + 1) / 2) (GeneralLinearGroup.det g) := by
    rw [hm]
    push_cast
    exact congrArg (fun X : GL (Fin n) k => absPow k (((j : ℂ) + 1) / 2) (GeneralLinearGroup.det X)) h0
  have e1 : absPow k (((modExp (fun a => Fin (dd n (j + 1) a)) (1 : Fin 2) : ℤ) : ℂ) / 2)
      (GeneralLinearGroup.det (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g 1)) = 1 := by
    rw [h1, map_one, map_one]
  rw [e0, e1, mul_one, detChar_apply, absPow_neg, MonoidHom.inv_apply]

theorem isSubquotient_of_quot {G X D : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup D] [Module ℂ D]
    (T : Representation ℂ G X) (R : Representation ℂ G D) (χ : G →* ℂˣ) (L : X →ₗ[ℂ] D)
    (hL : Function.Surjective L) (h : ∀ g x, L (T g x) = (χ g : ℂ) • R g (L x)) : IsSubquotient (twist R χ) T :=
  .of_surjective ⟨L, fun g => LinearMap.ext fun x => by
    show L (T g x) = twist R χ g (L x)
    rw [twist_apply, h]⟩ hL

abbrev iota (n t : ℕ) : GL (Fin n) k →* Levi k (fun a => Fin (dd n t a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (dd n t a)) k) (0 : Fin 2)

theorem isSubquotient_twist_deriv (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    IsSubquotient (twist (GlobalTheory.BZMir.deriv k ψ j π) (detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))))
      ((jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) :
        Representation ℂ (GL (Fin n) k) _) := by
  obtain ⟨L, hL, hLe⟩ := exists_jac_deriv ψ n j π
  refine isSubquotient_of_quot _ _ _ L hL fun g x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := congrArg (fun c : ℂˣ => (c : ℂ) • GlobalTheory.BZMir.deriv k ψ j π g (L (Submodule.Quotient.mk v)))
    (delta_mulSingle n j g)
  refine Eq.trans ?_ h1
  have h2 := hLe g v
  have h3 : (jac (stdBlocks (dd n (j + 1)) (dd_sum n j)) π).comp (iota n (j + 1)) g (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun a => Fin (dd n (j + 1) a))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g))⁻¹ : ℂˣ) : ℂ) •
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks (dd n (j + 1)) (dd_sum n j))
        (Pi.mulSingle (M := fun a => GL (Fin (dd n (j + 1) a)) k) (0 : Fin 2) g)) v) :=
    jac_mk _ π _ v
  rw [h3, map_smul, h2]

theorem exists_irr_block {n t : ℕ} {X W : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]
    (T : Representation ℂ (Levi k fun a => Fin (dd n t a)) X) (hT : HasFiniteLength T)
    (A : Representation ℂ (GL (Fin n) k) W) (hA : A.IsIrreducible)
    (h : IsSubquotient A (T.comp (iota n t) : Representation ℂ (GL (Fin n) k) X)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (dd n t a)) Y),
      τ.IsIrreducible ∧ IsSubquotient τ T ∧
        IsSubquotient A (τ.comp (iota n t) : Representation ℂ (GL (Fin n) k) Y) := by
  refine GlobalTheory.ProdSubquot.exists_irreducible_of_pred _ _ T
    (fun Y _ _ σ => IsSubquotient A (σ.comp (iota n t) : Representation ℂ (GL (Fin n) k) Y)) hT ?_ ?_ ?_ h
  · intro Y Y' _ _ _ _ σ σ' f hf' h
    exact h.trans (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp (.of_injective f hf') _)
  · intro Y _ _ σ h
    obtain ⟨R, f, hf⟩ := h
    have := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hA
    have : Nontrivial R.toSubmodule := hf.nontrivial
    exact R.toSubmodule.injective_subtype.nontrivial
  · intro B C hCB h
    let i : Representation.IntertwiningMap (C.toRepresentation.comp (iota n t) : Representation ℂ (GL (Fin n) k) _)
        (B.toRepresentation.comp (iota n t) : Representation ℂ (GL (Fin n) k) _) :=
      ⟨Submodule.inclusion hCB, fun _ => rfl⟩
    let q : Representation.IntertwiningMap (B.toRepresentation.comp (iota n t) : Representation ℂ (GL (Fin n) k) _)
        ((subQuot B C).comp (iota n t) : Representation ℂ (GL (Fin n) k) _) :=
      ⟨Submodule.mkQ _, fun _ => rfl⟩
    exact GlobalTheory.ProdSubquot.subquot_dichotomy _ _ _ _ _ _ _ _ _ i q hA (fun b hb =>
      ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (C.toSubmodule.comap B.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩) h

theorem exists_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n t : ℕ} {X W : Type} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (Levi k fun a => Fin (dd n t a)) X) (hs : IsSmooth T)
    (hT : HasFiniteLength T) (A : Representation ℂ (GL (Fin n) k) W) (hAi : A.IsIrreducible)
    (h : IsSubquotient A (T.comp (iota n t) : Representation ℂ (GL (Fin n) k) X)) :
    ∃ σ : ∀ a, IrrCl (GL (Fin (dd n t a)) k), IsSubquotient (piTensor fun a => (σ a).rep.ρ) T ∧
      Nonempty (Representation.Equiv (σ 0).rep.ρ A) := by
  obtain ⟨Y, _, _, τ, hτi, hτs, hP⟩ := exists_irr_block T hT A hAi h
  have hτsm : IsSmooth τ := hτs.isSmooth hs
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (dd n t) (⟨Y, τ, hτsm, hτi⟩ : IrrRep _)
  have h3 : IsSubquotient A ((piTensor fun a => (σ a).rep.ρ).comp (iota n t) :
      Representation ℂ (GL (Fin n) k) _) :=
    hP.trans (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _)
  have h4 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (fun a => (σ a).rep.ρ) (0 : Fin 2) hAi h3
  exact ⟨σ, (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective).trans hτs,
    GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hAi (σ 0).rep.irr h4⟩

theorem derivJac (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : GlobalTheory.BZSeg.DerivJac k := by
  intro ψ hc h1 n j V _ _ π hs hf S hS
  have hdd := dd_sum (n + 1) j
  have hχ : IsSmoothChar (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2)))) :=
    (isSmoothChar_absPow _).detChar
  have hSi := isIrreducible_twist S.irr (detChar (Fin (n + 1)) (absPow k (-(((j : ℂ) + 1) / 2))))
  have h2 := (isSubquotient_twist' hS _).trans (isSubquotient_twist_deriv ψ (n + 1) j π)
  obtain ⟨σ, hsub, ⟨E⟩⟩ := exists_tensor hA _ (isSmooth_jac _ hs)
    (GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ _ V π hs hf) _ hSi h2
  let y : Fin 2 → IrrGL k := fun a => ⟨dd (n + 1) (j + 1) a, σ a⟩
  have hy0 : y 0 = (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) := by
    rw [IrrGL.nu, IrrGL.tw_of]
    exact (IrrGL.of_rep (y 0)).symm.trans (IrrGL.of_eq_of.2 ⟨E⟩)
  have hy : y = ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), y 1] := by
    funext a
    fin_cases a
    · exact hy0
    · rfl
  have key : ∀ (w : Fin 2 → IrrGL k) (hw : ∑ a, (w a).1 = n + 1 + j + 1), w = y → 1 ≤ Zc.jm w hw π := by
    intro w hw hwy
    subst hwy
    exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 hsub)
  have hw : ∑ a, (y a).1 = n + 1 + j + 1 := hdd
  exact ⟨y 1, hy ▸ hw, rfl, key _ _ hy.symm⟩

theorem derivJac_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k :=
  fun _ _ _ _ _ hA => derivJac hA

end GlobalTheory.CompanionTheory.BZDerivJac

end
