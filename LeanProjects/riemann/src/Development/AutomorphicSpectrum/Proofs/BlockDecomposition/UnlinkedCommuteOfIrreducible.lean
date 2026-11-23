import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Matrix
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZSegComm

open Zc.Cos (invT)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Inv

variable {n : Type} [Fintype n] [DecidableEq n]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem invT_invT (g : GL n k) : invT (invT g) = g := Units.ext (transpose_transpose _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_invT (g : GL n k) :
    GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  show ((g⁻¹).valᵀ).det = ((g⁻¹ : GL n k).val).det
  rw [det_transpose]

theorem continuous_invT : Continuous (invT : GL n k → GL n k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end Inv

section Levi

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]

variable (k m) in

def leviInvT : Levi k m →* Levi k m where
  toFun g a := invT (g a)
  map_one' := funext fun _ => map_one _
  map_mul' _ _ := funext fun _ => map_mul _ _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in

theorem leviInvT_leviInvT (g : Levi k m) : leviInvT k m (leviInvT k m g) = g :=
  funext fun _ => invT_invT _

theorem deltaHalf_leviInvT (g : Levi k m) : deltaHalf k m (leviInvT k m g) = (deltaHalf k m g)⁻¹ := by
  rw [deltaHalf_apply, deltaHalf_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  show absPow k _ (GeneralLinearGroup.det (invT (g a))) = _
  rw [det_invT, map_inv]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem invT_mem_parab {e : (Σ a, m a) ≃ n} {p : GL n k} (hp : p ∈ parabLower k e) :
    invT p ∈ parab k e :=
  mem_parab_iff.2 fun a b i j hab => (mem_parabLower_iff k).1 (inv_mem hp) b a j i hab

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem invT_mem_parabLower {e : (Σ a, m a) ≃ n} {q : GL n k} (hq : q ∈ parab k e) :
    invT q ∈ parabLower k e :=
  (mem_parabLower_iff k).2 fun a b i j hab => mem_parab_iff.1 (inv_mem hq) b a j i hab

theorem leviProj_invT (e : (Σ a, m a) ≃ n) (p : parabLower k e) :
    leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩ = leviInvT k m (leviProjLower k e p) := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : ((leviProjLower k e p) a)⁻¹ = leviProjLower k e p⁻¹ a := by rw [map_inv]; rfl
  show ((p.1⁻¹ : GL n k).val) (e ⟨a, j⟩) (e ⟨a, i⟩) = ((((leviProjLower k e p) a)⁻¹ : GL (m a) k).val) j i
  rw [h]
  rfl

theorem leviProjLower_invT (e : (Σ a, m a) ≃ n) (q : parab k e) :
    leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩ = leviInvT k m (leviProj k e q) := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : ((leviProj k e q) a)⁻¹ = leviProj k e q⁻¹ a := by rw [map_inv]; rfl
  show ((q.1⁻¹ : GL n k).val) (e ⟨a, j⟩) (e ⟨a, i⟩) = ((((leviProj k e q) a)⁻¹ : GL (m a) k).val) j i
  rw [h]
  rfl

theorem parIndLower_equiv_comp_invT (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Nonempty ((parIndLower e (ρ.comp (leviInvT k m))).Equiv
      ((parInd e ρ).comp (invT : GL n k →* GL n k))) := by
  refine GlobalTheory.SmGL.Relabel.smInd_equiv_comp (invT : GL n k →* GL n k) invT continuous_invT continuous_invT
    invT_invT invT_invT (fun q => ⟨⟨invT q.1, invT_mem_parabLower q.2⟩, rfl, ?_⟩)
    (fun p => ⟨⟨invT p.1, invT_mem_parab p.2⟩, rfl, ?_⟩)
  · refine LinearMap.ext fun v => ?_
    show (((deltaHalf k m (leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩))⁻¹ : ℂˣ) : ℂ) •
        ρ (leviInvT k m (leviProjLower k e ⟨invT q.1, invT_mem_parabLower q.2⟩)) v =
      (deltaHalf k m (leviProj k e q) : ℂ) • ρ (leviProj k e q) v
    rw [leviProjLower_invT, deltaHalf_leviInvT, inv_inv, leviInvT_leviInvT]
  · refine LinearMap.ext fun v => ?_
    show (deltaHalf k m (leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩) : ℂ) •
        ρ (leviProj k e ⟨invT p.1, invT_mem_parab p.2⟩) v =
      (((deltaHalf k m (leviProjLower k e p))⁻¹ : ℂˣ) : ℂ) • ρ (leviInvT k m (leviProjLower k e p)) v
    rw [leviProj_invT, deltaHalf_leviInvT]

end Levi

section Two

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

variable (k a b) in

def invTProd : GL a k × GL b k →* GL a k × GL b k := MonoidHom.prodMap invT invT

theorem ind₂Lower_equiv_comp_invT (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :
    Nonempty ((ind₂Lower e (ρ.comp (invTProd k a b))).Equiv
      ((ind₂ e ρ).comp (invT : GL n k →* GL n k))) := by
  have h : (ρ.comp (invTProd k a b)).comp (leviTwo k a b).symm.toMonoidHom =
      (ρ.comp (leviTwo k a b).symm.toMonoidHom).comp (leviInvT k (Two a b)) :=
    MonoidHom.ext fun g => rfl
  unfold ind₂Lower ind₂
  rw [h]
  exact parIndLower_equiv_comp_invT (two e) _

theorem ind₂_swap_equiv_comp_invT (e₁ : a ⊕ b ≃ n) (e₂ : b ⊕ a ≃ n)
    (ρ : Representation ℂ (GL a k × GL b k) W) :
    Nonempty ((ind₂ e₂ ((ρ.comp (invTProd k a b)).comp
        (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)).Equiv
      ((ind₂ e₁ ρ).comp (invT : GL n k →* GL n k))) := by
  obtain ⟨A⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k Bool n (Two b a) (two e₂)
    (two ((Equiv.sumComm b a).trans e₁)) W).1
    (((ρ.comp (invTProd k a b)).comp
      (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom).comp
        (leviTwo k b a).symm.toMonoidHom)
  obtain ⟨B⟩ := (GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap k a b n e₁ W).1 (ρ.comp (invTProd k a b))
  obtain ⟨C⟩ := ind₂Lower_equiv_comp_invT e₁ ρ
  exact ⟨(A.trans B.symm).trans C⟩

def ind₂Equiv {V : Type} [AddCommGroup V] [Module ℂ V] (e : a ⊕ b ≃ n)
    {ρ : Representation ℂ (GL a k × GL b k) W} {σ : Representation ℂ (GL a k × GL b k) V} (φ : ρ.Equiv σ) :
    (ind₂ e ρ).Equiv (ind₂ e σ) :=
  parIndEquiv _ (compEquiv φ _)

end Two

section Pair

theorem nonempty_comp_invT_equiv_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)) (contra π)) :=
  GlobalTheory.GelfandKazhdan.equiv_contra k N V π ha hi

theorem nonempty_extTensor_swap {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty (Representation.Equiv
      (((extTensor π₁ π₂).comp (invTProd k (Fin r) (Fin t))).comp
        (MulEquiv.prodComm : GL (Fin t) k × GL (Fin r) k ≃* GL (Fin r) k × GL (Fin t) k).toMonoidHom)
      (extTensor (π₂.comp (invT : GL (Fin t) k →* GL (Fin t) k))
        (π₁.comp (invT : GL (Fin r) k →* GL (Fin r) k)))) :=
  ⟨.mk (TensorProduct.comm ℂ V W) fun g => by
    ext v w
    rfl⟩

def extTensorCongr {r t : ℕ} {V W V' W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    {σ₁ : Representation ℂ (GL (Fin r) k) V'} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : π₁.Equiv σ₁) (φ₂ : π₂.Equiv σ₂) : (extTensor π₁ π₂).Equiv (extTensor σ₁ σ₂) :=
  .mk (TensorProduct.congr φ₁.toLinearEquiv φ₂.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ₁.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (φ₂.toIntertwiningMap.isIntertwining _ _ g.2 w)

theorem nonempty_ind₂_equiv_multiProd {N : ℕ} {d : Fin 2 → ℕ} (hd : ∑ a, d a = N) (h : d 0 + d 1 = N)
    {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty ((ind₂ (stdSum h) (extTensor (π 0) (π 1))).Equiv (multiProd (stdBlocks d hd) π)) := by
  subst h
  exact nonempty_prod₂_equiv_multiProd hd π

theorem nonempty_ind₂_contra_equiv (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (F : Fin 2 → IrrGL k) {N : ℕ}
    (hd : ∑ a, (F a).1 = N) (h : (F 0).1 + (F 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra (F 0).rep) (contra (F 1).rep))).Equiv
      (contra (prodIrr F hd))) := by
  have E₂ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h
    (X := fun a => smoothPart (F a).rep.dual) fun a => contra (F a).rep
  have E₃ := GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr_multiProd hA F hd
  exact E₂.elim fun e₂ => E₃.elim fun e₃ => ⟨e₂.trans e₃⟩

theorem prodIrr_swap_of_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (F G : Fin 2 → IrrGL k)
    (e₀ : G 0 = F 1) (e₁ : G 1 = F 0) {N : ℕ} (hd : ∑ a, (F a).1 = N) (hd' : ∑ a, (G a).1 = N)
    (hX : (prodIrr F hd).IsIrreducible) (hY : (prodIrr G hd').IsIrreducible) :
    Nonempty ((prodIrr F hd).Equiv (prodIrr G hd')) := by
  have h : (F 0).1 + (F 1).1 = N := (Fin.sum_univ_two _).symm.trans hd
  have h' : (G 0).1 + (G 1).1 = N := (Fin.sum_univ_two _).symm.trans hd'
  have h'' : (F 1).1 + (F 0).1 = N := by rw [← e₀, ← e₁]; exact h'
  have E₁ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h fun a => (F a).rep
  have E₂ := nonempty_ind₂_contra_equiv hA G hd' h'
  have E₃ : ∀ (u v : IrrGL k), u = F 1 → v = F 0 → ∀ h₁ : u.1 + v.1 = N,
      Nonempty ((ind₂ (stdSum h'') (extTensor (contra (F 1).rep) (contra (F 0).rep))).Equiv
        (ind₂ (stdSum h₁) (extTensor (contra u.rep) (contra v.rep)))) := by
    rintro _ _ rfl rfl _
    exact ⟨.refl _⟩
  have E₄ := E₃ _ _ e₀ e₁ h'
  have Gx := nonempty_comp_invT_equiv_contra (F 0).rep (hA k _ _ _ (F 0).2.rep.smooth (F 0).2.rep.irr)
    (F 0).2.rep.irr
  have Gy := nonempty_comp_invT_equiv_contra (F 1).rep (hA k _ _ _ (F 1).2.rep.smooth (F 1).2.rep.irr)
    (F 1).2.rep.irr
  have T := nonempty_extTensor_swap (F 0).rep (F 1).rep
  have K := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h'') (extTensor (F 0).rep (F 1).rep)
  have aX := hA k N _ _ (isSmooth_prodIrr _ hd) hX
  have aY := hA k N _ _ (isSmooth_prodIrr _ hd') hY
  have GX := nonempty_comp_invT_equiv_contra (prodIrr F hd) aX hX
  refine (GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin N) k) (GlobalTheory.LocalThetaGL.compact_open_basis _)
    _ _ _ _ aX aY).2.2 ?_
  exact E₁.elim fun ε₁ => E₂.elim fun ε₂ => E₄.elim fun ε₄ => Gx.elim fun gx => Gy.elim fun gy => T.elim fun t =>
    K.elim fun κ => GX.elim fun gX =>
      ⟨(((compEquiv ε₁ _).trans gX).symm.trans (κ.symm.trans
        ((ind₂Equiv _ (t.trans (extTensorCongr gy gx))).trans ε₄))).trans ε₂⟩

end Pair

theorem lUnlinkedComm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.LUnlinkedIrr k → GlobalTheory.BZSeg.LUnlinkedComm k := by
  intro k _ _ _ _ hA hI Δ Δ' x y N hd hd' hl hx hy
  have hl' : ¬ Δ'.Linked Δ := fun h => hl h.symm
  have hXi : (prodIrr ![x, y] hd).IsIrreducible := by
    refine hI 2 N ![Δ, Δ'] ![x, y] hd ?_ ?_
    · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨Segment.not_linked_self _, hl⟩,
        Fin.forall_fin_two.2 ⟨hl', Segment.not_linked_self _⟩⟩
    · exact Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hYi : (prodIrr ![y, x] hd').IsIrreducible := by
    refine hI 2 N ![Δ', Δ] ![y, x] hd' ?_ ?_
    · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨Segment.not_linked_self _, hl'⟩,
        Fin.forall_fin_two.2 ⟨hl, Segment.not_linked_self _⟩⟩
    · exact Fin.forall_fin_two.2 ⟨hy, hx⟩
  exact prodIrr_swap_of_isIrreducible hA ![x, y] ![y, x] rfl rfl hd hd' hXi hYi

end GlobalTheory.CompanionTheory.BZSegComm

end
