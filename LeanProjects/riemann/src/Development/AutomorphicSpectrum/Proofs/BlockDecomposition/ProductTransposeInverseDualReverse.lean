import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaProd

theorem sum_castLE {h : ℕ} (f : Fin h → ℕ) (c : Fin h) :
    ∑ b : Fin c, f (Fin.castLE c.2.le b) = ∑ b with b < c, f b := by
  refine Finset.sum_bij (fun b _ => Fin.castLE c.2.le b) (fun b _ => ?_) (fun b _ b' _ hb => ?_)
    (fun b hb => ?_) (fun b _ => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 b.2⟩
  · exact Fin.castLE_injective _ hb
  · exact ⟨⟨b, Fin.lt_def.1 (Finset.mem_filter.1 hb).2⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem sum_split {h : ℕ} (d : Fin h → ℕ) (c : Fin h) :
    ∑ b, d b = (∑ b with b < c, d b) + d c + ∑ b with c < b, d b := by
  have hc : d c = ∑ b, if b = c then d b else 0 := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with hb | rfl | hb
  · simp [hb, hb.ne, not_lt.2 hb.le]
  · simp
  · simp [hb, hb.ne', not_lt.2 hb.le]

theorem sum_lt_rev {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b with b < a, d (Fin.rev b) = ∑ b with Fin.rev a < b, d b := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 1
  exact propext ⟨fun hb => by simpa using Fin.rev_lt_rev.2 hb, fun hb => by simpa using Fin.rev_lt_rev.2 hb⟩

theorem rev_stdBlocks {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (a : Fin h) (j : Fin (d (Fin.rev a))) :
    Fin.rev (stdBlocks (fun a => d (Fin.rev a)) hd' ⟨a, j⟩) = stdBlocks d hd ⟨Fin.rev a, Fin.rev j⟩ := by
  apply Fin.ext
  rw [Fin.val_rev (stdBlocks (fun a => d (Fin.rev a)) hd' ⟨a, j⟩)]
  simp only [stdBlocks_val, sum_castLE d]
  rw [sum_castLE (fun b => d (Fin.rev b)) a, sum_lt_rev, Fin.val_rev j]
  have h1 := sum_split d (Fin.rev a)
  have h2 := j.2
  omega

theorem modExp_rev {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    modExp (fun b => Fin (d (Fin.rev b))) (Fin.rev a) = -modExp (fun b => Fin (d b)) a := by
  unfold modExp
  simp only [Fintype.card_fin]
  have h1 : ∑ b with Fin.rev a < b, (d (Fin.rev b) : ℤ) = ∑ b with b < a, (d b : ℤ) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev]
  have h2 : ∑ b with b < Fin.rev a, (d (Fin.rev b) : ℤ) = ∑ b with a < b, (d b : ℤ) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev]
  rw [h1, h2]
  ring

theorem blk_rev {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) (i : Fin N) :
    blk (stdBlocks (fun a => d (Fin.rev a)) hd') (Fin.rev i) = Fin.rev (blk (stdBlocks d hd) i) := by
  obtain ⟨⟨a, j⟩, hj⟩ := (stdBlocks (fun a => d (Fin.rev a)) hd').surjective (Fin.rev i)
  have h1 := rev_stdBlocks d hd hd' a j
  rw [hj, Fin.rev_rev] at h1
  rw [← hj, blk_apply, h1, blk_apply, Fin.rev_rev]

variable {A : Type} [CommRing A]

theorem thetaW_mem_parab_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) A) :
    thetaW A N g ∈ parab A (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ parab A (stdBlocks d hd) := by
  rw [← inv_mem_iff (x := g), mem_parab, mem_parab]
  constructor
  · intro H i j hij
    have := H (Fin.rev j) (Fin.rev i) (by rw [blk_rev d hd hd', blk_rev d hd hd']; exact Fin.rev_lt_rev.2 hij)
    rwa [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, Fin.rev_rev, Fin.rev_rev] at this
  · intro H i j hij
    rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply]
    refine H _ _ ?_
    rw [← Fin.rev_rev i, ← Fin.rev_rev j, blk_rev d hd hd', blk_rev d hd hd'] at hij
    exact Fin.rev_lt_rev.1 hij

def thetaL {h : ℕ} (d : Fin h → ℕ) :
    Levi A (fun a => Fin (d a)) →* Levi A (fun a => Fin (d (Fin.rev a))) :=
  MonoidHom.pi fun a => (thetaW A (d (Fin.rev a))).comp (Pi.evalMonoidHom (fun b => GL (Fin (d b)) A) (Fin.rev a))

theorem leviProj_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (p : parab A (stdBlocks d hd)) :
    leviProj A (stdBlocks (fun a => d (Fin.rev a)) hd') ⟨thetaW A N p, (thetaW_mem_parab_iff d hd hd' _).2 p.2⟩ =
      thetaL d (leviProj A (stdBlocks d hd) p) := by
  funext a
  ext i j
  rw [leviProj_apply]
  show (thetaW A N (p : GL (Fin N) A)).1 _ _ = (thetaW A (d (Fin.rev a)) (leviProj A (stdBlocks d hd) p (Fin.rev a))).1 i j
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, GlobalTheory.CompanionTheory.ThetaInv.thetaW_val_apply, rev_stdBlocks d hd hd',
    rev_stdBlocks d hd hd']
  have e1 : (leviProj A (stdBlocks d hd) p (Fin.rev a))⁻¹ = leviProj A (stdBlocks d hd) p⁻¹ (Fin.rev a) := by
    rw [map_inv]; rfl
  rw [e1, leviProj_apply]
  rfl

theorem det_thetaW (N : ℕ) (g : GL (Fin N) A) :
    Matrix.GeneralLinearGroup.det (thetaW A N g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  have h1 : Matrix.GeneralLinearGroup.det (thetaW A N g) = Matrix.GeneralLinearGroup.det g⁻¹ := by
    ext
    simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.det_submatrix_equiv_self,
      Matrix.det_transpose]
  rw [h1, map_inv]

theorem continuous_thetaW [TopologicalSpace A] [IsTopologicalRing A] (N : ℕ) :
    Continuous (thetaW A N) := by
  have hT : Continuous (invT : GL (Fin N) A → GL (Fin N) A) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_coe_inv.matrix_transpose
    · exact Units.continuous_val.matrix_transpose
  have hR : Continuous ((Matrix.reindexAlgEquiv A A (Fin.revPerm : Equiv.Perm (Fin N))).toAlgHom.toMonoidHom) := by
    show Continuous fun m : Matrix (Fin N) (Fin N) A => Matrix.reindexAlgEquiv A A (Fin.revPerm : Equiv.Perm (Fin N)) m
    simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
    exact continuous_id.matrix_submatrix _ _
  exact (Continuous.units_map _ hR).comp hT

section Modulus

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_thetaL {h : ℕ} (d : Fin h → ℕ) (g : Levi k (fun a => Fin (d a))) :
    deltaHalf k (fun a => Fin (d (Fin.rev a))) (thetaL d g) = deltaHalf k (fun a => Fin (d a)) g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  have hg : ∀ a, Matrix.GeneralLinearGroup.det (thetaL d g a) = (Matrix.GeneralLinearGroup.det (g (Fin.rev a)))⁻¹ :=
    fun a => det_thetaW _ _
  simp only [hg]
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, modExp_rev, Int.cast_neg, neg_div, absPow_neg, map_inv,
    MonoidHom.inv_apply, inv_inv]
  exact congrArg (fun b => (absPow k ((modExp (fun b => Fin (d b)) a : ℂ) / 2)) (Matrix.GeneralLinearGroup.det (g b)))
    (Fin.rev_rev a)

end Modulus

section Tensor

open scoped TensorProduct

def revPi {h : ℕ} (Γ : Fin h → Type) [∀ a, Group (Γ a)] : (∀ a, Γ a) →* ∀ a, Γ (Fin.rev a) :=
  MonoidHom.pi fun a => Pi.evalMonoidHom Γ (Fin.rev a)

def revTensor {h : ℕ} (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] a, X (Fin.rev a) :=
  PiTensorProduct.reindex ℂ X Fin.revPerm

theorem revTensor_tprod {h : ℕ} {X : Fin h → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (x : ∀ a, X a) : revTensor X (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun a => x (Fin.rev a) :=
  PiTensorProduct.reindex_tprod _ _

def piTensorRevEquiv {h : ℕ} {Γ X : Fin h → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (piTensor τ).Equiv ((piTensor fun a => τ (Fin.rev a)).comp (revPi Γ)) :=
  .mk (revTensor X) fun g => by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply]
    rw [piTensor_tprod, revTensor_tprod, revTensor_tprod, piTensor_tprod]
    rfl

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def equivCompOfInv {θ : G →* G} (hθ : ∀ g, θ (θ g) = g) {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : Representation.Equiv (ρ.comp θ) σ) : ρ.Equiv (σ.comp θ) :=
  .mk e.toLinearEquiv fun g => by
    have := e.toIntertwiningMap.isIntertwining' (θ g)
    simpa only [MonoidHom.comp_apply, hθ] using this

def equivOfCompInv {θ : G →* G} (hθ : ∀ g, θ (θ g) = g) {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : ρ.Equiv (σ.comp θ)) : Representation.Equiv (ρ.comp θ) σ :=
  .mk e.toLinearEquiv fun g => by
    have := e.toIntertwiningMap.isIntertwining' (θ g)
    simpa only [MonoidHom.comp_apply, hθ] using this

end Tensor

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

@[irreducible] def dualClass (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) : IrrCl (GL (Fin y.1) k) :=
  (⟨_, contra y.rep, isSmooth_smoothRep _, GlobalTheory.CompanionTheory.Zcore.isIrreducible_contra_rep hA y⟩ : IrrRep _).cl

abbrev dualOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) : IrrGL k := ⟨y.1, dualClass hA y⟩

theorem dualOf_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) : dualOf hA y = dualCl y := by
  rw [GlobalTheory.CompanionTheory.Zcore.dualCl_eq_of hA y, dualOf, dualClass]
  rfl

def dualOfEquiv (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) :
    (contra y.rep).Equiv (dualOf hA y).rep := by
  unfold dualOf dualClass
  exact IrrGL.equivOf _ _ _

abbrev dualRev (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) : Fin h → IrrGL k :=
  fun a => dualOf hA (x (Fin.rev a))

theorem dualRev_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    dualRev hA x = fun a => dualCl (x (Fin.rev a)) :=
  funext fun _ => dualOf_eq hA _

theorem sum_dualRev (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : ∑ a, (dualRev hA x a).1 = N :=
  (Equiv.sum_comp Fin.revPerm fun a => (x a).1).trans hd

def blockEquiv (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h : ℕ} (x : Fin h → IrrGL k)
    (a : Fin h) : (x (Fin.rev a)).rep.Equiv ((dualRev hA x a).rep.comp (thetaW k (x (Fin.rev a)).1)) := by
  have e1 := (GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK _ (x (Fin.rev a)).rep (x (Fin.rev a)).2.rep.smooth
      (x (Fin.rev a)).2.rep.irr).some
  have e2 := dualOfEquiv hA (x (Fin.rev a))
  exact equivCompOfInv (GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW _) (e1.trans e2)

theorem parInd_thetaW {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ (Levi k fun a => Fin (d (Fin.rev a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (ρ'.comp (thetaL d))).Equiv
      ((parInd (stdBlocks (fun a => d (Fin.rev a)) hd') ρ').comp (thetaW k N))) := by
  refine GlobalTheory.SmGL.Relabel.smInd_equiv_comp (thetaW k N) (thetaW k N) (continuous_thetaW N)
    (continuous_thetaW N) (GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW N) (GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW N)
    (fun q => ?_) (fun p => ?_)
  · let p : parab k (stdBlocks d hd) := ⟨thetaW k N q,
      (thetaW_mem_parab_iff d hd hd' _).1 (by rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]; exact q.2)⟩
    have hq : leviProj k (stdBlocks (fun a => d (Fin.rev a)) hd') q =
        thetaL d (leviProj k (stdBlocks d hd) p) := by
      have hpq : (⟨thetaW k N p, (thetaW_mem_parab_iff d hd hd' _).2 p.2⟩ :
          parab k (stdBlocks (fun a => d (Fin.rev a)) hd')) = q :=
        Subtype.ext (GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW N (q : GL (Fin N) k))
      rw [← hpq, leviProj_thetaW d hd hd' p]
    refine ⟨p, rfl, ?_⟩
    show twist (ρ'.comp (thetaL d)) (deltaHalf k _) (leviProj k _ p) =
      twist ρ' (deltaHalf k _) (leviProj k _ q)
    rw [hq]
    ext v
    simp only [twist_apply, MonoidHom.comp_apply, deltaHalf_thetaL]
  · refine ⟨⟨thetaW k N p, (thetaW_mem_parab_iff d hd hd' _).2 p.2⟩, rfl, ?_⟩
    have hl := leviProj_thetaW d hd hd' p
    show twist ρ' (deltaHalf k _) (leviProj k _ _) =
      twist (ρ'.comp (thetaL d)) (deltaHalf k _) (leviProj k _ p)
    rw [hl]
    ext v
    simp only [twist_apply, MonoidHom.comp_apply, deltaHalf_thetaL]

theorem piTensor_comp_thetaL {h : ℕ} (d : Fin h → ℕ) {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (σ : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (Y a)) :
    (piTensor fun a => (σ a).comp (thetaW k (d (Fin.rev a)))).comp (revPi fun a => GL (Fin (d a)) k) =
      (piTensor σ).comp (thetaL d) := by
  refine MonoidHom.ext fun g => PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, MonoidHom.comp_apply, piTensor_tprod]
  rfl

def equivOfEq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ σ : Representation ℂ G V} (h : ρ = σ) :
    ρ.Equiv σ :=
  .mk (LinearEquiv.refl ℂ V) fun g => by rw [h]; rfl

theorem product_compose_transpose_inverse (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Nonempty (Representation.Equiv ((prodIrr x hd).comp (thetaW k N))
      (prodIrr (dualRev hA x) (sum_dualRev hA x hd))) := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have φ₂ := (parInd_thetaW (k := k) (fun a => (x a).1) hd hd' (piTensor fun a => (dualRev hA x a).rep)).some
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  have φ₁ := parIndEquiv (stdBlocks (fun a => (x a).1) hd) T
  exact ⟨equivOfCompInv (GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW N) (φ₁.trans φ₂)⟩

theorem exists_equiv_prodIrr_of_eq {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL k} (hyz : y = z) (hy : ∑ a, (y a).1 = N)
    (H : Nonempty (R.Equiv (prodIrr y hy))) : ∃ hz : ∑ a, (z a).1 = N, Nonempty (R.Equiv (prodIrr z hz)) := by
  subst hyz
  exact ⟨hy, H⟩

theorem prodIrr_comp_thetaW : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      ∃ hd' : ∑ a, (dualCl (x (Fin.rev a))).1 = N,
        Nonempty (Representation.Equiv ((prodIrr x hd).comp (thetaW k N))
          (prodIrr (fun a => dualCl (x (Fin.rev a))) hd')) := by
  intro k _ _ _ _ hA hGK h N x hd
  exact exists_equiv_prodIrr_of_eq (dualRev_eq hA x) _ (product_compose_transpose_inverse hA hGK x hd)

end Main

end GlobalTheory.CompanionTheory.ThetaProd
