import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveSemilinearNablaTWtOpEquivariant
import Development.AutomorphicArithmetic.DivisorFrames.EvalLocalElementMatrixEqOneOfPrimeNotDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem core {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] {n : ℕ} (F : Frame l ι n) {H : Type} [Group H]
    (e : F.G ≃* H) (io : PadicAlgCl l ≃+* ℂ) (A : H →* (ι → GL (Fin n) (PadicAlgCl l))) (bs : ι → GL (Fin n) (PadicAlgCl l))
    (sh : ι → ℤ) (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hf : F.IsEig mu θ) :
    ∃ Fm : H → NablaT ℂ n mu, Fm ≠ 0 ∧
      (∀ γ, e.symm γ ∈ F.Γ → ∀ g,
        Fm (γ * g) = wtOp ℂ n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (A γ τ)) (Fm g)) ∧
      (∀ κ : F.K, (∀ τ, Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) = (bs τ)⁻¹ * A (e κ) τ * bs τ) → ∀ c : ℂ,
        io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * c = 1 → ∀ g, Fm (g * e κ) = c • Fm g) ∧
      ∀ i (S : Finset H), (∀ g, g ∈ F.tr i ↔ e g ∈ S) → F.cst i = 1 → (∀ a ∈ S, A a = 1) → ∀ g,
        ∑ a ∈ S, Fm (g * a) = io (θ i) • Fm g := by
  classical
  obtain ⟨f, hf0, ⟨hf1, hf2⟩, hf3⟩ := hf
  obtain ⟨Φ, hΦ, hΦs, hΦw⟩ := UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant _ _ io n ι mu sh
  refine ⟨fun g => Φ (wtOp _ n mu sh (A g * bs) (f (e.symm g))), fun h => hf0 ?_, fun γ hγ g => ?_, fun κ hκ c hc g => ?_,
    fun i S hS hc hA g => ?_⟩
  · funext x
    have h1 : Φ (wtOp _ n mu sh (A (e x) * bs) (f (e.symm (e x)))) = 0 := congrFun h (e x)
    rw [e.symm_apply_apply, ← Φ.map_zero] at h1
    have h2 := congrArg (wtOp _ n mu sh (A (e x) * bs)⁻¹) (hΦ h1)
    rw [← Module.End.mul_apply, ← wtOp_mul, inv_mul_cancel, wtOp_one, map_zero] at h2
    exact h2
  · show Φ _ = wtOp _ _ _ _ _ (Φ _)
    rw [← hΦw, map_mul, map_mul, hf1 _ hγ, mul_assoc, wtOp_mul, Module.End.mul_apply]
  · show Φ _ = c • Φ _
    have hk : A (g * e κ) * bs = (A g * bs) * fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) := by
      funext τ
      simp only [Pi.mul_apply, map_mul, hκ]
      group
    rw [hk, map_mul, e.symm_apply_apply, wtOp_mul, Module.End.mul_apply, ← hf2 κ (e.symm g),
      wtOp_apply _ _ _ _ (fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)), LinearMap.map_smul, LinearMap.map_smul, hΦs, hΦs, smul_smul]
    congr 1
    have hd : ∀ τ, ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)) : (PadicAlgCl l)ˣ) :
        PadicAlgCl l) = F.emb (F.kap κ τ).val.det := fun τ => by
      simp [RingHom.map_det]
    simp only [zpow_neg, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hd]
    rw [map_mul] at hc
    rw [map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hc]
    ring
  · have h1 : ∑ a ∈ S, f (e.symm g * e.symm a) = ∑ s ∈ F.tr i, f (e.symm g * s) :=
      (Finset.sum_equiv e.toEquiv hS fun s _ => by simp).symm
    have h2 := hf3 i (e.symm g)
    rw [hc, map_one, one_smul, ← h1] at h2
    show ∑ a ∈ S, Φ _ = _ • Φ _
    rw [← hΦs, ← LinearMap.map_smul, ← h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, map_mul, hA a ha, mul_one]

set_option maxHeartbeats 800000 in
theorem UpperTheory.exists_nonzero_vectorValued_eigenform_unitary :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime]
        (F : Frame l D.what₂.Tau (Vc D j).rank) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
        (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
        (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l), F.IsEig mu θ →
        ∃ Fm : Bridge.Gf (Vc D j) → NablaT ℂ (Vc D j).rank mu, Fm ≠ 0 ∧
          (∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (γ₀ : GL (Fin (Vc D j).rank) D.host.E),
            Formalism.L2.Theta.matHom (Vc D j) γ = Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.incA D) γ₀ → ∀ g,
            Fm (Bridge.ratF (Vc D j) γ * g) = wtOp ℂ (Vc D j).rank mu T.sh
              (fun τ => Matrix.GeneralLinearGroup.map (T.io.toRingHom.comp (inc τ)) γ₀) (Fm g)) ∧
          (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) ∧
          ∀ i, (∀ a ∈ hkA p j t (ix i), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t (ix i).1) a) → ∀ g,
            ∑ a ∈ hkA p j t (ix i), Fm (g * a) = T.io (θ i) • Fm g := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t l _ F e0 ix inc T mu θ hf
  obtain ⟨A, hA⟩ : ∃ A : Bridge.Gf (Vc D j) →* (D.what₂.Tau → GL (Fin (Vc D j).rank) (PadicAlgCl l)),
      ∀ g τ, (A g τ).val = (matOf j g).map (T.ev τ) :=
    ⟨MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (T.ev τ)).comp (Bridge.Gf (Vc D j)).subtype, fun _ _ => rfl⟩
  obtain ⟨Fm, h0, h1, h2, h3⟩ := core F T.e T.io A T.bs T.sh mu θ hf
  refine ⟨Fm, h0, fun γ γ₀ hγ g => ?_, fun κ g => ?_, fun i hi g => ?_⟩
  · rw [h1 _ ((T.rat _).2 ⟨γ, (T.e.apply_symm_apply _).symm⟩)]
    congr 2
    funext τ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h4 : (Formalism.L2.Theta.matHom (Vc D j) γ).val a b = Formalism.L2.Theta.incA D (γ₀.val a b) := by rw [hγ]; rfl
    have h5 : matOf j (Bridge.ratF (Vc D j) γ) a b = 1 ⊗ₜ[D.host.F] γ₀.val a b :=
      congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) h4
    show T.io ((A _ τ).val a b) = T.io (inc τ (γ₀.val a b))
    rw [hA, Matrix.map_apply, h5, T.ev_rat]
  · have hrk : (T.rk : Fin (Vc D j).rank → Fin (Vc D j).rank) = id := by
      rw [Subsingleton.elim T.rk (OrderIso.refl _)]; rfl
    have hk : ∀ (k : F.K) τ, Matrix.GeneralLinearGroup.map F.emb (F.kap k τ) = (T.bs τ)⁻¹ * A (T.e k) τ * T.bs τ := by
      intro k τ
      have h := T.kap k τ
      rw [hrk, Matrix.submatrix_id_id, ← hA, ← Units.val_mul, ← Units.val_mul] at h
      exact Units.ext h
    obtain ⟨κ, hκ⟩ := κ
    obtain ⟨k, rfl⟩ := T.e.surjective κ
    obtain ⟨k', rfl⟩ : ∃ k' : F.K, (k' : F.G) = k := ⟨⟨k, (T.lev k).2 hκ⟩, rfl⟩
    exact h2 k' (hk k') _ (T.chi k' hκ) g
  · refine h3 i _ (T.tr i) (T.cst i) (fun a ha => ?_) g
    funext τ
    exact Units.ext ((hA a τ).trans
      (UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd D (Vc D j) l (T.ev τ) (T.ev_int τ) _ ((T.ix_range _).1 ⟨i, rfl⟩).2.2 a (hi a ha)))
