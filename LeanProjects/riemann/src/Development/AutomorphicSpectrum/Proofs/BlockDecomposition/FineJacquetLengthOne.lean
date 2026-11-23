import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.CompanionTheory.SegFine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {n : ℕ}

abbrev ev (k : Type) [Field k] (n : ℕ) : (∀ _ : Fin 1, GL (Fin n) k) →* GL (Fin n) k :=
  Pi.evalMonoidHom (fun _ : Fin 1 => GL (Fin n) k) 0

abbrev lv (τ : Representation ℂ (GL (Fin n) k) X) : Representation ℂ (∀ _ : Fin 1, GL (Fin n) k) X := τ.comp (ev k n)

theorem stdBlocks_one (h : ∑ _ : Fin 1, n = n) (a : Fin 1) (i : Fin n) :
    stdBlocks (fun _ : Fin 1 => n) h ⟨a, i⟩ = i :=
  Fin.ext (by rw [stdBlocks_val, Subsingleton.elim a 0]; simp)

theorem leviEmb_one (h : ∑ _ : Fin 1, n = n) (g : ∀ _ : Fin 1, GL (Fin n) k) :
    leviEmb k (stdBlocks (fun _ : Fin 1 => n) h) g = g 0 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := leviEmb_apply_same k (stdBlocks (fun _ : Fin 1 => n) h) g 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

theorem unipRad_one (h : ∑ _ : Fin 1, n = n) : unipRad k (stdBlocks (fun _ : Fin 1 => n) h) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => Units.ext (Matrix.ext fun i j => ?_)
  have := (mem_unipRad.1 hu).2 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

def jacEquiv (h : ∑ _ : Fin 1, n = n) (π : Representation ℂ (GL (Fin n) k) V) :
    (lv π).Equiv (jac (stdBlocks (fun _ : Fin 1 => n) h) π) := by
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 = ⊥ := by
    rw [unipRad_one]
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp
  have hd : ∀ g, deltaHalf k (fun _ : Fin 1 => Fin n) g = 1 := fun g => by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  let f : (lv π).IntertwiningMap (jac (stdBlocks (fun _ : Fin 1 => n) h) π) :=
    ⟨(twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1).mkQ, fun g => LinearMap.ext fun v => by
      show Submodule.Quotient.mk (π (g 0) v) = jac _ π g (Submodule.Quotient.mk v)
      rw [jac_mk, hd, leviEmb_one]
      simp⟩
  refine equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, Submodule.Quotient.mk_surjective _⟩
  have : v ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  rw [hK] at this
  exact this

def piTensorEquiv (τ : Representation ℂ (GL (Fin n) k) X) :
    (lv τ).Equiv (piTensor fun _ : Fin 1 => τ) := by
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => X) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  let f : (lv τ).IntertwiningMap (piTensor fun _ : Fin 1 => τ) :=
    ⟨L.toLinearMap, fun g => LinearMap.ext fun v => by
      show L (τ (g 0) v) = piTensor (fun _ : Fin 1 => τ) g (L v)
      rw [hL, hL, piTensor_tprod]
      exact congrArg _ (funext fun a => by rw [Subsingleton.elim a 0])⟩
  exact equivOfBijective f L.bijective

def subrepComp (τ : Representation ℂ (GL (Fin n) k) X) :
    Subrepresentation (lv τ) ≃o Subrepresentation τ where
  toFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (fun _ => g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (g 0) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {τ : Representation ℂ (GL (Fin n) k) X} (h : τ.IsIrreducible) :
    (lv τ).IsIrreducible := (subrepComp τ).isSimpleOrder_iff.2 h

theorem jhMult_one (h : ∑ _ : Fin 1, n = n) (τ : Representation ℂ (GL (Fin n) k) X)
    (π : Representation ℂ (GL (Fin n) k) V) :
    jhMult (piTensor fun _ : Fin 1 => τ) (jac (stdBlocks (fun _ : Fin 1 => n) h) π) =
      jhMult (lv τ) (lv π) := by
  rw [← jhMult_congr_left (piTensorEquiv τ), ← jhMult_congr_right _ (jacEquiv h π)]

theorem jm_eq_one (x : IrrGL k) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL k) (hy : ∑ a, (y a).1 = x.1) (hyx : y = fun _ => x) : jm y hy π = 1 := by
  subst hyx
  refine (jhMult_one hy x.rep π).trans ?_
  rw [jhMult_congr_right _ (compEquiv φ (ev k x.1))]
  exact jhMult_self (isIrreducible_comp x.2.rep.irr)

theorem eq_of_one_le_jm (x : IrrGL k) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL k) (hy : ∑ a, (y a).1 = x.1) (h : 1 ≤ jm y hy π) : y 0 = x := by
  obtain ⟨z, rfl⟩ : ∃ z, y = fun _ => z := ⟨y 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨d, c⟩ := z
  obtain ⟨m, b⟩ := x
  obtain rfl : d = m := by simpa using hy
  have h0 : jhMult (lv c.rep.ρ) (lv π) ≠ 0 := by
    rw [← jhMult_one hy]
    exact ENat.one_le_iff_ne_zero.1 h
  have hπ : π.IsIrreducible := isIrreducible_of_equiv φ.symm b.rep.irr
  obtain ⟨E⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv (isIrreducible_comp c.rep.irr) (isIrreducible_comp hπ)
  let f : π.IntertwiningMap c.rep.ρ := ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun v =>
    E.toIntertwiningMap.isIntertwining _ _ (fun _ => g) v⟩
  have E' : c.rep.ρ.Equiv b.rep.ρ := (equivOfBijective f E.toLinearEquiv.bijective).symm.trans φ
  exact congrArg (Sigma.mk d) (irrCl_eq_iff.2 ⟨E'⟩)

theorem dec_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : dec (Segment.single ρ hρ) = fun _ => ρ := funext fun a => by
  show ρ.nu (((Fin.rev (a : Fin 1) : Fin 1) : ℕ) : ℂ) = ρ
  simp [Fin.val_eq_zero]

theorem not_one_le_jm {N c : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsCuspidal π)
    (y : Fin (c + 2) → IrrGL k) (hy : ∑ a, (y a).1 = N) (hc : ∀ a, (y a).IsCusp) : ¬ 1 ≤ jm y hy π := by
  intro h
  have hne : unipRad k (stdBlocks (fun a => (y a).1) hy) ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2
    ⟨stdBlocks (fun a => (y a).1) hy ⟨0, ⟨0, (hc 0).1⟩⟩, stdBlocks (fun a => (y a).1) hy ⟨1, ⟨0, (hc 1).1⟩⟩, by simp⟩
  have := hπ.2 _ _ _ hne
  have hn : Nontrivial (PiTensorProduct ℂ fun a => (y a).2.rep.V) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ fun a => Model.nontrivial_of_isIrreducible (y a).2.rep.irr
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h)
  exact not_subsingleton _ hf.subsingleton

theorem fineJac_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJac Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  obtain rfl : ρ.1 = N := by
    have := hπ.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique hπ
  refine ⟨fun hd => jm_eq_one ρ π φ _ hd (dec_single ρ hρ), fun c y hy hc h1 => ?_⟩
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL k) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (dec_single ρ hρ) _).symm⟩
  · exact absurd h1 (not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

end GlobalTheory.CompanionTheory.SegFine

end
