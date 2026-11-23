import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCInduction

open Formalism.L2.DIV GlobalTheory.BI

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem parab_eq_blockTri (b : Fin r → Fin s) :
    parab K b = blockTri (κ := K) (fun i => (b i : ℕ)) := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    exact ⟨hg, (blockTri (κ := K) (fun i => (b i : ℕ))).inv_mem hg⟩

omit [Fintype K] [DecidableEq K] in

def blockGL (b : Fin r → Fin s) (c : Fin s) :
    GL (Fin (Fintype.card {i // b i = c})) K ≃* GL {i // b i = c} K :=
  glEquiv K (Fintype.equivFin {i // b i = c}).symm

omit [Fintype K] [DecidableEq K] in
theorem blockGL_apply (b : Fin r → Fin s) (c : Fin s) (g : GL (Fin (Fintype.card {i // b i = c})) K)
    (x y : {i // b i = c}) :
    ((blockGL b c g : GL {i // b i = c} K) : Matrix _ _ K) x y =
      (g : Matrix _ _ K) (Fintype.equivFin _ x) (Fintype.equivFin _ y) := rfl

theorem sum_unipRadical_eq_zero (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K))
    (hτ : IsCuspidal K τ) (c' : Fin (Fintype.card {i // b i = c}) → ℕ) (hc' : ∃ i j, c' i ≠ c' j) :
    ∑ᶠ u : GlobalTheory.FiniteGL.unipRadical K c', LinearMap.trace ℂ τ (τ.ρ (blockGL b c u)) = 0 := by
  classical
  let _ : Fintype (GlobalTheory.FiniteGL.unipRadical K c') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let ρu : Representation ℂ (GlobalTheory.FiniteGL.unipRadical K c') τ :=
    τ.ρ.comp ((blockGL b c).toMonoidHom.comp (GlobalTheory.FiniteGL.unipRadical K c').subtype)
  refine (GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff ρu).2 ?_
  intro v hv
  obtain ⟨i0, j0, h0⟩ : ∃ i0 j0, c' i0 < c' j0 := by
    obtain ⟨i, j, hij⟩ := hc'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  let F := Fintype.equivFin {i // b i = c}
  let bb : {i // b i = c} → Fin 2 := fun x => if c' (F x) ≤ c' i0 then 0 else 1
  have hbb : Function.Surjective bb := by
    intro k
    fin_cases k
    · exact ⟨F.symm i0, by simp [bb]⟩
    · exact ⟨F.symm j0, by simp [bb, not_le.2 h0]⟩
  refine hτ 2 bb hbb le_rfl v fun u hu => ?_
  set u' := (blockGL b c).symm u with hu'def
  have hu'u : blockGL b c u' = u := MulEquiv.apply_symm_apply _ _
  have hent : ∀ k l, (u' : Matrix _ _ K) k l = (u : Matrix _ _ K) (F.symm k) (F.symm l) := by
    intro k l
    rw [← hu'u, blockGL_apply]
    simp [F]
  have hmem : u' ∈ GlobalTheory.FiniteGL.unipRadical K c' := by
    rw [GlobalTheory.FiniteGL.mem_unipRadical]
    intro k l hlk
    rw [Matrix.sub_apply, hent]
    have hb : ∀ m, bb (F.symm m) = if c' m ≤ c' i0 then 0 else 1 := fun m => by simp [bb]
    by_cases hkl : bb (F.symm k) = bb (F.symm l)
    · rw [hu.2 _ _ hkl]
      by_cases e : k = l
      · subst e; simp
      · rw [if_neg (fun h => e (F.symm.injective h)), Matrix.one_apply_ne e, sub_zero]
    · have hk : ¬ c' k ≤ c' i0 := fun hk => hkl (by rw [hb, hb, if_pos hk, if_pos (hlk.trans hk)])
      have hl : c' l ≤ c' i0 := by
        by_contra hl
        exact hkl (by rw [hb, hb, if_neg hk, if_neg hl])
      have hlt : bb (F.symm l) < bb (F.symm k) := by
        rw [hb, hb, if_neg hk, if_pos hl]; decide
      have ekl : k ≠ l := fun e => hkl (by rw [e])
      rw [hu.1.1 _ _ hlt, Matrix.one_apply_ne ekl, sub_zero]
  have := hv ⟨u', hmem⟩
  simpa [ρu, hu'u] using this

theorem isIrrChar_block (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K)) (hτ : Simple τ) :
    IsIrrChar ℂ ℂ (fun g : GL (Fin (Fintype.card {i // b i = c})) K => LinearMap.trace ℂ τ (τ.ρ (blockGL b c g))) := by
  have hi := GlobalTheory.FinGL.Transport.isIrreducible_comp τ.ρ (blockGL b c).toMonoidHom (blockGL b c).surjective
    (GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hτ)
  have h := (isChar_and_isIrrChar_of_rep ℂ ℂ _ τ (τ.ρ.comp (blockGL b c).toMonoidHom)).2 hi
  simpa [Representation.character] using h

theorem isCuspProdChar_trace_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b →
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  intro K _ _ _ r s b lam _ hlam hmono
  classical
  let b₀ : Fin r → ℕ := fun i => (b i : ℕ)
  have hb₀ : Monotone b₀ := fun i j h => hmono h
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let e : (Σ c, Fin (d c)) ≃ Fin r :=
    (Equiv.sigmaCongrRight fun c => (Fintype.equivFin {i // b i = c}).symm).trans (Equiv.sigmaFiberEquiv b)
  have hbe : ∀ x, b (e x) = x.1 := fun x => ((Fintype.equivFin {i // b i = x.1}).symm x.2).2
  have he : ∀ x y, b₀ (e x) = b₀ (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [b₀, hbe, Fin.val_inj]
  let χ : ∀ c, GL (Fin (d c)) K → ℂ := fun c g => LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c g))
  obtain ⟨n, σ, hσ, hch⟩ := GlobalTheory.GoodTypeGeneric.exists_isCuspDatum (F := K) hb₀ e he χ
    (fun c => isIrrChar_block b c (lam c) (hlam c).1)
    (fun c c' hc' => sum_unipRadical_eq_zero b c (lam c) (hlam c).2 c' hc')
  refine ⟨n, b₀, σ, hσ, fun x => ?_⟩
  have hPB := parab_eq_blockTri (K := K) b
  let f : blockTri (κ := K) b₀ →* parab K b :=
    MonoidHom.codRestrict (blockTri (κ := K) b₀).subtype (parab K b) (fun p => by rw [hPB]; exact p.2)
  have hf : Function.Surjective f := fun p => ⟨⟨p.1, by rw [← hPB]; exact p.2⟩, rfl⟩
  have h1 : LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) =
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam)).character x := rfl
  show LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) = _
  have h2 := GlobalTheory.FinGL.Transport.character_coind (parab K b).subtype (blockTri (κ := K) b₀).subtype
    (PI.SerBridgeGLW.inflRep K b lam) (MulEquiv.refl _) f hf (fun _ => rfl) x
  rw [MulEquiv.refl_apply] at h2
  rw [h1, ← h2]
  rw [GlobalTheory.GoodTypeGeneric.character_coind_eq_ind, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  congr 1
  funext p
  rw [hch p]
  show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi K b c (f p))) = _
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  show _ = LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c _))
  congr 3
  apply Units.ext
  ext x y
  rw [blockGL_apply, GlobalTheory.GoodTypeGeneric.blocksHom_apply]
  have hx : ∀ z : {i // b i = c}, e ⟨c, Fintype.equivFin _ z⟩ = z.1 := fun z => by
    simp [e, Equiv.sigmaFiberEquiv]
  rw [hx, hx]
  rfl

end GlobalTheory.HCInduction
