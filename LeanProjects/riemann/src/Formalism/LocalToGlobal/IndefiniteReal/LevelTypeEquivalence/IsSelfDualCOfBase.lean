import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VecDiagYOf
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SelfDualLatticeIsSelfDual
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.IoExist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSelfDualC_of_base {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ N) : IsSelfDualC V Λ := by
  obtain ⟨-, hdual, hN, hin, hout⟩ := hB
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hl0 := (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.self_dual_lattice_is_self_dual V).1
  let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hφ : ∀ x, φ x = (N : D.host.E) • x := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) x, map_natCast]
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · have hφinj : Function.Injective φ := fun a b hab => by
      rw [hφ, hφ] at hab
      exact smul_right_injective _ hN0 hab
    have hle : Λ.map φ ≤ Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set, hφ]
      exact hout x hx
    have : IsNoetherian (𝓞 D.host.E) (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V) := isNoetherian_of_fg_of_noetherian _ hl0.fg
    have h1 : ((Λ.map φ).comap (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective φ hφinj h2
  · rw [eq_top_iff, ← hl0.span_eq_top, Submodule.span_le]
    intro x hx
    have hNx : (N : D.host.E) • x ∈ Λ := hin x ((Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set V x).1 hx)
    have : x = (N : D.host.E)⁻¹ • ((N : D.host.E) • x) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
    have key : (N : D.host.E)⁻¹ • ((N : D.host.E) • x) ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span hNx)
    rw [← this] at key
    exact key
  · rw [Formalism.IndefR.Eqv.dual_of_dualL hdual y]
    simp only [Formalism.UG.hform, starRingEnd_apply, RingHom.mem_range]

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) :
    ∃ (p : ℕ) (σ : Fin n ≃ Fin n), ∀ a : Fin n, (ε (σ a) = true ↔ a.val < p) := by
  classical
  let P := {i : Fin n // ε i = true}
  let Q := {i : Fin n // ¬ ε i = true}
  have hcard : Fintype.card P + Fintype.card Q = n := by
    have h1 : Fintype.card Q = n - Fintype.card P := by
      show Fintype.card {i : Fin n // ¬ ε i = true} = n - Fintype.card {i : Fin n // ε i = true}
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have h2 : Fintype.card P ≤ n := by
      show Fintype.card {i : Fin n // ε i = true} ≤ n
      have := Fintype.card_subtype_le (fun i : Fin n => ε i = true)
      rwa [Fintype.card_fin] at this
    rw [h1]
    omega
  let e : Fin n ≃ P ⊕ Q := (Equiv.sumCompl (fun i : Fin n => ε i = true)).symm
  let f : P ⊕ Q ≃ Fin (Fintype.card P) ⊕ Fin (Fintype.card Q) := (Fintype.equivFin P).sumCongr (Fintype.equivFin Q)
  let g : Fin (Fintype.card P) ⊕ Fin (Fintype.card Q) ≃ Fin n := finSumFinEquiv.trans (finCongr hcard)
  refine ⟨Fintype.card P, (e.trans (f.trans g)).symm, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := g.surjective a
  have hx : (e.trans (f.trans g)).symm (g x) = e.symm (f.symm x) := by
    simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rw [hx]
  rcases x with x | x
  · have h1 : e.symm (f.symm (Sum.inl x)) = ((Fintype.equivFin P).symm x).1 := by
      simp [e, f, Equiv.sumCompl]
    have h2 : (g (Sum.inl x)).val = x.val := by simp [g]
    rw [h1, h2]
    simp only [((Fintype.equivFin P).symm x).2, true_iff]
    exact x.2
  · have h1 : e.symm (f.symm (Sum.inr x)) = ((Fintype.equivFin Q).symm x).1 := by
      simp [e, f, Equiv.sumCompl]
    have h2 : (g (Sum.inr x)).val = Fintype.card P + x.val := by simp [g]
    rw [h1, h2]
    have := ((Fintype.equivFin Q).symm x).2
    simp only [Bool.not_eq_true] at this
    simp [this]

theorem exists_onb {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ), IsONBasis (gramAt D V τ) (Formalism.IndefR.Links.cart M τ) B p := by
  obtain ⟨p, σ, hσ⟩ := exists_sort (M.ε τ)
  have hu : IsUnit (M.fr τ) := M.fr_unit τ
  have hinv : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hinv' : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  let B := ((M.fr τ)⁻¹).submatrix id σ
  let ε' : Fin V.rank → ℝ := fun a => if M.ε τ (σ a) then 1 else -1
  have hG : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]
    calc ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv']; simp
  have hC : Formalism.IndefR.Links.cart M τ * (M.fr τ)⁻¹ = (M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.IndefR.Links.cart
    simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)).submatrix σ σ = Matrix.diagonal fun a => ((ε' a : ℝ) : ℂ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1; funext a
    simp only [ε']
    by_cases h : M.ε τ (σ a) = true <;> simp [h]
  refine ⟨B, p, ε', fun a => ?_, ?_, ?_⟩
  · by_cases h : M.ε τ (σ a) = true
    · left; exact ⟨by simp [ε', h], (hσ a).1 h⟩
    · right
      have hf : M.ε τ (σ a) = false := by simpa using h
      refine ⟨by simp [ε', hf], ?_⟩
      by_contra hlt
      exact h ((hσ a).2 (not_le.1 hlt))
  · show (((M.fr τ)⁻¹).submatrix id σ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹).submatrix id σ = _
    rw [← hJ, ← hG]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.conjTranspose_apply]
  · show Formalism.IndefR.Links.cart M τ * ((M.fr τ)⁻¹).submatrix id σ = ((M.fr τ)⁻¹).submatrix id σ * _
    rw [← hJ]
    ext i j
    have h1 := congrFun (congrFun hC i) (σ j)
    simp only [Matrix.mul_apply] at h1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rw [h1]
    exact (Equiv.sum_comp σ (fun k => (M.fr τ)⁻¹ i k * Formalism.REAL.Jm (M.ε τ) k (σ j))).symm

section R

open Formalism.IndefR.Links Formalism.IndefR.Links.RealDat

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Classical in

theorem sideYR_of (hLev : R.toLevCh.Is A.μ0) (hC : R.IsChain) {t : T} {k : ℕ} (hk : k + 1 < D.R.m)
    (hdisj : Disjoint R.Pg (R.Q t))
    (hsph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1))
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k))
    (hunr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
        Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2)
    (htG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
        Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1))
    (htQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
        Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1) :
    SideYR R t k := by
  obtain ⟨cS, hBS⟩ := hLev.βY k (by omega)
  obtain ⟨cT, hBT⟩ := hLev.βY (k + 1) hk
  choose BS pS hS using fun τ => exists_onb (R.MY k) τ
  choose BT pT hT using fun τ => exists_onb (R.MY (k + 1)) τ
  refine ⟨⟨BS, BT, pS, pT, ?_⟩, hsph, hunr, htG, htQ⟩
  exact
    { cartS := fun τ => Formalism.IndefR.Fock.IoExist.cart_isCartanInv (R.MY k) τ
      cartT := fun τ => Formalism.IndefR.Fock.IoExist.cart_isCartanInv (R.MY (k + 1)) τ
      onbS := hS
      onbT := hT
      frS := hBS.1
      frT := hBT.1
      sdS := isSelfDualC_of_base hBS
      sdT := isSelfDualC_of_base hBT
      disj := hdisj
      vec := hC.vY t k hk }

end R

end Formalism.IndefR.Eqv.KerDiag

end
