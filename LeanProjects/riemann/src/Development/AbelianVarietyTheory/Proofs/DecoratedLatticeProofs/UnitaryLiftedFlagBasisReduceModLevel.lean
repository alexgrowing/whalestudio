import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FlagUnit

theorem flagGram_map' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n ρ k : ℕ) :
    (flagGram A n ρ k).map f = flagGram B n ρ k := by
  ext i j; simp only [flagGram, Matrix.map_apply]; split_ifs <;> simp

theorem gramIn_eq_cT (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    gramIn I β = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp only [gramIn, hA, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gramIn_invariant (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf)
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hM : I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * M) :
    Formalism.UG.cT (sigA I) M * gramIn I β * M = gramIn I β := by
  have hx : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := x.2
  rw [gramIn_eq_cT]
  calc Formalism.UG.cT (sigA I) M * (Formalism.UG.cT (sigA I) (β : Matrix _ _ _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix _ _ _)) * M
      = Formalism.UG.cT (sigA I) ((β : Matrix _ _ _) * M) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *
          ((β : Matrix _ _ _) * M) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT (sigA I) (β : Matrix _ _ _) * (Formalism.UG.cT (sigA I) (I.fmat x) *
          I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * I.fmat x) * (β : Matrix _ _ _) := by
        rw [← hM, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hx]

theorem unitary_reduce : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  intro I g ρ k β hG K _ p hg x m hx
  have hG' : ∀ i j, ∃ t ∈ IntAf I.F I.E, gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j =
      (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t := hG
  choose t ht htt using hG'
  let ts : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E) := fun i j => ⟨t i j, ht i j⟩
  let GS : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E) := fun i j => flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j + (g : (Formalism.L2.Herm.intAf I.F I.E)) * ts i j
  have hGS : GS.map (Formalism.L2.Herm.intAf I.F I.E).subtype = gramIn I β := by
    ext i j
    have := htt i j
    have h2 : (Formalism.L2.Herm.intAf I.F I.E).subtype (flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j) = flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j := by
      rw [← Matrix.map_apply (f := (Formalism.L2.Herm.intAf I.F I.E).subtype), flagGram_map']
    show (Formalism.L2.Herm.intAf I.F I.E).subtype (GS i j) = _
    simp only [GS, ts, map_add, map_mul, map_natCast, h2]
    show _ + (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t i j = _
    rw [← this]; ring
  have hM : I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (Formalism.L2.Herm.intAf I.F I.E).subtype := by
    show ((x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * _ = _
    rw [← hx]
    simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, Units.val_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rfl
  have hinv := gramIn_invariant I β x _ hM
  have hS : ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (sigInt I))ᵀ * GS * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) = GS := by
    apply Matrix.map_injective (f := (Formalism.L2.Herm.intAf I.F I.E).subtype) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, hGS]
    convert hinv using 3
    ext i j
    simp [Formalism.UG.cT, sigInt_coe]
  have := congrArg (fun N => N.map p) hS
  simp only [Matrix.map_mul] at this
  have hGK : GS.map p = flagGram K I.n ρ k := by
    ext i j
    show p (GS i j) = _
    have h2 : p (flagGram (Formalism.L2.Herm.intAf I.F I.E) I.n ρ k i j) = flagGram K I.n ρ k i j := by
      rw [← Matrix.map_apply (f := p), flagGram_map']
    simp only [GS, map_add, map_mul, map_natCast, hg, zero_mul, add_zero, h2]
  rw [hGK] at this
  convert this using 3
  ext i j
  simp [Matrix.map_apply]

end GlobalTheory.FlagUnit

end
