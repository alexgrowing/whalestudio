import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveSubmatrices.GlobalTheory

noncomputable section

open Matrix UpperTheory.V.KL
open scoped Kronecker

namespace PositivityTheory.KB

namespace PsiBlockMatrix

theorem psi_eq (R : Type) [CommRing R] (q n : ℕ) :
    psi R q n = (blk R q n).comp (MonoidHom.pi fun _ : Fin q => MonoidHom.id (GL (Fin n) R)) := by
  ext A i j
  have hs : ∀ x : Fin (q * n), (ee q n).symm x = (x.modNat, x.divNat) := fun _ => rfl
  simp [psi, blk, blkM, hs, blockDiagonal_apply, Matrix.one_apply]

variable {G H : Type} [Group G] [Group H]

theorem bd_map (hC : SChain) (f : G →* H) {k : ℕ} {w : Chn G (k + 1)} (hw : IsBd w) :
    IsBd (cmap f (k + 1) w) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
  exact LinearMap.mem_range.2 ⟨cmap f (k + 2) x, hC.2.1 G H f (k + 1) x⟩

theorem cyc_map (hC : SChain) (f : G →* H) {k : ℕ} {w : Chn G (k + 1)} (hw : IsCyc w) :
    IsCyc (cmap f (k + 1) w) := by
  unfold IsCyc at *
  rw [hC.2.1 G H f k w, hw, map_zero]

theorem prim_push (hC : SChain) (φ : G × G →* H) {k : ℕ} {z : Chn G (k + 1)} (hz : IsPrim z) :
    IsBd (cmap (φ.comp ((MonoidHom.id G).prod (MonoidHom.id G))) (k + 1) z -
      cmap (φ.comp (MonoidHom.inl G G)) (k + 1) z - cmap (φ.comp (MonoidHom.inr G G)) (k + 1) z) := by
  have e := fun f : G →* G × G => hC.2.2.1 G (G × G) H f φ (k + 1) z
  rw [e, e, e, ← map_sub, ← map_sub]
  exact bd_map hC φ hz

end PsiBlockMatrix

private theorem exists_conj_blk_mulSingle_eq_stab (R : Type) [CommRing R] (q n : ℕ) (h : n ≤ q * n) (i : Fin q) :
    ∃ P : GL (Fin (q * n)) R, (PsiBlockMatrix.blk R q n).comp (MonoidHom.mulSingle (fun _ : Fin q => GL (Fin n) R) i) =
      (MulAut.conj P).toMonoidHom.comp (stab R n (q * n) h) := by
  classical
  haveI : NeZero q := ⟨by rintro rfl; exact i.elim0⟩
  have hs : ∀ x : Fin (q * n), (PsiBlockMatrix.ee q n).symm x = (x.modNat, x.divNat) := fun _ => rfl
  have hE : ∀ (a : Fin n) (b : Fin q),
      (PsiBlockMatrix.ee q n (a, b)).modNat = a ∧ (PsiBlockMatrix.ee q n (a, b)).divNat = b := by
    intro a b
    have e := (PsiBlockMatrix.ee q n).symm_apply_apply (a, b)
    rw [hs] at e
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have hlt : ∀ x : Fin (q * n), (x : ℕ) < n ↔ x.divNat = 0 := by
    intro x
    rw [Fin.ext_iff, Fin.coe_divNat, Fin.val_zero, Nat.div_eq_zero_iff]
    have : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact x.elim0)
    omega
  let σ : Equiv.Perm (Fin (q * n)) := (PsiBlockMatrix.ee q n).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.swap (0 : Fin q) i)).trans (PsiBlockMatrix.ee q n))
  have hσm : ∀ x, (σ x).modNat = x.modNat := fun x => (hE _ _).1
  have hσd : ∀ x, (σ x).divNat = Equiv.swap (0 : Fin q) i x.divNat := fun x => (hE _ _).2
  have hinj : ∀ x y : Fin (q * n), x = y ↔ x.modNat = y.modNat ∧ x.divNat = y.divNat := by
    intro x y
    rw [← Prod.mk.injEq, ← hs, ← hs, (PsiBlockMatrix.ee q n).symm.apply_eq_iff_eq]
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    rw [hinj, hσm, hσm, hσd, hσd, Equiv.swap_apply_self]
    exact ⟨rfl, rfl⟩
  let Pm : Matrix (Fin (q * n)) (Fin (q * n)) R := σ.toPEquiv.toMatrix
  have hPP : Pm * Pm = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext x y
    simp [Pm, Matrix.one_apply, PEquiv.toMatrix_apply, hσσ]
  refine ⟨⟨Pm, Pm, hPP, hPP⟩, MonoidHom.ext fun A => Units.ext ?_⟩
  have hpad : ∀ X Y : Fin (q * n), padMat R (A : Matrix (Fin n) (Fin n) R) X Y =
      if X.divNat = 0 ∧ Y.divNat = 0 then (A : Matrix (Fin n) (Fin n) R) X.modNat Y.modNat
      else if X = Y then 1 else 0 := by
    intro X Y
    have e1 : ∀ (Z : Fin (q * n)) (hZ : (Z : ℕ) < n), (⟨Z, hZ⟩ : Fin n) = Z.modNat :=
      fun Z hZ => Fin.ext (by simp [Fin.coe_modNat, Nat.mod_eq_of_lt hZ])
    simp only [padMat, Matrix.of_apply, e1]
    by_cases hX : X.divNat = 0
    · by_cases hY : Y.divNat = 0
      · rw [dif_pos ⟨(hlt X).2 hX, (hlt Y).2 hY⟩, if_pos ⟨hX, hY⟩]
      · rw [dif_neg (fun hh => hY ((hlt Y).1 hh.2)),
          if_neg (fun hh : X.divNat = 0 ∧ Y.divNat = 0 => hY hh.2)]
    · rw [dif_neg (fun hh => hX ((hlt X).1 hh.1)),
        if_neg (fun hh : X.divNat = 0 ∧ Y.divNat = 0 => hX hh.1)]
  ext x y
  rw [show (((MulAut.conj (⟨Pm, Pm, hPP, hPP⟩ : GL (Fin (q * n)) R)).toMonoidHom.comp
      (stab R n (q * n) h)) A : Matrix _ _ R) = Pm * (stab R n (q * n) h A : Matrix _ _ R) * Pm from rfl]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  have hy : σ.symm y = σ y := by rw [Equiv.symm_apply_eq, hσσ]
  simp only [Matrix.submatrix_apply, id, hy]
  change _ = padMat R (A : Matrix (Fin n) (Fin n) R) (σ x) (σ y)
  simp only [hpad, hσd, hσm, σ.injective.eq_iff, hinj x y]
  simp [PsiBlockMatrix.blk, PsiBlockMatrix.blkM, hs, blockDiagonal_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff]
  by_cases h1 : x.divNat = i <;> by_cases h2 : y.divNat = i <;>
    by_cases h3 : x.divNat = y.divNat <;> simp [h1, h2, h3, Matrix.one_apply]
  all_goals rw [if_neg (fun e => h2 e.symm), if_neg (fun e => h2 e.2.symm)]

private theorem isBd_cmap_pi_sub_sum_cmap_mulSingle_of_isPrim (hC : SChain) {G : Type} [Group G] {k : ℕ} {z : Chn G (k + 1)}
    (hz : IsPrim z) (q : ℕ) :
    IsBd (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z -
      ∑ j, cmap (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) (k + 1) z) := by
  induction q with
  | zero =>
    have e : (MonoidHom.pi fun _ : Fin 1 => MonoidHom.id G) =
        MonoidHom.mulSingle (fun _ : Fin 1 => G) 0 := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      rw [Fin.fin_one_eq_zero j]
      simp
    rw [Fin.sum_univ_one, e, sub_self]
    exact Submodule.zero_mem _
  | succ q ih =>
    let φ : G × G →* (Fin (q + 2) → G) :=
      MonoidHom.pi fun j => Fin.cases (motive := fun _ => G × G →* G) (MonoidHom.fst G G)
        (fun _ => MonoidHom.snd G G) j
    let ψ : (Fin (q + 1) → G) →* (Fin (q + 2) → G) :=
      MonoidHom.pi fun j => Fin.cases (motive := fun _ => (Fin (q + 1) → G) →* G) 1
        (fun l => Pi.evalMonoidHom (fun _ => G) l) j
    have e1 : φ.comp ((MonoidHom.id G).prod (MonoidHom.id G)) = MonoidHom.pi fun _ => MonoidHom.id G := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ]
    have e2 : φ.comp (MonoidHom.inl G G) = MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) 0 := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ, Pi.mulSingle_apply]
    have e3 : φ.comp (MonoidHom.inr G G) = ψ.comp (MonoidHom.pi fun _ => MonoidHom.id G) := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ, ψ]
    have e4 : ∀ j : Fin (q + 1), ψ.comp (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) =
        MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ := by
      intro j
      refine MonoidHom.ext fun a => funext fun l => ?_
      cases l using Fin.cases <;> simp [ψ, Pi.mulSingle_apply]
    have hp := PsiBlockMatrix.prim_push hC φ hz
    rw [e1, e2, e3, hC.2.2.1] at hp
    have hq := PsiBlockMatrix.bd_map hC ψ ih
    have e5 : ∀ j : Fin (q + 1), cmap ψ (k + 1) (cmap (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) (k + 1) z) =
        cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ) (k + 1) z := fun j => by
      rw [← hC.2.2.1, e4]
    rw [map_sub, map_sum] at hq
    simp only [e5] at hq
    have key : cmap (MonoidHom.pi fun _ : Fin (q + 2) => MonoidHom.id G) (k + 1) z -
        ∑ j, cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j) (k + 1) z =
        (cmap (MonoidHom.pi fun _ : Fin (q + 2) => MonoidHom.id G) (k + 1) z -
          cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) 0) (k + 1) z -
          cmap ψ (k + 1) (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z)) +
        (cmap ψ (k + 1) (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z) -
          ∑ j : Fin (q + 1), cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ) (k + 1) z) := by
      rw [Fin.sum_univ_succ]
      abel
    show _ ∈ LinearMap.range _
    rw [key]
    exact Submodule.add_mem _ hp hq

open PsiBlockMatrix in
theorem sPsi_of (hC : SChain) : SPsi := by
  intro R _ d n k h z hzc hzp
  rw [PsiBlockMatrix.psi_eq R (d + 1) n, hC.2.2.1]
  have h1 := PsiBlockMatrix.bd_map hC (PsiBlockMatrix.blk R (d + 1) n) (isBd_cmap_pi_sub_sum_cmap_mulSingle_of_isPrim hC hzp d)
  rw [map_sub, map_sum] at h1
  simp only [← hC.2.2.1] at h1
  rw [hC.2.2.1 _ _ _ (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R))
    (PsiBlockMatrix.blk R (d + 1) n)] at h1
  have h2 : ∀ j : Fin (d + 1), cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
      (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z -
      cmap (stab R n ((d + 1) * n) h) (k + 1) z ∈ LinearMap.range (bd (GL (Fin ((d + 1) * n)) R) (k + 1)) := by
    intro j
    obtain ⟨P, hP⟩ := exists_conj_blk_mulSingle_eq_stab R (d + 1) n h j
    rw [hP, hC.2.2.1]
    exact hC.2.2.2 _ P k _ (PsiBlockMatrix.cyc_map hC _ hzc)
  have h3 := Submodule.sum_mem _ (fun j (_ : j ∈ Finset.univ) => h2 j)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h3
  have key : cmap (PsiBlockMatrix.blk R (d + 1) n) (k + 1)
      (cmap (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R)) (k + 1) z) -
      ((d : ℝ) + 1) • cmap (stab R n ((d + 1) * n) h) (k + 1) z =
      (cmap (PsiBlockMatrix.blk R (d + 1) n) (k + 1)
        (cmap (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R)) (k + 1) z) -
        ∑ j, cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
          (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z) +
      (∑ j, cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
          (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z -
        (d + 1) • cmap (stab R n ((d + 1) * n) h) (k + 1) z) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_succ]
    abel
  show _ ∈ LinearMap.range _
  rw [key]
  exact Submodule.add_mem _ h1 h3

end PositivityTheory.KB
