import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerFix

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG3

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_up {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, b < a → lmat Z p g ρ l a b = 0) ∧ ∀ a, lmat Z p g ρ l a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hρ0 a b h, hl0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem modeG (hs : (Z.M p).split = some g) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M)
    (hcong : Cq Z p g (locU Z p N * locU Z p M - 1)) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set Nl := locU Z p N with hNl
  set Ml := locU Z p M with hMl
  set K := (Nl.map (Z.M p).L.cj)ᵀ with hKdef
  have hK0 : ∀ a b, a < b → K a b = 0 := fun a b h => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
  have hK1 : ∀ a, K a a = 1 := fun a => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
  have hKO : IntM Z p K := fun i j => PI.LocCntLat.GC.cj_mem_O _ (hNO j i)
  have hKdet : K.det = 1 := det_lower p hK0 hK1
  have hKu : IsUnit K.det := by rw [hKdet]; exact isUnit_one
  have hNdet : Nl.det = 1 := det_upper p hN0 hN1
  have hNu : IsUnit Nl.det := by rw [hNdet]; exact isUnit_one
  have hl0O : IntM Z p K⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O K hKO hKdet
  have hNiO : IntM Z p Nl⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O Nl hNO hNdet
  have hl0low : (∀ a b, a < b → K⁻¹ a b = 0) ∧ ∀ a, K⁻¹ a a = 1 := by
    have h := Formalism.L2.SG.TermLoc.inv_unitri Kᵀ (fun a b h => by rw [Matrix.transpose_apply]; exact hK0 b a h)
      (fun a => by rw [Matrix.transpose_apply]; exact hK1 a)
    rw [← Matrix.transpose_nonsing_inv] at h
    exact ⟨fun a b hab => by have := h.1 b a hab; rwa [Matrix.transpose_apply] at this,
      fun a => by have := h.2 a; rwa [Matrix.transpose_apply] at this⟩
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * Ml := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul]

  set Cm : Formalism.L2.SG.LsDatumB.MatP D p := Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
      g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
        (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0 with hCm
  have hZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X =
      emap Z p g (Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X) - Cm := by
    intro X
    ext a b
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, emap, hCm, Matrix.sub_apply,
      Matrix.of_apply]
  obtain ⟨hL0, hL1⟩ := lmat_low Z p g hl0low.1 hl0low.2 hM0 hM1
  obtain ⟨hR0, hR1⟩ := lmat_up Z p g hl0low.1 hl0low.2 hM0 hM1
  have hcorner := corner_fix p hL0 hL1 hR0 hR1 (C := Cm) (fun a b h => by
    simp only [hCm, Matrix.of_apply]; rw [if_neg h])
  have hmain : Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ =
      lmat Z p g K⁻¹ Ml * Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * lmat Z p g Ml K⁻¹ := by
    rw [hZZ, hZZ, hY, emap_mul, Matrix.mul_sub, Matrix.sub_mul, hcorner]

  have hKc : K.map (Z.M p).L.cj = Nlᵀ := by
    ext i j
    simp [hKdef, (Z.M p).L.cj_cj]
  have hA : Cq Z p g (Ml - ((K⁻¹).map (Z.M p).L.cj)ᵀ) := by
    have e1 : ((K⁻¹).map (Z.M p).L.cj)ᵀ = Nl⁻¹ := by
      rw [map_cj_inv Z p K hKu, hKc, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    have e2 : Ml - Nl⁻¹ = Nl⁻¹ * (Nl * Ml - 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul, Matrix.mul_one]
    rw [e1, e2]
    exact cq_mul_left Z p g hNiO hcong
  have hB : Cq Z p g (K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ) := by
    have e1 : Ml * Nl - 1 = Nl⁻¹ * (Nl * Ml - 1) * Nl := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul,
        Matrix.mul_one, Matrix.nonsing_inv_mul Nl hNu]
    have h1 : Cq Z p g (Ml * Nl - 1) := by
      rw [e1]; exact cq_mul_right Z p g (cq_mul_left Z p g hNiO hcong) hNO
    have e2 : ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ = K * (Ml.map (Z.M p).L.cj)ᵀ - 1 := by
      have m1 : (Ml * Nl - 1).map (Z.M p).L.cj = (Ml * Nl).map (Z.M p).L.cj - 1 := by
        ext i j
        rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
        congr 1
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      rw [m1, map_cj_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hKdef]
    have e3 : K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ = -(K⁻¹ * ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ) := by
      rw [e2, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul, Matrix.mul_one,
        neg_sub]
    rw [e3]
    exact cq_neg Z p g (cq_mul_left Z p g hl0O (cq_transpose Z p g (cq_map_cj Z p g h1)))
  have hLint : Formalism.MainNotions.S.TieN.IntLow (Z.M p) (lmat Z p g K⁻¹ Ml) := by
    refine ⟨hL1, hL0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hB a b
    exact lmat_mem_R Z p g hs (hl0O a b) (hMO b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  have hRint : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (lmat Z p g Ml K⁻¹) := by
    refine ⟨hR1, hR0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hA a b
    exact lmat_mem_R Z p g hs (hMO a b) (hl0O b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  refine ⟨lmat Z p g K⁻¹ Ml, Formalism.L2.SG.LsDatumB.sgnP p * lmat Z p g Ml K⁻¹ * Formalism.L2.SG.LsDatumB.sgnP p,
    hLint, sgn_conj_intUp Z p hRint, ?_⟩
  rw [hmain]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeG3

end Formalism.L2.SG.Pf.FibQ
