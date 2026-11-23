import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.S6
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlCSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerRankBoundLaurent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EvenCocyclesLiftLaurent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurentAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PresOut0
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.CotangentIndependentOfResidues
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DiscImp
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OoExKer

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

private theorem ctx_out {l : ℕ} [Fact l.Prime] (S : Ctx l) (D0 : ℕ) (h1 : K1 S.h S.k D0) (h2 : K2 S.h S.k) (h3 : K3 S.h S.k)
    (Z Q : Ideal S.Bh) (hZ : Z.IsPrime) (hQ : Q.IsPrime) (hs : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Z)
    (hd : ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.Bh ⧸ Z))
    (hq : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q ∨ NonSS S.P.ker (algebraMap S.B S.Bh) Q) : Z ≤ Q := by
  obtain ⟨X, m, c, hX, hm, hc, hg, hr⟩ := pres l S D0 (k1F l _ _ _ S.h _ _ S.k D0 h1) (k2F l _ _ _ S.h _ _ S.k h2)
    (k3F l _ _ _ S.h _ _ S.k h3)
  by_cases ha : S.x.a = S.n
  · have hN := S.U.typeI ha
    have hi : ired S.U.N = ⊥ := by
      refine le_bot_iff.1 (Ideal.span_le.2 ?_)
      rintro b ⟨y, hy, z, -, e⟩
      rw [hN, Submodule.mem_bot] at hy
      rw [hy, zero_mul] at e
      exact S.U.inj (by rw [← e, map_zero])
    refine presOut0 S.OO S.Bh D0 X hX ?_ Z Q hZ hQ hd
    simpa only [Ctx.J2, hi, sup_bot_eq] using hg
  · haveI := S.U.fin
    refine presOut1 S.OO S.Bh S.U.AA S.U.N S.U.inj S.U.compl S.U.mul_mem D0 S.k.g X m c hX hm hc hg hr Z Q hZ hQ hd
      ((discImp l S Z hZ hs).resolve_left ha) ?_
    rcases hq with hq | hq
    · exact Or.inl ((discImp l S Q hQ hq).resolve_left ha)
    · exact Or.inr (S.U.thick Q hQ hq)

theorem galOut : GalOut := by
  intro l _ L G G0 h n x k O _ _ _ hO _ _ r B _ _ _ u P Bh _ _ _ D0 hl hc h1 h2 h3 Z Q hZ hQ hs hd hq
  haveI := hO.complete
  obtain ⟨rF, hf, hk⟩ := rfEx x.K O B Bh P.f hc
  obtain ⟨U⟩ := s6 l L G G0 h n x O r B u P Bh rF hl hc hf hk
  obtain ⟨OO, i1, i2, i3, i4, i5, i6, a1, a2, a3, a4⟩ := ooEx x.K O B Bh P.f P.s rF P.surj P.f_s hc hf
  exact ctx_out
    { odd := hl, L := L, G := G, G0 := G0, h := h, n := n, x := x, k := k, O := O, r := r, B := B, u := u, P := P, Bh := Bh,
      cpl := hc, rF := rF, rF_f := hf, rF_ker := hk, U := U, OO := OO, d6 := i6, oo_A := a1, oo_O := a2, ordinaryPointSection := a3, oo_surj := a4 }
    D0 h1 h2 h3 Z Q hZ hQ hs hd hq

end UpperTheory.V.Pa
