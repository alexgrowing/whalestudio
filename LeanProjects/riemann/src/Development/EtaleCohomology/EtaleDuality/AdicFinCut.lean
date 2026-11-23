import Development.EtaleCohomology.EtaleDuality.PointClasses
import Development.EtaleCohomology.KummerTheory.AdicDegPf

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.EDual

theorem exists_nsmul_eq_of_coprime {q u : ℕ} {G : Type*} [AddCommGroup G] [Module (ZMod q) G] (h : Nat.Coprime u q)
    (x : G) : ∃ z : G, u • z = x := by
  refine ⟨(((ZMod.unitOfCoprime u h)⁻¹ : (ZMod q)ˣ) : ZMod q) • x, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod q), smul_smul, ← ZMod.coe_unitOfCoprime u h, Units.mul_inv, one_smul]

theorem adicFin_of (h1 : LateralTheory.KummerTheory.Bock) (h2 : LateralTheory.KummerTheory.AdicLim) : AdicFin := by
  rintro ⟨-, -, -, -, -, -, -, -, -, a7, a8, -, a10, a11, -⟩ l hl E i hI hF n
  obtain ⟨hfin, -, M, hM, hc⟩ := h2 a11 l E i (fun b => h1 a7 a8 a10 a11 l b E i hI) hF n
  obtain ⟨c, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.out.ne_one
  refine ⟨hfin, c, fun m x => ?_⟩
  have hco : Nat.Coprime u (l ^ m) := ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hu).symm.pow_right m
  obtain ⟨z, rfl⟩ := exists_nsmul_eq_of_coprime hco x
  obtain ⟨y, hy⟩ := hc m z
  exact ⟨y, hy.trans (mul_smul _ _ _)⟩

end LateralTheory.EDual
end
