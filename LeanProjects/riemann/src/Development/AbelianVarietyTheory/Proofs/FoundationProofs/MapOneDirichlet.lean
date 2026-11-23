import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT

open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois

theorem map_smF_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : f (smF c j M ζ a b n) = smF c j M (f ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite f, map_ofNat]

theorem map_cmul_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (u v : ℕ → K) (n : ℕ) :
    f (cmul u v n) = cmul (fun i => f (u i)) (fun i => f (v i)) n := by
  simp [cmul, map_sum, map_mul]

theorem map_one_dirichlet {K L : Type} [Field K] [Field L] (f : K →+* L) (q : ℕ) (x : ZMod q) :
    f ((1 : DirichletCharacter K q) x) = (1 : DirichletCharacter L q) x := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    simp [MulChar.one_apply_coe]
  · simp [MulChar.map_nonunit _ h]

theorem map_pieceT_one : ∀ (N p m k : ℕ) [NeZero p] (K L : Type) [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (S : Finset (GL (Fin 2) (ZMod (p ^ m)))) (r : ℕ),
    f (pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' ζ S r) =
      pieceT N p m m k (1 : DirichletCharacter L (p ^ m)) c d w w' (f ζ) S r := by
  intro N p m k _ K L _ _ _ _ f c d w w' ζ S r
  simp only [pieceT, map_mul, map_neg, map_zpow₀, map_natCast, map_sum, map_cmul_hom, map_smF_hom, map_one_dirichlet]

end GlobalTheory.KummerEisensteinGalois
