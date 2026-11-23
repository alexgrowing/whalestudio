import Formalism.SharpRestriction.InertJacobiLevels.BTopOfGe

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem FC.Large.mono {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large K' CH) (hK : K.le K') : C.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

def fcOf (p t : ℝ) (o : Out) (M N : ℝ) : FC where
  Ct := t
  Cc := o.Cc
  CT2 := o.CT2
  CGam := M
  Csz := M
  Cr := 1
  CTu := o.CTu
  Cdg := o.Cdg
  C5 := o.C5
  full := o.full
  GK := ⟨M, N, N, N, N, N, N, N, N, N, N, 5, 4, 1, N⟩
  cX := ⟨1, ⟨12, 3, M⟩⟩
  P := ⟨N, N, N, N⁻¹, 10, N, N, o.CLw, o.Cj0, N, o.cw, N, N, N, N, N, N, o.CetaF, N, o.CYL, o.Cpde, o.CccK, M⟩
  T := ⟨p, o.eP, o.Cp, N, o.cTO, N, N⟩

theorem exists_large (K : TransportedAlt) (out : ℝ → ℝ → Out) :
    ∃ (C : FC) (CH : ℝ), 0 ≤ CH ∧ C.out = out C.T.CP C.Ct ∧ C.GK.Nonneg ∧ 1 ≤ C.Cr ∧ C.Large K CH ∧ C.P.CF = CH ∧
      C.GK.Pr1 = 1 ∧ C.GK.dl1 = 5 ∧ C.GK.dl2 = 4 ∧ C.cX.Ce = 1 ∧ C.cX.err.c6 = 12 ∧ C.cX.err.dig = 3 ∧ C.Cr = 1 ∧
      C.P.CnW = 10 ∧ C.Ct = 401 := by
  set p := K.pre with hp
  set t : ℝ := 401 with ht
  set o := out p t with ho
  set M := max (K.mid (fcOf p t o 0 0).cOut) 1 with hM
  set N := max (K.last ((fcOf p t o 0 0).cOut ++ (fcOf p t o M 0).cMid M)) 1 with hN
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hN0 : 0 ≤ N := le_trans zero_le_one (le_max_right _ _)
  refine ⟨fcOf p t o M N, M, hM0, rfl, ⟨hM0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, by show (0 : ℝ) ≤ 5; norm_num, by show (0 : ℝ) ≤ 4; norm_num,
      by show (0 : ℝ) ≤ 1; norm_num, hN0⟩,
    le_refl _, ⟨?_, trivial, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    have hc' : c = p := by
      simp only [FC.cPre, fcOf, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact hc
    rw [hc']
  · intro c hc
    have hc' : c = M := by
      simp only [FC.cMid, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _
  · intro c hc
    have hc' : c = N := by
      simp only [FC.cLast, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self, inv_inv] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _

end Formalism.MainNotions.Inhab

end
