import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFS

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem conj_ddPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (hLG _ hne _).1 fun p => Formalism.L2.SG.Pf.StabIntSh.locMem_conj δ M hA p hk ((hLG _ hne _).2 hx p)

theorem conj_qdPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k := by
  unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at *
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨D.conjF z, conj_ddPow δ M hA hk hz, ?_⟩
  rw [map_mul]
  congr 1
  simp

theorem bt_sgn (uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (j i : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.StabIntSh.bt D (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) j i = uu' j i := by
  unfold Formalism.L2.SG.Pf.StabIntSh.bt Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : ((-1 : D.host.E) ^ (D.R.rS - j.val)) * (-1) ^ (D.R.rS - j.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have h2 : ((-1 : D.host.E) ^ (D.R.rS - i.val)) * (-1) ^ (D.R.rS - i.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (uu' j i * (-1) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val)) * h1 + uu' j i * h2

theorem star_conjF (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem frameShape_holds : Formalism.L2.SG.Pf.ZsVolIn.FrameShapeP M δ u u' F0 what₂ := by
  intro γ w F' L U hH s hs uu uu' huu huu' hfr hfr'
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨⟨⟨hLift', _, hFOK⟩, _⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hR.1 γ.lam γ.mem
  have hsΛ : ∀ v ∈ γ.lam, s v ∈ γ.lam := fun v hv => by
    have h := hs.1.1.2
    rw [← h]
    exact Submodule.mem_map_of_mem hv
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := by
    intro b
    have h := hAdm.2.2 b
    convert h using 3
    simp [frameAct, Matrix.one_apply]
    rfl
  intro i j hji
  have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
  have h1 := frame_entry (lf D F0) γ.lam hXF hLift.1 s hsΛ uu huu hfr j i hji
  have h2 := frame_entry F' γ.lam hFOK.2 hLift'.1 s hsΛ uu' huu' hfr' j i hji
  have h3 := cong_glob (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm s hsΛ uu uu' huu huu' hfr hfr' j i hji
  rw [Matrix.conjTranspose_apply, bt_sgn, star_conjF]
  refine ⟨conj_ddPow δ M hA hk h1, h2, ?_⟩
  rw [← map_sub]
  exact conj_qdPow δ M hA hk h3

end Formalism.L2.SG.Pf.ZsVolLat

end
