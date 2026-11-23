import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.LocalToGlobal.GroupLattices.Joint0

noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

theorem mulLat_ideal_smul {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) : mulLat g (I • L) = I • mulLat g L := by
  unfold mulLat
  exact Submodule.map_smul'' _ _ _

theorem natSmul_mem_of_sup {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (t : ℕ) (ht : (t : E) ≠ 0) (z : Fin n → E) (hz : z ∈ L) (y : Fin n → E)
    (hy : y ∈ L ⊔ Submodule.span (𝓞 E) {(t : E)⁻¹ • z}) : ((t : ℕ) : 𝓞 E) • y ∈ L := by
  obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hm
  rw [smul_add]
  refine L.add_mem (L.smul_mem _ hl) ?_
  have e : ((t : ℕ) : 𝓞 E) • ((t : E)⁻¹ • z) = z := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [smul_comm, e]
  exact L.smul_mem r hz

theorem avoid_two {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P Q : Ideal R)
    (M : Submodule R W) (x : W) (s t : R) (hs : s ∉ P) (ht : t ∉ Q) (hsx : s • x ∈ M) (htx : t • x ∈ M) :
    ∃ a : R, a ∉ P ∧ a ∉ Q ∧ a • x ∈ M := by
  by_cases hsQ : s ∈ Q
  · by_cases htP : t ∈ P
    · refine ⟨s + t, fun h => hs ?_, fun h => ht ?_, ?_⟩
      · simpa using P.sub_mem h htP
      · simpa using Q.sub_mem h hsQ
      · rw [add_smul]; exact M.add_mem hsx htx
    · exact ⟨t, htP, ht, htx⟩
  · exact ⟨s, hs, hsQ, hsx⟩

theorem use₄ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    (g : GL (Fin n) E) {M N : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) M) = Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) N) = Formalism.HermitianLatticesTheory.localization₂ P M := by
  apply le_antisymm
  · have := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
    rwa [rlv_mulLat_inv] at this
  · have := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
    rwa [rlv_mulLat_inv] at this

variable {D : D7} {u : D.what₂.Word}

set_option synthInstance.maxHeartbeats 400000 in

theorem cls_le_ld (T : Forms0 D u) (c : (D.mem u).C.cls 0) :
    clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c := by
  have h1 : clsCrd D u 0 (Nat.zero_le _) c = Formalism.UG.CS.globLat (T.cls0.y c).1 T.cls0.lev.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat (tld_isLat (D := D) (u := u) 0 (Nat.zero_le _) c) _
      (fun x => T.cls0.y_lat c x)
  rw [h1, dual_class_lattice_eq_global T.cls0 c]
  intro x hx
  have hLb : T.cls0.lev.Lb ≤ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb :=
    fun y hy => Submodule.subset_span (T.cls0.lev.Lb_int y hy)
  exact Submodule.span_mono (Set.image_mono hLb) hx

theorem pr_congr (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z z' : ↥(Ld D u 0 (Nat.zero_le _) c)) (h : z.1 = z'.1) : T.lv0.pr v c z = T.lv0.pr v c z' :=
  congrArg _ (Subtype.ext h)

theorem pr_tr (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hg : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z z' : ↥(Ld D u 0 (Nat.zero_le _) c)) (hzz : T.lv0.pr v c z = T.lv0.pr v c z')
    (hz : g *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c') (hz' : g *ᵥ z'.1 ∈ Ld D u 0 (Nat.zero_le _) c') :
    T.lv0.pr v c' ⟨_, hz⟩ = T.lv0.pr v c' ⟨_, hz'⟩ := by
  have h0 : T.lv0.pr v c (z - z') = 0 := by rw [map_sub, hzz, sub_self]
  rw [T.lv0.pr_ker] at h0
  have h1 : g *ᵥ (z - z').1 ∈ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c' := by
    rw [← hg, ← mulLat_ideal_smul]
    exact ⟨_, h0, rfl⟩
  rw [← sub_eq_zero, ← map_sub, T.lv0.pr_ker]
  simpa [Matrix.mulVec_sub] using h1

end CrossDiaZero

end
