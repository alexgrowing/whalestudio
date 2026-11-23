import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxExZeroQ

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem parL_self (q kj n c : ℕ) (h : n ≤ kj) : LocE.parL P q kj n c = stdAt E (n + c) P := by
  ext x
  unfold LocE.parL
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.GO.ChRoot.mem_stdAt']
  refine forall_congr' fun l => ?_
  rw [if_neg (by omega)]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P :=
  Submodule.ext fun _ => GlobalTheory.GO.ChRoot.mem_lamY_zero

omit [StarRing E] in

theorem lamQB_empty {K : Type} [Field K] (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ) (hn : n ≤ kj) {N : ℕ}
    (h : HomE E N N) : LocE.lamQB ξ kj n h = 1 := by
  unfold LocE.lamQB
  haveI : IsEmpty (Fin (n - kj)) := ⟨fun i => by have := i.2; omega⟩
  have h1 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [Matrix.det_isEmpty]
  unfold LocE.unitV
  rw [dif_pos (by rw [h1]; exact isUnit_one)]
  have : ∀ hu : IsUnit (redP P (1 : E)), hu.unit = 1 := fun hu => Units.ext (by simp [h1])
  rw [this, map_one]
  simp

end Loc

theorem zero_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  intro X Pr R Ch sel S mu cst P hP hc
  have hN : R.N 0 ≤ R.k + 0 := by rw [Ranks.N_zero]; omega
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp 0 P.1 = stabL X.E _ (stdAt X.E (R.N 0 + cOf R 0) P.1) := by
    unfold Jat
    rw [if_neg hP]
    unfold LocE.JQ
    rw [parL_self _ _ _ _ hN, inf_idem]
  have e : ∀ r : AutY X R 0, (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r = r := by
    intro r
    simp
  constructor
  · unfold GrpQ
    symm
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_subgroupOf]
    refine ⟨GlobalTheory.CongLevel.extE _ g.1, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ g.1, ?_⟩, GlobalTheory.CongLevel.extE_inX _ g.1⟩
    show (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R 0) g.1) ∈ Jat (Pr := Pr) cst.sharp 0 P.1
    rw [e, hJ, ← lamY_zero (qOf P.1)]
    exact GlobalTheory.CongLevel.extE_stab _ _ _ _ _ g.2
  · intro g r hr _
    have h2 : (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp 0 P.1 := hr.2
    rw [e, hJ] at h2
    have hint : IntAt P.1 (1 * Loc.n1Arg r) :=
      GlobalTheory.GO.ChRoot.intAt_n1Arg 1 r fun x hx => by rw [one_smul]; exact (h2 x).2 hx
    rw [one_mul] at hint
    unfold chiInv lamRow
    rw [if_neg hP, hc.psi_int P _ hint, lamQB_empty _ _ _ hN]
    simp

end GlobalTheory.Mem.Col2.IdxExZeroQ
