import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section CosetFixAux

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem redV_qsmul_of_mem {v : Sp E n} (hv : v ∈ stdAt E n P) : redV P (((qOf P : ℕ) : E) • v) = 0 := by
  funext i
  show redP P (((qOf P : ℕ) : E) * v i) = 0
  rw [reduction_mul (GlobalTheory.TopStep.intAt_nat _) (GlobalTheory.TopStep.mem_stdAt.1 hv i), GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_mul]

theorem mem_stdAt_iff_redV_qsmul (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {v : Sp E n}
    (hv : ((qOf P : ℕ) : E) • v ∈ stdAt E n P) : v ∈ stdAt E n P ↔ redV P (((qOf P : ℕ) : E) • v) = 0 := by
  refine ⟨redV_qsmul_of_mem, fun h => GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_⟩
  have hi : IntAt P (((qOf P : ℕ) : E) * v i) := GlobalTheory.TopStep.mem_stdAt.1 hv i
  have h0 : redP P (((qOf P : ℕ) : E) * v i) = 0 := congrFun h i
  have := GlobalTheory.TopStep.intAt_div_of_redP hq hi h0
  rwa [mul_div_cancel_left₀ _ (GlobalTheory.TopStep.qOf_ne_zero (P := P))] at this

theorem redV_sub_of_mem {v w : Sp E n} (hv : v ∈ stdAt E n P) (hw : w ∈ stdAt E n P) :
    redV P (v - w) = redV P v - redV P w := by
  funext i
  exact GlobalTheory.TopStep.reduction_sub (GlobalTheory.TopStep.mem_stdAt.1 hv i) (GlobalTheory.TopStep.mem_stdAt.1 hw i)

theorem redV_qsmul_eq {a b : Sp E n} (hba : b - a ∈ stdAt E n P) (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) :
    redV P (((qOf P : ℕ) : E) • b) = redV P (((qOf P : ℕ) : E) • a) := by
  have hd : ((qOf P : ℕ) : E) • (b - a) ∈ stdAt E n P := by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hba _
  have hb : ((qOf P : ℕ) : E) • b ∈ stdAt E n P := by
    have := add_mem hd ha
    rwa [← smul_add, sub_add_cancel] at this
  have h1 := redV_sub_of_mem hb ha
  rw [← smul_sub, redV_qsmul_of_mem hba] at h1
  exact (sub_eq_zero.1 h1.symm)

end CosetFixAux

theorem setOf_sub_mem_eq_iff {V : Type} [AddCommGroup V] {A : Type} [Ring A] [Module A V] (M : Submodule A V) (a b : V) :
    {z | z - b ∈ M} = {z | z - a ∈ M} ↔ b - a ∈ M := by
  constructor
  · intro h
    have hb : b ∈ {z | z - b ∈ M} := by simp
    rw [h] at hb
    exact hb
  · intro h
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz
      have := add_mem hz h
      rwa [sub_add_sub_cancel] at this
    · intro hz
      have := sub_mem hz h
      rwa [sub_sub_sub_cancel_right] at this

section CosetFix

set_option maxHeartbeats 1000000 in

theorem cosetIn_smul_eq_iff : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG X.E (R.N j) Pr.vGs), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  intro X Pr R sel S mu cst u j hj p p' h h1 h2 P hP hdu
  classical
  obtain ⟨y, hy, hY⟩ := p.mem_ybSet hj
  have hyP : ((qOf P.1 : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := (Submodule.mem_iInf _).1 hy P
    simpa [Submodule.mem_comap, hP] using this
  have hN : p'.1.1.deco.1.N = p.1.1.deco.1.N := by
    rw [h1]
    exact Submodule.map_id _
  have hY' : p'.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) p'.1.1.deco.1.N
      fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)} := by
    rw [h2, hN]
    exact hY
  have hc := GlobalTheory.BaseCosetPt.cosetIn_eq_of p P hP y _ (by simp [hP]) hY
  have hc' := GlobalTheory.BaseCosetPt.cosetIn_eq_of p' P hP y _ (by simp [hP]) hY'
  set w : Pr.vGs := ⟨P.1, hP⟩ with hw
  have hf : GlobalTheory.TopStep.IsLiftFr p.1.1.deco.1 w (frsF sel mu p.1.1 P) := by
    unfold frsF
    rw [dif_pos hP]
    exact GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
  have key : ∀ q : ChPt (R := R) sel mu u j,
      q = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 →
      GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (q.deco.1.liftFr w) := by
    intro q hq
    have := GlobalTheory.TopStep.liftFr_spec q.deco.2 w
    subst hq
    exact this
  have hf' : GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (frsF sel mu p'.1.1 P) := by
    unfold frsF
    rw [dif_pos hP]
    exact key _ h1
  set κ := GlobalTheory.TopStep.passFr 1 h hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL _ P.1 κ = h w := GlobalTheory.TopStep.redGL_passFr 1 h hf hf'
  set a := (frsF sel mu p.1.1 P).symm y with ha
  have hκa : κ.1 a = (frsF sel mu p'.1.1 P).symm y := by
    change (frsF sel mu p'.1.1 P).symm ((frsF sel mu p.1.1 P) a) = _
    rw [ha, LinearEquiv.apply_symm_apply]
  have hqa : ((qOf P.1 : ℕ) : X.E) • a ∈ stdAt X.E (R.N j) P.1 := by
    rw [ha, ← map_smul]
    exact GlobalTheory.BaseCosetPt.frsF_symm_mem p.1.1 P hyP
  have hqd : ((qOf P.1 : ℕ) : X.E) • (κ.1 a - a) ∈ stdAt X.E (R.N j) P.1 := by
    rw [smul_sub, ← map_smul]
    exact sub_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa
  have hcv : cvec p P = redV P.1 (((qOf P.1 : ℕ) : X.E) • a) := by
    unfold cvec
    have hm : ∃ z, z ∈ cosetIn p P := ⟨a, by rw [hc]; simp⟩
    have hε := Classical.epsilon_spec (p := fun z => z ∈ cosetIn p P) hm
    generalize Classical.epsilon (fun z => z ∈ cosetIn p P) = ε at hε ⊢
    rw [hc] at hε
    exact redV_qsmul_eq hε hqa
  rw [hc, hc', ← hκa, setOf_sub_mem_eq_iff, mem_stdAt_iff_redV_qsmul hdu.2 hqd, smul_sub, ← map_smul,
    redV_sub_of_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa, GlobalTheory.TopStep.redV_redGL κ hqa, hred, sub_eq_zero, hcv]

end CosetFix

end GlobalTheory.Mem.Col2.TypeRead
