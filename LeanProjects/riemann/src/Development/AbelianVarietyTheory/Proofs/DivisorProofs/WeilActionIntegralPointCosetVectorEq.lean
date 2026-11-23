import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.Move

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem eig_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    {g' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) (hH : H ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) : P.W.Om k 1 H = s • H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) = k := mul_one k
  have f2 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = s • P.W.Om 1 g' P.e0 := by
    rw [← e1, e2, he, P.W.smul _ _ _ _ hT]
  rw [hc', P.W.smul _ _ _ _ hH, smul_comm s c H] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_eig (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) :
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      s • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact eig_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)
    (GlobalTheory.FunObj.CosetFix.iop_facts hI P h𝔪).1 k s he

theorem exists_close {𝔪 : Ideal (𝓞 D.host.E)} (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)
    (z : Matrix (Fin d) (Fin a) D.host.E) (hz : Approx 𝔪 o k z) (m : ℕ) (hm : 0 < m) :
    ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧
      CloseTo D ⊤ m (k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
        (unitBlock D o a d) (z + w) := by
  choose b hb y hy hby using fun i j => GlobalTheory.CongApprox.exists_mem_approx D 𝔪 m hm _ (neg_mem (hz i j))
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have e1 : (((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := by
    simp
  unfold CloseTo
  refine fun i j => ⟨y i j, hy i j, Eq.trans ?_ (hby i j)⟩
  rw [e1, Matrix.one_mul, Matrix.map_add _ (map_add (inc D))]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply]
  ring

theorem wd_smul (δ : ℂ) {a d : ℕ} (x : VC D a d) (c : ℂ) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
  funext y
  simp only [Wd, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_cosetVec : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk c hc z hzi hz
  have h1 := hD.g1
  have he := P.vac.1
  have hIT := (GlobalTheory.FunObj.CosetFix.iop_facts hD P h𝔪).1
  have hfix := iop_eig hD P h𝔪 k c hc
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  obtain ⟨w, hw, hclose⟩ := exists_close o k z hz m hm
  have hmain := hl _ hclose
  rw [hfix, wd_smul] at hmain
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := (GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ ⊤ z
    (fun i j => (hzi i j).imp fun b hb => ⟨Submodule.mem_top, hb⟩)).1
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hIT
  unfold cosetVec cosV
  rw [P.W.smul _ _ _ _ hWT, hmain, ← h3, smul_comm]

end GlobalTheory.StdRead.Move
