import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerTwSplit
open GlobalTheory.EulerTw GlobalTheory.EulerTwU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem theta_mem {v w : Pl E} (f : v.adicCompletion E →+* w.adicCompletion E) (hf : ∀ x, Valued.v (f x) = Valued.v x)
    {g : GLw n v} (hg : g ∈ GlobalTheory.LFun.KGL v n) :
    thetaGL n (RingHom.id _) (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL w n := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f g := Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) (GeneralLinearGroup.map f g)) * (PhiU n _)⁻¹ ∈ _
  rw [hid]
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n) (GlobalTheory.BCT.LocGlue.intst E n v w f hf g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem thF_mem_Kglob {x : GL (Fin n) (Af E)} (hx : x ∈ Kglob E n) : thF E n x ∈ Kglob E n := by
  rw [mem_Kglob_iff] at hx ⊢
  intro v
  rw [pc_thF]
  exact theta_mem _ (conjLoc_spec _ v).2.2 (hx _)

theorem pc_one (v : Pl E) : GeneralLinearGroup.map (n := Fin n) (pLoc E v) 1 = 1 := map_one _

theorem pc_thU {u v : Pl E} (hv : v ∈ orb E u) (z : Gam E n u) :
    GeneralLinearGroup.map (pLoc E v) ((thU E n u z : Gam E n u) : GL (Fin n) (Af E)) =
      GeneralLinearGroup.map (pLoc E v) (thF E n z) :=
  pc_pfU hv _

theorem pc_thF_congr {v : Pl E} {x x' : GL (Fin n) (Af E)}
    (h : GeneralLinearGroup.map (pLoc E (cPl E v)) x = GeneralLinearGroup.map (pLoc E (cPl E v)) x') :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = GeneralLinearGroup.map (pLoc E v) (thF E n x') := by
  rw [pc_thF, pc_thF, h]

theorem pc_thF_pfU {u v : Pl E} (hv : v ∈ orb E u) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n ((pfU E n u g : Gam E n u) : GL (Fin n) (Af E))) =
      GeneralLinearGroup.map (pLoc E v) (thF E n g) :=
  pc_thF_congr (pc_pfU (cPl_mem_orb hv) g)

theorem thU_mem_KU {u : Pl E} {z : Gam E n u} (hz : z ∈ KU E n u) : thU E n u z ∈ KU E n u := by
  rw [show KU E n u = (Kglob E n).subgroupOf (Gam E n u) from rfl, Subgroup.mem_subgroupOf] at hz ⊢
  rw [mem_Kglob_iff] at hz ⊢
  intro v
  by_cases hv : v ∈ orb E u
  · rw [pc_thU hv]
    exact (mem_Kglob_iff _).1 (thF_mem_Kglob ((mem_Kglob_iff _).2 hz)) v
  · rw [pc_gam _ hv]; exact one_mem _

theorem locGL_mem_Kglob {u : Pl E} {g : GLw n u} (hg : g ∈ GlobalTheory.LFun.KGL u n) : locGL E n u g ∈ Kglob E n := by
  rw [mem_Kglob_iff]
  intro v
  by_cases h : v = u
  · subst h; rw [pLoc_locGL]; exact hg
  · rw [pLoc_locGL_of_ne h]; exact one_mem _

set_option hygiene false in
local notation "PC[" v "]" => GeneralLinearGroup.map (pLoc E v)

theorem split_twCent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E), GlobalTheory.EulerTw.cPl E u ≠ u → ∀ D : GL (Fin n) (Af E), (∀ v ∈ GlobalTheory.EulerTw.orb E u, (GeneralLinearGroup.map (pLoc E v) D ∈ GlobalTheory.LFun.KGL v n ∧ GeneralLinearGroup.map (pLoc E v) (D * thF E n D) ∈ GlobalTheory.LFun.KGL v n ∧ ∃ a b : (v.adicCompletion E)[X], (∀ i, a.coeff i ∈ v.adicCompletionIntegers E) ∧ (∀ i, b.coeff i ∈ v.adicCompletionIntegers E) ∧ a * (GeneralLinearGroup.map (pLoc E v) (D * thF E n D)).val.charpoly + b * derivative (GeneralLinearGroup.map (pLoc E v) (D * thF E n D)).val.charpoly = 1)) → ∀ y, y⁻¹ * GlobalTheory.EulerTw.pfU E n u D * GlobalTheory.EulerTw.thU E n u y ∈ GlobalTheory.EulerTw.KU E n u → ∃ t ∈ twCent (GlobalTheory.EulerTw.thU E n u) (GlobalTheory.EulerTw.pfU E n u D), ∃ k ∈ GlobalTheory.EulerTw.KU E n u, y = t * k := by
  intro E _ _ _ n u hne D hD y hy
  have hu : u ∈ orb E u := mem_orb.2 (Or.inl rfl)
  have hub : cPl E u ∈ orb E u := mem_orb.2 (Or.inr rfl)
  have memKU : ∀ z : Gam E n u, z ∈ KU E n u ↔ ∀ v, PC[v] z.1 ∈ GlobalTheory.LFun.KGL v n := fun z => by
    rw [show KU E n u = (Kglob E n).subgroupOf (Gam E n u) from rfl, Subgroup.mem_subgroupOf, mem_Kglob_iff]
  have pcmul : ∀ v (a b : Gam E n u), PC[v] (a * b).1 = PC[v] a.1 * PC[v] b.1 := fun v a b => by
    rw [Subgroup.coe_mul, map_mul]
  have pcinv : ∀ v (a : Gam E n u), PC[v] (a⁻¹).1 = (PC[v] a.1)⁻¹ := fun v a => by
    rw [Subgroup.coe_inv, map_inv]
  have pcδ : ∀ v ∈ orb E u, PC[v] (pfU E n u D).1 = PC[v] D := fun v hv => pc_pfU hv D
  have pcθδ : ∀ v ∈ orb E u, PC[v] (thU E n u (pfU E n u D)).1 = PC[v] (thF E n D) := fun v hv => by
    rw [pc_thU hv, pc_thF_pfU hv]

  have hMM : (y⁻¹ * pfU E n u D * thU E n u y) * thU E n u (y⁻¹ * pfU E n u D * thU E n u y) =
      y⁻¹ * (pfU E n u D * thU E n u (pfU E n u D)) * y := by
    simp only [map_mul, map_inv, thU_thU]; group
  have hconj : (PC[u] y.1)⁻¹ * PC[u] (D * thF E n D) * PC[u] y.1 ∈ GlobalTheory.LFun.KGL u n := by
    have h := (memKU _).1 (mul_mem hy (thU_mem_KU hy)) u
    rw [hMM, pcmul, pcmul, pcinv, pcmul, pcδ u hu, pcθδ u hu] at h
    rw [map_mul]; exact h
  obtain ⟨t1, ht1, k1, hk1, hg1⟩ :=
    GlobalTheory.SplitUniq.splitUniq E n u _ (PC[u] y.1) (hD u hu).2.1 (hD u hu).2.2 hconj

  set T : Gam E n u := pfU E n u (locGL E n u t1) with hT
  have pcTu : PC[u] T.1 = t1 := by rw [hT, pc_pfU hu]; exact pLoc_locGL _ _
  have pcTo : ∀ v, v ≠ u → PC[v] T.1 = 1 := by
    intro v h
    by_cases hv : v ∈ orb E u
    · rw [hT, pc_pfU hv]; exact pLoc_locGL_of_ne h _
    · exact pc_gam _ hv
  have pcθTu : PC[u] (thU E n u T).1 = 1 := by
    rw [pc_thU hu, hT, pc_thF_pfU hu, pc_thF_congr (x' := 1) (by rw [pLoc_locGL_of_ne hne]; exact (map_one _).symm), map_one, map_one]
  have pcθTb : PC[cPl E u] (thU E n u T).1 = PC[cPl E u] (thF E n (locGL E n u t1)) := by
    rw [pc_thU hub, hT, pc_thF_pfU hub]
  have hN : PC[u] (D * thF E n D) = PC[u] D * PC[u] (thF E n D) := map_mul _ _ _
  refine ⟨T * pfU E n u D * thU E n u T * (pfU E n u D)⁻¹, ?_, (T * pfU E n u D * thU E n u T * (pfU E n u D)⁻¹)⁻¹ * y, ?_, by group⟩
  · show T * pfU E n u D * thU E n u T * (pfU E n u D)⁻¹ * pfU E n u D =
      pfU E n u D * thU E n u (T * pfU E n u D * thU E n u T * (pfU E n u D)⁻¹)
    simp only [map_mul, map_inv, thU_thU]
    apply Subtype.ext; apply gl_ext; intro v
    by_cases hv : v ∈ orb E u
    · rcases mem_orb.1 hv with h | h <;> rw [h]
      · simp only [pcmul, pcinv, pcTu, pcθTu, pcδ u hu, pcθδ u hu]
        rw [hN] at ht1
        have key : t1 * PC[u] D = PC[u] D * (PC[u] (thF E n D) * t1 * (PC[u] (thF E n D))⁻¹) := by
          calc t1 * PC[u] D = t1 * (PC[u] D * PC[u] (thF E n D)) * (PC[u] (thF E n D))⁻¹ := by group
            _ = PC[u] D * PC[u] (thF E n D) * t1 * (PC[u] (thF E n D))⁻¹ := by rw [ht1]
            _ = _ := by group
        calc _ = t1 * PC[u] D := by group
          _ = _ := key
          _ = _ := by group
      · simp only [pcmul, pcinv, pcTo _ hne, pcθTb, pcδ _ hub, pcθδ _ hub]
        group
    · simp [pcmul, pcinv, pc_gam _ hv]
  · rw [memKU]
    intro v
    simp only [pcmul, pcinv]
    by_cases hv : v ∈ orb E u
    · rcases mem_orb.1 hv with h | h <;> rw [h]
      · simp only [pcTu, pcθTu, pcδ u hu]
        convert hk1 using 1
        rw [hg1]; group
      · simp only [pcTo _ hne, pcθTb, pcδ _ hub]
        have hB : PC[cPl E u] (thF E n (locGL E n u t1)) =
            PC[cPl E u] (thF E n y.1) * (PC[cPl E u] (thF E n (locGL E n u k1)))⁻¹ := by
          have ht1' : t1 = PC[u] y.1 * k1⁻¹ := by rw [hg1]; group
          rw [ht1', map_mul, map_inv, map_mul, map_inv, map_mul, map_inv]
          rw [pc_thF_congr (x' := y.1) (by rw [cPl_cPl]; exact pLoc_locGL _ _)]
        have hMb : PC[cPl E u] (y⁻¹ * pfU E n u D * thU E n u y).1 =
            (PC[cPl E u] y.1)⁻¹ * PC[cPl E u] D * PC[cPl E u] (thF E n y.1) := by
          rw [pcmul, pcmul, pcinv, pcδ _ hub, pc_thU hub]
        have h1 := (memKU _).1 hy (cPl E u)
        rw [hMb] at h1
        have h2 : PC[cPl E u] (thF E n (locGL E n u k1)) ∈ GlobalTheory.LFun.KGL (cPl E u) n :=
          (mem_Kglob_iff _).1 (thF_mem_Kglob (locGL_mem_Kglob hk1)) _
        convert mul_mem (mul_mem (hD _ hub).1 h2) (inv_mem h1) using 1
        rw [hB]; group
    · simp only [pc_gam _ hv, inv_one, mul_one, one_mul]
      exact one_mem _

end GlobalTheory.EulerTwSplit
