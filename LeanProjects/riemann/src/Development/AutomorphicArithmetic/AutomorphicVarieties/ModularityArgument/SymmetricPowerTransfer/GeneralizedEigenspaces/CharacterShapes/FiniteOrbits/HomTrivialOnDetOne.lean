import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Gl2

open Matrix

variable {K : Type} [Field K]

private def upU (x : K) : GL (Fin 2) K :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

private def loU (x : K) : GL (Fin 2) K :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

private def sc1 (h : (2 : K) ≠ 0) : GL (Fin 2) K :=
  ⟨!![2, 0; 0, 1], !![2⁻¹, 0; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h]⟩

private def sc2 (h : (2 : K) ≠ 0) : GL (Fin 2) K :=
  ⟨!![1, 0; 0, 2], !![1, 0; 0, 2⁻¹], by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h]⟩

variable {C : Type} [CommGroup C] (D : GL (Fin 2) K →* C)

private theorem D_upU (h : (2 : K) ≠ 0) (x : K) : D (upU x) = 1 := by
  have e1 : sc1 h * upU x * (sc1 h)⁻¹ = upU x * upU x := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    simp [sc1, upU, Matrix.mul_fin_two]
    ring
  have e2 := congrArg D e1
  rw [map_mul, map_mul, map_inv, map_mul, mul_comm (D (sc1 h)), mul_inv_cancel_right] at e2
  exact (left_eq_mul.1 e2)

private theorem D_loU (h : (2 : K) ≠ 0) (x : K) : D (loU x) = 1 := by
  have e1 : sc2 h * loU x * (sc2 h)⁻¹ = loU x * loU x := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    simp [sc2, loU, Matrix.mul_fin_two]
    ring
  have e2 := congrArg D e1
  rw [map_mul, map_mul, map_inv, map_mul, mul_comm (D (sc2 h)), mul_inv_cancel_right] at e2
  exact (left_eq_mul.1 e2)

private theorem D_of_ne (h : (2 : K) ≠ 0) (g : GL (Fin 2) K) (hg : GeneralLinearGroup.det g = 1)
    (hc : g.val 1 0 ≠ 0) : D g = 1 := by
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    have := congrArg Units.val hg
    simpa [Matrix.det_fin_two] using this
  have e : g = upU ((g.val 0 0 - 1) / g.val 1 0) * loU (g.val 1 0) * upU ((g.val 1 1 - 1) / g.val 1 0) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upU, loU, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | ring1 | linear_combination hd | linear_combination -hd
  rw [e, map_mul, map_mul, D_upU D h, D_upU D h, D_loU D h, mul_one, mul_one]

private theorem hom_trivial_on_det_one (h : (2 : K) ≠ 0) (g : GL (Fin 2) K) (hg : GeneralLinearGroup.det g = 1) : D g = 1 := by
  by_cases hc : g.val 1 0 = 0
  · have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.det_fin_two] using this
    have h11 : g.val 1 1 ≠ 0 := fun h0 => by simp [hc, h0] at hd
    have h2 : D (g * loU 1) = 1 := by
      refine D_of_ne D h _ ?_ ?_
      · rw [map_mul, hg, one_mul]
        ext
        simp [loU, Matrix.det_fin_two]
      · simpa [loU, Matrix.mul_apply, Fin.sum_univ_two, hc] using h11
    rwa [map_mul, D_loU D h, mul_one] at h2
  · exact D_of_ne D h g hg hc

end Gl2

section Lev

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem det_diagonal_two (d : Fin 2 → kˣ) : GeneralLinearGroup.det (Sig.dg d) = d 0 * d 1 := by
  ext
  simp [Sig.dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem det_in_H (V : Lev k) (g : GL (Fin 2) k) (hg : g ∈ V.J 2) : GeneralLinearGroup.det g ∈ V.H := by
  obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V 2).1 g hg
  have h2 := (mem_unipB _).1 ha.1
  have h3 := GlAx.mem_low.1 hb.1
  have da : GeneralLinearGroup.det a = 1 := by
    ext
    simp [Matrix.det_fin_two, h2.1 1 0 (by decide), h2.2]
  have db : GeneralLinearGroup.det b = 1 := by
    ext
    simp [Matrix.det_fin_two, h3.1 0 1 (by decide), h3.2]
  rw [map_mul, map_mul, da, db, one_mul, mul_one, show diagT k (Fin 2) s = Sig.dg s from rfl, det_diagonal_two]
  exact mul_mem (hs 0 trivial) (hs 1 trivial)

private theorem dg_comm {n : ℕ} (a b : Fin n → kˣ) : Sig.dg a * Sig.dg b = Sig.dg b * Sig.dg a := by
  rw [Sig.dg, Sig.dg, ← map_mul, ← map_mul, mul_comm]

end Lev

private theorem two_ne {L : Type} [Field L] [NumberField L] (w : Plc L) : (2 : Kw w) ≠ 0 := by
  have h : algebraMap L (Kw w) 2 ≠ 0 := (map_ne_zero _).2 two_ne_zero
  rwa [map_ofNat] at h

theorem UpperTheory.V.Z.Sym.So.torUA :
    UpperTheory.V.Z.Sym.So.TorUA := by
  intro L _ _ _ U₀ S VL hP hF u hu
  classical
  obtain ⟨fA, -, -, -, fE, fF, fG, fH⟩ := uaFacts L 2
  have huU : u ∈ U₀ := (Subgroup.mem_inf.1 hu).1
  have huJ : ∀ w ∈ S, cLoc w u ∈ (VL w).J 2 := fun w hw =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).2 w) hw
  have huK : u ∈ Kall L 2 := hF.1 huU
  have hKfin : ∀ {y : UA L 2}, y ∈ U₀ → y ∈ finU L 2 := fun hy => (Subgroup.mem_inf.1 (hF.1 hy)).1
  let δ : ∀ w : Plc L, (Kw w)ˣ := fun w => Matrix.GeneralLinearGroup.det (cLoc w u)
  let e : ∀ w : Plc L, GL (Fin 2) (Kw w) := fun w => Sig.dg ![δ w, 1]
  let g : ∀ w : Plc L, GL (Fin 2) (Kw w) := fun w => (cLoc w u)⁻¹ * e w
  have hδ : ∀ w ∈ S, δ w ∈ (VL w).H := fun w hw => det_in_H _ _ (huJ w hw)
  have hg1 : ∀ w, Matrix.GeneralLinearGroup.det (g w) = 1 := fun w => by
    simp only [g, e, map_mul, map_inv, det_diagonal_two]
    simp [δ]
  have hgK : ∀ w ∈ S, g w ∈ GlobalTheory.LFun.KGL w 2 := fun w hw => by
    refine mul_mem (inv_mem ?_) ?_
    · exact Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 huK).2 w
    · rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
      refine dg_mem_KO fun i => ?_
      fin_cases i
      · exact (VL w).H_le (hδ w hw)
      · exact one_mem _
  have piece : ∀ w ∈ S, secW 2 w (g w) ∈ U₀ ∧ secW 2 w (g w) ∈ finU L 2 ⊓ SUA L ∧ cLoc w (secW 2 w (g w)) = g w ∧
      ∀ w' ∈ S, w' ≠ w → cLoc w' (secW 2 w (g w)) = 1 := fun w hw => by
    have hs := hP.split w hw
    obtain ⟨a1, a2, -, -⟩ := fA w hs
    have hl := a1 (g w)
    have hc := a2 (g w)
    have hoff : ∀ u' : Plc L, un u' ≠ un w → cLoc u' (secW 2 w (g w)) = 1 := fun u' hne =>
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u') hne)
    have hfin := (Subgroup.mem_inf.1 hl).1
    refine ⟨?_, ?_, hc, fun w' hw' hne => hoff w' fun h => hne (hP.inj hw' hw h)⟩
    · refine hF.2 w hw (Subgroup.mem_inf.2 ⟨hl, Subgroup.mem_inf.2 ⟨hfin, Subgroup.mem_iInf.2 fun u' => ?_⟩⟩)
      by_cases h : un u' = un w
      · exact fH w hs _ (by rw [hc]; exact hgK w hw) u' h
      · rw [Subgroup.mem_comap, hoff u' h]
        exact one_mem _
    · refine Subgroup.mem_inf.2 ⟨hfin, ?_⟩
      exact hom_trivial_on_det_one ((Matrix.GeneralLinearGroup.det.comp (UA L 2).subtype).comp (secW 2 w)) (two_ne w) _ (hg1 w)
  have prod : ∀ T : Finset (Plc L), T ⊆ S → ∃ p : UA L 2, p ∈ U₀ ∧ p ∈ finU L 2 ⊓ SUA L ∧
      (∀ w ∈ T, cLoc w p = g w) ∧ ∀ w ∈ S, w ∉ T → cLoc w p = 1 := fun T => by
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_mem _, one_mem _, by simp, by simp⟩
    | insert w₀ T hw₀ ih =>
      intro hT
      have hw₀S := hT (Finset.mem_insert_self _ _)
      obtain ⟨p, p1, p2, p3, p4⟩ := ih fun x hx => hT (Finset.mem_insert_of_mem hx)
      obtain ⟨q1, q2, q3, q4⟩ := piece w₀ hw₀S
      refine ⟨p * secW 2 w₀ (g w₀), mul_mem p1 q1, mul_mem p2 q2, fun w hw => ?_, fun w hw hn => ?_⟩
      · rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [map_mul, p4 _ hw₀S hw₀, q3, one_mul]
        · rw [map_mul, p3 w hw, q4 w (hT (Finset.mem_insert_of_mem hw)) (fun h => hw₀ (h ▸ hw)), mul_one]
      · have hn1 : w ≠ w₀ := fun h => hn (h ▸ Finset.mem_insert_self _ _)
        have hn2 : w ∉ T := fun h => hn (Finset.mem_insert_of_mem h)
        rw [map_mul, p4 w hw hn2, q4 w hw hn1, one_mul]
  obtain ⟨p, p1, p2, p3, -⟩ := prod S subset_rfl
  have hcw : ∀ w ∈ S, cLoc w (u * p) = e w := fun w hw => by
    rw [map_mul, p3 w hw]
    simp [g]
  have hc : u * p ∈ lev U₀ S VL := by
    refine Subgroup.mem_inf.2 ⟨mul_mem huU p1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_⟩
    rw [Subgroup.mem_comap, hcw w hw]
    refine (VL w).dg_mem fun i => ?_
    fin_cases i
    · exact hδ w hw
    · exact one_mem _
  refine ⟨u * p, hc, ?_, ?_, fun x d hx hd => ?_⟩
  · have : u * (u * p)⁻¹ = u * p⁻¹ * u⁻¹ := by group
    rw [this]
    have hn : (finU L 2 ⊓ SUA L).Normal := by
      have h1 : (finU L 2).Normal := MonoidHom.normal_ker _
      have h2 : (SUA L).Normal := MonoidHom.normal_ker _
      exact Subgroup.normal_inf_normal _ _
    exact hn.conj_mem _ (inv_mem p2) u
  · have : (u * p)⁻¹ * u = p⁻¹ := by group
    rw [this]
    exact inv_mem p2
  · set c := u * p with hcdef
    have hcfin : c ∈ finU L 2 := hKfin (mul_mem huU p1)
    set z := c * x * c⁻¹ * x⁻¹ with hz
    have hzfin : z ∈ finU L 2 := mul_mem (mul_mem (mul_mem hcfin hx.1) (inv_mem hcfin)) (inv_mem hx.1)
    have hz1 : ∀ w ∈ S, cLoc w z = 1 := fun w hw => by
      simp only [hz, map_mul, map_inv]
      rw [hcw w hw, hd w hw]
      show Sig.dg _ * Sig.dg _ * (Sig.dg _)⁻¹ * (Sig.dg _)⁻¹ = 1
      rw [dg_comm]
      group
    have hzall : ∀ w : Plc L, cLoc w z = 1 := fun w => by
      by_cases h : ∃ w' ∈ S, un w = un w'
      · obtain ⟨w', hw', he⟩ := h
        obtain ⟨a, ha, ha'⟩ := fG w' z hzfin
        have h0 : cLoc w' a = 1 := by rw [ha' w' rfl, hz1 w' hw']
        have h1 : a = 1 := by
          rw [(fA w' (hP.split w' hw')).2.2.2 a ha, h0, map_one]
        rw [← ha' w he, h1, map_one]
      · have h1 : cLoc w x = 1 := hx.2 w fun w' hw' he => h ⟨w', hw', he⟩
        simp [hz, h1]
    have hz0 : z = 1 := fE z 1 (fun w => by rw [hzall w, map_one]) fun τ => by
      rw [(fF z).1.1 hzfin τ, map_one]
    have : c * x * c⁻¹ * x⁻¹ = 1 := hz0
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this

end
