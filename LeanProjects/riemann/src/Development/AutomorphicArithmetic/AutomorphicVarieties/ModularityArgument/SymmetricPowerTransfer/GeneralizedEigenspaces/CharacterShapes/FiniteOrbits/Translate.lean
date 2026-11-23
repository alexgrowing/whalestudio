import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.WeakOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools Matrix
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Comm

variable {K G : Type} [Field K] [CommGroup G]

private def e12 (x : K) : GL (Fin 2) K :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two], by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

private def e21 (x : K) : GL (Fin 2) K :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two], by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

private def dt (t : K) (h : t ≠ 0) : GL (Fin 2) K :=
  ⟨!![t, 0; 0, 1], !![t⁻¹, 0; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h], by simp [Matrix.mul_fin_two, Matrix.one_fin_two, h]⟩

private theorem upper_elementary_add (x y : K) : e12 (x + y) = e12 x * e12 y :=
  Units.ext (by simp [e12, Matrix.mul_fin_two, add_comm])

private theorem lower_elementary_add (x y : K) : e21 (x + y) = e21 x * e21 y :=
  Units.ext (by simp [e21, Matrix.mul_fin_two, add_comm])

private theorem hom_trivial_on_upper_elementary (t : K) (h : t ≠ 0) (y : K) : dt t h * e12 y = e12 (t * y) * dt t h :=
  Units.ext (by simp [e12, dt, Matrix.mul_fin_two])

private theorem diagonal_conj_lower_elementary (t : K) (h : t ≠ 0) (y : K) : dt t h * e21 (y * t) = e21 y * dt t h :=
  Units.ext (by simp [e21, dt, Matrix.mul_fin_two])

private theorem diagonal_conj_upper_elementary (D : GL (Fin 2) K →* G) (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (x : K) : D (e12 x) = 1 := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.2 h1
  set y := x / (t - 1) with hy
  have e : t * y = y + x := by rw [hy]; field_simp; ring
  have h := congrArg D (hom_trivial_on_upper_elementary t h0 y)
  rw [map_mul, map_mul, e, upper_elementary_add, map_mul, mul_comm (D (dt t h0))] at h
  have h2 := mul_right_cancel h
  simpa using h2

private theorem hom_trivial_on_lower_elementary (D : GL (Fin 2) K →* G) (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (x : K) : D (e21 x) = 1 := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.2 h1
  set y := x / (t - 1) with hy
  have e : y * t = y + x := by rw [hy]; field_simp; ring
  have h := congrArg D (diagonal_conj_lower_elementary t h0 y)
  rw [map_mul, map_mul, e, lower_elementary_add, map_mul, mul_comm (D (dt t h0))] at h
  have h2 := mul_right_cancel h
  simpa using h2

private theorem D_ne (D : GL (Fin 2) K →* G) (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (g : GL (Fin 2) K)
    (hd : (g.val).det = 1) (hc : g.val 1 0 ≠ 0) : D g = 1 := by
  have e : g = e12 ((g.val 0 0 - 1) / g.val 1 0) * e21 (g.val 1 0) * e12 ((g.val 1 1 - 1) / g.val 1 0) := by
    rw [Matrix.det_fin_two] at hd
    refine Units.ext ?_
    have ev := Matrix.eta_fin_two g.val
    generalize g.val 0 0 = a at *
    generalize g.val 0 1 = b at *
    generalize g.val 1 0 = c at *
    generalize g.val 1 1 = d at *
    rw [ev]
    simp only [Units.val_mul, e12, e21, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
    all_goals first | ring1 | linear_combination hd | linear_combination -hd | linear_combination 2 * hd | linear_combination -2 * hd
  rw [e, map_mul, map_mul, diagonal_conj_upper_elementary D t h0 h1, diagonal_conj_upper_elementary D t h0 h1, hom_trivial_on_lower_elementary D t h0 h1]
  simp

private theorem D_one (D : GL (Fin 2) K →* G) (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (g : GL (Fin 2) K)
    (hd : (g.val).det = 1) : D g = 1 := by
  by_cases hc : g.val 1 0 = 0
  · have ha : g.val 0 0 ≠ 0 := by
      intro ha
      rw [Matrix.det_fin_two, hc, ha] at hd
      simp at hd
    have h := D_ne D t h0 h1 (e21 1 * g) (by
      rw [Units.val_mul, Matrix.det_mul, hd, mul_one]
      simp [e21, Matrix.det_fin_two]) (by
      simpa [e21, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha)
    rw [map_mul, hom_trivial_on_lower_elementary D t h0 h1, one_mul] at h
    exact h
  · exact D_ne D t h0 h1 g hd hc

end Comm

section Ad

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem locU_off {n : ℕ} {w u : Plc L} {x : UA L n} (hx : x ∈ locU n w) (h : un u ≠ un w) : cLoc u x = 1 := by
  have h2 := (Subgroup.mem_inf.1 hx).2
  simp only [Subgroup.mem_iInf] at h2
  exact h2 u h

private theorem exProd {n : ℕ} (S : Finset (Plc L)) (hs : ∀ w ∈ S, IsSplitAt w)
    (hi : Set.InjOn (fun w : Plc L => un w) (S : Set (Plc L))) (g : ∀ w : Plc L, GL (Fin n) (Kw w)) :
    ∃ p : UA L n, (∀ H : Subgroup (UA L n), (∀ w ∈ S, secW n w (g w) ∈ H) → p ∈ H) ∧
      ∀ w ∈ S, ∀ u, un u = un w → cLoc u p = cLoc u (secW n w (g w)) := by
  classical
  have hF := (uaFacts L n).1
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun H _ => H.one_mem, by simp⟩
  | insert a T ha ih =>
    obtain ⟨p, h1, h2⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw))
      (hi.mono (by simp [Set.subset_def]; tauto))
    have hne : ∀ w ∈ T, un w ≠ un a := fun w hw e => ha (by
      have := hi (by simp [hw]) (by simp) e
      exact this ▸ hw)
    have hsa := (hF a (hs a (Finset.mem_insert_self _ _))).1 (g a)
    refine ⟨p * secW n a (g a), fun H hH => H.mul_mem (h1 H fun w hw => hH w (Finset.mem_insert_of_mem hw))
      (hH a (Finset.mem_insert_self _ _)), ?_⟩
    intro w hw u hu
    rw [map_mul]
    rcases Finset.mem_insert.1 hw with rfl | hw'
    · have : p ∈ (cLoc u : UA L n →* _).ker := h1 _ fun v hv =>
        MonoidHom.mem_ker.2 (locU_off ((hF v (hs v (Finset.mem_insert_of_mem hv))).1 _) (hu ▸ (hne v hv).symm))
      rw [MonoidHom.mem_ker.1 this, one_mul]
    · rw [h2 w hw' u hu, locU_off hsa (hu ▸ hne w hw'), mul_one]

private theorem int_of_Uo (w : Plc L) (x : (Kw w)ˣ) (h : x ∈ Uo (Kw w)) : (x : Kw w) ∈ w.adicCompletionIntegers L := by
  have h1 : valuation (Kw w) (x : Kw w) = 1 := h
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one.1 h1.le

private theorem dg_KGL (w : Plc L) (d : Fin 2 → (Kw w)ˣ) (hd : ∀ i, d i ∈ Uo (Kw w)) : dg d ∈ GlobalTheory.LFun.KGL w 2 := by
  have key : ∀ (e : Fin 2 → (Kw w)ˣ), (∀ i, e i ∈ Uo (Kw w)) → ∀ a b, (dg e).val a b ∈ w.adicCompletionIntegers L := by
    intro e he a b
    rw [val_diagT, Matrix.diagonal_apply]
    split_ifs
    · exact int_of_Uo w _ (he a)
    · exact zero_mem _
  refine GlobalTheory.BCT.GoodConj.mem_KGL_of_entries w _ (key d hd) ?_
  rw [← map_inv]
  exact key _ fun i => inv_mem (hd i)

private theorem sec_Kall (w : Plc L) (hw : IsSplitAt w) (g : GL (Fin 2) (Kw w)) (hg : g ∈ GlobalTheory.LFun.KGL w 2) :
    secW 2 w g ∈ Kall L 2 := by
  obtain ⟨hsec, -, -, -, -, -, -, hint⟩ := uaFacts L 2
  obtain ⟨h1, h2, -, -⟩ := hsec w hw
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (h1 g)).1, Subgroup.mem_iInf.2 fun u => ?_⟩
  by_cases h : un u = un w
  · exact hint w hw _ (by rw [h2]; exact hg) u h
  · rw [Subgroup.mem_comap, locU_off (h1 g) h]
    exact one_mem _

private theorem sec_SU (w : Plc L) (hw : IsSplitAt w) (g : GL (Fin 2) (Kw w)) (hg : (g.val).det = 1) :
    secW 2 w g ∈ SUA L := by
  have h2 : (algebraMap L (Kw w) 2) ≠ 0 := by simp
  have h3 : (algebraMap L (Kw w) 2) ≠ 1 := by
    intro h
    have : (2 : L) = 1 := (algebraMap L (Kw w)).injective (by simpa using h)
    norm_num at this
  exact D_one (((GeneralLinearGroup.det.comp (UA L 2).subtype)).comp (secW 2 w)) _ h2 h3 g hg

end Ad

theorem UpperTheory.V.Z.Sym.So.translate :
    UpperTheory.V.Z.Sym.So.Translate := by
  intro L _ _ _ S VL hP V _ _ R φ hφ hne
  obtain ⟨hsec, hcom, hfk, hfkc, hext, hmem, hloc, hint⟩ := uaFacts L 2
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  have hinf : ∀ a x : UA L 2, x ∈ infU L 2 → φ (a * x) ≠ 0 → φ a ≠ 0 := fun a x hx h h0 =>
    h (by rw [hφ.inf x hx a, h0]; simp)
  obtain ⟨f, hf, k, hk, rfl⟩ := hfk g
  have hf0 : φ f ≠ 0 := hinf _ _ hk hg
  obtain ⟨δ, hδ, hδS⟩ := weakOne L S hP (fun w => (GeneralLinearGroup.det (cLoc w f))⁻¹) (fun w => (VL w).c + 1)
  set m : GL (Fin 2) L := diagT L (Fin 2) ![δ, 1] with hm
  have hmU : ratGL L 2 m ∈ UA L 2 := by
    refine (Br.ratFacts L 2 m).1.2 ?_
    rw [hm, val_diagT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simpa [mul_comm] using hδ
    · simp
  set γ : UA L 2 := ⟨ratGL L 2 m, hmU⟩ with hγ
  have hγr : γ ∈ ratU L 2 := ⟨m, rfl⟩
  have hγl : ∀ w, mL w γ = (m : Matrix (Fin 2) (Fin 2) L).map (algebraMap L (Kw w)) := ((Br.ratFacts L 2 m).2.2 hmU).1
  obtain ⟨a, ha, b, hb, hab⟩ := hfk γ
  have hbw : ∀ w, cLoc w b = 1 := ((hmem b).2).1 hb
  have hdet : ∀ w, GeneralLinearGroup.det (cLoc w a) = Units.map (algebraMap L (Kw w) : L →* Kw w) δ := by
    intro w
    have e : cLoc w a = cLoc w γ := by rw [hab, map_mul, hbw, mul_one]
    refine Units.ext ?_
    rw [e, Matrix.GeneralLinearGroup.val_det_apply]
    change (mL w γ).det = _
    rw [hγl, hm, val_diagT, Matrix.diagonal_map (map_zero _), Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
  have haf : φ (a * f) ≠ 0 := by
    refine hinf _ b hb ?_
    have e : a * f * b = γ * f := by
      rw [hab, mul_assoc, mul_assoc, (hfkc f hf b hb).eq]
    rw [e, hφ.left γ hγr]
    exact hf0
  set h : ∀ w : Plc L, (Kw w)ˣ := fun w => Units.map (algebraMap L (Kw w) : L →* Kw w) δ / (GeneralLinearGroup.det (cLoc w f))⁻¹ with hh
  have hH : ∀ w ∈ S, h w ∈ (VL w).H := fun w hw => (VL w).le (hδS w hw)
  have hdaf : ∀ w, GeneralLinearGroup.det (cLoc w (a * f)) = h w := by
    intro w
    rw [map_mul, map_mul, hdet, hh]
    simp
  have hInj : Set.InjOn (fun w : Plc L => un w) (S : Set (Plc L)) := hP.inj
  have hSp : ∀ w ∈ S, IsSplitAt w := fun w hw => hP.split w hw
  obtain ⟨u, hu1, hu2⟩ := exProd S hSp hInj (fun w => dg ![(h w)⁻¹, 1])
  have hwu : ∀ w ∈ S, cLoc w u = dg ![(h w)⁻¹, 1] := fun w hw => by
    rw [hu2 w hw w rfl]
    exact (hsec w (hSp w hw)).2.1 _
  have hHe : ∀ w ∈ S, ∀ i, (![(h w)⁻¹, 1] : Fin 2 → (Kw w)ˣ) i ∈ (VL w).H := by
    intro w hw i
    fin_cases i
    · exact inv_mem (hH w hw)
    · exact one_mem _
  have huL : u ∈ lev (Kall L 2) S VL := by
    refine Subgroup.mem_inf.2 ⟨hu1 _ fun w hw => sec_Kall w (hSp w hw) _ (dg_KGL w _ fun i => (VL w).H_le (hHe w hw i)), ?_⟩
    refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_
    rw [Subgroup.mem_comap, hwu w hw]
    exact (VL w).dg_mem (hHe w hw)
  set y : UA L 2 := a * f * u with hy
  have hy0 : φ y ≠ 0 := by
    rw [hy, hφ.level u huL]
    exact haf
  have hufin : u ∈ finU L 2 := hu1 _ fun w hw => (Subgroup.mem_inf.1 ((hsec w (hSp w hw)).1 _)).1
  have hyfin : y ∈ finU L 2 := mul_mem (mul_mem ha hf) hufin
  have hdy : ∀ w ∈ S, ((cLoc w y).val).det = 1 := by
    intro w hw
    have e : GeneralLinearGroup.det (cLoc w y) = 1 := by
      have e2 : GeneralLinearGroup.det (dg ![(h w)⁻¹, 1]) = (h w)⁻¹ := by
        refine Units.ext ?_
        rw [Matrix.GeneralLinearGroup.val_det_apply, val_diagT, Matrix.det_diagonal]
        simp [Fin.prod_univ_two]
      rw [hy, map_mul, map_mul, hdaf, hwu w hw, e2, mul_inv_cancel]
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val e
  obtain ⟨s, hs1, hs2⟩ := exProd S hSp hInj (fun w => cLoc w y)
  have hsm : s ∈ finU L 2 ⊓ SUA L := hs1 _ fun w hw =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ((hsec w (hSp w hw)).1 _)).1, sec_SU w (hSp w hw) _ (hdy w hw)⟩
  refine ⟨s⁻¹ * y, mul_mem (inv_mem (Subgroup.mem_inf.1 hsm).1) hyfin, ?_, s, hsm, ?_⟩
  · intro w hw v hv
    obtain ⟨c, hc, hcu⟩ := hloc w y hyfin
    have e : c = secW 2 w (cLoc w y) := by
      have := (hsec w (hSp w hw)).2.2.2 c hc
      rwa [hcu w rfl] at this
    rw [map_mul, map_inv, hs2 w hw v hv, ← e, hcu v hv, inv_mul_cancel]
  · rw [mul_inv_cancel_left]
    exact hy0

end
