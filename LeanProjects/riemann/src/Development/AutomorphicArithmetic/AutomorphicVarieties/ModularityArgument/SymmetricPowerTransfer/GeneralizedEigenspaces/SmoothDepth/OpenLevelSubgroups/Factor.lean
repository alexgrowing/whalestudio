import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

noncomputable section

namespace UpperTheory.V.Z.Sym.Al.FactorizationTer

open GlobalTheory.SplitPts GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ua_ext {g h : UA E n} (h1 : cInf g = cInf h) (h2 : ∀ u, cLoc u g = cLoc u h) : g = h := by
  refine Subtype.ext (ga_ext h1 ?_)
  refine Units.ext (matAf_ext fun u => ?_)
  exact congrArg Units.val (h2 u)

open Classical in

private def idem (P : HeightOneSpectrum (𝓞 E) → Prop) : Af E :=
  ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
private theorem pLoc_idem (P : HeightOneSpectrum (𝓞 E) → Prop) (u : HeightOneSpectrum (𝓞 E)) :
    pLoc E u (idem P) = if P u then 1 else 0 := rfl

private def cutM (P : HeightOneSpectrum (𝓞 E) → Prop) (A : Matrix (Fin n) (Fin n) (Af E)) :
    Matrix (Fin n) (Fin n) (Af E) := idem P • A + (1 - idem P) • 1

private theorem map_cutM_pos {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = RingHom.mapMatrix (pLoc E u) A := by
  ext i j
  simp [cutM, Matrix.add_apply, Matrix.smul_apply, pLoc_idem, h]

private theorem map_cutM_neg {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : ¬ P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = 1 := by
  have h0 : pLoc E u (idem P) = 0 := by rw [pLoc_idem, if_neg h]
  refine Matrix.ext fun i j => ?_
  change pLoc E u (idem P * A i j + (1 - idem P) * (1 : Matrix (Fin n) (Fin n) (Af E)) i j) =
    (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j
  rw [map_add, map_mul, map_mul, map_sub, map_one, h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem cutM_mul (P : HeightOneSpectrum (𝓞 E) → Prop) {A B : Matrix (Fin n) (Fin n) (Af E)}
    (h : A * B = 1) : cutM P A * cutM P B = 1 := by
  refine matAf_ext fun u => ?_
  rw [map_mul, map_one]
  by_cases hu : P u
  · rw [map_cutM_pos _ hu, map_cutM_pos _ hu, ← map_mul, h, map_one]
  · rw [map_cutM_neg _ hu, map_cutM_neg _ hu, one_mul]

private def cut (P : HeightOneSpectrum (𝓞 E) → Prop) (k : GL (Fin n) (Af E)) : GL (Fin n) (Af E) where
  val := cutM P k.val
  inv := cutM P (k⁻¹).val
  val_inv := cutM_mul P (by simp)
  inv_val := cutM_mul P (by simp)

private theorem under_conj (u : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (conjE E) u).under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (conjPl_self_conjSrc u))

private theorem exists_part (w : HeightOneSpectrum (𝓞 E)) (g : UA E n) :
    ∃ x : UA E n, cInf x = 1 ∧
      (∀ u, u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = cLoc u g) ∧
      ∀ u, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = 1 := by
  set P : HeightOneSpectrum (𝓞 E) → Prop := fun u =>
    u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) with hP
  set k : GL (Fin n) (Af E) := cut P (Matrix.GeneralLinearGroup.map (pFin E) g.1) with hk
  have hpos : ∀ u, P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = cLoc u g := fun u hu =>
    Units.ext (map_cutM_pos _ hu)
  have hneg : ∀ u, ¬ P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = 1 := fun u hu =>
    Units.ext (map_cutM_neg _ hu)
  have hmem : finGL E n k ∈ UA E n := by
    refine finGL_mem_UA k fun u => ?_
    by_cases hu : P u
    · have hc : P (conjSrc (conjE E) u) := (under_conj u).trans hu
      rw [hpos u hu, hpos _ hc]
      exact comp_eq g u
    · have hc : ¬ P (conjSrc (conjE E) u) := fun h => hu ((under_conj u).symm.trans h)
      rw [hneg u hu, hneg _ hc]
      simp
  have hloc : ∀ u, cLoc u (⟨_, hmem⟩ : UA E n) = Matrix.GeneralLinearGroup.map (pLoc E u) k := fun u => by
    change Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
    exact Units.ext (congrArg (fun M : GL (Fin n) (Af E) => RingHom.mapMatrix (pLoc E u) M.val) (pFin_finGL k))
  exact ⟨⟨_, hmem⟩, pInf_finGL k, fun u hu => (hloc u).trans (hpos u hu),
    fun u hu => (hloc u).trans (hneg u hu)⟩

end UpperTheory.V.Z.Sym.Al.FactorizationTer

end

theorem UpperTheory.V.Z.Sym.Al.factor :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L),
        (∀ x ∈ locU n w, ∀ y ∈ away n w, x * y = y * x) ∧
        (∀ g : UA L n, ∃ x ∈ locU n w, ∃ y ∈ away n w, g = x * y) ∧
        (∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → locU n w' ≤ away n w) ∧ infU L n ≤ away n w ∧
        (∀ x ∈ locU n w, x ∈ Kall L n ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w n) ∧
        ∀ x ∈ locU n w, ∀ y ∈ away n w, (x * y ∈ Kall L n ↔ x ∈ Kall L n ∧ y ∈ Kall L n) := by
  intro L _ _ _ n w
  have hfin : ∀ {x : UA L n}, x ∈ locU n w → cInf x = 1 := fun hx => (Subgroup.mem_inf.1 hx).1
  have hout : ∀ {x : UA L n}, x ∈ locU n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) →
      cLoc u x = 1 := fun hx u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  have hin : ∀ {y : UA L n}, y ∈ away n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) →
      cLoc u y = 1 := fun hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu)
  have haway : ∀ {y : UA L n}, (∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → cLoc u y = 1) →
      y ∈ away n w := fun h =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 (h u hu)
  have hK : ∀ {x : UA L n}, x ∈ Kall L n → ∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u n := fun hx u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
  have hKmk : ∀ {x : UA L n}, x ∈ finU L n → (∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u n) → x ∈ Kall L n :=
    fun h1 h2 => Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (h2 u)⟩
  have hKf : ∀ {x : UA L n}, x ∈ Kall L n → x ∈ finU L n := fun hx => (Subgroup.mem_inf.1 hx).1
  refine ⟨fun x hx y hy => ?_, fun g => ?_, fun w' hw' x hx => ?_, fun x hx => ?_, fun x hx => ⟨fun h => hK h w, fun h => ?_⟩,
    fun x hx y hy => ⟨fun h => ?_, fun h => mul_mem h.1 h.2⟩⟩
  · refine FactorizationTer.ua_ext ?_ fun u => ?_
    · rw [map_mul, map_mul, hfin hx, one_mul, mul_one]
    · rw [map_mul, map_mul]
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu, one_mul, mul_one]
      · rw [hout hx u hu, one_mul, mul_one]
  · obtain ⟨x, h1, h2, h3⟩ := FactorizationTer.exists_part w g
    refine ⟨x, Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
      MonoidHom.mem_ker.2 (h3 u hu)⟩, x⁻¹ * g, haway fun u hu => ?_, by group⟩
    rw [map_mul, map_inv, h2 u hu, inv_mul_cancel]
  · refine haway fun u hu => ?_
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact hw'.symm))
  · refine haway fun u _ => ?_
    have h : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
    have h' := congrArg (Matrix.GeneralLinearGroup.map (pLoc L u)) h
    rw [map_one] at h'
    exact h'
  · refine hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_
    by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with e | e
      · subst e
        exact h
      · subst e
        exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w h
    · rw [hout hx u hu]
      exact one_mem _
  · have hf : cInf (x * y) = 1 := hKf h
    rw [map_mul, hfin hx, one_mul] at hf
    refine ⟨hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_, hKmk hf fun u => ?_⟩
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have := hK h u
        rwa [map_mul, hin hy u hu, mul_one] at this
      · rw [hout hx u hu]
        exact one_mem _
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu]
        exact one_mem _
      · have := hK h u
        rwa [map_mul, hout hx u hu, one_mul] at this
