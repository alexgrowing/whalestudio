import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.map (pLoc E w) g).1 i j = pLoc E w (g.1 i j) := rfl

theorem loc_inv_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (pLoc E w) g)⁻¹).1 i j = pLoc E w ((g⁻¹).1 i j) := by
  rw [← map_inv]; rfl

theorem gl_ext {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g = Matrix.GeneralLinearGroup.map (pLoc E w) h) :
    g = h :=
  Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w =>
    congrArg (fun x : GLw n w => x.1 i j) (H w)))

theorem mem_KGL_iff {w : Pl E} {x : GLw n w} : x ∈ GlobalTheory.LFun.KGL w n ↔
    (∀ i j, x.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (x⁻¹).1 i j ∈ w.adicCompletionIntegers E :=
  GlobalTheory.AdelicU.mem_GLint_iff

theorem mem_Kglob {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    g ∈ Kglob E n ↔ ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  simp only [Kglob, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem coe_Kglob : (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    (PIW.ClassFinD.KGL E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  ext g
  change g ∈ Kglob E n ↔ PIW.ClassFinD.MatInt g.val ∧ PIW.ClassFinD.MatInt (g⁻¹).val
  rw [mem_Kglob]
  simp only [mem_KGL_iff, loc_val, loc_inv_val]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

theorem isCompact_Kglob : IsCompact (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  rw [coe_Kglob]; exact GlobalTheory.isCompact_KGL E n

theorem isOpen_Kglob : IsOpen (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  have hO : IsOpen ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} := by
    have e : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => M i j) ⁻¹'
          ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) := by
      ext M; simp [PIW.ClassFinD.MatInt]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((continuous_apply j).comp (continuous_apply i))
  rw [coe_Kglob]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage Units.continuous_coe_inv)

theorem mem_orb_iff (u w : Pl E) :
    w ∈ orb E u ↔ w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  rw [orb, Finset.mem_insert, Finset.mem_singleton, GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact GlobalTheory.SplitPts.conjPl_self_conjSrc u
  · have e := eq_conjSrc h
    change w = conjSrc (IsCMField.complexConj E).toRingEquiv u
    rw [e]
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm

theorem existsUnique_orb {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) : ∃! u, u ∈ S ∧ w ∈ orb E u := by
  obtain ⟨u, ⟨huS, hu⟩, huniq⟩ := hS w
  exact ⟨u, ⟨huS, (mem_orb_iff u w).2 hu.symm⟩,
    fun u' h => huniq u' ⟨h.1, ((mem_orb_iff u' w).1 h.2).symm⟩⟩

end GlobalTheory.EulerTwRestr

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (pLoc E w) (prjG E n T g) =
      if w ∈ T then Matrix.GeneralLinearGroup.map (pLoc E w) g else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [loc_val]
  have he : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl
  change pLoc E w ((idem E T • g.1 + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) i j) = _
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
    map_sub, map_one, he]
  split_ifs with h
  · rw [one_mul, sub_self, zero_mul, add_zero, loc_val]
  · rw [zero_mul, zero_add, sub_zero, one_mul, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem prjG_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    prjG E n T (prjG E n T g) = prjG E n T g :=
  gl_ext fun w => by rw [loc_prjG, loc_prjG]; split_ifs with h <;> simp [loc_prjG, h]

theorem loc_eq_one_of_mem_Gam {u w : Pl E} {y : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} (hy : y ∈ Gam E n u)
    (hw : w ∉ orb E u) : Matrix.GeneralLinearGroup.map (pLoc E w) y = 1 := by
  obtain ⟨g, rfl⟩ := hy
  rw [loc_prjG, if_neg hw]

theorem pfU_val (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (pfU E n u g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) = prjG E n (orb E u) g := rfl

theorem mem_KU_pfU {u : Pl E} {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    pfU E n u g ∈ KU E n u ↔ ∀ w ∈ orb E u, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  rw [show KU E n u = (Kglob E n).subgroupOf (Gam E n u) from rfl, Subgroup.mem_subgroupOf, pfU_val, mem_Kglob]
  refine ⟨fun h w hw => ?_, fun h w => ?_⟩
  · have := h w
    rwa [loc_prjG, if_pos hw] at this
  · rw [loc_prjG]
    split_ifs with hw
    · exact h w hw
    · exact one_mem _

theorem continuous_prjM (T : Finset (Pl E)) : Continuous (prjM E n T) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) =>
    idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
  exact (continuous_const_smul _).add continuous_const

theorem continuous_prjG (T : Finset (Pl E)) : Continuous (prjG E n T) :=
  Units.continuous_iff.2 ⟨(continuous_prjM T).comp Units.continuous_val,
    (continuous_prjM T).comp Units.continuous_coe_inv⟩

theorem continuous_pfU (u : Pl E) : Continuous (pfU E n u) :=
  continuous_induced_rng.2 (continuous_prjG (orb E u))

end GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw GlobalTheory.EulerTwRestr in

theorem GlobalTheory.EulerTwRestr.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)),
    IsSection S → GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)))
      (fun u : S => GlobalTheory.EulerTw.pfU E n u.1) (fun u : S => GlobalTheory.EulerTw.KU E n u.1) := by
  intro E _ _ _ n S hS
  have hu := existsUnique_orb hS
  choose σ hσS hσw using fun w => (hu w).exists
  have hσu : ∀ (w u : Pl E), u ∈ S → w ∈ orb E u → u = σ w := fun w u h1 h2 =>
    (hu w).unique ⟨h1, h2⟩ ⟨hσS w, hσw w⟩
  have hlev : ∀ x, (∀ u : S, pfU E n u.1 x ∈ KU E n u.1) ↔ x ∈ Kglob E n := by
    intro x
    rw [mem_Kglob]
    exact ⟨fun h w => mem_KU_pfU.1 (h ⟨σ w, hσS w⟩) w (hσw w), fun h u => mem_KU_pfU.2 fun w _ => h w⟩
  refine ⟨fun w => w.elim, fun u => continuous_pfU _, fun u => ?_, fun u => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_Kglob.preimage continuous_subtype_val
  · have e : (KU E n u.1 : Set (Gam E n u.1)) = pfU E n u.1 '' (Kglob E n : Set _) := by
      ext y
      refine ⟨fun hy => ⟨y.1, hy, Subtype.ext ?_⟩, ?_⟩
      · obtain ⟨g, hg⟩ := y.2
        rw [pfU_val, ← hg, prjG_prjG]
      · rintro ⟨g, hg, rfl⟩
        exact mem_KU_pfU.2 fun w _ => mem_Kglob.1 hg w
    rw [e]
    exact isCompact_Kglob.image (continuous_pfU _)
  · intro x y _ hf
    refine gl_ext fun w => ?_
    have h := congrArg (fun z : Gam E n (σ w) => Matrix.GeneralLinearGroup.map (pLoc E w) z.1) (hf ⟨σ w, hσS w⟩)
    simp only [pfU_val, loc_prjG, if_pos (hσw w)] at h
    exact h
  · intro x
    have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
      eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
    have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
      eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
    have hx : ∀ᶠ w in cofinite, Matrix.GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
      filter_upwards [h1, h2] with w h1 h2
      exact mem_KGL_iff.2 ⟨fun i j => by rw [loc_val]; exact h1 i j, fun i j => by rw [loc_inv_val]; exact h2 i j⟩
    have hB := eventually_cofinite.1 hx
    refine eventually_cofinite.2 (((hB.preimage Subtype.val_injective.injOn).union
      (hB.preimage ((conjSrc_injective (IsCMField.complexConj E).toRingEquiv).comp Subtype.val_injective).injOn)).subset ?_)
    intro u hu
    simp only [Set.mem_setOf_eq, mem_KU_pfU, not_forall] at hu
    obtain ⟨w, hw, hwx⟩ := hu
    rcases (by simpa [orb] using hw : w = u.1 ∨ w = cPl E u.1) with rfl | rfl
    · exact Or.inl hwx
    · exact Or.inr hwx
  · intro a y hy
    have hc : ∀ᶠ w in cofinite,
        Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1 ∈ GlobalTheory.LFun.KGL w n := by
      have hB := eventually_cofinite.1 hy
      refine eventually_cofinite.2 ((hB.biUnion fun u _ => (orb E u.1).finite_toSet).subset ?_)
      intro w hw
      exact Set.mem_iUnion₂.2 ⟨⟨σ w, hσS w⟩,
        fun h => hw (mem_Kglob.1 (Subgroup.mem_subgroupOf.1 h) w), hσw w⟩
    let M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) := Matrix.of fun i j =>
      ⟨fun w => (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).1 i j,
        hc.mono fun w h => (mem_KGL_iff.1 h).1 i j⟩
    let M' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) := Matrix.of fun i j =>
      ⟨fun w => ((Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1)⁻¹).1 i j,
        hc.mono fun w h => (mem_KGL_iff.1 h).2 i j⟩
    have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
        (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
      Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
    have hMM' : M * M' = 1 := hloc _ _ fun w => by
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).mul_inv
    have hM'M : M' * M = 1 := hloc _ _ fun w => by
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).inv_mul
    let x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) := ⟨M, M', hMM', hM'M⟩
    have hx : ∀ w, Matrix.GeneralLinearGroup.map (pLoc E w) x =
        Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1 := fun w =>
      Units.ext (Matrix.ext fun i j => rfl)
    refine ⟨x, fun w => w.elim, fun u => Subtype.ext (gl_ext fun w => ?_)⟩
    rw [pfU_val, loc_prjG]
    split_ifs with hw
    · have e : (⟨σ w, hσS w⟩ : S) = u := Subtype.ext (hσu w u.1 u.2 hw).symm
      rw [hx w, e]
    · exact (loc_eq_one_of_mem_Gam (y u).2 hw).symm
  · have e : {x | ∀ u : S, pfU E n u.1 x ∈ KU E n u.1} = (Kglob E n : Set _) := Set.ext hlev
    rw [e]
    exact isOpen_Kglob
  · intro C _
    have e : {x | (∀ w, GlobalTheory.RestrMeas.noArch (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) w x ∈ C w) ∧
        ∀ u : S, pfU E n u.1 x ∈ KU E n u.1} = (Kglob E n : Set _) :=
      Set.ext fun x => ⟨fun h => (hlev x).1 h.2, fun h => ⟨fun w => w.elim, (hlev x).2 h⟩⟩
    rw [e]
    exact isCompact_Kglob
