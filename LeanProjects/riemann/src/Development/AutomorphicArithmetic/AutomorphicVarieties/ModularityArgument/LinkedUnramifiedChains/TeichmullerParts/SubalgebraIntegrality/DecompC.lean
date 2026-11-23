import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicLocalComponentsContinuousLevelsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL

noncomputable section

section Conj

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem UpperTheory.V.Z.J.D.Dc.int_conj (x : UA E n) (u : Pl E)
    (h : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) u) n) :
    cLoc u x ∈ GlobalTheory.LFun.KGL u n := by
  have h1 := GlobalTheory.BCT.LocGlue.intst E n _ u (conjLoc (GlobalTheory.SplitPts.conjE E) u) (conjLoc_spec _ u).2.2 _ h
  have e : cLoc u x = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x)) := by
    have hce := GlobalTheory.SplitPts.comp_eq x u
    generalize hB : GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x) = B
    have hB' : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) = B.val := by
      rw [← hB]
      rfl
    rw [hB'] at hce
    apply Units.ext
    change (cLoc u x).val = ((B⁻¹ : GL (Fin n) _).val)ᵀ
    have h2 : ((B⁻¹ : GL (Fin n) _).val)ᵀ * (B.val)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc (cLoc u x).val = (((B⁻¹ : GL (Fin n) _).val)ᵀ * (B.val)ᵀ) * (cLoc u x).val := by rw [h2, Matrix.one_mul]
      _ = ((B⁻¹ : GL (Fin n) _).val)ᵀ := by rw [Matrix.mul_assoc, hce, Matrix.mul_one]
  rw [e]
  exact h1

theorem UpperTheory.V.Z.J.D.Dc.int_over {w u : Pl E}
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : UA E n)
    (h : cLoc w x ∈ GlobalTheory.LFun.KGL w n) : cLoc u x ∈ GlobalTheory.LFun.KGL u n := by
  by_cases e : u = w
  · subst e
    exact h
  · rcases (GlobalTheory.SplitPts.over_split (w := w) ⟨u, e, hu⟩).2.2 u hu with rfl | rfl
    · exact h
    · refine UpperTheory.V.Z.J.D.Dc.int_conj x _ ?_
      have e2 : ∀ v, v = w → cLoc v x ∈ GlobalTheory.LFun.KGL v n := by
        rintro v rfl
        exact h
      exact e2 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w)

end Conj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.Dc

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω]

theorem unrOf (s : HidaSetting l L Ω) : GlobalTheory.BCT.Unr L := fun w => by
  haveI : IsGalois (Lp L) L := inferInstance
  have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
    obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
    ext x
    apply (algebraMap L Ω).injective
    exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
  have hb : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
  have h1 := UpperTheory.V.CF.ineCard.1 (Lp L) L w
  rw [hb, Subgroup.card_bot] at h1
  haveI := w.isPrime
  haveI := w.isMaximal
  haveI : (w.asIdeal.under (𝓞 (Lp L))).IsMaximal := Ideal.IsMaximal.under _ _
  exact Ideal.ramificationIdx_eq_one_iff.1 h1.symm

theorem under_w (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

theorem secRange (s : HidaSetting l L Ω) : GlobalTheory.BCT.IsSection (Set.range s.w) := fun w => by
  refine ⟨s.w (w.under (𝓞 (Lp L))), ⟨⟨_, rfl⟩, under_w s _⟩, ?_⟩
  rintro _ ⟨⟨v, rfl⟩, h⟩
  have e : v = w.under (𝓞 (Lp L)) := (under_w s v).symm.trans h
  rw [e]

open Classical in

def Pc (s : HidaSetting l L Ω) (n c : ℕ) (w : Plc L) : Subgroup (GLw n w) :=
  if w ∈ s.w '' s.S then Kc _ n c else GlobalTheory.LFun.KGL w n

def Kf (s : HidaSetting l L Ω) (n c : ℕ) (w : GlobalTheory.BCT.Pl L) : Subgroup (GlobalTheory.BCT.UL n w) :=
  (Pc s n c w).subgroupOf (GlobalTheory.BCT.UL n w)

variable (s : HidaSetting l L Ω) (n c : ℕ)

theorem Pc_le (w : Plc L) : Pc s n c w ≤ GlobalTheory.LFun.KGL w n := by
  unfold Pc
  split_ifs
  · rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko]
    exact UpperTheory.V.Hi.GlAx.Kc_le c
  · exact le_rfl

theorem Pc_open (w : Plc L) : IsOpen (Pc s n c w : Set (GLw n w)) := by
  unfold Pc
  split_ifs
  · exact (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 w c
  · rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko, ← UpperTheory.V.Hi.GlAx.Kc_zero]
    exact (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 w 0

variable {s n c}

theorem Pc_notS {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) : Pc s n c w = GlobalTheory.LFun.KGL w n := by
  unfold Pc
  refine if_neg ?_
  rintro ⟨v, hv, rfl⟩
  exact hw ((under_w s v).symm ▸ hv)

theorem Pc_S {v : Plc (Lp L)} (hv : v ∈ s.S) : Pc s n c (s.w v) = Kc _ n c := by
  unfold Pc
  exact if_pos ⟨v, hv, rfl⟩

theorem Kf_notS {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) : Kf s n c w = GlobalTheory.BCT.KL n w := by
  unfold Kf GlobalTheory.BCT.KL
  rw [Pc_notS hw]

theorem levFam (hfin : s.S.Finite) :
    GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) (Kf s n c) := by
  refine ⟨fun w => ⟨(Pc_open s n c w).preimage continuous_subtype_val, fun k hk => Pc_le s n c w hk, fun k hk => hk⟩, ?_⟩
  filter_upwards [(hfin.image s.w).compl_mem_cofinite] with w hw
  unfold Kf GlobalTheory.BCT.KL Pc
  rw [if_neg hw]

theorem loc_of_glob (hU : GlobalTheory.BCT.Unr L) {k : finU L n} (hk : k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c))
    (v : Plc (Lp L)) : cLoc (s.w v) (k : UA L n) ∈ Pc s n c (s.w v) :=
  (GlobalTheory.BCT.HopLev.mem_globLev hU _ _ k).1 hk (s.w v) ⟨v, rfl⟩

theorem glob_of_loc (hU : GlobalTheory.BCT.Unr L) {k : finU L n} (h : ∀ v, cLoc (s.w v) (k : UA L n) ∈ Pc s n c (s.w v)) :
    k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c) :=
  (GlobalTheory.BCT.HopLev.mem_globLev hU _ _ k).2 (by
    rintro _ ⟨v, rfl⟩
    exact h v)

theorem cmp_mem {w : Plc L} (U : Subgroup (GLw n w)) (x : UA L n) (hx : cLoc w x ∈ U) :
    cmp n w ((away l L n).rangeRestrict x) ∈ U := by
  unfold CaseU.cmp
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [dif_pos h]
    exact hx
  · rw [dif_neg h]
    exact one_mem _

private theorem pi_mem_first_iwahori_filtration {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) (b : ℕ)
    (g : ∀ v, G v) (hg : ∀ v, g v ∈ (I v).I1 b) : g ∈ (piIwa I).I1 b := by
  choose x hx t ht y hy e using fun v => (iwMem _ (I v) b (g v)).2.1.1 (hg v)
  exact (iwMem _ (piIwa I) b g).2.1.2 ⟨x, fun v _ => hx v, t, fun v _ => ht v, y, fun v _ => hy v, funext e⟩

theorem Q_empty {V : s.Lev} (hV : V.S' = s.S) (Q : QData V) : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
  have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  rwa [hV] at h)⟩

theorem goodOf {V : s.Lev} (hV : V.S' = s.S) (Q : QData V) {cf : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) cf.O)
    (b : ℕ) (hc : ∀ g : KT n (wt s), (∀ u, (g : GV n (wt s)) u ∈ Kc _ n c) → τ₀ g = 1) (h1 : 1 ≤ c) (hb : b + 1 ≤ c)
    (hU : GlobalTheory.BCT.Unr L) (k : finU L n) (hk : k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c)) :
    (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧
      (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := by
  haveI := Q_empty hV Q
  have hS : ∀ v ∈ s.S, cLoc (s.w v) (k : UA L n) ∈ Kc _ n c := fun v hv => by
    have := loc_of_glob hU hk v
    rwa [Pc_S hv] at this
  have hu : (away l L n).rangeRestrict (k : UA L n) ∈ Ub n s :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => cmp_mem _ _ (UpperTheory.V.Hi.GlAx.Kc_le c (hS u (Or.inr (Or.inl u.2)))),
      cmp_mem _ _ (UpperTheory.V.Hi.GlAx.Kc_anti h1 (hS s.v0 (Or.inr (Or.inr rfl))))⟩
  refine ⟨⟨⟨_, hu⟩, ?_, rfl, ?_⟩, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_,
      Subgroup.mem_iInf.2 fun q => isEmptyElim q⟩
    rw [hV] at hw
    have h2 := loc_of_glob hU hk (w.under (𝓞 (Lp L)))
    rw [Pc_notS (by rwa [under_w])] at h2
    have h3 := int_over (under_w s (w.under (𝓞 (Lp L)))).symm (k : UA L n) h2
    rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko] at h3
    exact cmp_mem _ _ h3
  · exact hc _ fun u => cmp_mem _ _ (hS u (Or.inr (Or.inl u.2)))
  · exact pi_mem_first_iwahori_filtration (fun v : V.frame.Vl => glIwa ((s.w v.1).adicCompletion L) n) b _ fun v =>
      (glBridge ((s.w v.1).adicCompletion L) n ℂ 1).2.2.2.2.1 b (UpperTheory.V.Hi.GlAx.Kc_anti hb (hS v.1 (Or.inl v.2)))

theorem exC {cf : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) cf.O) (hτ : IsOpen (τ₀.ker : Set (KT n (wt s)))) :
    ∃ c0 : ℕ, ∀ c, c0 ≤ c → ∀ g : KT n (wt s), (∀ u, (g : GV n (wt s)) u ∈ Kc _ n c) → τ₀ g = 1 := by
  classical
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hτ
  let H : Subgroup (GV n (wt s)) := τ₀.ker.map (KT n (wt s)).subtype
  have hHo : IsOpen (H : Set (GV n (wt s))) := by
    refine H.isOpen_of_mem_nhds (g := 1) ?_
    have h0 : IsOpen (Set.pi Set.univ fun u : s.St => (Kc ((wt s u).adicCompletion L) n 0 : Set (GLw n (wt s u)))) :=
      isOpen_set_pi Set.finite_univ fun u _ => (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 _ 0
    have h1 : (1 : GV n (wt s)) ∈ U := by
      have : (1 : KT n (wt s)) ∈ Subtype.val ⁻¹' U := by
        rw [hUe]
        exact one_mem τ₀.ker
      exact this
    refine Filter.mem_of_superset ((hU.inter h0).mem_nhds ⟨h1, fun u _ => one_mem _⟩) ?_
    rintro g ⟨hg, hg0⟩
    have hK : g ∈ KT n (wt s) := fun u _ => UpperTheory.V.Hi.GlAx.Kc_le 0 (hg0 u trivial)
    have : (⟨g, hK⟩ : KT n (wt s)) ∈ (τ₀.ker : Set (KT n (wt s))) := by
      rw [← hUe]
      exact hg
    exact ⟨⟨g, hK⟩, this, rfl⟩
  have hloc : ∀ u : s.St, ∃ cu, Kc ((wt s u).adicCompletion L) n cu ≤
      H.comap (MonoidHom.mulSingle (fun u => GLw n (wt s u)) u) := fun u =>
    (glBridge ((wt s u).adicCompletion L) n ℂ 1).2.2.2.1 _ (hHo.preimage (continuous_mulSingle u))
  choose cu hcu using hloc
  refine ⟨Finset.univ.sup cu, fun c hc g hg => ?_⟩
  have hpi : Subgroup.pi Set.univ (fun u : s.St => Kc ((wt s u).adicCompletion L) n c) ≤ H :=
    Subgroup.pi_le_iff.2 fun u => by
      rw [Subgroup.map_le_iff_le_comap]
      exact (UpperTheory.V.Hi.GlAx.Kc_anti ((Finset.le_sup (Finset.mem_univ u)).trans hc)).trans (hcu u)
  obtain ⟨g', hg', e⟩ := hpi (show (g : GV n (wt s)) ∈ _ from fun u _ => hg u)
  have : g' = g := Subtype.ext e
  rw [← this]
  exact hg'

theorem unramOf (hU : GlobalTheory.BCT.Unr L) (π : Submodule ℂ (UA L n → ℂ))
    (hne : π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c)) ≠ ⊥) (w : Plc L)
    (hw : w.under (𝓞 (Lp L)) ∉ s.S) : IsUnramU π w := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨φ, hφ.1, h0, fun x hx hK => ?_⟩
  have hxf : x ∈ finU L n := (Subgroup.mem_inf.1 hx).1
  have hmem : (⟨x, hxf⟩ : finU L n) ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c) := glob_of_loc hU fun v => by
    by_cases e : v = w.under (𝓞 (Lp L))
    · subst e
      rw [Pc_notS (by rwa [under_w])]
      exact int_over (under_w s _) x hK
    · have h1 : cLoc (s.w v) x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1
        (Subgroup.mem_inf.1 hx).2 (s.w v)) (by rwa [under_w]))
      change cLoc (s.w v) x ∈ _
      rw [h1]
      exact one_mem _
  have h2 := hφ.2 ⟨⟨x, hxf⟩, hmem⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h2
  exact h2

end UpperTheory.V.Z.J.D.Dc
