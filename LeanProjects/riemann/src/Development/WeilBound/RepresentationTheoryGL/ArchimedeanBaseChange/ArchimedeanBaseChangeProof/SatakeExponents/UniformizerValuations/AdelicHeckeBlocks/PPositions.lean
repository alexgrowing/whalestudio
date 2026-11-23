import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKGLIffVal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.TopoThetaRCont

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Slots

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev loc (n : ℕ) (w : Pl E) : GL (Fin n) (Af E) →* GLw n w := GeneralLinearGroup.map (pLoc E w)

abbrev cP (w : Pl E) : Pl E := GlobalTheory.EulerTw.cPl E w

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (loc (E := E) n w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (RestrictedProduct.continuous_eval w))

theorem loc_thF_congr {n : ℕ} {g h : GL (Fin n) (Af E)} (u : Pl E) (H : loc n (cP u) g = loc n (cP u) h) :
    loc n u (thF E n g) = loc n u (thF E n h) := by
  have hi : loc n (cP u) g⁻¹ = loc n (cP u) h⁻¹ := by rw [map_inv, map_inv, H]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e : pLoc E (cP u) ((g⁻¹ : GL (Fin n) (Af E)).val j.rev i.rev) =
      pLoc E (cP u) ((h⁻¹ : GL (Fin n) (Af E)).val j.rev i.rev) :=
    congrArg (fun k : GLw n (cP u) => k.val j.rev i.rev) hi
  show pLoc E u ((GlobalTheory.CuspRep.thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) =
    pLoc E u ((GlobalTheory.CuspRep.thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) h).val i j)
  rw [GlobalTheory.ThetaPull.thetaGL_apply, GlobalTheory.ThetaPull.thetaGL_apply, map_mul, map_mul, pLoc_conjFin, pLoc_conjFin]
  exact congrArg _ (congrArg _ e)

theorem loc_thF_mem {n : ℕ} {g : GL (Fin n) (Af E)} (u : Pl E)
    (hg : loc n (cP u) g ∈ GlobalTheory.LFun.KGL (cP u) n) : loc n u (thF E n g) ∈ GlobalTheory.LFun.KGL u n := by
  have hs := (GlobalTheory.EulerTwKU.mem_KGL_iff_val _).1 hg
  rw [GlobalTheory.EulerTwKU.mem_KGL_iff_val]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GlobalTheory.EulerTwKU.val_pLoc_thF, map_inv]
    exact hs.2 _ _
  · rw [← map_inv, ← map_inv, GlobalTheory.EulerTwKU.val_pLoc_thF, inv_inv]
    exact hs.1 _ _

theorem exists_lift {n : ℕ} (Y : ∀ u : Pl E, GLw n u) (hc : ∀ᶠ u in cofinite, Y u ∈ GlobalTheory.LFun.KGL u n) :
    ∃ g : GL (Fin n) (Af E), ∀ u, loc n u g = Y u := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun u => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_loc_mem {n : ℕ} (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, loc n w g ∈ GlobalTheory.LFun.KGL w n := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => h1 i j, fun i j => h2 i j⟩

theorem ev_sum {α β : Type} {P : α ⊕ β → Prop} (h1 : ∀ᶠ a in cofinite, P (Sum.inl a))
    (h2 : ∀ᶠ b in cofinite, P (Sum.inr b)) : ∀ᶠ i in cofinite, P i := by
  rw [eventually_cofinite] at h1 h2 ⊢
  refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
  rintro (a | b) h
  · exact Or.inl ⟨a, h, rfl⟩
  · exact Or.inr ⟨b, h, rfl⟩

theorem ev_dite {n : ℕ} {p : Pl E → Prop} (y : ∀ w : {w // p w}, GLw n w.1)
    (h : ∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w.1 n) :
    ∀ᶠ u : Pl E in cofinite, (if hu : p u then y ⟨u, hu⟩ else 1) ∈ GlobalTheory.LFun.KGL u n := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image Subtype.val).subset fun u hu => ?_
  by_cases hp : p u
  · refine ⟨⟨u, hp⟩, ?_, rfl⟩
    have hu' : ¬ (if hu : p u then y ⟨u, hu⟩ else 1) ∈ GlobalTheory.LFun.KGL u n := hu
    rw [dif_pos hp] at hu'
    exact hu'
  · exact absurd (by rw [dif_neg hp]; exact one_mem _) hu

theorem cP_cP (v : Pl E) : cP (cP v) = v := GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl v

theorem cP_eq_of_not_split {v : Pl E} (h : ¬ IsSplitAt v) : cP v = v := by
  by_contra hne
  exact h (GlobalTheory.CompanionTheory.SuppFinTw.split_of_conj_ne hne)

def cpn (n : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, GL (Fin n) (Af E) →* GLw n i.pl
  | .inl w => loc n w.1
  | .inr w => (loc n w.1).comp (thF E n)

def cpH (a b : ℕ) {S : Set (Pl E)} (i : Slot S) : Gf E a b →* GLw a i.pl × GLw b i.pl :=
  (cpn a i).prodMap (cpn b i)

theorem cp_eq {a b : ℕ} {S : Set (Pl E)} (i : Slot S) (x : Gf E a b) : i.cp a b x = cpH a b i x := by
  cases i <;> rfl

theorem continuous_cpn (n : ℕ) {S : Set (Pl E)} (i : Slot S) : Continuous (cpn (E := E) n i) := by
  rcases i with w | w
  · show Continuous (loc n w.1)
    exact continuous_loc n w.1
  · show Continuous ((loc n w.1).comp (thF E n))
    exact (continuous_loc n w.1).comp (PositivityTheory.Rg.BcB.G8.topo_holds E n).2.2.2.2.1

theorem continuous_cpH (a b : ℕ) {S : Set (Pl E)} (i : Slot S) : Continuous (cpH (E := E) a b i) :=
  ((continuous_cpn a i).comp continuous_fst).prodMk ((continuous_cpn b i).comp continuous_snd)

theorem F_exists {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) (y : ∀ i : Slot S, GLw n i.pl)
    (hy : ∀ᶠ i in cofinite, y i ∈ GlobalTheory.LFun.KGL i.pl n) : ∃ g : GL (Fin n) (Af E), ∀ i, cpn n i g = y i := by
  have hy1 : ∀ᶠ w : {w // w ∈ S} in cofinite, y (.inl w) ∈ GlobalTheory.LFun.KGL w.1 n :=
    Sum.inl_injective.tendsto_cofinite.eventually hy
  have hy2 : ∀ᶠ w : {w // w ∈ S ∧ IsSplitAt w} in cofinite, y (.inr w) ∈ GlobalTheory.LFun.KGL w.1 n :=
    Sum.inr_injective.tendsto_cofinite.eventually hy
  obtain ⟨g₁, h₁⟩ := exists_lift (n := n) _ (ev_dite (fun w => y (.inl w)) hy1)
  obtain ⟨g₂, h₂⟩ := exists_lift (n := n) _ (ev_dite (fun w => y (.inr w)) hy2)
  have hS1 : ∀ w : Pl E, w ∈ S → loc n w (thF E n g₂) = 1 := by
    intro w hw
    have hn : ¬ (cP w ∈ S ∧ IsSplitAt (cP w)) := by
      rintro ⟨hc, hsp⟩
      by_cases hw' : IsSplitAt w
      · exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS hw hw' hc
      · rw [cP_eq_of_not_split hw'] at hsp
        exact hw' hsp
    have h0 : loc n (cP w) g₂ = loc n (cP w) 1 := by
      rw [h₂, map_one]
      exact dif_neg hn
    rw [loc_thF_congr w h0, map_one, map_one]
  have hS2 : ∀ w : Pl E, w ∈ S → IsSplitAt w → loc n w (thF E n g₁) = 1 := by
    intro w hw hsp
    have h0 : loc n (cP w) g₁ = loc n (cP w) 1 := by
      rw [h₁, map_one]
      exact dif_neg (GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS hw hsp)
    rw [loc_thF_congr w h0, map_one, map_one]
  refine ⟨g₁ * thF E n g₂, fun i => ?_⟩
  rcases i with w | w
  · show loc n w.1 (g₁ * thF E n g₂) = y (.inl w)
    rw [map_mul, hS1 w.1 w.2, mul_one, h₁]
    exact dif_pos w.2
  · show loc n w.1 (thF E n (g₁ * thF E n g₂)) = y (.inr w)
    rw [map_mul, map_mul, GlobalTheory.EulerTw.Comm.thF_thF, hS2 w.1 w.2.1 w.2.2, one_mul, h₂]
    exact dif_pos w.2

theorem F_ext {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {g h : GL (Fin n) (Af E)}
    (H : ∀ i : Slot S, cpn n i g = cpn n i h) : g = h := by
  refine GlobalTheory.EulerTwRestr.gl_ext fun u => ?_
  rcases GlobalTheory.CompanionTheory.SuppFinTw.mem_or_conj hS u with hu | ⟨v, hv, rfl⟩
  · exact H (.inl ⟨u, hu⟩)
  · by_cases hsp : IsSplitAt v
    · have H2 : loc n (cP (cP v)) (thF E n g) = loc n (cP (cP v)) (thF E n h) := by
        rw [cP_cP]
        exact H (.inr ⟨v, hv, hsp⟩)
      have := loc_thF_congr (cP v) H2
      rwa [GlobalTheory.EulerTw.Comm.thF_thF, GlobalTheory.EulerTw.Comm.thF_thF] at this
    · show loc n (cP v) g = loc n (cP v) h
      rw [cP_eq_of_not_split hsp]
      exact H (.inl ⟨v, hv⟩)

theorem F_ev {n : ℕ} {S : Set (Pl E)} (g : GL (Fin n) (Af E)) :
    ∀ᶠ i : Slot S in cofinite, cpn n i g ∈ GlobalTheory.LFun.KGL i.pl n :=
  ev_sum (Subtype.val_injective.tendsto_cofinite.eventually (eventually_loc_mem g))
    (Subtype.val_injective.tendsto_cofinite.eventually (eventually_loc_mem (thF E n g)))

theorem F_mem {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) (g : GL (Fin n) (Af E)) :
    g ∈ Kf E n ↔ ∀ i : Slot S, cpn n i g ∈ GlobalTheory.LFun.KGL i.pl n := by
  have hK : g ∈ Kf E n ↔ ∀ u, loc n u g ∈ GlobalTheory.LFun.KGL u n := by
    rw [Kf, Subgroup.mem_iInf]
    rfl
  rw [hK]
  refine ⟨fun H i => ?_, fun H u => ?_⟩
  · rcases i with w | w
    · exact H w.1
    · exact loc_thF_mem w.1 (H _)
  · rcases GlobalTheory.CompanionTheory.SuppFinTw.mem_or_conj hS u with hu | ⟨v, hv, rfl⟩
    · exact H (.inl ⟨u, hu⟩)
    · by_cases hsp : IsSplitAt v
      · have H2 : loc n (cP (cP v)) (thF E n g) ∈ GlobalTheory.LFun.KGL (cP (cP v)) n := by
          rw [cP_cP]
          exact H (.inr ⟨v, hv, hsp⟩)
        have := loc_thF_mem (cP v) H2
        rwa [GlobalTheory.EulerTw.Comm.thF_thF] at this
      · show loc n (cP v) g ∈ GlobalTheory.LFun.KGL (cP v) n
        rw [cP_eq_of_not_split hsp]
        exact H (.inl ⟨v, hv⟩)

theorem pair_exists {a b : ℕ} {S : Set (Pl E)} (hS : IsSection S) (y : ∀ i : Slot S, GLw a i.pl × GLw b i.pl)
    (hy : ∀ᶠ i in cofinite, y i ∈ K2 a b i.pl) : ∃ x : Gf E a b, ∀ i, cpH a b i x = y i := by
  obtain ⟨g₁, h₁⟩ := F_exists hS (fun i => (y i).1) (hy.mono fun i h => (Subgroup.mem_prod.1 h).1)
  obtain ⟨g₂, h₂⟩ := F_exists hS (fun i => (y i).2) (hy.mono fun i h => (Subgroup.mem_prod.1 h).2)
  exact ⟨(g₁, g₂), fun i => Prod.ext (h₁ i) (h₂ i)⟩

theorem pair_mem {a b : ℕ} {S : Set (Pl E)} (hS : IsSection S) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ i : Slot S, cpH a b i x ∈ K2 a b i.pl := by
  rw [Subgroup.mem_prod, F_mem hS, F_mem hS]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact Subgroup.mem_prod.2 ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (Subgroup.mem_prod.1 (h i)).1, fun i => (Subgroup.mem_prod.1 (h i)).2⟩

theorem pair_compact {a b : ℕ} {S : Set (Pl E)} (hS : IsSection S) (C : ∀ i : Slot S, Set (GLw a i.pl × GLw b i.pl))
    (hC : ∀ i, IsCompact (C i)) (hCK : ∀ᶠ i in cofinite, C i = K2 a b i.pl) :
    IsCompact {x : Gf E a b | ∀ i : Slot S, cpH a b i x ∈ C i} := by
  obtain ⟨T, hT⟩ : ∃ T : Set (Slot S), T = {i | ¬ C i = K2 a b i.pl} := ⟨_, rfl⟩
  have hTf : T.Finite := by
    rw [hT]
    exact eventually_cofinite.1 hCK
  have hopen : ∀ i : Slot S, IsOpen (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)) := fun i => by
    show IsOpen (((GlobalTheory.LFun.KGL i.pl a).prod (GlobalTheory.LFun.KGL i.pl b) : Subgroup _) : Set (GLw a i.pl × GLw b i.pl))
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL i.pl a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL i.pl b).1
  have hcov : ∀ i : Slot S, ∃ t : Finset (GLw a i.pl × GLw b i.pl),
      C i ⊆ ⋃ c ∈ t, {z | c⁻¹ * z ∈ K2 a b i.pl} := fun i => by
    obtain ⟨t, -, ht⟩ := (hC i).elim_nhds_subcover (fun c => {z | c⁻¹ * z ∈ K2 a b i.pl}) fun c _ =>
      ((hopen i).preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show c⁻¹ * c ∈ K2 a b i.pl
        rw [inv_mul_cancel]
        exact one_mem _)
    exact ⟨t, ht⟩
  choose t ht using hcov
  have : Finite T := hTf.to_subtype
  have hlift : ∀ c : (∀ i : T, {d // d ∈ t i.1}), ∃ x : Gf E a b, ∀ i,
      cpH a b i x = if h : i ∈ T then ((c ⟨i, h⟩).1 : GLw a i.pl × GLw b i.pl) else 1 := fun c => by
    refine pair_exists hS _ ?_
    rw [eventually_cofinite]
    refine hTf.subset fun i hi => ?_
    by_contra hn
    exact hi (by
      show (if h : i ∈ T then ((c ⟨i, h⟩).1 : GLw a i.pl × GLw b i.pl) else 1) ∈ K2 a b i.pl
      rw [dif_neg hn]
      exact one_mem _)
  choose xc hxc using hlift
  have hcl : IsClosed {x : Gf E a b | ∀ i : Slot S, cpH a b i x ∈ C i} := by
    have e : {x : Gf E a b | ∀ i : Slot S, cpH a b i x ∈ C i} = ⋂ i, cpH a b i ⁻¹' C i := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    exact isClosed_iInter fun i => (hC i).isClosed.preimage (continuous_cpH a b i)
  refine (isCompact_iUnion fun c : (∀ i : T, {d // d ∈ t i.1}) =>
    ((GlobalTheory.CompanionTheory.EulerV.isCompact_Kf (E := E) (n := a)).prod (GlobalTheory.CompanionTheory.EulerV.isCompact_Kf (E := E) (n := b))).image
      (continuous_const.mul continuous_id (f := fun _ : Gf E a b => xc c))).of_isClosed_subset hcl ?_
  intro x hx
  have hd : ∀ i : T, ∃ d : {d // d ∈ t i.1}, (d.1)⁻¹ * cpH a b i.1 x ∈ K2 a b i.1.pl := fun i => by
    have h := ht i.1 (hx i.1)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h
    obtain ⟨d, hd, h⟩ := h
    exact ⟨⟨d, hd⟩, h⟩
  choose c hc using hd
  refine Set.mem_iUnion.2 ⟨c, (xc c)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
  have hk : (xc c)⁻¹ * x ∈ (Kf E a).prod (Kf E b) := by
    refine (pair_mem hS _).2 fun i => ?_
    rw [map_mul, map_inv, hxc]
    by_cases hi : i ∈ T
    · rw [dif_pos hi]
      exact hc ⟨i, hi⟩
    · rw [dif_neg hi, inv_one, one_mul]
      have hi' : ¬ ¬ C i = K2 a b i.pl := by
        rw [hT] at hi
        exact hi
      have := hx i
      rwa [not_not.1 hi'] at this
  exact Subgroup.mem_prod.1 hk

end Slots

open Slots in

theorem slots : Slots := by
  intro E _ _ _ a b S hS
  refine ⟨fun i x y => ?_, fun i => ?_, fun x y H => ?_, fun y hy => ?_, fun x => ?_, fun x => ?_, fun C hC hCK => ?_⟩
  · rw [cp_eq, cp_eq, cp_eq, map_mul]
  · have e : i.cp a b = cpH a b i := funext (cp_eq i)
    rw [e]
    exact continuous_cpH a b i
  · have H' : ∀ i : Slot S, cpH a b i x = cpH a b i y := fun i => (cp_eq i x).symm.trans ((H i).trans (cp_eq i y))
    exact Prod.ext (F_ext hS fun i => congrArg Prod.fst (H' i)) (F_ext hS fun i => congrArg Prod.snd (H' i))
  · obtain ⟨x, hx⟩ := pair_exists hS y hy
    exact ⟨x, fun i => (cp_eq i x).trans (hx i)⟩
  · filter_upwards [F_ev (S := S) x.1, F_ev (S := S) x.2] with i h1 h2
    rw [cp_eq]
    exact Subgroup.mem_prod.2 ⟨h1, h2⟩
  · rw [pair_mem hS]
    simp only [cp_eq]
  · have e : {x : Gf E a b | ∀ i : Slot S, i.cp a b x ∈ C i} = {x | ∀ i : Slot S, cpH a b i x ∈ C i} := by
      ext x
      simp only [Set.mem_ofPred_eq, cp_eq]
    rw [e]
    exact pair_compact hS C hC hCK

end PositivityTheory.Rg.BcB.F

end
