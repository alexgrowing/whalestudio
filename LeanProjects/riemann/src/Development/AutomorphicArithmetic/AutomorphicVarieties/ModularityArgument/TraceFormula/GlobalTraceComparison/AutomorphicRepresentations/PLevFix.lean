import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKUConjOfComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem core_exists {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K O : Subgroup G) (hK : IsCompact (K : Set G)) (hO : IsOpen (O : Set G)) :
    ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ O ∧ ∀ k ∈ K, ∀ x ∈ M, k * x * k⁻¹ ∈ M := by
  have hU : ∀ k : G, IsOpen {y : G | k⁻¹ * y ∈ O} := fun k => hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨T, hTK, hT⟩ := hK.elim_nhds_subcover (fun k => {y : G | k⁻¹ * y ∈ O})
    (fun k _ => (hU k).mem_nhds (by simpa using O.one_mem))
  have hT' : ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ O := fun k hk => by
    simpa using hT hk
  let M : Subgroup G :=
    { carrier := {x | ∀ t ∈ T, t⁻¹ * x * t ∈ O}
      one_mem' := fun t _ => by simpa using O.one_mem
      mul_mem' := fun {a b} ha hb t ht => by
        have := O.mul_mem (ha t ht) (hb t ht)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha t ht => by
        have := O.inv_mem (ha t ht)
        simpa [mul_assoc] using this }
  refine ⟨M, ?_, ?_, ?_⟩
  · have e : (M : Set G) = ⋂ t ∈ T, (fun x => t⁻¹ * x * t) ⁻¹' (O : Set G) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_biInter_finset fun t _ =>
      hO.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · intro x hx
    obtain ⟨t, ht, h⟩ := hT' 1 K.one_mem
    have h1 : t⁻¹ ∈ O := by simpa using h
    have h2 := O.mul_mem (O.mul_mem (O.inv_mem h1) (hx t ht)) h1
    have e : t⁻¹⁻¹ * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h2
  · intro k hk x hx t ht
    obtain ⟨t', ht', h⟩ := hT' (k⁻¹ * t) (K.mul_mem (K.inv_mem hk) (hTK t ht))
    have h2 := O.mul_mem (O.mul_mem (O.inv_mem h) (hx t' ht')) h
    have e : (t'⁻¹ * (k⁻¹ * t))⁻¹ * (t'⁻¹ * x * t') * (t'⁻¹ * (k⁻¹ * t)) = t⁻¹ * (k * x * k⁻¹) * t := by group
    rwa [e] at h2

private theorem fin_reduce {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)] (q : ∀ i, G →* A i)
    (Kg H : Subgroup G) (Y : Finset ι) (base : ∀ k ∈ Kg, (∀ v ∈ Y, q v k = 1) → k ∈ H) (T : Finset ι) :
    ∀ k ∈ Kg, (∀ v ∈ Y, v ∉ T → q v k = 1) →
      (∀ v ∈ T, ∃ e ∈ H, e ∈ Kg ∧ q v e = q v k ∧ ∀ u, u ≠ v → q u e = 1) → k ∈ H := by
  induction T using Finset.induction_on with
  | empty => exact fun k hk h0 _ => base k hk fun v hv => h0 v hv (by simp)
  | insert v T hv ih =>
    intro k hk h0 h1
    obtain ⟨e, heH, heK, hev, heu⟩ := h1 v (Finset.mem_insert_self _ _)
    have hk1 : k * e⁻¹ ∈ H := by
      refine ih _ (Kg.mul_mem hk (Kg.inv_mem heK)) (fun u hu huT => ?_) (fun u huT => ?_)
      · by_cases huv : u = v
        · subst huv
          simp [hev]
        · rw [map_mul, map_inv, heu u huv, inv_one, mul_one]
          exact h0 u hu (by simp [huv, huT])
      · have huv : u ≠ v := fun h => hv (h ▸ huT)
        obtain ⟨e', h1', h2', h3', h4'⟩ := h1 u (Finset.mem_insert_of_mem huT)
        refine ⟨e', h1', h2', ?_, h4'⟩
        rw [h3', map_mul, map_inv, heu u huv, inv_one, mul_one]
    simpa using H.mul_mem hk1 heH

private def stb {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : Sm E n) : Subgroup (GF E n) where
  carrier := {k | finRep E n k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem exists_fin {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (hq : ∀ w : Pl E, Continuous (qw n w false)) (H : Subgroup (GF E n)) (hH : IsOpen (H : Set (GF E n))) :
    ∃ Y : Finset (Pl E), ∀ k ∈ Kf E n, (∀ v ∈ Y, qw n v false k = 1) → k ∈ H := by
  have hC : IsCompact ((Kf E n : Set (GF E n)) ∩ (H : Set (GF E n))ᶜ) :=
    GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.inter_right hH.isClosed_compl
  obtain ⟨Y, hY⟩ := hC.elim_finite_subcover (fun v : Pl E => {g : GF E n | qw n v false g ≠ 1})
    (fun v => (isClosed_singleton.preimage (hq v)).isOpen_compl) (fun x hx => by
      by_contra hc
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hc
      have : x = 1 := GlobalTheory.LocFactor.glAf_ext fun v => by
        rw [map_one]
        exact hc v
      exact hx.2 (this ▸ H.one_mem))
  refine ⟨Y, fun k hk h1 => by_contra fun hkH => ?_⟩
  have := hY ⟨hk, hkH⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨v, hv, hne⟩ := this
  exact hne (h1 v hv)

theorem levFix_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → SlotBasic → JointFix → LevFix := by
  intro hP hS hJ E _ _ _ n π S Z hSec hZ hOff
  obtain ⟨hinv, -, hloc, -, -, -, hK⟩ := hS E n S hSec
  obtain ⟨-, hcP, -, hSP⟩ := hP E
  have hcc : ∀ w : Pl E, cPl (cPl w) = w := fun w => (hcP w).1
  have mem : ∀ (M : ∀ w : Pl E, Subgroup (GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have memK : ∀ x : GF E n, x ∈ Kf E n ↔ ∀ u : Pl E, qw n u false x ∈ KGL u n := by
    intro x
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
    rfl
  have hq : ∀ w : Pl E, Continuous (qw n w false) := fun w => (hloc w false).2.1

  have hth : ∀ (u : Pl E) (g : GF E n), qw n (cPl u) false g = 1 → qw n u true g = 1 := by
    intro u g h
    have := GlobalTheory.EulerTw.IntRead.map_thF (n := n) u g
    change qw n u true g = _ at this
    rw [this]
    have h' : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E u)) g = 1 := h
    rw [h', map_one]
  have hC : ∀ (w : Pl E) (g : GF E n), qw n w true g = 1 → qw n (cPl w) false g = 1 := by
    intro w g h
    have := hth (cPl w) (thF E n g) (by rw [hcc]; exact h)
    change qw n (cPl w) false (thF E n (thF E n g)) = 1 at this
    rwa [hinv] at this

  obtain ⟨ψ₀, hψ₀, hψ₀0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨Y₀, hY₀⟩ := exists_fin n hq (stb n ψ₀) (π.cusp ψ₀ hψ₀).1.level
  set Z2 : Finset (Pl E) := Z ∪ Z.image cPl with hZ2
  set Y : Finset (Pl E) := Y₀ ∪ Z2 with hY
  set U : Subgroup (GF E n) := Kf E n ⊓ ⨅ v ∈ Y, (qw n v false).ker with hU
  have memU : ∀ k, k ∈ U ↔ k ∈ Kf E n ∧ ∀ v ∈ Y, qw n v false k = 1 := by
    intro k
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  obtain ⟨ψ, hψ, hψ0, hψU, hψP⟩ := hJ E n π (Y \ Z2)
    (fun w hw => hOff w ⟨fun h => (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_left _ h), fun h =>
      (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hcc w⟩))⟩)
    U (fun k hk w hw => ((memU k).1 hk).2 w (Finset.mem_sdiff.1 hw).1)
    ⟨ψ₀, hψ₀, hψ₀0, fun k hk => hY₀ k ((memU k).1 hk).1 fun v hv =>
      ((memU k).1 hk).2 v (Finset.mem_union_left _ hv)⟩

  have hHo : IsOpen (stb n ψ : Set (GF E n)) := (π.cusp ψ hψ).1.level
  have hcore : ∀ w : Pl E, ∃ M : Subgroup (GLw n w), IsOpen (M : Set (GLw n w)) ∧
      M ≤ KGL w n ⊓ (stb n ψ).comap (jw n w false) ⊓ (stb n ψ).comap (jw n w true) ∧
      ∀ k ∈ KGL w n, ∀ x ∈ M, k * x * k⁻¹ ∈ M := fun w =>
    core_exists _ _ (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
      (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.inter (hHo.preimage (hloc w false).1)).inter
        (hHo.preimage (hloc w true).1))
  choose M hMo hMle hMn using hcore
  refine ⟨fun w => if w ∈ Z then M w else KGL w n, fun w => ?_, ψ, hψ, hψ0, fun k hk => ?_⟩
  · by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact ⟨hMo w, fun x hx => (hMle w hx).1.1, hMn w, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl,
        fun k hk x hx => (KGL w n).mul_mem ((KGL w n).mul_mem hk hx) ((KGL w n).inv_mem hk), fun _ => trivial⟩
  have hkN := (mem _ k).1 hk
  have hkK : k ∈ Kf E n := (hK k).1 ((mem _ k).2 fun i hi => by
    have := hkN i hi
    by_cases hz : i.1 ∈ Z
    · simp only [if_pos hz] at this
      exact (hMle _ this).1.1
    · simpa only [if_neg hz] using this)
  have hkv := (memK k).1 hkK
  have hlocal : ∀ v : Pl E, jw n v false (qw n v false k) ∈ Kf E n ∧
      qw n v false (jw n v false (qw n v false k)) = qw n v false k ∧
      ∀ u, u ≠ v → qw n u false (jw n v false (qw n v false k)) = 1 := by
    intro v
    have h1 : qw n v false (jw n v false (qw n v false k)) = qw n v false k := (hloc v false).2.2.1 _
    have h2 : ∀ u, u ≠ v → qw n u false (jw n v false (qw n v false k)) = 1 := fun u hu =>
      pLoc_locGL_of_ne hu _
    refine ⟨(memK _).2 fun u => ?_, h1, h2⟩
    by_cases hu : u = v
    · subst hu
      rw [h1]
      exact hkv u
    · rw [h2 u hu]
      exact one_mem _
  refine fin_reduce (fun v => qw n v false) (Kf E n) (stb n ψ) Y
    (fun k' hk' h' => hψU k' ((memU k').2 ⟨hk', h'⟩)) Y k hkK (fun v hv h => absurd hv h) (fun v hv => ?_)
  by_cases hvZ : v ∈ Z
  · have h0 := hkN (v, false) ⟨(hZ v hvZ).1, by simp⟩
    simp only [if_pos hvZ] at h0
    exact ⟨_, (hMle v h0).1.2, hlocal v⟩
  by_cases hvZ2 : v ∈ Z2
  · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Z, cPl w = v := by
      rcases Finset.mem_union.1 hvZ2 with h | h
      · exact absurd h hvZ
      · exact Finset.mem_image.1 h
    have hsp := (hZ w hw).2
    have h0 := hkN (w, true) ⟨(hZ w hw).1, fun _ => hsp⟩
    simp only [if_pos hw] at h0
    set b := qw n w true k with hb
    set e := jw n w true b with he
    have heH : e ∈ stb n ψ := (hMle w h0).2
    have hew : qw n w true e = b := (hloc w true).2.2.1 b
    have hev : qw n (cPl w) false e = qw n (cPl w) false k := by
      have : qw n (cPl w) false (k * e⁻¹) = 1 := hC w _ (by
        rw [map_mul, map_inv, hew, ← hb, mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this.symm
    have heu : ∀ u, u ≠ cPl w → qw n u false e = 1 := by
      intro u hu
      have hne : cPl u ≠ w := fun h => hu (by rw [← h, hcc])
      have := GlobalTheory.EulerTw.IntRead.map_thF (n := n) u (locGL E n w b)
      refine this.trans ?_
      have h1 : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E u)) (locGL E n w b) = 1 :=
        pLoc_locGL_of_ne hne b
      rw [h1, map_one]
    refine ⟨e, heH, (memK _).2 fun u => ?_, hev, heu⟩
    by_cases hu : u = cPl w
    · subst hu
      rw [hev]
      exact hkv _
    · rw [heu u hu]
      exact one_mem _
  · have hvP : v ∈ Y \ Z2 := Finset.mem_sdiff.2 ⟨hv, hvZ2⟩
    exact ⟨_, GlobalTheory.LGrp.mem_fixed.1 (hψP v hvP) _ (hkv v), hlocal v⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
