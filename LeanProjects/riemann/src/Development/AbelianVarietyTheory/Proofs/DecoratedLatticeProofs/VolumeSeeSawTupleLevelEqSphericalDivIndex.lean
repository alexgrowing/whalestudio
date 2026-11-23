import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

theorem core {D : D7} (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)]
    [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
    (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i))
    (hinj : Function.Injective fun i => (q i).v)
    (hlat : ∀ i, IntIn (q i) S (F i) N) (J : (i : Fin r) → Subgroup (GL (Y i) (k i)))
    (hJ : ∀ i, J i ≤ GlobalTheory.SplitWeil.KO (k i) (Y i)) (hJo : ∀ i, IsOpen (J i : Set (GL (Y i) (k i))))
    (μ : Measure (GfC S)) [μ.IsHaarMeasure] (U U' : Subgroup (GA D S)) (b : GA D S) (hb : b ∈ GfC S) (hU : U ≤ GfC S)
    (hUc : IsCompact (U : Set (GA D S))) (hUo : IsOpen ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)))
    (hK : ∀ κ, InK S N (fun p => ∃ i, (q i).v = p) κ → κ ∈ U)
    (hM : ∀ g ∈ U, Moves S g N N (fun p => ∃ i, (q i).v = p))
    (hU' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (Y i) (k i)), (mt S g).map (q i).pr = (F i).β * x.val * (F i).γ → x ∈ J i) :
    μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) : ℝ) =
      μ.real {g | b * g.1 * b⁻¹ ∈ U} := by
  set φ : GA D S →* ((i : Fin r) → GL (Y i) (k i)) := MonoidHom.pi fun i => locHom (q i) S (F i) with hφ
  have hφi : ∀ g i, φ g i = locHom (q i) S (F i) g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i := by
    intro g
    rw [hU' g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle : U' ≤ U := fun g hg => ((hU'' g).1 hg).1

  have hidx : U'.relIndex U = ∏ i, (J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (k i) (Y i)) J hJ ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (q i) S (F i) N _ ⟨i, rfl⟩ (hlat i) g (hM g hg) _ ((eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S N hN k q Y F hinj hlat x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm

  let cj : GfC S →* GfC S :=
    { toFun := fun g => ⟨b * g.1 * b⁻¹, (GfC S).mul_mem ((GfC S).mul_mem hb g.2) ((GfC S).inv_mem hb)⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [mul_assoc] }
  have hcj : Continuous cj :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hcjb : Function.Bijective cj := by
    refine ⟨fun g h e => ?_, fun g => ⟨⟨b⁻¹ * g.1 * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) g.2) hb⟩, ?_⟩⟩
    · have := congrArg Subtype.val e
      ext1; simpa [cj] using this
    · ext1; simp [cj, mul_assoc]
  set H := (U.subgroupOf (GfC S)).comap cj
  set H' := (U'.subgroupOf (GfC S)).comap cj
  have eH : {g : GfC S | b * g.1 * b⁻¹ ∈ U} = (H : Set (GfC S)) := rfl
  have eH' : {g : GfC S | b * g.1 * b⁻¹ ∈ U'} = (H' : Set (GfC S)) := rfl
  have hHH' : H'.relIndex H = U'.relIndex U := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcjb.2, Subgroup.relIndex_subgroupOf hU]

  have hHc : IsCompact (H : Set (GfC S)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have e : Subtype.val '' (H : Set (GfC S)) = (fun g => b⁻¹ * g * b) '' (U : Set (GA D S)) := by
      ext y; constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨b * g.1 * b⁻¹, hg, by simp [mul_assoc]⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨b⁻¹ * u * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) (hU hu)) hb⟩, ?_, rfl⟩
        change b * (b⁻¹ * u * b) * b⁻¹ ∈ U
        simpa [mul_assoc] using hu
    convert hUc.image ((continuous_const.mul continuous_id).mul continuous_const) using 1
    exact e

  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => locHom (q i) S (F i) g.1) ⁻¹' (J i : Set (GL (Y i) (k i))) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact hUo.inter (isOpen_iInter_of_finite fun i =>
      (hJo i).preimage ((continuous_locHom (q i) S (F i)).comp continuous_subtype_val))
  have hH'o : IsOpen (H' : Set (GfC S)) := hU'o.preimage hcj
  have hH'H : H' ≤ H := fun g hg => hle hg
  rw [eH, eH', ← Nat.cast_prod, ← hidx, ← hHH']
  exact vol_mul_relIndex μ H H' hH'H hHc hH'o

end GlobalTheory.LevIdx

theorem GlobalTheory.LevIdx.vol_level_eq : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  intro D c v t w F hP
  have hQ : (· ∈ w.Q) = fun p => ∃ i, (F.Q i).q.v = p := funext fun p => propext (hP.places p)
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨fun j hj hN μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_, fun hN hTo μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_⟩
  · let d : Fin F.r → ℕ := fun i => (F.Q i).s + 1 - j
    have hd : ∀ i, j + d i = (F.Q i).s + 1 := fun i => by have := hs i; simp only [d]; omega
    rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core (c.V j) (v.N j) hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).X j ⊕ Fin (d i))
      (fun i => (F.Q i).FY j (d i) (hd i)) hP.inj (fun i => (F.Q i).latY j (d i) (hd i))
      (fun i => ((F.Q i).T.lev j (d i) (hd i)).J) (fun i => (F.Q i).le j (d i) (hd i))
      (fun i => ((F.Q i).reg.2.2 j (d i) (hd i)).1) μ U U' b hb hU hUc hUo hK hM ?_
    · have e : ∀ i, (F.Q i).idx j = (((F.Q i).T.lev j (d i) (hd i)).J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
        fun i => (F.Q i).idx_mid j (d i) (hd i)
      simp only [e]
      exact key
    · intro g
      rw [hU' g]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun h x hx => h (d i) (hd i) x hx, fun h d' hd' x hx => ?_⟩
      obtain rfl : d' = d i := by have := hd i; omega
      exact h x hx
  · rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core c.T v.NT hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).Z)
      (fun i => (F.Q i).FT) hP.inj (fun i => (F.Q i).latT)
      (fun i => (F.Q i).T.levTop.J) (fun i => (F.Q i).leT) hTo μ U U' b hb hU hUc hUo hK hM hU'
    have e : ∀ i, (F.Q i).idx D.R.m = ((F.Q i).T.levTop.J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
      fun i => by rw [← hs i]; exact (F.Q i).idx_top
    simp only [e]
    exact key

end
