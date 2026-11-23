import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs
open GlobalTheory.CuspRep.LocEx GlobalTheory.DiscLocEx GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinDiscN

section Top

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_glSub_iff (k : GL (Fin n) (Af E)) :
    k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E) ↔
      ∀ v, GeneralLinearGroup.map (pLoc E v) k ∈ GlobalTheory.LFun.KGL v n := by
  constructor
  · rintro ⟨h1, h2⟩ v
    obtain ⟨U, hU, e⟩ := GlobalTheory.DualDivU.exists_glint (Ov E v)
      (GeneralLinearGroup.map (pLoc E v) k).val (GeneralLinearGroup.map (pLoc E v) k)⁻¹.val
      (congrArg Units.val (mul_inv_cancel _)) (congrArg Units.val (inv_mul_cancel _)) (fun i j => h1 i j v) (fun i j => by
        have := h2 i j v
        rw [← map_inv]
        exact this)
    rwa [← Units.ext e]
  · intro h
    refine ⟨fun i j v => GlobalTheory.DualDivU.entry_mem _ (h v) i j, fun i j v => ?_⟩
    have := GlobalTheory.DualDivU.entry_mem _ (Subgroup.inv_mem _ (h v)) i j
    rw [← map_inv] at this
    exact this

theorem exists_finset_of_isOpen (L : Set (GL (Fin n) (Af E))) (hL : IsOpen L) (h1 : 1 ∈ L) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin n) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) k ∈ GlobalTheory.LFun.KGL v n) →
      (∀ w ∈ T, GeneralLinearGroup.map (pLoc E w) k = 1) → k ∈ L := by
  by_contra h
  push Not at h
  choose k hk1 hk2 hk3 using h
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  have hU : IsCompact (GlobalTheory.GLIntegral.glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring E) : Set (GL (Fin n) (Af E))) :=
    GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E)
  obtain ⟨c, -, hc⟩ := hU.exists_mapClusterPt (f := Filter.atTop) (u := k)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.Eventually.of_forall fun T => (mem_glSub_iff _).2 (hk1 T))))
  have hc1 : c = 1 := GlobalTheory.CuspRep.LocUniq.gl_ext fun v => by
    rw [map_one]
    by_contra hne
    have hs : (GeneralLinearGroup.map (pLoc E v) : GL (Fin n) (Af E) → _) ⁻¹' {1}ᶜ ∈ nhds c :=
      (isOpen_compl_singleton.preimage (continuous_map_pLoc v)).mem_nhds hne
    obtain ⟨T, hT, hT2⟩ := ((hc.frequently hs).and_eventually (Filter.eventually_ge_atTop {v})).exists
    exact hT (hk2 T v (hT2 (Finset.mem_singleton_self v)))
  subst hc1
  obtain ⟨T, hT⟩ := (hc.frequently (hL.mem_nhds h1)).exists
  exact hk3 T hT

end Top

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def TypeW (W : Submodule ℂ (Kinf E N → ℂ)) (φ : Sm E N) : Prop :=
  ∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W

theorem exists_fixed_step {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (W : Submodule ℂ (Kinf E N → ℂ))
    (w : HeightOneSpectrum (𝓞 E)) {K : Subgroup (GL (Fin N) (w.adicCompletion E))}
    (hK : IsCompact (K : Set (GL (Fin N) (w.adicCompletion E))))
    {x : V} (hx0 : x ≠ 0) (hx : x ∈ fixed (locRepD hV.stable w) K)
    (C : Set (GL (Fin N) (Af E))) (hC : ∀ c ∈ C, GeneralLinearGroup.map (pLoc E w) c = 1)
    {ψ : Sm E N} (hψ : ψ ∈ V) (h0 : ψ ≠ 0) (ht : TypeW W ψ) (hc : ∀ c ∈ C, finRep E N c ψ = ψ) :
    ∃ ψ' ∈ V, ψ' ≠ 0 ∧ TypeW W ψ' ∧ (∀ c ∈ C, finRep E N c ψ' = ψ') ∧
      ∀ k ∈ K, finRep E N (locGL E N w k) ψ' = ψ' := by
  let X : Submodule ℂ V :=
    { carrier := {y | TypeW W y.1 ∧ ∀ c ∈ C, finRep E N c y.1 = y.1}
      add_mem' := fun {a b} ha hb => ⟨fun g => W.add_mem (ha.1 g) (hb.1 g), fun c h => by
        rw [Submodule.coe_add, map_add, ha.2 c h, hb.2 c h]⟩
      zero_mem' := ⟨fun g => W.zero_mem, fun c _ => map_zero _⟩
      smul_mem' := fun r a ha => ⟨fun g => W.smul_mem r (ha.1 g), fun c h => by
        rw [Submodule.coe_smul, map_smul, ha.2 c h]⟩ }
  have hX : ∀ g, ∀ v ∈ X, locRepD hV.stable w g v ∈ X := by
    intro g v hv
    refine ⟨fun y => ?_, fun c h => ?_⟩
    · convert hv.1 (y * finGL E N (locGL E N w g)) using 2 with k
      change v.1.1 (y * infGL E N _ * finGL E N _) = v.1.1 (y * finGL E N _ * infGL E N _)
      rw [mul_assoc, mul_assoc, infGL_comm]
    · change finRep E N c (finRep E N (locGL E N w g) v.1) = finRep E N (locGL E N w g) v.1
      rw [← Module.End.mul_apply, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w (hC c h), map_mul,
        Module.End.mul_apply, hv.2 c h]
  have hne : X ⊓ fixed (locRepD hV.stable w) K ≠ ⊥ := fun hb => by
    have h2 := eq_bot_of_fixedD hV w hK hx0 hx X hX hb
    have h3 : (⟨ψ, hψ⟩ : V) ∈ X := ⟨ht, hc⟩
    rw [h2] at h3
    exact h0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h3))
  obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  exact ⟨y.1, y.2, fun e => hy0 (Subtype.ext e), hy1.1, hy1.2, fun k hk =>
    congrArg Subtype.val (mem_fix.1 hy2 k hk)⟩

end Loc

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def locLevel (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E)))
    (w : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin N) (w.adicCompletion E)) := GlobalTheory.LFun.KGL w N ⊓ Kf w

def adLevel (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) :
    Subgroup (GL (Fin N) (Af E)) := ⨅ v, (locLevel Kf v).comap (GeneralLinearGroup.map (pLoc E v))

theorem mem_adLevel {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    {k : GL (Fin N) (Af E)} : k ∈ adLevel Kf ↔ ∀ v, GeneralLinearGroup.map (pLoc E v) k ∈ locLevel Kf v := by
  simp [adLevel, Subgroup.mem_iInf]

theorem isCompact_locLevel {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    (hK : PositivityTheory.Rg.BcB.F.F5.IsLevel Kf) (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (locLevel Kf w : Set (GL (Fin N) (w.adicCompletion E))) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w N).2.inter_right (Subgroup.isClosed_of_isOpen _ (hK.1 w))

theorem isOpen_adLevel {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    (hK : PositivityTheory.Rg.BcB.F.F5.IsLevel Kf) : IsOpen (adLevel Kf : Set (GL (Fin N) (Af E))) := by
  have hB : {w | ¬ GlobalTheory.LFun.KGL w N ≤ Kf w}.Finite := hK.2
  have e : (adLevel Kf : Set (GL (Fin N) (Af E))) =
      (GlobalTheory.GLIntegral.glSub (ι := Fin N) (GlobalTheory.GLIntegral.intSubring E) : Set (GL (Fin N) (Af E))) ∩
        ⋂ w ∈ hB.toFinset, (GeneralLinearGroup.map (pLoc E w) : GL (Fin N) (Af E) → _) ⁻¹' (Kf w : Set _) := by
    ext k
    simp only [SetLike.mem_coe, mem_adLevel, Set.mem_inter_iff, Set.mem_iInter, mem_glSub_iff, Set.mem_preimage,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨fun h => ⟨fun v => (h v).1, fun w _ => (h w).2⟩, fun h v => ⟨h.1 v, ?_⟩⟩
    by_cases hv : GlobalTheory.LFun.KGL v N ≤ Kf v
    · exact hv (h.1 v)
    · exact h.2 v hv
  rw [e]
  exact (GlobalTheory.GLIntegral.isOpen_glSub _ (RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring _))).inter
    (isOpen_biInter_finset fun w _ => (hK.1 w).preimage (continuous_map_pLoc w))

theorem exists_vector {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    (hK : PositivityTheory.Rg.BcB.F.F5.IsLevel Kf) {W : Submodule ℂ (Kinf E N → ℂ)} {V : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) {σ' : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))}
    (hloc : ∀ w, IsLocCompGL V w (σ' w)) (hsph : ∀ w, GlobalTheory.LGrp.IsSpherical (σ' w).ρ (Kf w))
    (hty : PositivityTheory.Rg.BcB.F.F5.HasKType W V) :
    ∃ ψ ∈ V, ψ ≠ 0 ∧ TypeW W ψ ∧ ∀ k ∈ adLevel Kf, finRep E N k ψ = ψ := by
  classical

  have hloc0 : ∀ w, ∃ x : V, x ≠ 0 ∧ x ∈ fixed (locRepD hV.stable w) (locLevel Kf w) := by
    intro w
    obtain ⟨f, hf0, hf1, hf⟩ := hloc w
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (hsph w)
    have hinj : Function.Injective f := by
      have hker : LinearMap.ker f = ⊥ := by
        rcases ((isIrreducible_iff (σ' w).ρ).1 (σ' w).irred).2 (LinearMap.ker f) (fun g u hu => by
          rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]) with h | h
        · exact h
        · exact absurd (LinearMap.ker_eq_top.1 h) hf0
      exact LinearMap.ker_eq_bot.1 hker
    refine ⟨⟨f v, hf1 v⟩, fun e => hv0 (hinj ((congrArg Subtype.val e).trans (map_zero f).symm)), mem_fix.2 fun k hk => ?_⟩
    exact Subtype.ext ((hf k v).symm.trans (congrArg f (mem_fix.1 hv k hk.2)))
  obtain ⟨φ, hφV, hφ0, hφt⟩ := hty

  let L : Subgroup (GL (Fin N) (Af E)) := stab (finRep E N) φ
  have hLo : IsOpen (L : Set (GL (Fin N) (Af E))) := (hV.aut φ hφV).level
  obtain ⟨T, hT⟩ := exists_finset_of_isOpen (L : Set (GL (Fin N) (Af E))) hLo L.one_mem

  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), ∃ ψ ∈ V, ψ ≠ 0 ∧ TypeW W ψ ∧
      (∀ k ∈ L, (∀ u ∈ S, GeneralLinearGroup.map (pLoc E u) k = 1) → finRep E N k ψ = ψ) ∧
      ∀ u ∈ S, ∀ g ∈ locLevel Kf u, finRep E N (locGL E N u g) ψ = ψ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨φ, hφV, hφ0, hφt, fun k hk _ => hk, fun u hu => absurd hu (Finset.notMem_empty u)⟩
    | insert w S hw ih =>
      obtain ⟨ψ, hψV, hψ0, hψt, hψ1, hψ2⟩ := ih
      obtain ⟨x, hx0, hx⟩ := hloc0 w
      obtain ⟨ψ', h1, h2, h3, h4, h5⟩ := exists_fixed_step hV W w (isCompact_locLevel hK w) hx0 hx
        ({k | k ∈ L ∧ ∀ u ∈ insert w S, GeneralLinearGroup.map (pLoc E u) k = 1} ∪
          {c | ∃ u ∈ S, ∃ g ∈ locLevel Kf u, c = locGL E N u g}) (by
          rintro c (⟨-, hc⟩ | ⟨u, hu, g, -, rfl⟩)
          · exact hc w (Finset.mem_insert_self w S)
          · exact pLoc_locGL_of_ne (by rintro rfl; exact hw hu) g) hψV hψ0 hψt (by
          rintro c (⟨hc1, hc2⟩ | ⟨u, hu, g, hg, rfl⟩)
          · exact hψ1 c hc1 fun u hu => hc2 u (Finset.mem_insert_of_mem hu)
          · exact hψ2 u hu g hg)
      refine ⟨ψ', h1, h2, h3, fun k hk hk' => h4 k (Or.inl ⟨hk, hk'⟩), fun u hu g hg => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact h5 g hg
      · exact h4 _ (Or.inr ⟨u, hu, g, hg, rfl⟩)
  obtain ⟨ψ, hψV, hψ0, hψt, hψ1, hψ2⟩ := key T
  refine ⟨ψ, hψV, hψ0, hψt, ?_⟩
  have hall : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S ⊆ T → ∀ k ∈ adLevel Kf,
      (∀ u ∈ T, u ∉ S → GeneralLinearGroup.map (pLoc E u) k = 1) → finRep E N k ψ = ψ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ k hk h1
      have h2 : ∀ u ∈ T, GeneralLinearGroup.map (pLoc E u) k = 1 := fun u hu => h1 u hu (Finset.notMem_empty u)
      exact hψ1 k (hT k (fun v => (mem_adLevel.1 hk v).1) h2) h2
    | insert w S hw ih =>
      intro hS k hk h1
      obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
      have hgl : g ∈ locLevel Kf w := hg ▸ mem_adLevel.1 hk w
      have hk1 : (locGL E N w g)⁻¹ * k ∈ adLevel Kf := mem_adLevel.2 fun v => by
        by_cases hv : v = w
        · subst hv
          rw [hg, map_pLoc_inv_mul]
          exact one_mem _
        · rw [map_mul, map_inv, pLoc_locGL_of_ne hv, inv_one, one_mul]
          exact mem_adLevel.1 hk v
      have h2 := ih (fun u hu => hS (Finset.mem_insert_of_mem hu)) _ hk1 fun u hu huS => by
        by_cases huw : u = w
        · subst huw
          rw [hg, map_pLoc_inv_mul]
        · rw [map_mul, map_inv, pLoc_locGL_of_ne huw, inv_one, one_mul]
          exact h1 u hu fun h => huS ((Finset.mem_insert.1 h).resolve_left huw)
      have h3 : k = locGL E N w g * ((locGL E N w g)⁻¹ * k) := (mul_inv_cancel_left _ _).symm
      rw [h3, map_mul, Module.End.mul_apply, h2]
      exact hψ2 w (hS (Finset.mem_insert_self w S)) g hgl
  exact fun k hk => hall T subset_rfl k hk fun u hu hu' => absurd hu hu'

end Level

section Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

open GlobalTheory.CuspRep.LocUniq in

theorem isoPart_opD {V : Submodule ℂ (Sm E N)} (hs : IsStable V) (w : HeightOneSpectrum (𝓞 E)) {X : Type}
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X) (o : Op E N) {x : V}
    (hx : x ∈ isoPart σ (locRepD hs w)) : opD hs o x ∈ isoPart σ (locRepD hs w) := by
  cases o with
  | fin k => exact isoPart_fin (finPartD hs) w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E N (infGL E N (Unitary.toUnits k)) * rt E N (finGL E N (locGL E N w g))) y.1 =
      (rt E N (finGL E N (locGL E N w g)) * rt E N (infGL E N (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E N w g)) y.1

open GlobalTheory.CuspRep.LocUniq in

theorem isLocCompGL_unique {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) (h' : IsLocCompGL V w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, h1, hf⟩ := h
  obtain ⟨f', h0', h1', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  let F : σ.ρ.IntertwiningMap (locRepD hV.stable w) :=
    ⟨f.codRestrict V h1, fun g => LinearMap.ext fun v => Subtype.ext (hf g v)⟩
  let F' : σ'.ρ.IntertwiningMap (locRepD hV.stable w) :=
    ⟨f'.codRestrict V h1', fun g => LinearMap.ext fun v => Subtype.ext (hf' g v)⟩
  refine equiv_of_isoPart σ.ρ σ'.ρ (locRepD hV.stable w) ?_ F' fun e => h0' (LinearMap.ext fun v => ?_)
  · have hi := Submodule.map_injective_of_injective V.injective_subtype
    rcases hV.irred ((isoPart σ.ρ (locRepD hV.stable w)).map V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, isoPart_opD hV.stable w σ.ρ o hx, rfl⟩) with h2 | h2
    · refine absurd (LinearMap.ext fun v => ?_) h0
      have h3 : isoPart σ.ρ (locRepD hV.stable w) = ⊥ := hi (h2.trans (Submodule.map_bot _).symm)
      have h4 : F.toLinearMap v ∈ isoPart σ.ρ (locRepD hV.stable w) :=
        Submodule.mem_iSup_of_mem F ⟨v, rfl⟩
      rw [h3] at h4
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h4)
    · exact hi (h2.trans (Submodule.map_subtype_top _).symm)
  · have := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap e) v
    exact congrArg Subtype.val this

end Uniq

section Iso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

variable (E N) in

abbrev OpAlg : Subalgebra ℂ (Module.End ℂ (Sm E N)) := Algebra.adjoin ℂ (Set.range (act : Op E N → _))

def opOf (o : Op E N) : OpAlg E N := ⟨act o, Algebra.subset_adjoin ⟨o, rfl⟩⟩

instance : IsScalarTower ℂ (OpAlg E N) (Sm E N) := ⟨fun _ _ _ => rfl⟩

def toR (V : Submodule ℂ (Sm E N)) (hV : IsStable V) : Submodule (OpAlg E N) (Sm E N) where
  carrier := V
  add_mem' := V.add_mem
  zero_mem' := V.zero_mem
  smul_mem' := by
    rintro ⟨r, hr⟩ x hx
    change r x ∈ V
    induction hr using Algebra.adjoin_induction generalizing x with
    | mem y hy =>
      obtain ⟨o, rfl⟩ := hy
      exact hV o x hx
    | algebraMap c => exact V.smul_mem c hx
    | add a b _ _ ha hb => exact V.add_mem (ha hx) (hb hx)
    | mul a b _ _ ha hb => exact ha (hb hx)

theorem isSimple_toR {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    IsSimpleModule (OpAlg E N) (toR V hV.stable) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨fun e => hV.ne_bot ?_, fun b hb => ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have : x ∈ toR V hV.stable := hx
    rw [e] at this
    exact this
  · have hle : b.restrictScalars ℂ ≤ V := fun x hx => hb.le hx
    rcases hV.irred _ hle (fun o x hx => b.smul_mem (opOf o) hx) with h | h
    · exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).1 h
    · refine absurd ?_ hb.ne
      refine le_antisymm hb.le fun x hx => ?_
      have : x ∈ V := hx
      rw [← h] at this
      exact this

theorem linearIndependent_of_not_iso {ι : Type*} (V : ι → Submodule ℂ (Sm E N)) (hV : ∀ i, IsDiscrete (V i))
    (hne : ∀ i j, Nonempty (toR (V i) (hV i).stable ≃ₗ[OpAlg E N] toR (V j) (hV j).stable) → i = j)
    (ψ : ι → Sm E N) (hψ : ∀ i, ψ i ∈ V i) (h0 : ∀ i, ψ i ≠ 0) : LinearIndependent ℂ ψ := by
  classical
  have hs : ∀ i, IsSimpleModule (OpAlg E N) (toR (V i) (hV i).stable) := fun i => isSimple_toR (hV i)
  let c : ι → Submodule (OpAlg E N) (Sm E N) := fun i => isotypicComponent (OpAlg E N) (Sm E N) (toR (V i) (hV i).stable)
  have hcm : ∀ i, c i ∈ isotypicComponents (OpAlg E N) (Sm E N) := fun i => ⟨_, hs i, rfl⟩
  have hle : ∀ i, toR (V i) (hV i).stable ≤ c i := fun i => Submodule.le_isotypicComponent _
  have hinj : ∀ i j, c i = c j → i = j := fun i j e => by
    have h1 : toR (V i) (hV i).stable ≤ c j := e ▸ hle i
    obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (OpAlg E N) (Sm E N) (toR (V j) (hV j).stable)) _ h1
    exact hne i j ⟨e'⟩
  have hind := sSupIndep_isotypicComponents (OpAlg E N) (Sm E N)
  have hC : iSupIndep V := by
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : x ∈ c i := hle i hx
    have h2 : (⨆ (j) (_ : j ≠ i), V j) ≤
        (sSup (isotypicComponents (OpAlg E N) (Sm E N) \ {c i})).restrictScalars ℂ := by
      refine iSup₂_le fun j hj y hy => ?_
      have hm : c j ∈ isotypicComponents (OpAlg E N) (Sm E N) \ {c i} := ⟨hcm j, fun e => hj (hinj _ _ e)⟩
      exact le_sSup hm (hle j hy)
    exact Submodule.disjoint_def.1 (hind (hcm i)) x h1 (h2 hx')
  exact hC.linearIndependent V hψ h0

end Iso

section Main

open GlobalTheory.CompanionTheory.AdmDiscFin

theorem equiv_val_smul {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p q : Submodule R M} (e : p ≃ₗ[R] q)
    (r : R) (x y : p) (h : y.1 = r • x.1) : (e y).1 = r • (e x).1 := by
  have : y = r • x := Subtype.ext h
  rw [this, map_smul]
  rfl

theorem isLocCompGL_of_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V V' : Submodule ℂ (Sm E N)} (hV : IsStable V) (hV' : IsStable V')
    (e : toR V hV ≃ₗ[OpAlg E N] toR V' hV') (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) : IsLocCompGL V' w σ := by
  obtain ⟨f, h0, h1, hf⟩ := h
  let F : σ.V →ₗ[ℂ] Sm E N :=
    { toFun := fun v => (e ⟨f v, h1 v⟩).1
      map_add' := fun a b => by
        have : (⟨f (a + b), h1 (a + b)⟩ : toR V hV) = ⟨f a, h1 a⟩ + ⟨f b, h1 b⟩ := Subtype.ext (map_add f a b)
        rw [this, map_add]
        rfl
      map_smul' := fun c a => by
        exact equiv_val_smul e (algebraMap ℂ (OpAlg E N) c) ⟨f a, h1 a⟩ ⟨f (c • a), h1 _⟩ (map_smul f c a) }
  refine ⟨F, fun hF => h0 (LinearMap.ext fun v => ?_), fun v => (e ⟨f v, h1 v⟩).2, fun g v => ?_⟩
  · have h2 : e ⟨f v, h1 v⟩ = 0 := Subtype.ext (LinearMap.congr_fun hF v)
    exact congrArg Subtype.val ((map_eq_zero_iff e e.injective).1 h2)
  · exact equiv_val_smul e (opOf (.fin (locGL E N w g))) ⟨f v, h1 v⟩ ⟨f (σ.ρ g v), h1 _⟩ (hf g v)

theorem finDiscN : PositivityTheory.Rg.BcB.F.F5.FinDiscN := by
  intro E _ _ _ N Kf W m hK hW
  classical
  haveI := hW
  let Y : Submodule ℂ (Kinf E N → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E N, TypeW W φ ∧ ∃ g : GA E N, f = fun k => φ.1 (g * infGL E N (Unitary.toUnits k))}
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, g, rfl⟩
    exact hφ g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφ, g * infGL E N (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, g, rfl⟩ := hf
      exact continuous_slice φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  let c : (E →+* ℂ) → ℂ → ℂ := fun τ u => ((m τ).map (u + ·)).prod
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N (adLevel Kf) (isOpen_adLevel hK) (Module.Dual ℂ Y)
    (dualRep Y hYl) (isContRep_dualRep Y hYl hYc) c
  let Sys := ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.LocGL.IrrGL (w.adicCompletion E)
  let cls : (∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))) → Sys := fun σ' w =>
    GlobalTheory.LocGL.IrrGL.of (σ' w).ρ (σ' w).smooth (σ' w).irred
  let Good : Submodule ℂ (Sm E N) → (∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))) → Prop :=
    fun V σ' => IsDiscrete V ∧ (∀ w, IsLocCompGL V w (σ' w)) ∧ (∀ τ, HasInfCharGL V τ (m τ)) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (σ' w).ρ (Kf w)) ∧ PositivityTheory.Rg.BcB.F.F5.HasKType W V
  let S : Set Sys := {s | ∃ V σ', Good V σ' ∧ cls σ' = s}
  have hS : ∀ s : S, ∃ V σ', Good V σ' ∧ cls σ' = s.1 := fun s => s.2
  choose Vs σs hg hcl using hS
  have hvec := fun s : S => exists_vector hK (hg s).1 (hg s).2.1 (hg s).2.2.2.1 (hg s).2.2.2.2
  choose ψ hψV hψ0 hψt hψl using hvec
  have hli : LinearIndependent ℂ ψ := by
    refine linearIndependent_of_not_iso Vs (fun s => (hg s).1) (fun s t ⟨e⟩ => ?_) ψ hψV hψ0
    refine Subtype.ext ((hcl s).symm.trans (Eq.trans (funext fun w => ?_) (hcl t)))
    obtain ⟨e'⟩ := isLocCompGL_unique (hg t).1 w (σs s w) (σs t w)
      (isLocCompGL_of_equiv _ _ e w _ ((hg s).2.1 w)) ((hg t).2.1 w)
    exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 ⟨e'⟩
  let F := Submodule.span ℂ (AutFinGL.forms (adLevel Kf) (dualRep Y hYl) c)
  have hψF : ∀ s, ψ s ∈ F := fun s => Submodule.subset_span
    ⟨(hg s).1.aut _ (hψV s), hψl s, fun g => le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨ψ s, hψt s, g, rfl⟩),
      fun τ u => ((hg s).2.2.1 τ).2 u _ (hψV s)⟩
  have hli' : LinearIndependent ℂ (fun s => (⟨ψ s, hψF s⟩ : F)) :=
    LinearIndependent.of_comp F.subtype hli
  haveI : Finite S := hli'.finite_of_isNoetherian
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨k, fun j => σs (e.symm j), fun V σ' h1 h2 h3 h4 h5 => ?_⟩
  have hs : cls σ' ∈ S := ⟨V, σ', ⟨h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨e ⟨_, hs⟩, fun w => ?_⟩
  have h3 : cls (σs (e.symm (e ⟨_, hs⟩))) = cls σ' := by
    rw [Equiv.symm_apply_apply]
    exact hcl _
  exact congrFun h3 w

end Main

end GlobalTheory.CompanionTheory.FinDiscN

end
