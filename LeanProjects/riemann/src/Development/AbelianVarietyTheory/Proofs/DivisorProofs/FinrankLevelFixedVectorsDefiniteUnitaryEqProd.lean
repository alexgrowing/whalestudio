import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.DimFac

open GlobalTheory.DefU GlobalTheory.DefU.LocRet GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ua_ext {g h : UA E n} (h1 : cInf g = cInf h) (h2 : ∀ u : Pl E, cLoc u g = cLoc u h) : g = h :=
  Subtype.ext (ga_ext' h1 h2)

variable (n) in

def proj (S : Set (Pl E)) : InfinitePlace E ⊕ S → UA E n →* UA E n :=
  Sum.elim (fun v => (embU n v.embedding).subtype.comp (embRet v.embedding)) fun w => ret0 w.1 n

def lev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (UA E n) :=
  (globLev S K').map (finU E n).subtype

theorem mem_lev {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {g : UA E n} :
    g ∈ lev S K' ↔ cInf g = 1 ∧ ∀ w ∈ S, (⟨cLoc w g, cLoc_mem_UL w g⟩ : UL n w) ∈ K' w := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (mem_globLev S K' k).1 hk⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h1⟩, (mem_globLev S K' _).2 h2, rfl⟩

variable {S : Set (Pl E)}

theorem cInf_inl (v : InfinitePlace E) (g : UA E n) : cInf (proj n S (.inl v) g) = cutGL v (cInf g) := by
  have := cInf_embRet v.embedding g
  rwa [InfinitePlace.mk_embedding] at this

theorem cLoc_inl (v : InfinitePlace E) (g : UA E n) (u : Pl E) : cLoc u (proj n S (.inl v) g) = 1 := by
  have h : GeneralLinearGroup.map (pFin E) (proj n S (.inl v) g).1 = 1 := (embRet v.embedding g).2.1
  have e : cLoc u (proj n S (.inl v) g) =
      GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) (proj n S (.inl v) g).1) := Units.ext rfl
  rw [e, h, map_one]

theorem cInf_inr (w : S) (g : UA E n) : cInf (proj n S (.inr w) g) = 1 := infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one g

theorem cLoc_inr_eq (w : S) (g : UA E n) {u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.1.under (𝓞 (maximalRealSubfield E))) :
    cLoc u (proj n S (.inr w) g) = cLoc u g := localProj_unitaryAdelicLocalRetractionEnd_of_under_eq h g

theorem cLoc_inr_ne (w : S) (g : UA E n) {u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) ≠ w.1.under (𝓞 (maximalRealSubfield E))) :
    cLoc u (proj n S (.inr w) g) = 1 := localProj_unitaryAdelicLocalRetractionEnd_of_under_ne h g

theorem under_ne (hS : IsSection S) {w w' : S} (h : w ≠ w') :
    w.1.under (𝓞 (maximalRealSubfield E)) ≠ w'.1.under (𝓞 (maximalRealSubfield E)) := fun e =>
  h (Subtype.ext ((hS w'.1).unique ⟨w.2, e⟩ ⟨w'.2, rfl⟩))

theorem proj_proj (i : InfinitePlace E ⊕ S) (g : UA E n) : proj n S i (proj n S i g) = proj n S i g := by
  rcases i with v | w
  · exact congrArg Subtype.val (embRet_apply v.embedding (embRet v.embedding g))
  · exact congrArg Subtype.val (ret_of_mem (ret w.1 n g))

theorem proj_proj_ne (hS : IsSection S) (i j : InfinitePlace E ⊕ S) (h : i ≠ j) (g : UA E n) :
    proj n S i (proj n S j g) = 1 := by
  rcases i with v | w
  · refine ua_ext ?_ fun u => by rw [cLoc_inl, map_one]
    rw [cInf_inl, map_one]
    rcases j with v' | w'
    · rw [cInf_inl]
      refine gl_ext_evGL fun u => ?_
      rw [map_one]
      by_cases hu : u = v
      · subst hu
        rw [evGL_cutGL_self, evGL_cutGL_of_ne fun e => h (by rw [e])]
      · exact evGL_cutGL_of_ne hu _
    · rw [cInf_inr, map_one]
  · refine ua_ext (by rw [cInf_inr, map_one]) fun u => ?_
    rw [map_one]
    by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.1.under (𝓞 (maximalRealSubfield E))
    · rw [cLoc_inr_eq w _ hu]
      rcases j with v' | w'
      · exact cLoc_inl _ _ _
      · exact cLoc_inr_ne w' g (hu ▸ under_ne hS fun e => h (by rw [e]))
    · exact cLoc_inr_ne w _ hu

theorem commute_proj (i : InfinitePlace E ⊕ S) (g y : UA E n) : Commute ((proj n S i g)⁻¹ * g) (proj n S i y) := by
  rcases i with v | w
  · exact commute_embRet v.embedding g (embRet v.embedding y)
  · exact commute_ret g (ret w.1 n y)

variable {K' : ∀ w : Pl E, Subgroup (UL n w)}

theorem inl_mem_lev (v : InfinitePlace E) (g : UA E n) : proj n S (.inl v) g ∈ lev S K' ↔ evGL v (cInf g) = 1 := by
  rw [mem_lev, cInf_inl]
  refine ⟨fun h => ?_, fun h => ⟨gl_ext_evGL fun u => ?_, fun w _ => ?_⟩⟩
  · rw [← evGL_cutGL_self, h.1, map_one]
  · rw [map_one]
    by_cases hu : u = v
    · subst hu
      rw [evGL_cutGL_self, h]
    · exact evGL_cutGL_of_ne hu _
  · convert (K' w).one_mem using 1
    exact Subtype.ext (cLoc_inl v g w)

theorem inr_mem_lev (hS : IsSection S) (w : S) (g : UA E n) :
    proj n S (.inr w) g ∈ lev S K' ↔ (⟨cLoc w.1 g, cLoc_mem_UL w.1 g⟩ : UL n w.1) ∈ K' w.1 := by
  rw [mem_lev]
  refine ⟨fun h => ?_, fun h => ⟨cInf_inr w g, fun w' hw' => ?_⟩⟩
  · convert h.2 w.1 w.2 using 1
    exact Subtype.ext (cLoc_inr_eq w g rfl).symm
  · by_cases e : (⟨w', hw'⟩ : S) = w
    · subst e
      convert h using 1
      exact Subtype.ext (cLoc_inr_eq _ g rfl)
    · convert (K' w').one_mem using 1
      exact Subtype.ext (cLoc_inr_ne w g (under_ne hS e))

theorem mem_lev_iff_proj (hS : IsSection S) (g : UA E n) : g ∈ lev S K' ↔ ∀ i, proj n S i g ∈ lev S K' := by
  rw [Sum.forall]
  simp only [inl_mem_lev, inr_mem_lev hS]
  rw [mem_lev]
  refine and_congr ⟨fun h v => by rw [h, map_one], fun h => gl_ext_evGL fun v => by rw [h, map_one]⟩ (by simp)

theorem eventually_cLoc_mem (g : UA E n) : ∀ᶠ w : Pl E in cofinite, cLoc w g ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ g : UA E n, ∀ᶠ w : Pl E in cofinite, ∀ i j, Valued.v ((cLoc w g).val i j) ≤ 1 := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (pFin E (g.1.val i j)).2
  filter_upwards [h g, h g⁻¹] with w a b
  exact (mem_KGL_iff_val w _).2 ⟨a, by rw [← map_inv]; exact b⟩

theorem finite_proj_notMem (hS : IsSection S) (hK : ∀ᶠ w in cofinite, K' w = KL n w) (g : UA E n) :
    {i | proj n S i g ∉ lev S K'}.Finite := by
  refine Set.finite_preimage_inl_and_inr.1 ⟨Set.toFinite _, ?_⟩
  have h := (Filter.eventually_cofinite.1 (hK.and (eventually_cLoc_mem g))).preimage
    (Subtype.val_injective (p := (· ∈ S))).injOn
  refine h.subset fun w hw h' => hw ((inr_mem_lev hS w g).2 ?_)
  rw [h'.1]
  exact h'.2

theorem exists_finset_subset (hU : Unr E) (hn : 1 ≤ n) (hS : IsSection S)
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (O : Set (finU E n)) (hO : IsOpen O)
    (h1 : 1 ∈ O) : ∃ T : Finset S, ∀ k ∈ globLev S K', (∀ w ∈ T, proj n S (.inr w) k = 1) → k ∈ O := by
  obtain ⟨-, hc, -, hle, -⟩ := globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨T, hT⟩ := (hc.diff hO).elim_finite_subfamily_closed
    (fun w : S => {k : finU E n | proj n S (.inr w) k = 1})
    (fun w => isClosed_eq ((continuous_subtype_val.comp (continuous_ret (w := w.1))).comp continuous_subtype_val)
      continuous_const) (by
      refine Set.eq_empty_of_forall_notMem fun k ⟨hk, hk'⟩ => hk.2 ?_
      have : k = 1 := by
        refine Subtype.ext (ua_ext (k.2.trans (map_one _).symm) fun u => ?_)
        obtain ⟨w, ⟨hw, hwu⟩, -⟩ := hS u
        have h2 : proj n S (.inr ⟨w, hw⟩) k = 1 := Set.mem_iInter.1 hk' ⟨w, hw⟩
        rw [← cLoc_inr_eq ⟨w, hw⟩ k.1 hwu.symm, h2]
        rfl
      rwa [this])
  refine ⟨T, fun k hk h => by_contra fun hk' => ?_⟩
  exact Set.eq_empty_iff_forall_notMem.1 hT k ⟨⟨hle hk, hk'⟩, Set.mem_iInter₂.2 h⟩

theorem hasComp_inl (π : AutSub E n) (v : InfinitePlace E) (lam : DomWeight n) (h : HasWeightAt π.V v.embedding lam) :
    HasComp π.rep (proj n S (.inl v)) (lev S K') (Module.finrank ℂ (nablaSq ℂ n lam)) := by
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  let σ := (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have heq : σ = (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb v.embedding (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible σ := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  have htop : fixed σ ⊥ = ⊤ := Submodule.eq_top_iff'.2 fun x => mem_fix.2 fun g hg => by
    rw [Subgroup.mem_bot.1 hg, map_one, Module.End.one_apply]
  have := hasComp_of_surjective π.rep (proj n S (.inl v)) (lev S K') (embRet v.embedding)
    (fun x => ⟨x, embRet_apply _ x⟩) (fun g => embRet_apply _ (embRet v.embedding g)) σ hσ ⊥
    (by rw [htop]; exact top_ne_bot) (f.codRestrict π.V hfm)
    (fun h => hf0 (LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun h x)))
    (fun g x => Subtype.ext (hf (embRet v.embedding g) x)) ⊥
    (fun g hg => Subgroup.mem_bot.2 (Subtype.ext (ua_ext
      ((cInf_inl (S := S) v g).trans (by rw [(mem_lev.1 hg).1, map_one]; exact (map_one _).symm))
      fun u => (cLoc_inl (S := S) v g u).trans (map_one _).symm)))
    (fun k hk => ⟨1, one_mem _, by rw [Subgroup.mem_bot.1 hk, map_one]⟩)
  rwa [htop, finrank_top] at this

theorem hasComp_inr (hU : Unr E) (hn : 1 ≤ n) (hS : IsSection S) (π : AutSub E n) (w : S) (σ : SmIrr (UL n w.1))
    (h : IsCompU π.V w.1 σ) :
    HasComp π.rep (proj n S (.inr w)) (lev S K') (Module.finrank ℂ (fixed σ.ρ (K' w.1))) := by
  obtain ⟨⟨σ₀, h₀, hadm⟩, huniq⟩ := GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn π.V π.isAut w.1
  obtain ⟨T⟩ := huniq σ σ₀ h h₀
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.BCT.LocCompU.exists_equiv hU n w.1
  have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
  have hq : ∀ g, p (ret w.1 n g) = ⟨cLoc w.1 g, cLoc_mem_UL w.1 g⟩ := fun g =>
    Subtype.ext ((hp _).trans (cLoc_inr_eq w g rfl))
  haveI := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).1
  obtain ⟨x, hx⟩ := exists_ne (0 : σ.V)
  let U : Subgroup (UL n w.1) :=
    { carrier := {g | σ.ρ g x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : σ.ρ a x = x) (hb : σ.ρ b x = x) => show σ.ρ (a * b) x = x by rw [← rep_mul, hb, ha]
      inv_mem' := fun {a} (ha : σ.ρ a x = x) => show σ.ρ a⁻¹ x = x by
        conv_lhs => rw [← ha, rep_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  haveI := hadm U (σ.smooth x)
  haveI : FiniteDimensional ℂ (fixed σ.ρ U) := by
    refine FiniteDimensional.of_injective (T.toLinearEquiv.toLinearMap.restrict (q := fixed σ₀.ρ U) fun y hy =>
      mem_fix.2 fun g hg => ?_) fun a b hab => Subtype.ext (T.toLinearEquiv.injective (congrArg Subtype.val hab))
    have := LinearMap.congr_fun (T.isIntertwining' g) y
    simp only [LinearMap.comp_apply] at this
    rw [← this, mem_fix.1 hy g hg]
  refine hasComp_of_surjective π.rep (proj n S (.inr w)) (lev S K') (p.comp (ret w.1 n))
    (fun k => ⟨(e.symm k : locU n w.1), by rw [MonoidHom.comp_apply, ret_of_mem, hpe, e.apply_symm_apply]⟩)
    (fun g => congrArg p (ret_of_mem (ret w.1 n g))) σ.ρ σ.irred U
    ((Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun g hg => hg, hx⟩) (f.codRestrict π.V hfm)
    (fun h => hf0 (LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun h x)))
    (fun g x => Subtype.ext (hf (ret w.1 n g) x)) (K' w.1) (fun g hg => ?_) fun k hk => ?_
  · rw [MonoidHom.comp_apply, hq]
    exact (mem_lev.1 hg).2 w.1 w.2
  · have h1 : p (ret w.1 n (e.symm k : locU n w.1)) = k := by rw [ret_of_mem, hpe, e.apply_symm_apply]
    refine ⟨proj n S (.inr w) (e.symm k : locU n w.1), (inr_mem_lev hS w _).2 (by rwa [← hq, h1]), ?_⟩
    exact (congrArg p (ret_of_mem (ret w.1 n _))).trans h1

theorem finrank_inf_fixed_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ lam : InfinitePlace E → DomWeight n, (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = dimW lam * ∏ᶠ w ∈ S, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) := by
  intro E _ _ _ hU n hn π hπ S hS lam hlam K' hK σ hσ
  let π' : AutSub E n := ⟨π, hπ⟩
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  obtain ⟨T₀, hT₀⟩ := exists_finset_subset hU hn hS hK _ (hπ.aut φ hφ).level (by simp)
  have hbad : {w : S | Module.finrank ℂ (fixed (σ w.1).ρ (K' w.1)) ≠ 1}.Finite := by
    have h := (Filter.eventually_cofinite.1 (hK.2.and (GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all E hU n hn π hπ σ hσ))).preimage
      (Subtype.val_injective (p := (· ∈ S))).injOn
    refine h.subset fun w hw h' => hw ?_
    rw [h'.1]
    exact h'.2
  let T : Finset S := T₀ ∪ hbad.toFinset
  have hT : ∀ w : S, w ∉ T → Module.finrank ℂ (fixed (σ w.1).ρ (K' w.1)) = 1 := fun w hw => by
    by_contra h
    exact hw (Finset.mem_union_right _ (hbad.mem_toFinset.2 h))
  have key := finrank_fixed_eq_prod (e := proj n S) (L := lev S K') proj_proj (proj_proj_ne hS) commute_proj
    (mem_lev_iff_proj hS) (finite_proj_notMem hS hK.2) (Finset.univ.disjSum T) π π'.rep π'.isIrreducible_rep
    (Sum.elim (fun v => Module.finrank ℂ (nablaSq ℂ n (lam v))) fun w => Module.finrank ℂ (fixed (σ w.1).ρ (K' w.1)))
    (by
      rintro (v | w)
      · exact hasComp_inl π' v _ (hlam v)
      · exact hasComp_inr hU hn hS π' w _ (hσ w.1))
    (by
      rintro (v | w) h
      · simp at h
      · exact hT w (by simpa using h))
    ⟨⟨φ, hφ⟩, fun h => hφ0 (congrArg Subtype.val h), by
      rintro _ ⟨k, hk, rfl⟩ h
      exact Subtype.ext (hT₀ k hk fun w hw => h _ (Finset.inr_mem_disjSum.2 (Finset.mem_union_left _ hw)))⟩
  have hmap : π ⊓ fixed (RF E n) (globLev S K') = (fixed π'.rep (lev S K')).map π.subtype := by
    ext ψ
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨ψ, h1⟩, mem_fix.2 ?_, rfl⟩
      rintro _ ⟨k, hk, rfl⟩
      exact Subtype.ext (mem_fix.1 h2 k hk)
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_fix.2 fun k hk => congrArg Subtype.val (mem_fix.1 hy k ⟨k, hk, rfl⟩)⟩
  rw [hmap, Submodule.finrank_map_subtype_eq, key, Finset.prod_disjSum, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod,
    ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_mulSupport_subset (s := T) _ fun w hw => by
      by_contra h
      exact hw (by simp [hT w h])]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_one, LinearMap.trace_one]
  rfl

end GlobalTheory.BCT.DimFac
