import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem comm_of_cLoc {w : Plc E} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private def CJ {w : Plc E} (J : Subgroup (GLw n w)) : Subgroup (UA E n) := locU n w ⊓ J.comap (cLoc w)

private theorem isCompact_CJ {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) : IsCompact (CJ J : Set (UA E n)) := by
  have hc : Continuous fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n) :=
    continuous_subtype_val.comp (locE hw).symm.continuous
  have he : (CJ J : Set (UA E n)) = (fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n)) '' (J : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨cLoc w g, h2, ?_⟩
      have : (locE hw).symm (cLoc w g) = ⟨g, h1⟩ := by
        apply (locE hw).injective
        rw [ContinuousMulEquiv.apply_symm_apply, locE_apply]
      simp [this]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((locE hw).symm x).2, ?_⟩
      show cLoc w (locF hw x).1 ∈ J
      rw [cLoc_locF]
      exact hx
  rw [he]
  exact hJ.image hc

private theorem finite_index {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ N : Subgroup (CJ J : Subgroup (UA E n)), N.FiniteIndex ∧ ∀ k ∈ N, RU E n (k : UA E n) φ = φ := by
  haveI : CompactSpace (CJ J : Subgroup (UA E n)) := isCompact_iff_compactSpace.1 (isCompact_CJ hw J hJ)
  let N : Subgroup (CJ J : Subgroup (UA E n)) :=
    { carrier := {k | RU E n (k : UA E n) φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show RU E n ((a * b : CJ J) : UA E n) φ = φ
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        show RU E n ((a⁻¹ : CJ J) : UA E n) φ = φ
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hle : (CJ J : Subgroup (UA E n)) ≤ finU E n := fun k hk => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1
  have hop : IsOpen (N : Set (CJ J : Subgroup (UA E n))) :=
    hφ.level.preimage (f := fun k : (CJ J : Subgroup (UA E n)) => (⟨k.1, hle k.2⟩ : finU E n))
      (Continuous.subtype_mk continuous_subtype_val _)
  haveI := Subgroup.quotient_finite_of_isOpen N hop
  exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun k hk => hk⟩

private theorem step_core (π : AutSub E n) (W : Wt E n) (f : algForms W) {w : Plc E} (hw : IsSplitAt w)
    (hf : f ∈ π.finPart W) (r : UA E n →₀ ℂ) (hr : ∀ g ∈ r.support, g ∈ locU n w) :
    ∃ f' ∈ π.finPart W, (∀ v, f'.1 v = r.sum fun g a => a • RU E n g (f.1 v)) ∧
      ∀ u : finU E n, cLoc w u.1 = 1 → algRep W u f = f → algRep W u f' = f' := by
  have hle : locU n w ≤ finU E n := inf_le_left
  let F : r.support → algForms W := fun g => r g.1 • algRep W ⟨g.1, hle (hr _ g.2)⟩ f
  have hval : ∀ v, (∑ g : r.support, F g).1 v = r.sum fun g a => a • RU E n g (f.1 v) := by
    intro v
    rw [Finsupp.sum, ← Finset.sum_coe_sort r.support, Submodule.coe_sum, LinearMap.sum_apply]
    rfl
  refine ⟨∑ g : r.support, F g, AutSub.mem_finPart.2 fun v => ?_, hval, fun u hu hfix => ?_⟩
  · rw [hval]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.isAut.stable _ _ (AutSub.mem_finPart.1 hf v))
  · rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hcm : u * (⟨g.1, hle (hr _ g.2)⟩ : finU E n) = ⟨g.1, hle (hr _ g.2)⟩ * u :=
      Subtype.ext (comm_of_cLoc hw u.1 hu g.1 (hr _ g.2)).symm
    simp only [F]
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, hcm, map_mul, Module.End.mul_apply, hfix]

private theorem mem_lev_off (hC : LocComm) {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {w : Plc E}
    (hw : IsSplitAt w) (hwS : w ∈ S) (hcj : cj w ∉ S) {J : Subgroup (GLw n w)} (u : finU E n)
    (hu : ofU u ∈ lev S (Function.update Kw w J)) (x : GLw n w) (u' : finU E n) (hx : u = locF hw x * u')
    (h1 : cLoc w u'.1 = 1) : ofU u' ∈ lev S Kw := by
  obtain ⟨-, hap, -, -, hcc, -⟩ := hC E n w hw
  obtain ⟨-, hu2, hu3⟩ := mem_lev.1 hu
  have hsame : ∀ t : Plc E, GlobalTheory.Cong.Apart t w → comp t (ofU u') = comp t (ofU u) := by
    intro t ht
    have h2 : comp t (loc hw x) = 1 := comp_loc_of_apart hw ht x
    rw [hx, map_mul, map_mul]
    have h3 : comp t (ofU (locF hw x)) = 1 := h2
    rw [h3, one_mul]
  refine mem_lev.2 ⟨by rw [sim_ofU]; exact one_mem _, fun t ht => ?_, fun t ht hct => ?_⟩
  · by_cases htw : t = w
    · subst htw
      rw [comp_ofU, h1]
      exact one_mem _
    · have hne : t ≠ cj w := fun h => hcj (h ▸ ht)
      rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
      have := hu2 t ht
      rwa [Function.update_of_ne htw] at this
  · have htw : t ≠ w := fun h => ht (h ▸ hwS)
    have hne : t ≠ cj w := fun h => hct (by rw [h, hcc]; exact hwS)
    rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
    exact hu3 t ht hct

end UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

open UpperTheory.Gal.CertificateRingHomMap.LevelShrinking in
theorem UpperTheory.Gal.CertificateRingHomMap.pStepAt_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.StepAt := by
  intro hA hC _ E _ _ _ n π W f hf hf0 S Kw w hw hwS hcj hfix J χ hJc hT
  obtain ⟨φ, hφπ, hφ0, hφ⟩ := hT
  let χ' : (CJ J : Subgroup (UA E n)) →* ℂˣ :=
    χ.comp (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J fun k => (Subgroup.mem_inf.1 k.2).2)
  have hf1 : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
  obtain ⟨r, hrH, ⟨v₀, hv₀⟩, hrχ⟩ := hA (UA E n) (UA E n → ℂ) W.Sp (RU E n) π.V π.isAut.stable π.isAut.irred
    (locU n w) (CJ J) inf_le_left
    (fun g => ⟨(locF hw (cLoc w g)).1, locF_mem hw _, (locF hw (cLoc w g)).1⁻¹ * g,
      fun y hy => (comm_of_cLoc hw _ (by simp) y hy).symm, by simp⟩)
    (fun ψ hψ => finite_index hw J hJc ψ (π.isAut.aut ψ hψ)) χ'
    ⟨φ, hφπ, hφ0, fun k => hφ k.1 (Subgroup.mem_inf.1 k.2).1 (Subgroup.mem_inf.1 k.2).2⟩
    f.1 hf1 (AutSub.mem_finPart.1 hf)
  obtain ⟨f', hf', hval, hoff⟩ := step_core π W f hw hf r hrH
  refine ⟨f', hf', fun h => hv₀ ?_, fun u hu h => ?_⟩
  · rw [← hval, h]
    rfl
  · set x := cLoc w u.1 with hxdef
    set a := locF hw x with hadef
    have hax : cLoc w a.1 = x := cLoc_locF hw x
    have h1 : cLoc w ((a⁻¹ * u : finU E n) : UA E n) = 1 := by
      have : ((a⁻¹ * u : finU E n) : UA E n) = a.1⁻¹ * u.1 := rfl
      rw [this, map_mul, map_inv, hax, ← hxdef, inv_mul_cancel]
    have hu' : u = a * (a⁻¹ * u) := by group
    have hfix' : algRep W (a⁻¹ * u) f = f :=
      hfix _ (mem_lev_off hC hw hwS hcj u hu x _ hu' h1)
    have hstep := hoff _ h1 hfix'
    have hak : a.1 ∈ (CJ J : Subgroup (UA E n)) :=
      Subgroup.mem_inf.2 ⟨locF_mem hw x, by show cLoc w a.1 ∈ J; rw [hax]; exact h⟩
    have hχ : ((χ' ⟨a.1, hak⟩ : ℂˣ) : ℂ) = ((χ ⟨x, h⟩ : ℂˣ) : ℂ) := by
      have : (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J
          fun k => (Subgroup.mem_inf.1 k.2).2) ⟨a.1, hak⟩ = ⟨x, h⟩ := Subtype.ext hax
      simp only [χ', MonoidHom.comp_apply, this]
    have e : algRep W u f' = algRep W a f' := by
      conv_lhs => rw [hu', map_mul, Module.End.mul_apply, hstep]
    rw [e]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h2 := hrχ ⟨a.1, hak⟩ v
    rw [← hval, hχ] at h2
    exact h2

end
