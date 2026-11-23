import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WithZeroLeOneEqExp

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  ValuativeRel

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem denF (x : D.host.E) : ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (d : D.host.F) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have : (b : 𝓞 D.host.E) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hbi : IsIntegral ℤ (b : D.host.E) := (b : 𝓞 D.host.E).2
  have hbc : IsIntegral ℤ (D.conjF (b : D.host.E)) := hbi.map (D.conjF.toRingHom.toIntAlgHom)
  obtain ⟨t0, ht0⟩ := conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E)) (by rw [map_mul, conjF_invol, mul_comm])
  have ht0i : IsIntegral ℤ t0 := (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1
    (by rw [ht0]; exact hbi.mul hbc)
  refine ⟨⟨t0, ht0i⟩, ?_, ?_⟩
  · intro h
    have h1 : t0 = 0 := congrArg Subtype.val h
    rw [h1, map_zero] at ht0
    have hc0 : D.conjF (b : D.host.E) ≠ 0 := by
      intro hc; apply hb0
      have := congrArg D.conjF hc
      rwa [conjF_invol, map_zero] at this
    exact mul_ne_zero hb0 hc0 ht0.symm
  · show IsIntegral ℤ (algebraMap D.host.F D.host.E t0 *
      (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)))
    have e : algebraMap D.host.F D.host.E t0 *
        (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)) =
        D.conjF (b : D.host.E) * (a : D.host.E) := by
      rw [ht0]
      have hb0' : algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E) ≠ 0 := hb0
      field_simp
    rw [e]; exact hbc.mul (a : 𝓞 D.host.E).2

theorem denE (p : PlF D) (a : (D.s.atP p).Ep) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) * a ∈ (D.s.atP p).O := by
  obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} 1 one_ne_zero
    (Function.update (fun q => (0 : (D.s.atP q).Ep)) p a)
  obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
  simp only [Function.update_self, map_one, one_mul] at hxo
  obtain ⟨d, hd0, hdx⟩ := denF x
  refine ⟨d, hd0, ?_⟩
  have hxeq : a = (D.s.atP p).ιE x - o := by rw [← hxo]; ring
  have hd : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O := by
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  rw [hxeq, mul_sub]
  refine (D.s.atP p).O.sub_mem ?_ ((D.s.atP p).O.mul_mem hd ho)
  have h2 := iE_int (D.s.atP p) hdx
  rw [map_mul, iE_alg] at h2
  exact h2

theorem baseChangeAt_frame (p : PlF D) (j : Fin (nV D)) : baseChange₂ D p ((VS D).frame j) = Pi.single j 1 := by
  funext i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

set_option maxHeartbeats 1000000 in

theorem exists_isLattice_eq_localLattice (Zd : LocDat D) (p : PlF D) (M : Submodule (Zd.M p).L.O (Vp D p)) (hfg : M.FG)
    (hsp : Submodule.span (D.s.atP p).Ep (M : Set (Vp D p)) = ⊤) :
    ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ' := by
  let u : 𝓞 D.host.F → (D.s.atP p).Ep := fun d => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F))
  have u_mem : ∀ d, u d ∈ (D.s.atP p).O := fun d => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  have u_mul : ∀ a b, u (a * b) = u a * u b := fun a b => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((a * b : 𝓞 D.host.F) : D.host.F)) = _
    push_cast; rw [map_mul, map_mul]
  have smulM : ∀ {z : (D.s.atP p).Ep}, z ∈ (D.s.atP p).O → ∀ {v : Vp D p}, v ∈ M → z • v ∈ M := fun {z} hz {v} hv => by
    have hz' : z ∈ (Zd.M p).L.O := by rw [hO Zd p]; exact hz
    exact M.smul_mem ⟨z, hz'⟩ hv
  obtain ⟨s, hs⟩ := hfg

  have hall : ∀ j : Fin (nV D), (Pi.single j 1 : Vp D p) ∈ Submodule.span (D.s.atP p).Ep ((s : Set (Vp D p))) := by
    intro j
    have h1 : Submodule.span (D.s.atP p).Ep (s : Set (Vp D p)) = ⊤ := by
      rw [← Submodule.span_span_of_tower (Zd.M p).L.O (D.s.atP p).Ep, hs, hsp]
    rw [h1]; exact Submodule.mem_top
  choose ε _ hε using fun j => Submodule.mem_span_finset.1 (hall j)
  choose d hd0 hdm using fun (j : Fin (nV D)) (m : Vp D p) => denE p (ε j m)
  set c : 𝓞 D.host.F := ∏ j, ∏ m ∈ s, d j m with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro j _
    rw [Finset.prod_ne_zero_iff]
    exact fun m _ => hd0 j m
  have hkey : ∀ j, ∀ m ∈ s, u c * ε j m ∈ (D.s.atP p).O := by
    intro j m hm
    have hdv : d j m ∣ c := (Finset.dvd_prod_of_mem _ hm).trans (Finset.dvd_prod_of_mem (fun j => ∏ m ∈ s, d j m)
      (Finset.mem_univ j))
    obtain ⟨r, hr⟩ := hdv
    rw [hr, mul_comm (d j m) r, u_mul, mul_assoc]
    exact (D.s.atP p).O.mul_mem (u_mem r) (hdm j m)
  have hsM : ∀ m ∈ s, m ∈ M := fun m hm => by rw [← hs]; exact Submodule.subset_span hm
  have hce : ∀ j, u c • (Pi.single j 1 : Vp D p) ∈ M := by
    intro j
    rw [← hε j, Finset.smul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [smul_smul]
    exact smulM (hkey j m hm) (hsM m hm)
  have hdec : ∀ w : Vp D p, u c • w = ∑ i, w i • (u c • (Pi.single i 1 : Vp D p)) := by
    intro w
    funext j
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j), mul_comm]
  have hcv : ∀ v : Vp D p, (∀ i, v i ∈ (D.s.atP p).O) → u c • v ∈ M := by
    intro v hv
    rw [hdec v]
    exact Submodule.sum_mem _ fun i _ => smulM (hv i) (hce i)

  have happ : ∀ m : Vp D p, ∃ xm : (VS D).V, ∃ ov : Vp D p, (∀ i, ov i ∈ (D.s.atP p).O) ∧ baseChange₂ D p xm - m = u c • ov := by
    intro m
    have h1 : ∀ i, ∃ x : D.host.E, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE x - m i = u c * o := by
      intro i
      obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} c hc0
        (Function.update (fun q => (0 : (D.s.atP q).Ep)) p (m i))
      obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
      simp only [Function.update_self] at hxo
      exact ⟨x, o, ho, hxo⟩
    choose x o ho hxo using h1
    refine ⟨(VS D).frame.equivFun.symm x, o, ho, ?_⟩
    funext i
    have hr : (VS D).frame.repr ((VS D).frame.equivFun.symm x) i = x i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    show (D.s.atP p).ιE ((VS D).frame.repr ((VS D).frame.equivFun.symm x) i) - m i = u c * o i
    rw [hr, hxo i]
  choose xs ov hov hxs using happ
  obtain ⟨G, hG⟩ : ∃ G : Set (VS D).V, G = xs '' (s : Set (Vp D p)) ∪
      Set.range (fun i : Fin (nV D) => algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) := ⟨_, rfl⟩
  have hGx : ∀ m ∈ s, xs m ∈ G := fun m hm => by rw [hG]; exact Or.inl ⟨m, hm, rfl⟩
  have hGc : ∀ i, algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ G := fun i => by
    rw [hG]; exact Or.inr ⟨i, rfl⟩
  have hGfin : G.Finite := by rw [hG]; exact (s.finite_toSet.image xs).union (Set.finite_range _)
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Λ' = Submodule.span (𝓞 D.host.E) G := ⟨_, rfl⟩
  have hbcf : ∀ i, baseChange₂ D p (algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) = u c • (Pi.single i 1 : Vp D p) := by
    intro i
    rw [baseChange_smul₂, baseChangeAt_frame, iE_alg]
  have hlat : Submodule.IsLattice D.host.E Λ' := by
    refine ⟨by rw [hΛ']; exact Submodule.fg_span hGfin, ?_⟩
    rw [eq_top_iff, ← (VS D).frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hcE : algebraMap D.host.F D.host.E (c : D.host.F) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact_mod_cast hc0
    have hmem : algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ Submodule.span D.host.E (Λ' : Set (VS D).V) :=
      Submodule.subset_span (by rw [hΛ']; exact Submodule.subset_span (hGc i))
    have e : (VS D).frame i = (algebraMap D.host.F D.host.E (c : D.host.F))⁻¹ •
        (algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) := by
      rw [smul_smul, inv_mul_cancel₀ hcE, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hmem
  refine ⟨Λ', hlat, le_antisymm ?_ ?_⟩
  · rw [← hs, Submodule.span_le]
    intro m hm
    have e : m = baseChange₂ D p (xs m) - u c • ov m := by rw [← hxs m]; abel
    rw [SetLike.mem_coe, e]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨xs m, by rw [hΛ']; exact Submodule.subset_span (hGx m hm), rfl⟩) ?_
    rw [hdec (ov m)]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hbcf i]
    exact smul_mem_localLattice Zd p (hov m i) (Submodule.subset_span ⟨_, by rw [hΛ']; exact Submodule.subset_span (hGc i), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hΛ'] at hy
    rw [SetLike.mem_coe]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [hG] at hy
      rcases hy with ⟨m, hm, rfl⟩ | ⟨i, rfl⟩
      · have e : baseChange₂ D p (xs m) = m + u c • ov m := by rw [← hxs m]; abel
        rw [e]
        exact M.add_mem (hsM m hm) (hcv _ (hov m))
      · rw [hbcf]; exact hce i
    | zero => rw [map_zero]; exact M.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
    | smul a y _ hy =>
      rw [oE_smul, baseChange_smul₂]
      exact smulM (iE_int (D.s.atP p) (a : 𝓞 D.host.E).2) hy

end Formalism.L2.SG.Pf.LocalDenominators
