import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenPiU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.FkFilt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanLeBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Gr

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

abbrev JK (k : ℕ) : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF) :=
  Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))

abbrev JKo (k : ℕ) : Submodule (Op X la G.N) ↥(HK X la G.w wF) := (JK G la k).restrictScalars (Op X la G.N)

theorem JK_anti {k l : ℕ} (h : k ≤ l) : JK G la l ≤ JK G la k :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

theorem bcol_sum {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((bcol (D := D) (j := j) jj α).sum fun _ n => n) = ∑ i, α i := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [bcol, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem smulOp_HK (o : Op X la G.N) (x : ↥(HK X la G.w wF)) :
    o • x = (algebraMap (Op X la G.N) (Kp X la G.N) o) • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, algebraMap_smul]

def toWKo (a : ℕ) : ↥(HK X la G.w wF) →ₗ[Op X la G.N] WK X la G.w wF a where
  toFun := toWK X la G.w wF a
  map_add' := map_add _
  map_smul' o x := by
    rw [smulOp_HK, LinearMap.map_smul_of_tower]
    rfl

theorem hasse_mem_HK (β : Idx D j G.N →₀ ℕ) (x : ↥(HK X la G.w wF)) :
    hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF :=
  (mem_HK X la G.w).2 (hasse_presentation X la G.w wF β _ ((mem_HK X la G.w).1 x.2))

def dH (β : Idx D j G.N →₀ ℕ) : ↥(HK X la G.w wF) →+ SectionSheafQuotient X la G.w wF where
  toFun x := toA0K X la G.w wF ⟨hasse X la G.w β (x : Lw X la G.w), hasse_mem_HK G la β x⟩
  map_zero' := by
    rw [← (toA0K X la G.w wF).map_zero]
    congr 1
    apply Subtype.ext
    exact (hasse X la G.w β).map_zero
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact (hasse X la G.w β).map_add _ _

def vals (k : ℕ) : ↥(HK X la G.w wF) →+ Vg G la :=
  AddMonoidHom.pi fun p => if p.2 ∈ mon D j k then dH G la (bcol p.1 p.2) else 0

theorem vals_apply (k : ℕ) (x : ↥(HK X la G.w wF)) (p : Fin G.N × (Fin (WeightFamilies.dimY D j) → ℕ)) :
    vals G la k x p = if p.2 ∈ mon D j k then dH G la (bcol p.1 p.2) x else 0 := by
  show (if p.2 ∈ mon D j k then dH G la (bcol p.1 p.2) else 0) x = _
  split_ifs <;> rfl

def Uk (k : ℕ) : (↥(mon D j k) → SectionSheafQuotient X la G.w wF) →ₗ[Op X la G.N] Vg G la where
  toFun b p := if h : p.2 ∈ mon D j k then uC G la p.1 p.2 • b ⟨p.2, h⟩ else 0
  map_add' b b' := by
    funext p
    simp only [Pi.add_apply]
    split_ifs
    · exact smul_add _ _ _
    · exact (add_zero 0).symm
  map_smul' o b := by
    funext p
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · exact smul_comm _ _ _
    · exact (smul_zero o).symm

theorem Uk_inj (hUI : UInj) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (k : ℕ) : Function.Injective (Uk G la k) := by
  refine (injective_iff_map_eq_zero (Uk G la k)).2 fun b hb => ?_
  funext a
  refine hUI G la Q S CRm T c hOk hw a.1 (b a) fun jj => ?_
  have h := congrFun hb (jj, a.1)
  simpa [Uk, a.2] using h

theorem vals_eq_U (hTH : TaylorHasse) (k : ℕ) (x : ↥(HK X la G.w wF)) (cf : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF))
    (hx : x - ∑ α ∈ mon D j k, ym G la α • cf α ∈ JK G la (k + 1)) :
    vals G la k x = Uk G la k (fun a => toA0K X la G.w wF (cf a)) := by
  funext p
  rw [vals_apply]
  show _ = if h : p.2 ∈ mon D j k then _ else _
  split_ifs with h
  · exact hTH G la k x cf hx p.1 p.2 h (hasse_mem_HK G la _ x)
  · rfl

def psi (hHS : HasseSmul) (k : ℕ) : ↥(JKo G la k) →ₗ[Op X la G.N] Vg G la where
  toFun x := vals G la k x
  map_add' x y := by rw [Submodule.coe_add, map_add]
  map_smul' o x := by
    funext p
    rw [RingHom.id_apply, Pi.smul_apply, vals_apply, vals_apply]
    split_ifs with h
    · exact hHS G la k o x x.2 _ (by rw [bcol_sum]; exact Finset.Nat.mem_antidiagonalTuple.1 h) _ _
    · exact (smul_zero o).symm

theorem Fk_eq (T k : ℕ) : Fk G la T k = (JKo G la k).map (toWKo G la (a0 D j T)) := by
  rw [← Submodule.span_eq ((JKo G la k).map (toWKo G la (a0 D j T))), Submodule.map_coe]
  rfl

def tau (T k : ℕ) : ↥(JKo G la k) →ₗ[Op X la G.N] ↥(Fk G la T k) :=
  LinearMap.codRestrict _ ((toWKo G la (a0 D j T)).comp (JKo G la k).subtype) fun x => by
    rw [Fk_eq]; exact Submodule.mem_map_of_mem x.2

theorem tau_surj (T k : ℕ) : Function.Surjective (tau G la T k) := by
  rintro ⟨y, hy⟩
  rw [Fk_eq, Submodule.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_tau_le (hHS : HasseSmul) (hHV : HasseVan) (T k : ℕ) (hk : k < a0 D j T) :
    LinearMap.ker (tau G la T k) ≤ LinearMap.ker (psi G la hHS k) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h0 : toWK X la G.w wF (a0 D j T) (x : ↥(HK X la G.w wF)) = 0 := congrArg Subtype.val hx
  rw [toWK_eq_zero_iff] at h0
  funext p
  show vals G la k x p = 0
  rw [vals_apply]
  split_ifs with h
  · exact hHV G la (a0 D j T) x h0 _ (by rw [bcol_sum, Finset.Nat.mem_antidiagonalTuple.1 h]; exact hk) _
  · rfl

def phi (hHS : HasseSmul) (hHV : HasseVan) (T k : ℕ) : ↥(Fk G la T k) →ₗ[Op X la G.N] Vg G la :=
  if hk : k < a0 D j T then
    ((LinearMap.ker (tau G la T k)).liftQ (psi G la hHS k) (ker_tau_le G la hHS hHV T k hk)) ∘ₗ
      ((tau G la T k).quotKerEquivOfSurjective (tau_surj G la T k)).symm.toLinearMap
  else 0

theorem phi_tau (hHS : HasseSmul) (hHV : HasseVan) (T k : ℕ) (hk : k < a0 D j T) (x : ↥(JKo G la k)) :
    phi G la hHS hHV T k (tau G la T k x) = psi G la hHS k x := by
  unfold phi
  rw [dif_pos hk, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have e : ((tau G la T k).quotKerEquivOfSurjective (tau_surj G la T k)).symm (tau G la T k x) =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [e, Submodule.liftQ_apply]

theorem phi_toWK (hHS : HasseSmul) (hHV : HasseVan) (T k : ℕ) (hk : k < a0 D j T) (x : ↥(HK X la G.w wF))
    (hx : x ∈ JK G la k) (hy : toWK X la G.w wF (a0 D j T) x ∈ Fk G la T k) :
    phi G la hHS hHV T k ⟨_, hy⟩ = vals G la k x :=
  phi_tau G la hHS hHV T k hk ⟨x, hx⟩

end Gr

theorem grBound_of (hTR : TaylorRep) (hTH : TaylorHasse) (hHS : HasseSmul) (hHV : HasseVan) (hUI : UInj)
    (hUB : UBall) (hAR : AARep) : GrBound := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hth hw hI
  classical
  refine ⟨phi G la hHS hHV T,
    fun k => (Submodule.pi Set.univ fun _ : ↥(mon D j k) => Q.A0).map (Uk G la k),
    fun k => (Submodule.pi Set.univ fun _ : ↥(mon D j k) =>
      Submodule.span (Op X la G.N) (Set.range (tL G la))).map (Uk G la k), ?_, ?_, ?_, ?_⟩
  ·
    intro k x hx0
    by_cases hk : k < a0 D j T
    · obtain ⟨x, hxF⟩ := x
      have hxF' := hxF
      rw [Fk_eq, Submodule.mem_map] at hxF'
      obtain ⟨y, hy, rfl⟩ := hxF'
      have e : phi G la hHS hHV T k ⟨toWKo G la (a0 D j T) y, hxF⟩ = vals G la k y :=
        phi_toWK G la hHS hHV T k hk y hy hxF
      obtain ⟨cf, hcf⟩ := hTR G la k y hy
      rw [e, vals_eq_U G la hTH k y cf hcf] at hx0
      have hb := (injective_iff_map_eq_zero _).1 (Uk_inj G la hUI Q S CRm T c hOk hw k) _ hx0
      have hmem : ∀ α ∈ mon D j k, ym G la α • cf α ∈ JK G la (k + 1) := by
        intro α hα
        have h1 : toA0K X la G.w wF (cf α) = 0 := congrFun hb ⟨α, hα⟩
        rw [reduction_eq_zero_iff_mem_ideal_smul] at h1
        have h2 : ym G la α ∈ Jid X la G.w ^ k := by
          have := prod_sfr_mem X la G.w α
          rwa [Finset.Nat.mem_antidiagonalTuple.1 hα] at this
        have h3 := Submodule.smul_mem_smul h2 h1
        rw [JK, pow_succ, Submodule.mul_smul]
        exact h3
      have hy1 : y ∈ JK G la (k + 1) := by
        have := Submodule.add_mem _ hcf (Submodule.sum_mem _ hmem)
        rwa [sub_add_cancel] at this
      show toWKo G la (a0 D j T) y ∈ Fk G la T (k + 1)
      rw [Fk_eq]
      exact Submodule.mem_map_of_mem hy1
    · have hF := fkFilt_holds G la T
      have h1 : (x : WK X la G.w wF (a0 D j T)) ∈ Fk G la T (a0 D j T) := hF.1 (not_lt.1 hk) x.2
      rw [hF.2.2, Submodule.mem_bot] at h1
      rw [h1]
      exact Submodule.zero_mem _
  ·
    intro k hk x hxA
    obtain ⟨x, hxF⟩ := x
    obtain ⟨x', hx'1, hx'2⟩ := hAR G la Q S CRm T c hOk hw x hxA
    have hxF' := hxF
    rw [Fk_eq, Submodule.mem_map] at hxF'
    obtain ⟨y, hy, hyx⟩ := hxF'
    have hd0 : toWK X la G.w wF (a0 D j T) (x' - y) = 0 := by
      rw [map_sub, hx'1, ← hyx]
      exact sub_self _
    have hd : x' - y ∈ JK G la (a0 D j T) := (toWK_eq_zero_iff X la G.w wF _ _).1 hd0
    have hx' : x' ∈ JK G la k := by
      have := Submodule.add_mem _ hy (JK_anti G la hk.le hd)
      rwa [add_sub_cancel] at this
    subst hx'1
    have e : phi G la hHS hHV T k ⟨toWK X la G.w wF (a0 D j T) x', hxF⟩ = vals G la k x' :=
      phi_toWK G la hHS hHV T k hk x' hx' hxF
    rw [e]
    obtain ⟨cf, hcf⟩ := hTR G la k x' hx'
    rw [vals_eq_U G la hTH k x' cf hcf]
    refine Submodule.mem_map_of_mem ?_
    rw [Submodule.mem_pi]
    intro a _
    refine hUB G la Q S CRm T c hOk hw a.1 _ fun jj => ?_
    have h5 := hTH G la k x' cf hcf jj a.1 a.2 (hasse_mem_HK G la _ x')
    have h6 := hx'2 (bcol jj a.1) (by rw [bcol_sum, Finset.Nat.mem_antidiagonalTuple.1 a.2]; omega)
      (hasse_mem_HK G la _ x')
    rw [h5] at h6
    exact h6
  ·
    intro k hk v hv
    rw [Submodule.mem_map] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    rw [Submodule.mem_pi] at hb
    have hc : ∀ a : ↥(mon D j k), ∃ cc : Fin G.del → Op X la G.N, ∑ i, cc i • tL G la i = b a :=
      fun a => (Submodule.mem_span_range_iff_exists_fun _).1 (hb a (Set.mem_univ a))
    choose cc hcc using hc
    have hg : ∀ (a : ↥(mon D j k)) (i : Fin G.del), ∃ (x : ↥(HK X la G.w wF)) (cg : ↥(HK X la G.w wF)),
        toWK X la G.w wF (a0 D j T) x ∈ firstLength_le_prime_bound G la T ∧ x = ym G la a.1 • cg ∧ toA0K X la G.w wF cg = tL G la i :=
      fun a i => taylorSpanGenerators G la T k hk a.1 a.2 i
    choose xg cg hxN hxe hcg using hg
    have hxJ : ∀ a i, xg a i ∈ JK G la k := by
      intro a i
      rw [hxe a i]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have := prod_sfr_mem X la G.w a.1
      rwa [Finset.Nat.mem_antidiagonalTuple.1 a.2] at this
    have hpsi : ∀ a i, psi G la hHS k ⟨xg a i, hxJ a i⟩ = Uk G la k (Pi.single a (tL G la i)) := by
      intro a i
      show vals G la k (xg a i) = _
      have hcf : xg a i - ∑ β ∈ mon D j k, ym G la β • (fun β => if β = a.1 then cg a i else 0) β ∈
          JK G la (k + 1) := by
        simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.coe_mem, ↓reduceIte]
        rw [← hxe a i, sub_self]
        exact Submodule.zero_mem _
      rw [vals_eq_U G la hTH k _ _ hcf]
      congr 1
      funext a'
      by_cases h : a' = a
      · subst h
        simp [hcg]
      · have h' : (a' : Fin (WeightFamilies.dimY D j) → ℕ) ≠ a := fun e => h (Subtype.ext e)
        simp [h, h']
    let Yo : ↥(JKo G la k) := ∑ a, ∑ i, cc a i • (⟨xg a i, hxJ a i⟩ : ↥(JKo G la k))
    have hN : ((tau G la T k Yo : ↥(Fk G la T k)) : WK X la G.w wF (a0 D j T)) ∈ firstLength_le_prime_bound G la T := by
      show toWKo G la (a0 D j T) (Yo : ↥(HK X la G.w wF)) ∈ firstLength_le_prime_bound G la T
      simp only [Yo, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxN a i)
    refine ⟨tau G la T k Yo, Submodule.mem_inf.2 ⟨hN, taylorSpanLeBound G la Q S CRm T c hOk hw hth hN⟩, ?_⟩
    rw [phi_tau G la hHS hHV T k hk]
    have hY : psi G la hHS k Yo = Uk G la k (∑ a, ∑ i, cc a i • Pi.single a (tL G la i)) := by
      simp only [Yo, map_sum, map_smul, hpsi]
    rw [hY]
    congr 1
    funext a'
    rw [← hcc a', Finset.sum_apply, Finset.sum_eq_single a']
    · simp [Finset.sum_apply]
    · intro a _ hne
      simp [Finset.sum_apply, Ne.symm hne]
    · simp
  ·
    intro k _
    have e := lenPiU_holds (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Vg G la) ↥(mon D j k) Q.A0
      (Submodule.span (Op X la G.N) (Set.range (tL G la))) (Uk G la k) (Uk_inj G la hUI Q S CRm T c hOk hw k)
    rw [e, Fintype.card_coe]
    push_cast
    rw [ENat.natCast_toNat hI]
    exact le_rfl

end PoleLengthBounds
