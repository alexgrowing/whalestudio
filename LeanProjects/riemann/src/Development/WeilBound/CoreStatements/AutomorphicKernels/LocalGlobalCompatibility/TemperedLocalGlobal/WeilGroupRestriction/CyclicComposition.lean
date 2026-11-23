import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CyclicComposition

section Grp

variable {Γ : Type*} [Group Γ]

theorem cyc_of_isCyclic {H : Subgroup Γ} [H.Normal] (hc : IsCyclic (Γ ⧸ H)) :
    ∃ g : Γ, H ⊔ Subgroup.zpowers g = ⊤ := by
  obtain ⟨q, hq⟩ := hc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hq (x : Γ ⧸ H))
  have hx : x = x * (g ^ k)⁻¹ * g ^ k := by group
  rw [hx]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers g k))
  rw [← QuotientGroup.eq_one_iff]
  simp [hk]

theorem isCyclic_of_cyc {H : Subgroup Γ} [H.Normal] (g : Γ) (hg : H ⊔ Subgroup.zpowers g = ⊤) :
    IsCyclic (Γ ⧸ H) := by
  refine ⟨⟨(g : Γ ⧸ H), fun q => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hle : H ⊔ Subgroup.zpowers g ≤ (Subgroup.zpowers (g : Γ ⧸ H)).comap (QuotientGroup.mk' H) := by
    refine sup_le (fun h hh => ?_) ?_
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).2 hh]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, QuotientGroup.mk'_apply]
      exact Subgroup.mem_zpowers _
  have hx : x ∈ H ⊔ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top x
  exact hle hx

theorem exists_index_prime {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card Q) : ∃ K : Subgroup Q, K.Normal ∧ K.index = p := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Q)
  have ho : orderOf q = Nat.card Q := orderOf_eq_card_of_forall_mem_zpowers hq
  refine ⟨Subgroup.zpowers (q ^ p), ⟨fun n hn g => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hq g)
    have hc : Commute (q ^ i) n := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      exact (((Commute.refl q).zpow_left i).pow_right p).zpow_right j
    rw [hc.eq, mul_inv_cancel_right]
    exact hn
  · have hc := Subgroup.card_mul_index (Subgroup.zpowers (q ^ p))
    have hd' : p ∣ orderOf q := by rw [ho]; exact hd
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero hd', ho] at hc
    obtain ⟨m, hm⟩ := hd
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at hc
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm
        exact absurd hm (Nat.card_pos (α := Q)).ne'
      · exact h
    exact Nat.eq_of_mul_eq_mul_left hm0 (hc.trans (mul_comm p m))

end Grp

section Gal

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

theorem range_resG (L : IntermediateField E Ω) :
    (resG E (E' := L) (Ω := Ω)).range = L.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun y => hσ y y.2), AlgEquiv.ext fun _ => rfl⟩

variable [NumberField E] [IsAlgClosure E Ω]

def ofIF (L : IntermediateField E Ω) [FiniteDimensional E L] (hcm : IsCMField L) : CMExt E Ω :=
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  { M := L }

def comp (X₁ : CMExt E Ω) (X₂ : CMExt X₁.M Ω) : CMExt E Ω :=
  letI : Algebra E X₂.M := ((algebraMap X₁.M X₂.M).comp (algebraMap E X₁.M)).toAlgebra
  haveI : IsScalarTower E X₂.M Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = algebraMap X₂.M Ω (algebraMap X₁.M X₂.M (algebraMap E X₁.M x))
    rw [← IsScalarTower.algebraMap_apply X₁.M X₂.M Ω, ← IsScalarTower.algebraMap_apply E X₁.M Ω]
  { M := X₂.M }

omit [NumberField E] [IsAlgClosure E Ω] in
theorem resG_comp (X₁ : CMExt E Ω) (X₂ : CMExt X₁.M Ω) (τ : G (comp X₁ X₂).M Ω) :
    resG E (E' := (comp X₁ X₂).M) (Ω := Ω) τ =
      resG E (E' := X₁.M) (Ω := Ω) (resG X₁.M (E' := X₂.M) (Ω := Ω) τ) :=
  AlgEquiv.ext fun _ => rfl

theorem trace_conj {l a : ℕ} [Fact l.Prime] (p x : GL (Fin a) (Qbar l)) :
    ((p * x * p⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      (x : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

end Gal

section Lift

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem lift_self (hL : GlobalTheory.Published.LocalLanglandsGL) {a : ℕ} (π : CuspSub E a) (hc : π.IsCsd)
    (hr : (CG.mk π).IsRegAlg) : IsLift Ω (CMExt.self E Ω) π π := by
  refine ⟨hc, hr, ?_⟩
  intro l _ ι r wt HT r' wt' HT' h h'
  obtain ⟨p, hp⟩ := GlobalTheory.TraceConjWeil.main E Ω l a r r' h.cont h'.cont h.ss h'.ss (fun w hw A hA σ => by
    obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w hA
    obtain ⟨σ0, hσ0, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π w
    exact GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι a r r' w A hA _ (h.away w hw A hA rc hrc σ0 hσ0)
      (h'.away w hw A hA rc hrc σ0 hσ0) σ)
  refine ⟨p, fun g => ?_⟩
  have e : resG E (E' := (CMExt.self E Ω).M) (Ω := Ω) g = g := AlgEquiv.ext fun _ => rfl
  rw [e]
  exact hp g

theorem range_self : (resG E (E' := (CMExt.self E Ω).M) (Ω := Ω)).range = ⊤ :=
  MonoidHom.range_eq_top.2 fun g => ⟨g, AlgEquiv.ext fun _ => rfl⟩

end Lift

theorem tower_ne_top (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hO : OneStep) : ∀ n : ℕ,
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT → ∀ H : Subgroup (G E Ω), GoodSub H → TrCond r H → H ≠ ⊤ →
      H.index ≤ n →
      ∃ (X : CMExt E Ω) (P : CuspSub X.M a), (resG E (E' := X.M) (Ω := Ω)).range = H ∧ IsLift Ω X π P := by
  intro n
  induction n with
  | zero =>
    intro E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT hne hn
    haveI : IsGalois E Ω := {}
    haveI : Finite (G E Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH.isOpen
    exact absurd (Nat.le_zero.1 hn) Subgroup.index_ne_zero_of_finite
  | succ n ih =>
    intro E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT hne hn
    haveI : IsGalois E Ω := {}
    haveI : Finite (G E Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH.isOpen
    haveI := hH.normal
    have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨g0, hg0⟩ := hH.cyc
    haveI : IsCyclic (G E Ω ⧸ H) := isCyclic_of_cyc g0 hg0
    obtain ⟨K, hKn, hKi⟩ := exists_index_prime (Q := G E Ω ⧸ H) hp (by rwa [← Subgroup.index_eq_card])
    set H1 : Subgroup (G E Ω) := K.comap (QuotientGroup.mk' H) with hH1def
    have hH1i : H1.index = p := by
      rw [hH1def, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective H)]
      exact hKi
    have hHH1 : H ≤ H1 := fun x hx => by
      rw [hH1def, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact K.one_mem
    haveI hH1n : H1.Normal := hKn.comap _
    have hH1o : IsOpen (H1 : Set (G E Ω)) := Subgroup.isOpen_mono hHH1 hH.isOpen
    have hH1c : IsClosed (H1 : Set (G E Ω)) := Subgroup.isClosed_of_isOpen H1 hH1o
    have hH1top : H1 ≠ ⊤ := fun h => hp.ne_one (hH1i.symm.trans (Subgroup.index_eq_one.2 h))
    set L : IntermediateField E Ω := IntermediateField.fixedField H1 with hLdef
    have hLfix : L.fixingSubgroup = H1 := InfiniteGalois.fixingSubgroup_fixedField ⟨H1, hH1c⟩
    haveI hLfd : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hLfix]; exact hH1o)
    haveI hLgal : IsGalois E L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLfix]; exact hH1n)
    have hLcm : IsCMField L := hH.cm L (by rw [hLfix]; exact hHH1)
    have hrk : Module.finrank E L = p := by
      haveI : (⟨H1, hH1c⟩ : ClosedSubgroup (G E Ω)).Normal := hH1n
      rw [← IsGalois.card_aut_eq_finrank, ← hH1i, Subgroup.index_eq_card]
      exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient ⟨H1, hH1c⟩).toEquiv).symm
    let X1 : CMExt E Ω := ofIF L hLcm
    have hX1r : (resG E (E' := X1.M) (Ω := Ω)).range = H1 := (range_resG L).trans hLfix
    have hTr : ∃ g, g ∉ (resG E (E' := X1.M) (Ω := Ω)).range ∧
        (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0 := by
      rw [hX1r]
      obtain ⟨g, -, hg, ht⟩ := hT H1 ⊤ hHH1 (lt_top_iff_ne_top.2 hH1top)
      exact ⟨g, hg, ht⟩
    have hX1gal : IsGalois E X1.M := hLgal
    have hX1p : (Module.finrank E X1.M).Prime := by
      show (Module.finrank E L).Prime
      rw [hrk]; exact hp
    obtain ⟨P1, hP1⟩ := hO E Ω a ha π hc hr X1 hX1gal hX1p l ι r wt HT hR hTr
    by_cases hEq : H1 ≤ H
    · exact ⟨X1, P1, hX1r.trans (le_antisymm hEq hHH1), hP1⟩
    obtain ⟨r1, wt1, HT1, hR1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι ha hP1.reg hP1.csd
    obtain ⟨p1, hp1⟩ := hP1.res l ι r wt HT r1 wt1 HT1 hR hR1
    set H' : Subgroup (G X1.M Ω) := H.comap (resG E (E' := X1.M) (Ω := Ω)) with hH'def
    have hH'i : H'.index = H.relIndex H1 := by rw [hH'def, Subgroup.index_comap, hX1r]
    have hrel : H.relIndex H1 * p = H.index := hH1i ▸ Subgroup.relIndex_mul_index hHH1
    have hrel1 : H.relIndex H1 ≠ 1 := fun h => hEq (Subgroup.relIndex_eq_one.1 h)
    have hrel0 : H.relIndex H1 ≠ 0 := fun h => h0 (by rw [← hrel, h, zero_mul])
    have hlt : H'.index ≤ n := by
      rw [hH'i]
      have := hp.two_le
      have := Nat.pos_of_ne_zero hrel0
      nlinarith
    have hne' : H' ≠ ⊤ := fun h => hrel1 (by rw [← hH'i, h, Subgroup.index_top])
    have hinj : Function.Injective (resG E (E' := X1.M) (Ω := Ω)) := resG_injective
    have hcont : Continuous (resG E (E' := X1.M) (Ω := Ω)) := continuous_resG
    haveI hH'n : H'.Normal := hH.normal.comap _
    have hH'good : GoodSub H' := by
      refine ⟨hH'n, hH.isOpen.preimage hcont, ?_, ?_⟩
      · apply cyc_of_isCyclic
        refine isCyclic_of_injective (QuotientGroup.map H' H (resG E (E' := X1.M) (Ω := Ω)) le_rfl) ?_
        intro x y hxy
        induction x using QuotientGroup.induction_on with
        | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
        have h2 : ((resG E (E' := X1.M) (Ω := Ω) x : G E Ω) : G E Ω ⧸ H) =
            ((resG E (E' := X1.M) (Ω := Ω) y : G E Ω) : G E Ω ⧸ H) := hxy
        rw [QuotientGroup.eq] at h2 ⊢
        rw [hH'def, Subgroup.mem_comap, map_mul, map_inv]
        exact h2
      · intro L' hL'
        have key : H ≤ (L'.restrictScalars E).fixingSubgroup := by
          intro σ hσ
          obtain ⟨τ, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
          have hτ : τ ∈ L'.fixingSubgroup := hL' hσ
          rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
          intro x hx
          exact hτ x hx
        exact hH.cm _ key
    have hT' : TrCond r1 H' := by
      intro K1 K2 hK1 hK12
      have hmap1 : H ≤ K1.map (resG E (E' := X1.M) (Ω := Ω)) := by
        intro σ hσ
        obtain ⟨τ, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
        exact ⟨τ, hK1 hσ, rfl⟩
      have hmap2 : K1.map (resG E (E' := X1.M) (Ω := Ω)) < K2.map (resG E (E' := X1.M) (Ω := Ω)) := by
        refine lt_of_le_of_ne (Subgroup.map_mono hK12.le) fun h => hK12.ne ?_
        rw [← Subgroup.comap_map_eq_self_of_injective hinj K1, h, Subgroup.comap_map_eq_self_of_injective hinj K2]
      obtain ⟨g, ⟨τ, hτ2, rfl⟩, hg1, ht⟩ := hT _ _ hmap1 hmap2
      refine ⟨τ, hτ2, fun h => hg1 ⟨τ, h, rfl⟩, ?_⟩
      rw [hp1 τ, trace_conj]
      exact ht
    obtain ⟨X2, P2, hX2r, hX2⟩ := ih X1.M Ω a ha P1 hP1.csd hP1.reg l ι r1 wt1 HT1 hR1 H' hH'good hT' hne' hlt
    refine ⟨comp X1 X2, P2, ?_, hX2.csd, hX2.reg, ?_⟩
    · ext σ
      constructor
      · rintro ⟨τ, rfl⟩
        rw [resG_comp]
        have : resG X1.M (E' := X2.M) (Ω := Ω) τ ∈ H' := by rw [← hX2r]; exact ⟨τ, rfl⟩
        exact this
      · intro hσ
        obtain ⟨τ1, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
        have : τ1 ∈ (resG X1.M (E' := X2.M) (Ω := Ω)).range := by rw [hX2r]; exact hσ
        obtain ⟨τ, rfl⟩ := this
        exact ⟨τ, resG_comp X1 X2 τ⟩
    · intro l' _ ι' r0 wt0 HT0 r' wt' HT' h0' h'
      obtain ⟨s1, ws1, Hs1, hs1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hP1.reg hP1.csd
      obtain ⟨q1, hq1⟩ := hP1.res l' ι' r0 wt0 HT0 s1 ws1 Hs1 h0' hs1
      obtain ⟨q2, hq2⟩ := hX2.res l' ι' s1 ws1 Hs1 r' wt' HT' hs1 h'
      refine ⟨q2 * q1, fun g => ?_⟩
      refine (hq2 g).trans ?_
      rw [hq1, resG_comp]
      simp only [mul_inv_rev, mul_assoc]

end CyclicComposition

open CyclicComposition in
theorem cyclic_composition_lift : LocalHeckeAlgebra := by
  intro hG hL hO E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT
  by_cases hne : H = ⊤
  · subst hne
    exact ⟨CMExt.self E Ω, π, range_self, lift_self hL π hc hr⟩
  · exact tower_ne_top hG hO H.index E Ω a ha π hc hr l ι r wt HT hR H hH hT hne le_rfl

end PositivityTheory.Pf1.CLGD.K

end
