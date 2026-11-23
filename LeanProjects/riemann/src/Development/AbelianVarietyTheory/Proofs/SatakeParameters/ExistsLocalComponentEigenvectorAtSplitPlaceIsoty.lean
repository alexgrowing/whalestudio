import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (π : Representation ℂ G V) (w : V) : Subgroup G where
  carrier := {g | π g w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_eigen_of_sum {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Representation ℂ G V) (θ : G →* ℂˣ) (H : Subgroup G) [H.FiniteIndex] (hHθ : H ≤ θ.ker)
    {ι : Type} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, ∀ h ∈ H, π h (u i) = u i)
    (T : ι → V →ₗ[ℂ] M) (f : M) (hf0 : f ≠ 0)
    (hf : ∀ g, ∑ i ∈ s, T i (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, π g w = ((θ g : ℂˣ) : ℂ) • w := by
  classical
  haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let F : V → G → V := fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w
  have hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x) := by
    intro w g x
    simp only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]
    congr 1
    have : ((θ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y := by
    intro i hi x y hxy
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h := ⟨x⁻¹ * y, hm, by group⟩
    have hθh : θ h = 1 := hHθ hh
    simp only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]
  let e : V → V := fun w => ∑ q : G ⧸ H, F w q.out
  have heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i) := by
    intro i hi g
    simp only [e, map_sum, hFg, ← Finset.smul_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    apply hFH i hi
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f := by
    simp only [e, map_sum]
    rw [Finset.sum_comm]
    have : ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f := by
      intro q
      simp only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  by_contra hne
  push_neg at hne
  have hz : ∀ i ∈ s, e (u i) = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨g, hg⟩ := hne _ h0
    exact hg (heig i hi g)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])] at htot
  have hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)

end Algebra

section Topology

theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  intro L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt
  classical
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hσ c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨φ, hφ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hφ i)
  let m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map c.toRingHom
  have hm : Continuous m := Units.continuous_map (continuous_id.matrix_map hc)
  let π : Representation ℂ K σ.V := σ.ρ.comp (m.comp K.subtype)
  have hπ : ∀ g : K, π g = σ.ρ (m g) := fun g => rfl
  have hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f := by
    rintro ⟨g, hg⟩
    obtain ⟨κ, hκ, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have : ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i) := by
      intro i _
      rw [hπ, ← hu i]
      exact i.2.2 κ hκ (u i)
    rw [Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]
    rw [← hsum]
    rfl
  let H : Subgroup K := θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)
  have hHo : IsOpen (H : Set K) := by
    rw [Subgroup.coe_inf]
    refine hθ.inter ?_
    simp only [Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)
  have hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :
      Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.SplitFlip.isCompact_KO
  haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_sum π θ H inf_le_left φ.support u
    (fun i hi h hh => by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)
      exact (Subgroup.mem_iInf.1 this hi))
    (fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF
  exact ⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩

end GlobalTheory.LocVec
