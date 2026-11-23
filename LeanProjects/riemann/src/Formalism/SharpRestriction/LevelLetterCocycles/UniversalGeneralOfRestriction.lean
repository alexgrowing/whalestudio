import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne

noncomputable section

open Module Submodule

namespace Formalism.MainNotions.UnusedSlot80.UnivF

variable {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]

def Sat {M : Type*} [AddCommGroup M] [Module O M] (N : Submodule O M) : Prop :=
  ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N

theorem adapted {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module O M] (b : Basis ι O M)
    (N : Submodule O M) (hN : Sat N) :
    ∃ (b' : Basis ι O M) (S : Finset ι), N = span O (b' '' (S : Set ι)) := by
  classical
  obtain ⟨k, snf⟩ := N.smithNormalForm b
  refine ⟨snf.bM, Finset.univ.map snf.f, le_antisymm ?_ ?_⟩
  · intro x hx
    have hx' : x = ∑ i, snf.bN.repr ⟨x, hx⟩ i • (snf.bN i : M) := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : N) : M) from rfl, ← snf.bN.sum_repr ⟨x, hx⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [snf.snf i]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨snf.f i, ?_, rfl⟩)
    simp
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Set.mem_range] at hj
    obtain ⟨i, rfl⟩ := hj
    have hne : snf.a i ≠ 0 := by
      intro h0
      have h := snf.snf i
      rw [h0, zero_smul] at h
      exact snf.bN.ne_zero i (Subtype.ext h)
    refine hN (snf.a i) _ hne ?_
    rw [← snf.snf i]
    exact (snf.bN i).2

variable (LL : Type*) [Field LL] [Algebra O LL] [IsFractionRing O LL]

def toLL (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → LL) :=
  LinearMap.pi fun j => (Algebra.linearMap O LL).comp (LinearMap.proj j)

theorem toLL_apply {d : ℕ} (x : Fin d → O) (j : Fin d) : toLL LL d x j = algebraMap O LL (x j) := rfl

theorem toLL_inj (d : ℕ) : Function.Injective (toLL (O := O) LL d) := by
  intro x y h
  funext j
  exact (IsFractionRing.injective O LL) (congrFun h j)

theorem clear (d : ℕ) (y : Fin d → LL) : ∃ (a : O) (z : Fin d → O), a ≠ 0 ∧ toLL (O := O) LL d z = a • y := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ) y
  choose z hz using fun j => hb j (Finset.mem_univ j)
  refine ⟨b, z, nonZeroDivisors.ne_zero b.2, funext fun j => ?_⟩
  rw [toLL_apply, hz j]
  rfl

variable {LL}

theorem mem_of_smul {d : ℕ} (P : Submodule LL (Fin d → LL)) {a : O} (ha : a ≠ 0) {y : Fin d → LL}
    (h : a • y ∈ P) : y ∈ P := by
  have hne : algebraMap O LL a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 ha
  have h' : algebraMap O LL a • y ∈ P := by rwa [algebraMap_smul]
  exact (Submodule.smul_mem_iff P hne).1 h'

theorem toLL_mem_span {d : ℕ} {T : Set (Fin d → O)} {z : Fin d → O} (hz : z ∈ span O T) :
    toLL LL d z ∈ span LL (toLL LL d '' T) := by
  have h1 : toLL LL d z ∈ span O (toLL LL d '' T) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hz
  exact Submodule.span_le_restrictScalars O LL _ h1

variable (LL)

theorem split (d : ℕ) (U V : Submodule LL (Fin d → LL)) :
    ∃ (d' : ℕ) (g : Basis (Fin d') O (Fin d → O)) (R : Finset (Fin d')),
      R.card + finrank LL U ≤ d + finrank LL V ∧
      (∀ k ∉ R, toLL LL d (g k) ∈ U) ∧
      V ≤ span LL ((fun k => toLL LL d (g k)) '' (R : Set (Fin d'))) := by
  classical
  let ι := toLL (O := O) LL d

  let N1 : Submodule O (Fin d → O) := (U.restrictScalars O).comap ι
  have hN1 : Sat N1 := by
    intro a x ha hx
    have h1 : ι (a • x) ∈ U := hx
    rw [map_smul] at h1
    exact mem_of_smul U ha h1
  obtain ⟨e, S1, hS1⟩ := adapted (Pi.basisFun O (Fin d)) N1 hN1
  set s1 : Set (Fin d) := (S1 : Set (Fin d)) with hs1
  let XC : Submodule LL (Fin d → LL) := span LL (ι '' (e '' s1))
  let X2 : Submodule LL (Fin d → LL) := span LL (ι '' (e '' s1ᶜ))
  have hliO : LinearIndependent O (ι ∘ e) :=
    e.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 (toLL_inj LL d))
  have hli : LinearIndependent LL (ι ∘ e) := (LinearIndependent.iff_fractionRing O LL).1 hliO
  have hdisj : Disjoint XC X2 := by
    have := hli.disjoint_span_image (s := s1) (t := s1ᶜ) disjoint_compl_right
    simpa only [Set.image_comp] using this

  have hint : ∀ z : Fin d → O, ι z ∈ XC ⊔ X2 := by
    intro z
    have hz : z ∈ span O (e '' s1 ∪ e '' s1ᶜ) := by
      rw [← Set.image_union, Set.union_compl_self, Set.image_univ, e.span_eq]
      exact Submodule.mem_top
    have := toLL_mem_span (LL := LL) hz
    rwa [Set.image_union, Submodule.span_union] at this
  have htop : ∀ y, y ∈ XC ⊔ X2 := by
    intro y
    obtain ⟨a, z, ha, hz⟩ := clear (O := O) LL d y
    exact mem_of_smul _ ha (hz ▸ hint z)

  have hXC_U : XC ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have : e k ∈ N1 := by rw [hS1]; exact Submodule.subset_span ⟨k, hk, rfl⟩
    exact this
  have hU_XC : U ≤ XC := by
    intro u hu
    obtain ⟨a, z, ha, hz⟩ := clear (O := O) LL d u
    have hzN : z ∈ N1 := by
      show ι z ∈ U
      rw [hz]; exact U.smul_of_tower_mem a hu
    rw [hS1] at hzN
    exact mem_of_smul _ ha (hz ▸ toLL_mem_span (LL := LL) hzN)

  have hliS : LinearIndependent O (fun k : ↥S1 => e k) :=
    e.linearIndependent.comp (fun k : ↥S1 => (k : Fin d)) Subtype.val_injective
  have hrangeS : span O (Set.range fun k : ↥S1 => e k) = N1 := by
    rw [hS1]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
  let bC : Basis ↥S1 O ↥N1 := (Basis.span hliS).map (LinearEquiv.ofEq _ _ hrangeS)

  let N2 : Submodule O ↥N1 := ((V ⊔ X2).restrictScalars O).comap (ι.comp N1.subtype)
  have hN2 : Sat N2 := by
    intro a x ha hx
    have h1 : ι ((a • x : ↥N1) : Fin d → O) ∈ V ⊔ X2 := hx
    rw [Submodule.coe_smul, map_smul] at h1
    exact mem_of_smul _ ha h1
  obtain ⟨f, S2, hS2⟩ := adapted bC N2 hN2
  have hfN1 : ∀ i, ((f i : ↥N1) : Fin d → O) ∈ N1 := fun i => (f i).2

  let G : ↥S1 ⊕ {k // k ∉ S1} → (Fin d → O) :=
    Sum.elim (fun i => ((f i : ↥N1) : Fin d → O)) (fun k => e k)
  have hspanf : ∀ x ∈ N1, x ∈ span O (Set.range fun i => ((f i : ↥N1) : Fin d → O)) := by
    intro x hx
    have h := Submodule.mem_map_of_mem (f := N1.subtype) (f.mem_span ⟨x, hx⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  have hGli : LinearIndependent O G := by
    refine LinearIndependent.sum_type (f.linearIndependent.map' N1.subtype (N1.ker_subtype))
      (e.linearIndependent.comp (fun k : {k // k ∉ S1} => (k : Fin d)) Subtype.val_injective) ?_
    have h1 : span O (Set.range fun i => ((f i : ↥N1) : Fin d → O)) ≤ span O (e '' s1) := by
      rw [Submodule.span_le, ← hS1]
      rintro _ ⟨i, rfl⟩
      exact (f i).2
    have h2 : span O (Set.range fun k : {k // k ∉ S1} => e k) = span O (e '' s1ᶜ) := by
      congr 1
      ext x
      constructor
      · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    rw [h2]
    exact (e.linearIndependent.disjoint_span_image disjoint_compl_right).mono_left h1
  have hGsp : ⊤ ≤ span O (Set.range G) := by
    rw [← e.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k ∈ S1
    · have hek : e k ∈ N1 := by rw [hS1]; exact Submodule.subset_span ⟨k, hk, rfl⟩
      refine Submodule.span_mono ?_ (hspanf _ hek)
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  let g0 : Basis (↥S1 ⊕ {k // k ∉ S1}) O (Fin d → O) := Basis.mk hGli hGsp
  have hg0 : ∀ x, g0 x = G x := fun x => Basis.mk_apply hGli hGsp x
  let eq := Fintype.equivFin (↥S1 ⊕ {k // k ∉ S1})
  let g : Basis (Fin (Fintype.card (↥S1 ⊕ {k // k ∉ S1}))) O (Fin d → O) := g0.reindex eq
  have hg : ∀ k, g k = G (eq.symm k) := fun k => by
    simp only [g, Basis.reindex_apply, hg0]
  let R0 : Finset (↥S1 ⊕ {k // k ∉ S1}) :=
    Finset.univ.filter fun x => Sum.elim (fun i => i ∈ S2) (fun _ => True) x
  let R : Finset (Fin (Fintype.card (↥S1 ⊕ {k // k ∉ S1}))) := R0.map eq.toEmbedding
  have hR : ∀ k, k ∈ R ↔ eq.symm k ∈ R0 := by
    intro k
    simp only [R, Finset.mem_map_equiv]
  refine ⟨_, g, R, ?_, ?_, ?_⟩
  ·
    have hRc : R.card ≤ S2.card + (d - S1.card) := by
      have hsub : R0 ⊆ S2.map Function.Embedding.inl ∪ Finset.univ.map Function.Embedding.inr := by
        intro x hx
        rcases x with i | k
        · simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl] at hx
          exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ hx)
        · exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ (Finset.mem_univ _))
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_map, Finset.card_map, Finset.card_univ] at hcard
      have hc2 : Fintype.card {k // k ∉ S1} = d - S1.card := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      rw [Finset.card_map]
      omega
    have hU : finrank LL U ≤ S1.card := by
      have hUe : U = XC := le_antisymm hU_XC hXC_U
      have : XC = span LL (Set.range fun k : ↥S1 => ι (e k)) := by
        show span LL (ι '' (e '' s1)) = _
        congr 1
        ext x
        constructor
        · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
        · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨e k, ⟨k, hk, rfl⟩, rfl⟩
      rw [hUe, this]
      exact (finrank_range_le_card (R := LL) _).trans (by simp)
    have hS2 : S2.card ≤ finrank LL V := by
      let A : Submodule LL (Fin d → LL) := (V ⊔ X2) ⊓ XC
      have hfam : LinearIndependent LL (fun i : ↥S2 => ι ((f i : ↥N1) : Fin d → O)) := by
        have h0 : LinearIndependent O (fun i : ↥S2 => ι ((f i : ↥N1) : Fin d → O)) := by
          have := (f.linearIndependent.map' N1.subtype (N1.ker_subtype)).map' ι
            (LinearMap.ker_eq_bot.2 (toLL_inj LL d))
          exact this.comp (fun i : ↥S2 => (i : ↥S1)) Subtype.val_injective
        exact (LinearIndependent.iff_fractionRing O LL).1 h0
      have hle : span LL (Set.range fun i : ↥S2 => ι ((f i : ↥N1) : Fin d → O)) ≤ A := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨i, hi⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · have : (f i : ↥N1) ∈ N2 := by rw [hS2]; exact Submodule.subset_span ⟨i, hi, rfl⟩
          exact this
        · have : ((f i : ↥N1) : Fin d → O) ∈ span O (e '' s1) := hS1 ▸ (f i).2
          exact toLL_mem_span (LL := LL) this
      have h1 := (finrank_span_eq_card hfam).symm.le.trans (Submodule.finrank_mono hle)
      rw [Fintype.card_coe] at h1
      have hA : finrank LL A ≤ finrank LL V := by
        have hAX : A ⊓ X2 = ⊥ := by
          refine eq_bot_iff.2 fun x hx => ?_
          exact (Submodule.disjoint_def.1 hdisj) x hx.1.2 hx.2
        have e1 := Submodule.finrank_sup_add_finrank_inf_eq A X2
        rw [hAX, finrank_bot, add_zero] at e1
        have e2 : finrank LL ↥(A ⊔ X2) ≤ finrank LL ↥(V ⊔ X2) :=
          Submodule.finrank_mono (sup_le inf_le_left le_sup_right)
        have e3 := Submodule.finrank_add_le_finrank_add_finrank V X2
        omega
      omega
    have hS1d : S1.card ≤ d := by simpa using Finset.card_le_univ S1
    omega
  ·
    intro k hk
    rw [hR] at hk
    rw [hg]
    rcases hx : eq.symm k with i | j
    · have : ((f i : ↥N1) : Fin d → O) ∈ N1 := (f i).2
      exact this
    · exfalso
      apply hk
      rw [hx]
      simp [R0]
  ·
    set P := span LL ((fun k => toLL LL d (g k)) '' (R : Set (Fin _))) with hP
    have hinl : ∀ i ∈ S2, ι ((f i : ↥N1) : Fin d → O) ∈ P := by
      intro i hi
      refine Submodule.subset_span ⟨eq (Sum.inl i), ?_, ?_⟩
      · show eq (Sum.inl i) ∈ R
        rw [hR, Equiv.symm_apply_apply]
        simp [R0, hi]
      · show ι (g (eq (Sum.inl i))) = _
        rw [hg, Equiv.symm_apply_apply]
        rfl
    have hinr : ∀ k (hk : k ∉ S1), ι (e k) ∈ P := by
      intro k hk
      refine Submodule.subset_span ⟨eq (Sum.inr ⟨k, hk⟩), ?_, ?_⟩
      · show eq (Sum.inr ⟨k, hk⟩) ∈ R
        rw [hR, Equiv.symm_apply_apply]
        simp [R0]
      · show ι (g (eq (Sum.inr ⟨k, hk⟩))) = _
        rw [hg, Equiv.symm_apply_apply]
        rfl
    have hX2P : X2 ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact hinr k hk
    intro v hv
    obtain ⟨y, hy, x2, hx2, rfl⟩ := Submodule.mem_sup.1 (htop v)
    refine P.add_mem ?_ (hX2P hx2)
    obtain ⟨a, z, ha, hz⟩ := clear (O := O) LL d y
    have hzN1 : z ∈ N1 := by
      show ι z ∈ U
      rw [hz]; exact U.smul_of_tower_mem a (hXC_U hy)
    have hyV : y ∈ V ⊔ X2 := by
      have : y = (y + x2) - x2 := by abel
      rw [this]
      exact (V ⊔ X2).sub_mem (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hx2)
    have hzN2 : (⟨z, hzN1⟩ : ↥N1) ∈ N2 := by
      show ι z ∈ V ⊔ X2
      rw [hz]; exact (V ⊔ X2).smul_of_tower_mem a hyV
    rw [hS2] at hzN2
    have hzs : z ∈ span O ((fun i => ((f i : ↥N1) : Fin d → O)) '' (S2 : Set ↥S1)) := by
      have h := Submodule.mem_map_of_mem (f := N1.subtype) hzN2
      rw [Submodule.map_span, ← Set.image_comp] at h
      exact h
    have hzP : ι z ∈ P := by
      have h := toLL_mem_span (LL := LL) hzs
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact hinl i hi
    exact mem_of_smul P ha (hz ▸ hzP)

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct Submodule

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem ιV_inj : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : ∀ x, ιV PD (LL := LL) (V := V) x =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ PD.ι_inj hxy

theorem φVB_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ x, φVB PD (LL := LL) (V := V) x = (PD.φ.toLinearMap.lTensor V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [φVB]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ PD.φ_inj hxy

theorem φVB_pow_inj (k : ℕ) :
    Function.Injective ((φVB PD (LL := LL) (V := V)) ^ k : Module.End LL (V ⊗[Qp] B)) := by
  rw [Module.End.coe_pow]
  exact (φVB_inj PD).iterate k

theorem filV_sep (x : V ⊗[Qp] BdR) (h : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  let bV := Basis.ofVectorSpace Qp V
  apply (TensorProduct.equivFinsuppOfBasisLeft bV).injective
  rw [map_zero]
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, Finsupp.coe_zero, Pi.zero_apply]
  apply PD.Fil_sep
  intro a
  have key : ∀ z : V ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp),
      TensorProduct.lid Qp BdR ((bV.coord i).rTensor BdR
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype z))
        ∈ PD.Fil a := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, Submodule.coe_subtype,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
    | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact (PD.Fil a).add_mem hx hy
  obtain ⟨z, hz⟩ := h a
  rw [← hz]
  exact key z

theorem filV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have hle : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    antitone_int_of_succ_le PD.Fil_anti hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ hle, ← LinearMap.id_comp (LinearMap.id : V →ₗ[LL] V),
    TensorProduct.AlgebraTensorModule.map_comp]
  exact LinearMap.range_comp_le_range _ _

theorem filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    refine ⟨a, ?_⟩
    refine ⟨v ⊗ₜ (⟨b, ha⟩ : ↥((PD.Fil a).restrictScalars Qp)), ?_⟩
    simp
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', Submodule.add_mem _ (filV_anti PD (min_le_left a a') ha)
      (filV_anti PD (min_le_right a a') ha')⟩

variable (ρ : Representation LL G V)

theorem fildR_anti {τ : K →ₐ[Qp] LL} {a b : ℤ} (h : a ≤ b) : FildR PD ρ τ b ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD h)

theorem tele_range (g : ℤ → ℤ) (x : ℤ) : ∀ k : ℕ,
    ∑ i ∈ Finset.range k, (g (x + i) - g (x + i + 1)) = g x - g (x + k)
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, tele_range g x k]
    push_cast
    ring_nf

theorem tele (g : ℤ → ℤ) (η : ℕ) :
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, (g a - g (a + 1)) = g (-(η : ℤ)) - g ((η : ℤ) + 1) := by
  have himg : Finset.Icc (-(η : ℤ)) η =
      (Finset.range (2 * η + 1)).image (fun k : ℕ => -(η : ℤ) + k) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(a + η).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun x _ y _ h => by simpa using h), tele_range g _ (2 * η + 1)]
  congr 2
  push_cast
  ring

theorem sum_mult (τ : K →ₐ[Qp] LL) (η : ℕ) :
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ (-(η : ℤ))) : ℤ) - finrank LL ↥(FildR PD ρ τ ((η : ℤ) + 1)) :=
  tele (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) η

theorem fildR_eq_top_of (τ : K →ₐ[Qp] LL) (u : ℤ) (hj : ∀ a, IsJumpV PD ρ τ a → u ≤ a) :
    FildR PD ρ τ u = DdRE PD ρ τ := by
  refine le_antisymm inf_le_left fun x hx => ?_
  obtain ⟨a₀, ha₀⟩ := filV_exh PD (LL := LL) (V := V) x
  rcases le_or_gt u a₀ with h | h
  · exact ⟨hx, filV_anti PD h ha₀⟩
  · have key : ∀ k : ℕ, a₀ + k ≤ u → x ∈ FildR PD ρ τ (a₀ + k) := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.cast_zero, add_zero]; exact Submodule.mem_inf.2 ⟨hx, ha₀⟩
      | succ k ih =>
        intro hk
        push_cast at hk
        have hnj : ¬ IsJumpV PD ρ τ (a₀ + k) := fun hjk => by have := hj _ hjk; omega
        unfold IsJumpV at hnj
        push_cast
        rw [← add_assoc, not_not.mp hnj]
        exact ih (by omega)
    have := key (u - a₀).toNat (by omega)
    rwa [show a₀ + ((u - a₀).toNat : ℤ) = u by omega] at this

theorem fildR_eq_bot_of (τ : K →ₐ[Qp] LL) (u : ℤ) (hj : ∀ a, IsJumpV PD ρ τ a → a < u) :
    FildR PD ρ τ u = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have key : ∀ k : ℕ, x ∈ FildR PD ρ τ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hnj : ¬ IsJumpV PD ρ τ (u + k) := fun hjk => by have := hj _ hjk; omega
      unfold IsJumpV at hnj
      push_cast
      rw [← add_assoc, not_not.mp hnj]
      exact ih
  refine (Submodule.mem_bot LL).2 (filV_sep PD (LL := LL) x fun a => ?_)
  rcases le_or_gt a u with h | h
  · exact filV_anti PD h (Submodule.mem_inf.1 hx).2
  · have := key (a - u).toNat
    have e : u + ((a - u).toNat : ℤ) = a := by omega
    rw [e] at this
    exact (Submodule.mem_inf.1 this).2

theorem fildR_const (τ : K →ₐ[Qp] LL) (u w : ℤ) (huw : u ≤ w)
    (hj : ∀ a, IsJumpV PD ρ τ a → u ≤ a → w ≤ a) : FildR PD ρ τ w = FildR PD ρ τ u := by
  have key : ∀ k : ℕ, u + k ≤ w → FildR PD ρ τ (u + k) = FildR PD ρ τ u := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hnj : ¬ IsJumpV PD ρ τ (u + k) := fun hjk => by
        have := hj _ hjk (by omega); push_cast at hk; omega
      unfold IsJumpV at hnj
      push_cast
      rw [← add_assoc, not_not.mp hnj]
      exact ih (by push_cast at hk; omega)
  have := key (w - u).toNat (by omega)
  rwa [show u + ((w - u).toNat : ℤ) = w by omega] at this

end Per

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Submodule

section Cnt

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_filCris (τ : K →ₐ[Qp] LL) (τ₀ : K₀ →ₐ[Qp] LL)
    (hF : ∀ a, FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ τ₀).map (ιV PD (LL := LL) (V := V)))
    (a : ℤ) :
    finrank LL ↥(FilCris PD ρ a ⊓ DcrisL PD ρ τ₀) = finrank LL ↥(FildR PD ρ τ a) := by
  rw [hF a]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (ιV_inj PD) _)

theorem codim_up (τ : K →ₐ[Qp] LL) (τ₀ : K₀ →ₐ[Qp] LL) (hdim : finrank LL ↥(DdRE PD ρ τ) = finrank LL V)
    (hF : ∀ a, FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ τ₀).map (ιV PD (LL := LL) (V := V)))
    (η b S : ℕ) (hηb : η < b)
    (hJ : JumpsInV PD ρ τ (Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η)) :
    (finrank LL V : ℤ) - finrank LL ↥(FilCris PD ρ b ⊓ DcrisL PD ρ τ₀) =
      ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a := by
  rw [sum_mult PD ρ τ η, finrank_filCris PD ρ τ τ₀ hF]
  have h1 : FildR PD ρ τ (-(η : ℤ)) = DdRE PD ρ τ := by
    refine fildR_eq_top_of PD ρ τ _ fun a ha => ?_
    rcases hJ a ha with h | h
    · have := h.1; omega
    · exact h.1
  have h2 : FildR PD ρ τ b = FildR PD ρ τ ((η : ℤ) + 1) := by
    refine fildR_const PD ρ τ _ _ (by omega) fun a ha hle => ?_
    rcases hJ a ha with h | h
    · exact h.1
    · have := h.2; omega
  rw [h1, h2, hdim]

theorem dim_down (τ : K →ₐ[Qp] LL) (τ₀ : K₀ →ₐ[Qp] LL)
    (hF : ∀ a, FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ τ₀).map (ιV PD (LL := LL) (V := V)))
    (η b S : ℕ) (hηb : η < b)
    (hJ : JumpsInV PD ρ τ (Set.Icc (-(b : ℤ) - S) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η)) :
    (finrank LL ↥(FilCris PD ρ (-(η : ℤ)) ⊓ DcrisL PD ρ τ₀) : ℤ) =
      ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a := by
  rw [sum_mult PD ρ τ η, finrank_filCris PD ρ τ τ₀ hF]
  have h1 : FildR PD ρ τ ((η : ℤ) + 1) = ⊥ := by
    refine fildR_eq_bot_of PD ρ τ _ fun a ha => ?_
    rcases hJ a ha with h | h
    · have := h.2; omega
    · have := h.2; omega
  rw [h1, finrank_bot]
  simp

theorem sum_mult_nonneg (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] (η : ℕ) :
    0 ≤ ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a := by
  rw [sum_mult PD ρ τ η]
  have hle : FildR PD ρ τ ((η : ℤ) + 1) ≤ FildR PD ρ τ (-(η : ℤ)) := fildR_anti PD ρ (by omega)
  have : FiniteDimensional LL ↥(FildR PD ρ τ (-(η : ℤ))) :=
    Submodule.finiteDimensional_of_le (inf_le_left : FildR PD ρ τ (-(η : ℤ)) ≤ DdRE PD ρ τ)
  have := Submodule.finrank_mono hle
  omega

end Cnt

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem cmpD_comb (T : LocLat G Qp LL O) {d : ℕ} (x : Fin d → W.DD T) (hx : ∀ j, x j ∈ W.N T)
    (o : Fin d → O) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (∑ j, o j • x j) =
      ∑ j, algebraMap O LL (o j) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x j) := by
  have hmem : ∑ j, o j • x j ∈ W.N T :=
    Submodule.sum_mem _ fun j _ => (W.N T).smul_of_tower_mem (o j) (hx j)
  unfold Formalism.MainNotions.ArcLiftingSetup.cmpD
  rw [dif_pos hmem]
  have e : (⟨∑ j, o j • x j, hmem⟩ : ↥(W.N T)) = ∑ j, o j • (⟨x j, hx j⟩ : ↥(W.N T)) := by
    ext
    simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [W.cmp_smul, dif_pos (hx j)]

theorem dv_change (T : LocLat G Qp LL O) (e : ℕ) {d d' : ℕ} (b : Fin d → W.DD T)
    (hb : ∀ j, b j ∈ W.N T) (g : Fin d' → Fin d → O) (k : Fin d') :
    Formalism.MainNotions.ArcLiftingSetup.dv W T e (fun k => ∑ j, g k j • b j) (Pi.single k 1) =
      Formalism.MainNotions.ArcLiftingSetup.dv W T e b (fun j => algebraMap O LL (g k j)) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.dv
  rw [Finset.sum_eq_single k (fun m _ hm => by simp [hm]) (by simp),
    Pi.single_eq_same, one_smul, cmpD_comb W T b hb (g k), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem frame_change (T : LocLat G Qp LL O) (i : ZMod n) {d d' : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) (g : Basis (Fin d') O (Fin d → O)) :
    Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i (fun k => ∑ j, g k j • b j) := by
  obtain ⟨hbm, hbu⟩ := hb
  set B : Fin d' → W.DD T := fun k => ∑ j, g k j • b j with hB
  refine ⟨fun k => Relay2.InNΔi_sum W T i _ _ fun j _ => Relay2.InNΔi_osmul W T i _ (hbm j),
    fun x hx => ?_⟩
  obtain ⟨a, ⟨hacond, hxeq⟩, hau⟩ := hbu x hx
  have ha : ∀ j, a j ∈ W.AΔ := fun j => (hacond j).1
  have hax : ∀ j, letE i * a j = a j := fun j => (hacond j).2
  let Q : Fin d → Fin d' → O := fun j k => g.repr (Pi.single j 1) k
  have hQ : ∀ j, ∑ k, Q j k • g k = Pi.single j 1 := fun j => g.sum_repr (Pi.single j 1)
  have hQm : ∀ j m, ∑ k, Q j k * g k m = (Pi.single j 1 : Fin d → O) m := by
    intro j m
    rw [← hQ j, Finset.sum_apply]
    rfl
  have hGQ : ∀ k' k, ∑ m, g k' m * Q m k = if k' = k then 1 else 0 := by
    intro k' k
    have h1 : g k' = ∑ m, g k' m • (Pi.single m 1 : Fin d → O) := by
      funext t
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    have h2 := congrArg (fun w => g.repr w k) h1
    simp only [Basis.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Finsupp.single_apply] at h2
    rw [← h2]
  have hsm : ∀ (o : O) (y : W.DD T), o • y = algebraMap O (LetA O n) o • y :=
    fun o y => (algebraMap_smul (LetA O n) o y).symm
  have hbj : ∀ j, b j = ∑ k, algebraMap O (LetA O n) (Q j k) • B k := by
    intro j
    simp only [hB, hsm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ m, ∑ k, algebraMap O (LetA O n) (Q j k) * algebraMap O (LetA O n) (g k m) =
        algebraMap O (LetA O n) ((Pi.single j 1 : Fin d → O) m) := by
      intro m
      rw [← hQm j m, map_sum]
      simp only [map_mul]
    simp only [← Finset.sum_smul, this]
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [hm]) (by simp)]
    simp
  let a' : Fin d' → LetA O n := fun k => ∑ j, algebraMap O (LetA O n) (Q j k) * a j
  have ha'Δ : ∀ k, a' k ∈ W.AΔ ∧ letE i * a' k = a' k := by
    intro k
    refine ⟨Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (ha j), ?_⟩
    simp only [a', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, hax j]
  have hxa' : x = ∑ k, a' k • B k := by
    calc x = ∑ j, a j • b j := hxeq
      _ = ∑ j, a j • ∑ k, algebraMap O (LetA O n) (Q j k) • B k :=
          Finset.sum_congr rfl fun j _ => by rw [← hbj j]
      _ = _ := by
          simp only [a', Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm]
  refine ⟨a', ⟨ha'Δ, hxa'⟩, fun a'' ⟨ha'', hxa''⟩ => ?_⟩
  let c : Fin d → LetA O n := fun m => ∑ k, a'' k * algebraMap O (LetA O n) (g k m)
  have hc : ∀ m, c m ∈ W.AΔ ∧ letE i * c m = c m := by
    intro m
    refine ⟨Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.mul_mem _ (ha'' k).1 (Subalgebra.algebraMap_mem _ _), ?_⟩
    simp only [c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, (ha'' k).2]
  have hxc : x = ∑ m, c m • b m := by
    rw [hxa'']
    simp only [hB, c, hsm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hca : c = a := hau c ⟨hc, hxc⟩
  funext k
  show a'' k = ∑ j, algebraMap O (LetA O n) (Q j k) * a j
  rw [← hca]
  simp only [c, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hk : ∀ k', ∑ j, algebraMap O (LetA O n) (Q j k) * (a'' k' * algebraMap O (LetA O n) (g k' j)) =
      a'' k' * algebraMap O (LetA O n) (if k' = k then 1 else 0) := by
    intro k'
    rw [← hGQ k' k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  simp only [hk]
  rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
  simp

theorem hor_exists (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) : ∃ sol, Formalism.MainNotions.ArcLiftingSetup.IsHor W T i b sol := by
  have h3 := (hH hA T hT i).2.2.1 d b hb 0 ⟨0, Relay2.InNΔi_zero W T i, (smul_zero _).symm⟩
  choose sol hsol using fun k : Fin d => (h3 (Pi.single k 1)).1
  refine ⟨sol, hb, fun k => ⟨(hsol k).1, ?_⟩⟩
  rw [(hsol k).2]
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [h]

end W

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Submodule Formalism.MainNotions.ArcLiftingSetup

theorem finrank_iSup_le {LL X : Type} [Field LL] [AddCommGroup X] [Module LL X]
    [FiniteDimensional LL X] {ι : Type} (s : Finset ι) (F : ι → Submodule LL X) :
    finrank LL ↥(⨆ i ∈ s, F i) ≤ ∑ i ∈ s, finrank LL ↥(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (⨆ i ∈ insert a s, F i) = F a ⊔ ⨆ i ∈ s, F i := by
      rw [Finset.iSup_insert]
    rw [e]
    exact le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) (Nat.add_le_add_left ih _)

theorem codim_iInf_le {LL X : Type} [Field LL] [AddCommGroup X] [Module LL X]
    [FiniteDimensional LL X] {ι : Type} (s : Finset ι) (F : ι → Submodule LL X) :
    finrank LL X ≤ finrank LL ↥(⨅ i ∈ s, F i) + ∑ i ∈ s, (finrank LL X - finrank LL ↥(F i)) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : (⨅ i ∈ (∅ : Finset ι), F i) = ⊤ :=
      iInf_eq_top.2 fun i => iInf_eq_top.2 fun h => by simp at h
    rw [h, finrank_top]
    simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha]
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (F a) (⨅ i ∈ s, F i)
    have e2 := Submodule.finrank_le (F a ⊔ ⨅ i ∈ s, F i)
    have e3 := Submodule.finrank_le (F a)
    omega

theorem finrank_comap_eq {LL X Y : Type} [Field LL] [AddCommGroup X] [Module LL X]
    [AddCommGroup Y] [Module LL Y] (Φ : X →ₗ[LL] Y) (hΦ : Function.Injective Φ)
    (Z : Submodule LL Y) (hZ : Z ≤ LinearMap.range Φ) :
    finrank LL ↥(Z.comap Φ) = finrank LL ↥Z := by
  have h1 : (Z.comap Φ).map Φ = Z := Submodule.map_comap_eq_of_le hZ
  calc finrank LL ↥(Z.comap Φ) = finrank LL ↥((Z.comap Φ).map Φ) :=
        (Submodule.equivMapOfInjective Φ hΦ _).finrank_eq
    _ = finrank LL ↥Z := by rw [h1]

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem filS_le (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (u : ℤ) :
    FilS W T c s u ≤ DcrisL PD T.ρ (W.emb c) := by
  rintro _ ⟨y, hy, rfl⟩
  have := Formalism.MainNotions.UnusedSlot80.UnivC.φVB_pow_letter W T (c - (s : ZMod n)) s (Submodule.mem_inf.1 hy).2
  rwa [sub_add_cancel] at this

theorem finrank_filS (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (u : ℤ) :
    finrank LL ↥(FilS W T c s u) =
      finrank LL ↥(FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))) :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (φVB_pow_inj PD s) _)).symm

theorem mult_le_lowCount [Fintype (K →ₐ[Qp] LL)] (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hb : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (η : ℕ) :
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hb i) a ≤
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T i η := by
  unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount
  refine Finset.single_le_sum (f := fun τ => ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ a)
    (fun τ _ => ?_) ?_
  · have := ((hDR hb T.V T.ρ T.cont hT).2 τ).1
    exact sum_mult_nonneg PD T.ρ τ η
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Formalism.MainNotions.UnusedSlot80.UnivC.τOver_over W hb i⟩

theorem univFrame_of [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    [Fintype (K →ₐ[Qp] LL)] (hArc : ArcCore W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivFrameCore PD W := by
  intro A m T₂ c hsit
  obtain ⟨hCA, h5, hA, hT, hlow, hc⟩ := hsit
  have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hcrys : IsCrys PD T₂.ρ := hT.1
  obtain ⟨d, b₀, hb₀⟩ := Relay2.frame_exists W T₂ (c - ((A.len c : ℕ) : ZMod n))
    (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA T₂ hcrys).2
  obtain ⟨sol₀, hsol₀⟩ := hor_exists W hH hCA T₂ hcrys _ b₀ hb₀
  have hAC := ((hArc hCA h5 A hA c hc (A.len c) hjL le_rfl).2 T₂ hT).2.2.2 d b₀ sol₀ hsol₀
  obtain ⟨hLI, hSp⟩ := hAC.1
  have hcc : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  rw [hcc] at hSp

  let β : Fin d → T₂.V ⊗[Qp] B := fun k => dv W T₂ (A.len c) b₀ (Pi.single k 1)
  let Φ : (Fin d → LL) →ₗ[LL] T₂.V ⊗[Qp] B := Fintype.linearCombination LL β
  have hβ : ∀ k, β k = ((φVB PD (LL := LL) (V := T₂.V)) ^ A.len c) (cmpD W T₂ (b₀ k)) := by
    intro k
    show dv W T₂ (A.len c) b₀ (Pi.single k 1) = _
    unfold dv
    rw [Finset.sum_eq_single k (fun m _ hm => by simp [hm]) (by simp), Pi.single_eq_same, one_smul]
  have hdvΦ : ∀ c₀, dv W T₂ (A.len c) b₀ c₀ = Φ c₀ := by
    intro c₀
    show _ = ∑ k, c₀ k • β k
    unfold dv
    exact Finset.sum_congr rfl fun k _ => by rw [hβ k]
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h0 : Φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := Fintype.linearIndependent_iff.1 hLI (x - y) h0
    funext k
    have := this k
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  have hΦrange : DcrisL PD T₂.ρ (W.emb c) ≤ LinearMap.range Φ := by
    intro y hy
    rw [← hSp] at hy
    obtain ⟨f, hf⟩ := Submodule.mem_span_range_iff_exists_fun LL |>.1 hy
    exact ⟨f, hf⟩

  let upS : Finset ℕ := (Finset.range (A.len c)).filter fun s =>
    (A.ty (c - (s : ZMod n))).isUp = true
  let downS : Finset ℕ := (Finset.range (A.len c)).filter fun s =>
    (A.ty (c - (s : ZMod n))).isDown = true
  let U' : Submodule LL (Fin d → LL) :=
    ⨅ s ∈ upS, (FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ
  let V' : Submodule LL (Fin d → LL) := ⨆ s ∈ downS, (FilS W T₂ c s (-(A.η : ℤ))).comap Φ
  obtain ⟨d', g, R, hcount, hout, hVR⟩ := split (O := O) LL d U' V'
  let b' : Fin d' → W.DD T₂ := fun k => ∑ j, g k j • b₀ j
  have hb' : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ (c - ((A.len c : ℕ) : ZMod n)) b' :=
    frame_change W T₂ _ b₀ hb₀ g
  obtain ⟨sol', hsol'⟩ := hor_exists W hH hCA T₂ hcrys _ b' hb'
  have hdv' : ∀ k, dv W T₂ (A.len c) b' (Pi.single k 1) = Φ (toLL LL d (g k)) := by
    intro k
    rw [dv_change W T₂ (A.len c) b₀ (fun j => (hb₀.1 j).1.1) g k, hdvΦ]
    rfl

  have hdV : d ≤ finrank LL T₂.V := by
    have hτ := (hDR hCA.1 T₂.V T₂.ρ T₂.cont hcrys).2 (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 c)
    have : FiniteDimensional LL ↥(DdRE PD T₂.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 c)) := hτ.1
    have hli2 : LinearIndependent LL (fun k => ιV PD (LL := LL) (V := T₂.V) (β k)) :=
      hLI.map' (ιV PD (LL := LL) (V := T₂.V)) (LinearMap.ker_eq_bot.2 (ιV_inj PD))
    have hle : span LL (Set.range fun k => ιV PD (LL := LL) (V := T₂.V) (β k)) ≤
        DdRE PD T₂.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 c) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Formalism.MainNotions.UnusedSlot80.UnivC.ι_DdRE T₂.ρ (W.emb c) _ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_alg W hCA.1 c)
        hCA.1.2 ?_
      rw [← hSp]
      exact Submodule.subset_span ⟨k, rfl⟩
    have h1 := (finrank_span_eq_card hli2).symm.le.trans (Submodule.finrank_mono hle)
    rw [Fintype.card_fin] at h1
    exact h1.trans hτ.2.1.le

  have hlev : ∀ s, ∀ τ₀ : K₀ →ₐ[Qp] LL, τ₀ = W.emb (c - (s : ZMod n)) →
      ∀ a, FildR PD T₂.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 (c - (s : ZMod n))) a =
        (FilCris PD T₂.ρ a ⊓ DcrisL PD T₂.ρ τ₀).map (ιV PD (LL := LL) (V := T₂.V)) := by
    intro s τ₀ hτ₀ a
    have := ((hDR hCA.1 T₂.V T₂.ρ T₂.cont hcrys).2
      (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 (c - (s : ZMod n)))).2.2 a
    rw [this, Formalism.MainNotions.UnusedSlot80.UnivC.τOver_over W hCA.1 (c - (s : ZMod n)), hτ₀]

  have hup : ∀ s ∈ upS, d - finrank LL ↥((FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ) ≤ m := by
    intro s hs
    obtain ⟨hsr, hsu⟩ := Finset.mem_filter.1 hs
    obtain ⟨bs, hbs⟩ : ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs := by
      revert hsu; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isUp]
    have hok : A.η < bs := by have := hA.2.2.2.2.1 (c - (s : ZMod n)); rw [hbs] at this; exact this
    have hJ := hT.2 (c - (s : ZMod n)) _ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_over W hCA.1 (c - (s : ZMod n)))
    rw [hbs] at hJ
    have hdim := ((hDR hCA.1 T₂.V T₂.ρ T₂.cont hcrys).2 (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 (c - (s : ZMod n)))).2.1
    have hcu := codim_up PD T₂.ρ _ (W.emb (c - (s : ZMod n))) hdim (hlev s _ rfl) A.η bs A.S hok hJ
    have hml := mult_le_lowCount W hDR hCA.1 T₂ hcrys (c - (s : ZMod n)) A.η
    have hlw := hlow (c - (s : ZMod n)) (by rw [hbs]; rfl)
    have hX : finrank LL ↥((FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ) =
        finrank LL ↥(FilCris PD T₂.ρ (bs : ℤ) ⊓ DcrisL PD T₂.ρ (W.emb (c - (s : ZMod n)))) := by
      rw [finrank_comap_eq Φ hΦinj _ ((filS_le W T₂ c s _).trans hΦrange), finrank_filS, hbs]
      rfl
    rw [hX]
    omega

  have hdown : ∀ s ∈ downS, finrank LL ↥((FilS W T₂ c s (-(A.η : ℤ))).comap Φ) ≤ m := by
    intro s hs
    obtain ⟨hsr, hsu⟩ := Finset.mem_filter.1 hs
    obtain ⟨bs, hbs⟩ : ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs := by
      revert hsu; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isDown]
    have hok : A.η < bs := by have := hA.2.2.2.2.1 (c - (s : ZMod n)); rw [hbs] at this; exact this
    have hJ := hT.2 (c - (s : ZMod n)) _ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_over W hCA.1 (c - (s : ZMod n)))
    rw [hbs] at hJ
    have hcd := dim_down PD T₂.ρ _ (W.emb (c - (s : ZMod n))) (hlev s _ rfl) A.η bs A.S hok hJ
    have hml := mult_le_lowCount W hDR hCA.1 T₂ hcrys (c - (s : ZMod n)) A.η
    have hlw := hlow (c - (s : ZMod n)) (by rw [hbs]; rfl)
    have hX : finrank LL ↥((FilS W T₂ c s (-(A.η : ℤ))).comap Φ) =
        finrank LL ↥(FilCris PD T₂.ρ (-(A.η : ℤ)) ⊓ DcrisL PD T₂.ρ (W.emb (c - (s : ZMod n)))) := by
      rw [finrank_comap_eq Φ hΦinj _ ((filS_le W T₂ c s _).trans hΦrange), finrank_filS]
    rw [hX]
    omega
  have hro : upS.card + downS.card = Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c := by
    unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext s
      simp only [upS, downS, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨h1, ?_⟩; revert h2; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isUp, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
        · refine ⟨h1, ?_⟩; revert h2; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isDown, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
      · rintro ⟨h1, h2⟩
        revert h2; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isUp, Formalism.MainNotions.LocalTheoryWindows.LT.isDown, Formalism.MainNotions.LocalTheoryWindows.LT.thick, h1]
    · rw [Finset.disjoint_filter]
      intro s _ h1 h2
      revert h1 h2; cases A.ty (c - (s : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.isUp, Formalism.MainNotions.LocalTheoryWindows.LT.isDown]
  refine ⟨d', b', sol', R, hsol', ?_, ?_, ?_⟩
  ·
    have hU := codim_iInf_le upS fun s => (FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ
    have hV := finrank_iSup_le downS fun s => (FilS W T₂ c s (-(A.η : ℤ))).comap Φ
    rw [Module.finrank_fin_fun] at hU
    have hU2 : ∑ s ∈ upS, (d - finrank LL ↥((FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ))
        ≤ upS.card * m := by
      simpa using Finset.sum_le_card_nsmul upS _ m hup
    have hV2 : ∑ s ∈ downS, finrank LL ↥((FilS W T₂ c s (-(A.η : ℤ))).comap Φ) ≤ downS.card * m := by
      simpa using Finset.sum_le_card_nsmul downS _ m hdown
    have : R.card ≤ (upS.card + downS.card) * m := by
      have := hcount
      simp only [U', V'] at this
      nlinarith
    rw [← hro]
    linarith
  ·
    intro k hk s hs bs hty
    have hsU : s ∈ upS := Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, by rw [hty]; rfl⟩
    have h1 : toLL LL d (g k) ∈ U' := hout k hk
    have h2 : toLL LL d (g k) ∈ (FilS W T₂ c s ((A.ty (c - (s : ZMod n))).size)).comap Φ :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h1 s) hsU
    rw [hty] at h2
    rw [hdv' k]
    exact h2
  ·
    intro s hs bs hty x hx
    have hsD : s ∈ downS := Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, by rw [hty]; rfl⟩
    obtain ⟨y, rfl⟩ := hΦrange (filS_le W T₂ c s _ hx)
    have hyV : y ∈ V' := (le_iSup₂ (f := fun s (_ : s ∈ downS) =>
      (FilS W T₂ c s (-(A.η : ℤ))).comap Φ) s hsD) hx
    have hy := hVR hyV
    have hm := Submodule.mem_map_of_mem (f := Φ) hy
    rw [Submodule.map_span, Set.image_image] at hm
    have hfun : (fun k => dv W T₂ (A.len c) b' (Pi.single k 1)) = fun k => Φ (toLL LL d (g k)) :=
      funext hdv'
    rw [hfun]
    exact hm

end Main

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup

section Sec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)

theorem lA_mem : lA W ∈ W.AΔ := W.AΔ.natCast_mem _

omit [TopologicalSpace G] in
theorem lin_sub_id {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (u Λ : R)
    (κ1 κ1' κ2 κ2' : ℕ) (x y S1 S2 : M) :
    u ^ (κ1' + κ2') • (u ^ (κ1 + κ2) • Λ • (x - y) - (u ^ κ2 • S1 - u ^ κ1 • S2)) =
      u ^ (κ2' + κ2) • (u ^ κ1' • (u ^ κ1 • Λ • x - S1)) -
        u ^ (κ1' + κ1) • (u ^ κ2' • (u ^ κ2 • Λ • y - S2)) := by
  module

omit [TopologicalSpace G] in
theorem lin_γ_id {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (u w' : R) (κ κ' : ℕ)
    (P S2 S3 : M) :
    u ^ κ' • (u ^ κ • (w' • P) - (w' • S2 - S3)) = w' • (u ^ κ' • (u ^ κ • P - S2)) + u ^ κ' • S3 := by
  module

theorem horTr_unique (hinj : Function.Injective (algebraMap O LL)) {R κ : ℕ} {k : Fin d}
    {x x' : W.DD T} (h : IsHorTr W T b sol R κ k x) (h' : IsHorTr W T b sol R κ k x') : x = x' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have : y r = y' r := funext fun m => hinj (by rw [hy r hr' m, hy' r hr' m])
  rw [this]

theorem horTr_scale {R κ : ℕ} {k : Fin d} {x : W.DD T} (h : IsHorTr W T b sol R κ k x) (t : ℕ) :
    IsHorTr W T b sol R (κ + t) k (lA W ^ t • x) := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨fun r m => ((PD.p : ℕ) : O) ^ t * y r m, fun r hr m => ?_, ?_⟩
  · rw [map_mul, hy r hr m, map_pow, map_natCast, pow_add]; ring
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_comm, ← Relay2.lsmul_eq W T t]
    congr 1
    unfold Formalism.MainNotions.LiftingTheory.vecB
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]

theorem γ_horTr {c' : ZMod n} {R κ : ℕ} {k : Fin d} (hs : Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k))
    {x : W.DD T} (h : IsHorTr W T b sol R κ k x) :
    ∃ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c' x' ∧ W.γ T x - x = W.π₀ ^ R • x' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨x', hx', he⟩ := hs R κ y hy
  exact ⟨x', hx', by rw [smul_zero, sub_zero] at he; exact he⟩

variable {T b sol}

theorem repVV_smul {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) {t : LetA O n} (ht : t ∈ W.AΔ) :
    RepVV W T c' e M Λ b sol (t • x) (fun k => algebraMap (LetA O n) W.EE t * f k) := by
  obtain ⟨κ, κ', Hh, a, hHh, ha, hD⟩ := h
  refine ⟨κ, κ', Hh, fun k => t * a k, hHh, fun k => ⟨W.AΔ.mul_mem ht (ha k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha k).2]; ring
  · have e1 : lA W ^ κ' • (lA W ^ κ • Λ • t • x - ∑ k, (t * a k) • ((W.φD T) ^ e) (Hh k)) =
        t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, smul_smul]
      congr 1
      · congr 1; ring
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1; ring
    rw [e1]
    exact Relay2.inMultiple_smul W T c' e _ ht hD

theorem repVV_sub (hinj : Function.Injective (algebraMap O LL)) {c' : ZMod n} {e M : ℕ}
    {Λ : LetA O n} {x y : W.DD T} {f g : Fin d → W.EE}
    (h1 : RepVV W T c' e M Λ b sol x f) (h2 : RepVV W T c' e M Λ b sol y g) :
    RepVV W T c' e M Λ b sol (x - y) (f - g) := by
  obtain ⟨κ1, κ1', H1, a1, hH1, ha1, hD1⟩ := h1
  obtain ⟨κ2, κ2', H2, a2, hH2, ha2, hD2⟩ := h2
  have hH : ∀ k, lA W ^ κ1 • H2 k = lA W ^ κ2 • H1 k := by
    intro k
    have e1 := horTr_scale W T b sol (hH1 k) κ2
    have e2 := horTr_scale W T b sol (hH2 k) κ1
    rw [add_comm κ2 κ1] at e2
    exact horTr_unique W T b sol hinj e2 e1
  refine ⟨κ1 + κ2, κ1' + κ2', fun k => lA W ^ κ2 • H1 k, fun k => a1 k - a2 k,
    fun k => by simpa using horTr_scale W T b sol (hH1 k) κ2,
    fun k => ⟨W.AΔ.sub_mem (ha1 k).1 (ha2 k).1, ?_⟩, ?_⟩
  · rw [Pi.sub_apply, mul_sub, (ha1 k).2, (ha2 k).2, map_sub]
  · set S1 := ∑ k, a1 k • ((W.φD T) ^ e) (H1 k)
    set S2 := ∑ k, a2 k • ((W.φD T) ^ e) (H2 k)
    have hS : ∑ k, (a1 k - a2 k) • ((W.φD T) ^ e) (lA W ^ κ2 • H1 k) =
        lA W ^ κ2 • S1 - lA W ^ κ1 • S2 := by
      simp only [S1, S2, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_smul]
      congr 1
      · rw [Relay2.φpow_lsmul, smul_comm]
      · rw [← hH k, Relay2.φpow_lsmul, smul_comm]
    have e1 : lA W ^ (κ1' + κ2') • (lA W ^ (κ1 + κ2) • Λ • (x - y) -
        ∑ k, (a1 k - a2 k) • ((W.φD T) ^ e) (lA W ^ κ2 • H1 k)) =
        lA W ^ (κ2' + κ2) • (lA W ^ κ1' • (lA W ^ κ1 • Λ • x - S1)) -
          lA W ^ (κ1' + κ1) • (lA W ^ κ2' • (lA W ^ κ2 • Λ • y - S2)) := by
      rw [hS]
      exact lin_sub_id (lA W) Λ κ1 κ1' κ2 κ2' x y S1 S2
    rw [e1]
    exact Relay2.inMultiple_sub W T c' e _ (Relay2.inMultiple_smul W T c' e _ (W.AΔ.pow_mem (lA_mem W) _) hD1)
      (Relay2.inMultiple_smul W T c' e _ (W.AΔ.pow_mem (lA_mem W) _) hD2)

theorem repVV_γ {c' : ZMod n} {e M : ℕ} {Λ : LetA O n}
    (hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k))
    (hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c' x' →
      InFP W T c' e (W.π₀ * Λ ^ 2) (((W.φD T) ^ e) (W.π₀ ^ M • x')))
    {w w' : LetA O n} (hw : w ∈ W.AΔ) (hw' : w' ∈ W.AΔ) (hww : w' * w = 1)
    (hΛ : W.γA W.gam Λ = w * Λ)
    (hπΛ : ∃ u, W.γA W.gam (W.π₀ * Λ ^ 2) = u * (W.π₀ * Λ ^ 2) ∧ u ∈ W.AΔ)
    {x : W.DD T} {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (W.γ T x) (fun k => W.γE W.gam (f k)) := by
  obtain ⟨κ, κ', Hh, a, hHh, ha, hD⟩ := h
  refine ⟨κ, κ', Hh, fun k => w' * W.γA W.gam (a k), hHh,
    fun k => ⟨W.AΔ.mul_mem hw' (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam (ha k).1), ?_⟩, ?_⟩
  · have h1 := congrArg (W.γE W.gam) (ha k).2
    rw [map_mul, W.γE_ext, W.γE_ext] at h1
    change algebraMap (LetA O n) W.EE (W.γA W.gam Λ) * W.γE W.gam (f k) =
      algebraMap (LetA O n) W.EE (W.γA W.gam (a k)) at h1
    rw [hΛ] at h1
    calc algebraMap (LetA O n) W.EE Λ * W.γE W.gam (f k)
        = algebraMap (LetA O n) W.EE (w' * w) * (algebraMap (LetA O n) W.EE Λ * W.γE W.gam (f k)) := by
          rw [hww, map_one, one_mul]
      _ = algebraMap (LetA O n) W.EE w' *
          (algebraMap (LetA O n) W.EE (w * Λ) * W.γE W.gam (f k)) := by
          simp only [map_mul]; ring
      _ = _ := by rw [h1, map_mul]
  ·
    have hX : InFP W T c' e (W.π₀ * Λ ^ 2)
        (W.γ T (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k)))) :=
      Relay2.InFP_γ W T c' e hπΛ hD
    have hY : InFP W T c' e (W.π₀ * Λ ^ 2) (lA W ^ κ' • ∑ k, (w' * W.γA W.gam (a k)) •
        (((W.φD T) ^ e) (W.γ T (Hh k)) - ((W.φD T) ^ e) (Hh k))) := by
      refine Relay2.inMultiple_smul W T c' e _ (W.AΔ.pow_mem (lA_mem W) _)
        (Relay2.inMultiple_sum W T c' e _ _ _ fun k _ => ?_)
      refine Relay2.inMultiple_smul W T c' e _ (W.AΔ.mul_mem hw' (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam (ha k).1)) ?_
      obtain ⟨x', hx', he⟩ := γ_horTr W T b sol (hsol k) (hHh k)
      rw [← map_sub, he]
      exact hJJ x' hx'
    have hγD : W.γ T (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) =
        lA W ^ κ' • (lA W ^ κ • ((w * Λ) • W.γ T x) -
          ∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (W.γ T (Hh k))) := by
      rw [Relay2.γ_lsmul, map_sub, Relay2.γ_lsmul, map_sum]
      show lA W ^ κ' • (lA W ^ κ • W.γD T W.gam (Λ • x) -
        ∑ k, W.γD T W.gam (a k • ((W.φD T) ^ e) (Hh k))) = _
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hΛ]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, Relay2.γ_φpow]
      rfl
    set P := (w * Λ) • W.γ T x with hP
    have hPΛ : Λ • W.γ T x = w' • P := by
      rw [hP, smul_smul, ← mul_assoc, hww, one_mul]
    set S1 := ∑ k, (w' * W.γA W.gam (a k)) • ((W.φD T) ^ e) (Hh k)
    set S2 := ∑ k, W.γA W.gam (a k) • ((W.φD T) ^ e) (W.γ T (Hh k))
    set S3 := ∑ k, (w' * W.γA W.gam (a k)) •
        (((W.φD T) ^ e) (W.γ T (Hh k)) - ((W.φD T) ^ e) (Hh k))
    have hS : S1 = w' • S2 - S3 := by
      simp only [S1, S2, S3, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_sub, smul_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      abel
    have e1 : lA W ^ κ' • (lA W ^ κ • Λ • W.γ T x - S1) =
        w' • (lA W ^ κ' • (lA W ^ κ • P - S2)) + lA W ^ κ' • S3 := by
      rw [hPΛ, hS]
      exact lin_γ_id (lA W) w' κ κ' P S2 S3
    show InFP W T c' e (W.π₀ * Λ ^ 2) (lA W ^ κ' • (lA W ^ κ • Λ • W.γ T x - S1))
    rw [e1]
    refine Relay2.inMultiple_add W T c' e _ (Relay2.inMultiple_smul W T c' e _ hw' ?_) hY
    rw [← hγD]
    exact hX

end Sec

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup

section Lift

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem lam_mem (A : ArcP n) (a : ZMod n) (e : ℕ) : abelian₂ W A a e ∈ W.AΔ :=
  W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s) _

theorem lam_unit (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W A a e)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  unfold abelian₂
  rw [map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun s _ => ?_
  rw [map_pow]
  exact (Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)).pow _

theorem lam_cancel (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (A : ArcP n) (a : ZMod n) (e : ℕ)
    (T : LocLat G Qp LL O) {z z' : W.DD T} (h : abelian₂ W A a e • z = abelian₂ W A a e • z') : z = z' := by
  rw [← algebraMap_smul W.EE (abelian₂ W A a e) z, ← algebraMap_smul W.EE (abelian₂ W A a e) z'] at h
  exact ((lam_unit W hR A a e).smul_left_cancel).1 h

theorem lam_γ (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    ∃ w ∈ W.AΔ, ∃ w' ∈ W.AΔ, w' * w = 1 ∧ W.γA W.gam (abelian₂ W A a e) = w * abelian₂ W A a e := by
  choose r hr r' hr' hrr hγ using hS
  refine ⟨∏ s ∈ Finset.range e, r s ^ A.Hs a e s,
    W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (hr s) _,
    ∏ s ∈ Finset.range e, r' s ^ A.Hs a e s,
    W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (hr' s) _, ?_, ?_⟩
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [← mul_pow, mul_comm, hrr s, one_pow]
  · unfold abelian₂
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, hγ s, mul_pow]

theorem jj_lam [IsDomain O] (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (h5 : 5 ≤ PD.p)
    (A : ArcP n) (hA : A.OK) (a : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (c' : ZMod n)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c' x) :
    InFP W T c' e (W.π₀ * abelian₂ W A a e ^ 2) (((W.φD T) ^ e) (W.π₀ ^ A.M PD.p • x)) := by
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hM : 2 * A.h ≤ (PD.p - 1) * A.M PD.p := (Formalism.MainNotions.UnusedSlot80.ArcC.two_h_lt A h5).le
  have h1 := Relay2.phij_pi0pow W T c' hπ (Formalism.MainNotions.LiftingTheory.frobenius_pow_uniformizer_factorisation W hR) e (2 * A.h) (A.M PD.p) hM hx
  have hM1 := Relay2.M_pos A PD.p
  let t : LetA O n := W.π₀ ^ (A.M PD.p - 1) *
    ∏ s ∈ Finset.range e, ps W s ^ (2 * A.h - 2 * A.Hs a e s)
  have ht : t ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hπ _)
    (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s) _)
  have hJ : Formalism.MainNotions.LiftingTheory.JJ W e (2 * A.h) (A.M PD.p) = (W.π₀ * abelian₂ W A a e ^ 2) * t := by
    unfold Formalism.MainNotions.LiftingTheory.JJ abelian₂
    have e1 : W.π₀ ^ A.M PD.p = W.π₀ * W.π₀ ^ (A.M PD.p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hM1]
    have e2 : ∏ k ∈ Finset.range e, Formalism.MainNotions.LiftingTheory.pk W k ^ (2 * A.h) =
        (∏ s ∈ Finset.range e, ps W s ^ A.Hs a e s) ^ 2 *
          ∏ s ∈ Finset.range e, ps W s ^ (2 * A.h - 2 * A.Hs a e s) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs := Formalism.MainNotions.UnusedSlot80.ArcC.hs_le_h A hA a e s
      rw [← pow_mul, ← pow_add]
      show ps W s ^ (2 * A.h) = _
      congr 1
      omega
    rw [e1, e2]
    ring
  obtain ⟨y, hy, hxy⟩ := h1
  refine ⟨t • y, Relay2.Pp_smul W T c' e ht y hy, ?_⟩
  rw [hxy, hJ, mul_smul]

theorem univLift_of [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    [Fintype (K →ₐ[Qp] LL)] (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W)
    (hP : ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivLiftCore PD W := by
  intro A m T₂ c hsit d b sol Rst hFO f hf hinv
  obtain ⟨hCA, h5, hA, hT, hlow, hc⟩ := hsit
  have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hcc : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hAC := (hArc hCA h5 A hA c hc (A.len c) hjL le_rfl).2 T₂ hT
  simp only [hcc] at hAC
  obtain ⟨hP1, hP2, -, hF⟩ := hAC
  have hhor := hFO.1
  obtain ⟨-, -, hlift, -, hNL, hzero, -⟩ := hF d b sol hhor
  set Λ := abelian₂ W A c (A.len c) with hΛdef
  set c' := c - ((A.len c : ℕ) : ZMod n) with hc'
  have hΛmem : Λ ∈ W.AΔ := lam_mem W A c (A.len c)
  obtain ⟨u, huP, huR⟩ := hlift f hf
  obtain ⟨p0, hp0, hup0⟩ := huP
  rw [one_smul] at hup0

  have hlet : InLet W T₂ c u := by
    show (letE c : LetA O n) • u = u
    refine lam_cancel W hR A c (A.len c) T₂ ?_
    rw [smul_comm, hup0]
    have := Relay2.Pp_letter W T₂ c' (A.len c) p0 hp0
    rwa [hcc] at this
  have hΔ : IsΔ W T₂ u := by
    intro δ hδ
    refine lam_cancel W hR A c (A.len c) T₂ ?_
    have h1 : W.γD T₂ δ (Λ • u) = Λ • W.γD T₂ δ u := by
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hΛmem δ hδ]
    rw [← h1, hup0, Relay2.Pp_Δ W T₂ c' (A.len c) p0 hp0 δ hδ]

  obtain ⟨w, hw, w', hw', hww, hγΛ⟩ := lam_γ W hS A c (A.len c)
  obtain ⟨u0, hu0, hγπ⟩ := hP W.gam
  have hπΛ : ∃ t, W.γA W.gam (W.π₀ * Λ ^ 2) = t * (W.π₀ * Λ ^ 2) ∧ t ∈ W.AΔ :=
    ⟨u0 * w ^ 2, by rw [map_mul, map_pow, hγπ, hγΛ]; ring, W.AΔ.mul_mem hu0 (W.AΔ.pow_mem hw _)⟩
  have hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x' →
      InFP W T₂ c' (A.len c) (W.π₀ * Λ ^ 2) (((W.φD T₂) ^ A.len c) (W.π₀ ^ A.M PD.p • x')) :=
    fun x' hx' => jj_lam W hR h5 A hA c (A.len c) T₂ c' hx'
  have hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T₂ c' b 0 (sol k) := fun k => (hhor.2 k).1
  have hγu := repVV_γ W hsol hJJ hw hw' hww hγΛ hπΛ huR
  obtain ⟨g, hgNL, hg⟩ := hinv
  obtain ⟨y, hyN, hyR⟩ := hNL g hgNL
  have hπy := repVV_smul W hyR hπ
  have hz := repVV_sub W hinj (repVV_sub W hinj hγu huR) hπy
  have hz0 : (((fun k => W.γE W.gam (lE W (A.σ PD.p) * f k)) - fun k => lE W (A.σ PD.p) * f k) -
      fun k => algebraMap (LetA O n) W.EE W.π₀ * (lE W (A.σ PD.p) * g k)) = 0 := by
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply, map_mul]
    have hl : W.γE W.gam (lE W (A.σ PD.p)) = lE W (A.σ PD.p) := by
      unfold lE; rw [map_pow, map_natCast]
    rw [hl, ← mul_sub, hg k]
    ring
  rw [hz0] at hz

  have hγΛu : InFP W T₂ c' (A.len c) 1 (Λ • W.γ T₂ u) := by
    have h1 : Λ • W.γ T₂ u = w' • W.γ T₂ (Λ • u) := by
      show _ = w' • W.γD T₂ W.gam (Λ • u)
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hγΛ, smul_smul, ← mul_assoc, hww, one_mul]
      rfl
    refine ⟨w' • W.γ T₂ p0, Relay2.Pp_smul W T₂ c' _ hw' _ (Relay2.Pp_γ W T₂ c' _ p0 hp0), ?_⟩
    rw [one_smul, h1, hup0]
  have hΛu : InFP W T₂ c' (A.len c) 1 (Λ • u) := ⟨p0, hp0, by rw [one_smul, hup0]⟩
  have hΛy : InFP W T₂ c' (A.len c) 1 (Λ • (W.π₀ • y)) := by
    rw [smul_comm]
    exact Relay2.inMultiple_smul W T₂ c' _ _ hπ (hP2 y hyN)
  have hΛz : InFP W T₂ c' (A.len c) 1 (Λ • (W.γ T₂ u - u - W.π₀ • y)) := by
    rw [smul_sub, smul_sub]
    exact Relay2.inMultiple_sub W T₂ c' _ _ (Relay2.inMultiple_sub W T₂ c' _ _ hγΛu hΛu) hΛy
  obtain ⟨p1, hp1, hzp⟩ := hzero _ hΛz hz
  obtain ⟨y2, hy2, hy2c, hy2e⟩ := hP1 p1 hp1
  obtain ⟨y1, hy1, hy1c, hy1e⟩ := hyN
  rw [one_smul] at hy2e hy1e
  refine ⟨u, ⟨hlet, hΔ, y1 + y2, (W.NΔ T₂).add_mem hy1 hy2, ?_, ?_⟩, ⟨p0, hp0, by rw [one_smul, hup0]⟩,
    huR⟩
  · rw [smul_add, hy1c, hy2c]
  · have : W.γ T₂ u - u = (W.γ T₂ u - u - W.π₀ • y) + W.π₀ • y := by abel
    rw [this, hzp, mul_smul, hy2e, hy1e, smul_add, add_comm]

end Lift

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup

theorem frame_inv_poly2 {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (p : ℕ)
    (hinj : Function.Injective (algebraMap O LL)) {d : ℕ}
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ₁ κ₂ : ℕ)
    (yy : Fin d → ℕ → Fin d → O)
    (hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (p : LL) ^ κ₁ * sol k r m)
    (zz : ℕ → Fin d → Fin d → O)
    (hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (p : LL) ^ κ₂ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m))
    {R : Type} [CommRing R] [Algebra O R] (Y : R) (k k' : Fin d) :
    ∃ ρ : Polynomial O, ∑ m, (∑ r ∈ Finset.range M, algebraMap O R (zz r k m) * Y ^ r) *
        (∑ r ∈ Finset.range M, algebraMap O R (yy k' r m) * Y ^ r) =
      algebraMap O R (((p : ℕ) : O) ^ (κ₁ + κ₂) * if k = k' then 1 else 0) +
        Y ^ M * Polynomial.aeval Y ρ := by
  set Hps : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hHps
  have hdet : IsUnit Hps.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (PowerSeries.constantCoeff : PowerSeries LL →+* LL).mapMatrix Hps = 1 := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHps, Matrix.of_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk, hsol0,
        Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hinv : Hps⁻¹ * Hps = 1 := Matrix.nonsing_inv_mul Hps hdet
  have hcoef : ∀ t, ∑ m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t,
      PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m = if t = 0 ∧ k = k' then 1 else 0 := by
    intro t
    have h := congrArg (fun Q : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff t (Q k k')) hinv
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, hHps, Matrix.of_apply,
      PowerSeries.coeff_mk] at h
    rw [h, Matrix.one_apply]
    by_cases hm : k = k'
    · by_cases ht : t = 0
      · subst ht; simp [hm]
      · simp [hm, ht, PowerSeries.coeff_one]
    · simp [hm]
  let GP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (zz r k m) * Polynomial.X ^ r
  let HP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (yy k' r m) * Polynomial.X ^ r
  have hGPc : ∀ m i, (GP m).coeff i = if i < M then zz i k m else 0 := by
    intro m i
    simp only [GP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hHPc : ∀ m i, (HP m).coeff i = if i < M then yy k' i m else 0 := by
    intro m i
    simp only [HP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  set cst : O := ((p : ℕ) : O) ^ (κ₁ + κ₂) * if k = k' then 1 else 0 with hcst
  set Q : Polynomial O := ∑ m, GP m * HP m - Polynomial.C cst with hQdef
  have hQ : ∀ t < M, Q.coeff t = 0 := by
    intro t ht
    apply hinj
    rw [map_zero, hQdef, Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C, map_sub,
      map_sum]
    have hk : ∀ m, algebraMap O LL ((GP m * HP m).coeff t) = (p : LL) ^ (κ₁ + κ₂) *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m := by
      intro m
      rw [Polynomial.coeff_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hGPc, hHPc, if_pos (by omega), if_pos (by omega), map_mul, hzz x.1 (by omega),
        hyy k' x.2 (by omega), pow_add]
      ring
    rw [Finset.sum_congr rfl fun m _ => hk m, ← Finset.mul_sum, hcoef t, hcst]
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hm : k = k' <;> simp [hm]
    · simp [ht0]
  obtain ⟨ρ, hρ⟩ := (Polynomial.X_pow_dvd_iff).2 hQ
  refine ⟨ρ, ?_⟩
  have h := congrArg (Polynomial.aeval Y) hρ
  simp only [hQdef, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, GP, HP,
    Polynomial.aeval_X] at h
  rw [← h]
  ring

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section Uq

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem frame_indep (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hq : IsUnit (algebraMap (LetA O n) W.EE W.q)) (c' : ZMod n)
    {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ)
    (γ : Fin d → LetA O n) (h : ∑ m, γ m • ((W.φD T) ^ e) (b m) = 0) :
    ∀ m, γ m * letE (c' + (e : ZMod n)) = 0 := by
  obtain ⟨⟨r, Bb, hB, huniq, hΔ⟩, -⟩ := hmod
  have hli := Formalism.MainNotions.UnusedSlot80.SatPW.linInd_φ_pow W T hT hs Bb hB huniq hq e
  choose α hα hbα using fun m => hΔ (b m) (hb.1 m).1
  have hBc : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c' ((letE c' : LetA O n) • Bb j) := by
    intro j
    refine Relay2.InNΔi_of W T c' (Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T
      (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c') (hB j)) ?_
    rw [smul_smul, letE_mul_self]
  choose β hβ hBβ using fun j => (hb.2 _ (hBc j)).exists

  have hcomp : ∀ m m'', letE c' * ∑ j, α m j * β j m'' =
      if m'' = m then (letE c' : LetA O n) else 0 := by
    intro m
    have hbm : b m = ∑ m', (letE c' * ∑ j, α m j * β j m') • b m' := by
      have h1 : b m = (letE c' : LetA O n) • b m := (Relay2.InNΔi_letter W T c' (hb.1 m)).symm
      conv_lhs => rw [h1, hbα m, Finset.smul_sum]
      simp only [smul_comm (letE c' : LetA O n) (α m _), hBβ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      linear_combination (-(α m j)) * (hβ j m').2
    have hc1 : ∀ m', (letE c' * ∑ j, α m j * β j m') ∈ W.AΔ ∧
        letE c' * (letE c' * ∑ j, α m j * β j m') = letE c' * ∑ j, α m j * β j m' := by
      intro m'
      refine ⟨W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c')
        (W.AΔ.sum_mem fun j _ => W.AΔ.mul_mem (hα m j) (hβ j m').1), ?_⟩
      rw [← mul_assoc, letE_mul_self]
    have hc2 : ∀ m', (if m' = m then (letE c' : LetA O n) else 0) ∈ W.AΔ ∧
        letE c' * (if m' = m then (letE c' : LetA O n) else 0) =
          if m' = m then (letE c' : LetA O n) else 0 := by
      intro m'
      split_ifs
      · exact ⟨Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c', letE_mul_self _⟩
      · exact ⟨W.AΔ.zero_mem, mul_zero _⟩
    have hbm2 : b m = ∑ m', (if m' = m then (letE c' : LetA O n) else 0) • b m' := by
      rw [Finset.sum_eq_single m (fun m' _ hm' => by simp [hm']) (by simp), if_pos rfl]
      exact (Relay2.InNΔi_letter W T c' (hb.1 m)).symm
    have := (hb.2 (b m) (hb.1 m)).unique ⟨hc1, hbm⟩ ⟨hc2, hbm2⟩
    exact fun m'' => congrFun this m''

  have hcoef : ∀ j, ∑ m, γ m * (W.φA ^ e) (α m j) = 0 := by
    have h2 : ∑ j, (∑ m, γ m * (W.φA ^ e) (α m j)) • ((W.φD T) ^ e) (Bb j) = 0 := by
      rw [← h]
      simp only [hbα, map_sum, Relay2.φpow_smul, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    have h3 : ∑ j, algebraMap (LetA O n) W.EE (∑ m, γ m * (W.φA ^ e) (α m j)) •
        ((W.φD T) ^ e) (Bb j) = 0 := by
      simpa only [algebraMap_smul] using h2
    intro j
    have := Fintype.linearIndependent_iff.1 hli _ h3 j
    exact W.EE_inj (by rw [this, map_zero])
  intro m''
  have h4 : ∑ j, (∑ m, γ m * (W.φA ^ e) (α m j)) * (W.φA ^ e) (β j m'') = 0 := by
    simp only [hcoef, zero_mul, Finset.sum_const_zero]
  have h5 : ∑ m, γ m * (W.φA ^ e) (∑ j, α m j * β j m'') = 0 := by
    rw [← h4]
    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have h6 := congrArg (fun z => (W.φA ^ e) (letE c' : LetA O n) * z) h5
  simp only [mul_zero, Finset.mul_sum] at h6
  have h7 : ∀ m, (W.φA ^ e) (letE c' : LetA O n) * (γ m * (W.φA ^ e) (∑ j, α m j * β j m'')) =
      γ m * (W.φA ^ e) (if m'' = m then (letE c' : LetA O n) else 0) := by
    intro m
    rw [← hcomp m m'', map_mul]
    ring
  simp only [h7] at h6
  rw [Finset.sum_eq_single m'' (fun m _ hm => by simp [Ne.symm hm]) (by simp), if_pos rfl,
    Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE] at h6
  exact h6

end Uq

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section Uq3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem upi_D (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.SatW.UPi PD.p (W.π₀ * abelian₂ W A a e ^ 2) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3).mul ((Formalism.MainNotions.UnusedSlot80.SatW.UPi.prod _ _ fun s _ =>
    (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s).pow _).pow 2)

theorem sec_zero [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (e : ℕ)
    (hje : A.j ≤ e) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hq : IsUnit (algebraMap (LetA O n) W.EE W.q))
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol)
    {h : Fin d → W.EE} {a₀ : ZMod n} (ha₀ : c' + (e : ZMod n) = a₀)
    (hz : RepVV W T c' e (A.M PD.p) (abelian₂ W A a₀ e) b sol 0 h) :
    ∀ k, ∃ t ∈ W.AΔ, algebraMap (LetA O n) W.EE (letE a₀) *
      (algebraMap (LetA O n) W.EE (abelian₂ W A a₀ e) * h k) =
      algebraMap (LetA O n) W.EE (letE a₀ * (W.π₀ * abelian₂ W A a₀ e ^ 2) * t) := by
  subst ha₀
  set a' : ZMod n := c' + (e : ZMod n) with ha'
  set Λ := abelian₂ W A a' e with hΛ
  set D := W.π₀ * Λ ^ 2 with hDdef
  have hO := Formalism.MainNotions.UnusedSlot80.SatW.p_nzd_O W hinj
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hLe : (letE a' : LetA O n) ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a'
  have hpA : ∀ t : ℕ, ((PD.p : ℕ) : LetA O n) ^ t ∈ W.AΔ := fun t => W.AΔ.pow_mem (W.AΔ.natCast_mem _) t
  obtain ⟨κ, κ', Hh, a, hHh, ha, hD⟩ := hz
  obtain ⟨y, hy, hyD⟩ := hD
  obtain ⟨β, hβ, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 y hy
  choose yy hyy hHhy using hHh
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) e
  let HY : Fin d → Fin d → LetA O n := fun k m =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (yy k r m) * Y ^ r
  have hφHh : ∀ k, ((W.φD T) ^ e) (Hh k) = ∑ m, HY k m • ((W.φD T) ^ e) (b m) := by
    intro k
    rw [hHhy k, Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

  have hS1 : lA W ^ κ' • ∑ k, a k • ((W.φD T) ^ e) (Hh k) =
      ∑ m, (lA W ^ κ' * ∑ k, a k * HY k m) • ((W.φD T) ^ e) (b m) := by
    simp only [hφHh, Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hS2 : D • y = ∑ m, (D * β m) • ((W.φD T) ^ e) (b m) := by
    rw [hyβ, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  have hrel : ∑ m, (lA W ^ κ' * ∑ k, a k * HY k m + D * β m) • ((W.φD T) ^ e) (b m) = 0 := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hS1, ← hS2, ← hyD]
    simp only [smul_zero, zero_sub, smul_neg]
    abel
  have hm := frame_indep W T hT hCA.2.1 hmod hq c' b hb.1 e _ hrel
  rw [← ha'] at hm

  have hHc := hH hCA T hT c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  let κ₂ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p (A.M PD.p)
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ₂ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hzz : ∀ r < A.M PD.p, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ₂ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  let GZ : Fin d → Fin d → LetA O n := fun k m =>
    ∑ r ∈ Finset.range (A.M PD.p), algebraMap O (LetA O n) (zz r k m) * Y ^ r
  have hGZ : ∀ k m, GZ k m ∈ W.AΔ := fun k m => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  obtain ⟨ν, hν, hYM⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.yM_mem W hR hTr hCA h5 A hA a' e hje
  intro k0
  choose ρ hρ using fun k => frame_inv_poly2 PD.p hinj sol (fun k => (hb.2 k).2) (A.M PD.p) κ κ₂
    yy hyy zz hzz Y k0 k

  let N : ℕ := κ' + (κ + κ₂)
  let t0 : LetA O n := -(((PD.p : ℕ) : LetA O n) ^ κ' * ν * (∑ k, a k * Polynomial.aeval Y (ρ k)) *
    letE a' + (∑ m, GZ k0 m * β m) * letE a')
  have ht0 : t0 ∈ W.AΔ := by
    refine W.AΔ.neg_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (hpA _) hν)
      (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (ha k).1
        (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _))) hLe)
      (W.AΔ.mul_mem (W.AΔ.sum_mem fun m _ => W.AΔ.mul_mem (hGZ k0 m) (hβ m)) hLe))
  have hkey : ((PD.p : ℕ) : LetA O n) ^ N * (a k0 * letE a') = D * t0 := by
    have e0 : ∑ m, GZ k0 m * ((lA W ^ κ' * ∑ k, a k * HY k m + D * β m) * letE a') = 0 := by
      simp [hm]
    have e1 : ∑ m, GZ k0 m * ((lA W ^ κ' * ∑ k, a k * HY k m + D * β m) * letE a') =
        lA W ^ κ' * (∑ k, a k * ∑ m, GZ k0 m * HY k m) * letE a' +
          D * (∑ m, GZ k0 m * β m) * letE a' := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
        ring
      · refine Finset.sum_congr rfl fun m _ => ?_
        ring
    have e2 : ∑ k, a k * ∑ m, GZ k0 m * HY k m = ((PD.p : ℕ) : LetA O n) ^ (κ + κ₂) * a k0 +
        Y ^ A.M PD.p * ∑ k, a k * Polynomial.aeval Y (ρ k) := by
      have hρ' : ∀ k, ∑ m, GZ k0 m * HY k m = algebraMap O (LetA O n)
          (((PD.p : ℕ) : O) ^ (κ + κ₂) * if k0 = k then 1 else 0) +
          Y ^ A.M PD.p * Polynomial.aeval Y (ρ k) := fun k => hρ k
      simp only [hρ', mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_eq_single k0 (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
        simp only [map_mul, map_pow, map_natCast, ite_true, map_one, mul_one]
        ring
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2, hYM] at e0
    simp only [t0, N]
    unfold lA at e0
    linear_combination e0
  obtain ⟨t', ht'⟩ := Formalism.MainNotions.UnusedSlot80.SatW.dvd_of_UPi hO (upi_D W hR A a' e) N t0 (a k0 * letE a') hkey
  have ht'Δ : t' ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.SatW.mem_AΔ_of_p_pow W hO N (ht' ▸ ht0)
  have heq : a k0 * letE a' = D * t' := by
    apply Formalism.MainNotions.UnusedSlot80.SatW.p_pow_cancel hO N
    rw [hkey, ht']
    ring
  refine ⟨letE a' * t', W.AΔ.mul_mem hLe ht'Δ, ?_⟩
  rw [(ha k0).2, ← map_mul]
  congr 1
  have hLL := letE_mul_self (O := O) a'
  linear_combination ((letE a' : LetA O n) ^ 2) * heq - (a k0) * ((letE a' : LetA O n) + 1) * hLL

end Uq3

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section SecM

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem jump_ge (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (T : LocLat G Qp LL O)
    (hT : Win W A T) (s : ℕ) (hs : s < A.len c) :
    ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ (c - (s : ZMod n)) → ∀ a, IsJumpV PD T.ρ τ a →
      -((A.Hs c (A.len c) s : ℕ) : ℤ) ≤ a := by
  intro τ hτ a ha
  have hJ := hT.2 (c - (s : ZMod n)) τ hτ a ha
  have hok := hA.2.2.2.2.1 (c - (s : ZMod n))
  have hGh := hA.2.2.2.2.2.1
  have hthick := hA.2.2.2.2.2.2.2.1 (c - (s : ZMod n))
  have hcut := (hA.2.2.1 c hc).2.2.1
  have hlet : c - (s : ZMod n) = (c - ((A.len c : ℕ) : ZMod n)) + ((A.len c - s : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hs.le]; ring
  unfold ArcP.Hs
  by_cases h1 : A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin ∨ A.len c - s ≤ A.j
  · rw [if_pos h1]
    have hG2 : A.ty (c - (s : ZMod n)) ≠ Formalism.MainNotions.LocalTheoryWindows.LT.thin →
        (A.ty (c - (s : ZMod n))).size + A.S ≤ A.G₀ := by
      intro hnt
      have h1' : A.len c - s ≤ A.j := h1.resolve_left hnt
      rcases hA.2.2.2.2.2.2.2.2 with hthin | ⟨hj1, -, hG⟩
      · have := hthin _ hcut (A.len c - s) (by omega) h1'
        rw [← hlet] at this
        exact absurd this hnt
      · have := hG _ hcut
        have e1 : A.len c - s = 1 := by omega
        rw [e1, Nat.cast_one] at hlet
        rw [← hlet] at this
        exact this
    rcases hty : A.ty (c - (s : ZMod n)) with _ | b | b
    · rw [hty] at hJ
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at hJ
      omega
    · rw [hty] at hJ hok hG2
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hJ
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
      have := hG2 (by simp)
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at this
      omega
    · rw [hty] at hJ hok hG2
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hJ
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
      have := hG2 (by simp)
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.size] at this
      omega
  · rw [if_neg h1]
    rcases hty : A.ty (c - (s : ZMod n)) with _ | b | b
    · exact absurd (Or.inl hty) h1
    · rw [hty] at hJ hok hthick
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hJ
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, true_implies] at hthick
      omega
    · rw [hty] at hJ hok hthick
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hJ
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, true_implies] at hthick
      omega

theorem inNL_lam (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (T : LocLat G Qp LL O)
    (hT : Win W A T) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) {d : ℕ} (b : Fin d → W.DD T)
    (hb : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T (c - ((A.len c : ℕ) : ZMod n)) (b m))
    (t : Fin d → LetA O n) (ht : ∀ k, t k ∈ W.AΔ) :
    InNL W T c (A.len c) (abelian₂ W A c (A.len c)) b
      (fun k => algebraMap (LetA O n) W.EE (letE c * abelian₂ W A c (A.len c) * t k)) := by
  refine ⟨fun k => ⟨abelian₂ W A c (A.len c) * (abelian₂ W A c (A.len c) * t k),
    W.AΔ.mul_mem (lam_mem W A c (A.len c)) (W.AΔ.mul_mem (lam_mem W A c (A.len c)) (ht k)), ?_⟩, 0, ?_⟩
  · rw [← map_mul]; congr 1; ring
  · refine ⟨d, fun i => algebraMap (LetA O n) W.EE (letE c * abelian₂ W A c (A.len c) * t i),
      fun i => Pi.single i 1, fun i s => (A.Hs c (A.len c) s : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
    · refine ⟨t i, ht i, ?_⟩
      simp only [Int.toNat_natCast, neg_nonpos, Nat.cast_nonneg, Int.toNat_of_nonpos, pow_zero,
        Finset.prod_const_one, map_one, one_mul]
      unfold abelian₂
      congr 1
    · intro s hs
      exact Formalism.MainNotions.UnusedSlot80.UnivC.dvO_mem_FilS W hCA T c (A.len c) s hs b hb _ _
        (jump_ge W A hA c hc T hT s hs)
    · simp only [lE, pow_zero, one_mul]
      rw [Finset.sum_eq_single k (fun i _ hi => by simp [Pi.single_apply, Ne.symm hi]) (by simp)]
      simp

end SecM

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section SecR

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def SecRestCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  ∀ (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n), Formalism.MainNotions.UnusedSlot80.UnivC.Situ PD W A m T₂ c →
  ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
    Formalism.MainNotions.UnusedSlot80.UnivC.FrameOK W A m T₂ c b sol Rst →
    ∀ w, InI W T₂ c w → InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
        (abelian₂ W A c (A.len c) • w) → PoleOK W A T₂ c b sol w →
    ∀ f : Fin d → W.EE, (∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (f k)) →
      RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
        (lA W ^ A.σ PD.p • w) f →
      InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f →
      ∀ k ∉ Rst,
          InFr W c 1 (mmDen W A c) (f k) ∧
          InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam (f k) - f k) ∧
          InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
            (W.γE W.gam (PPγ W (A.len c) (A.JS c) (f k)) - PPγ W (A.len c) (A.JS c) (f k)) ∧
          InFr W c 1 (nnDen W A c) (PPγ W (A.len c) (A.JS c) (f k)) ∧
          ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
            ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
              (lE W κ * PPγ W (A.len c) (A.JS c) (f k) -
                algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)

variable {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)

theorem letter_of_inFr (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (A : ArcP n) (a : ZMod n) (e : ℕ)
    {x : W.EE} (hx : InFr W a 1 (abelian₂ W A a e) x) :
    algebraMap (LetA O n) W.EE (letE a) * x = x := by
  obtain ⟨u, -, hu⟩ := hx
  obtain ⟨U, hU⟩ := lam_unit W hR A a e
  have h1 : (U : W.EE) * (algebraMap (LetA O n) W.EE (letE a) * x) = (U : W.EE) * x := by
    rw [hU, mul_left_comm, hu, ← map_mul, ← mul_assoc, ← mul_assoc, letE_mul_self]
  have := congrArg (fun z => ((U⁻¹ : W.EEˣ) : W.EE) * z) h1
  simpa [← mul_assoc] using this

theorem univSec_of [IsDomain O] [Fintype (K →ₐ[Qp] LL)] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W)
    (hP : ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hRest : SecRestCore PD W) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivSecCore PD W := by
  intro A m T₂ c hsit d b sol Rst hFO w hwI hwP hwPole
  obtain ⟨hCA, h5, hA, hT, hlow, hc⟩ := hsit
  have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hcrys : IsCrys PD T₂.ρ := hT.1
  have hTr : Formalism.MainNotions.LiftingTheory.coreTr W := Formalism.MainNotions.LiftingTheory.coreTr_of W (fun _ => hR) hO2
  have hcc : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hAC := (hArc hCA h5 A hA c hc (A.len c) hjL le_rfl).2 T₂ hT
  simp only [hcc] at hAC
  obtain ⟨-, -, -, hF⟩ := hAC
  have hhor := hFO.1
  obtain ⟨-, hsec, -, hNsec, -, -, -⟩ := hF d b sol hhor
  obtain ⟨f, hfF, hfR⟩ := hsec w hwP

  have hinv : InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f := by
    obtain ⟨-, -, y₀, hy₀N, hy₀c, hγw⟩ := hwI
    have hyN : InFNc W T₂ c 1 y₀ := ⟨y₀, hy₀N, hy₀c, (one_smul _ _).symm⟩
    obtain ⟨g, hgNL, hgR⟩ := hNsec y₀ hyN
    obtain ⟨w₁, hw₁, w', hw', hww, hγΛ⟩ := lam_γ W hS A c (A.len c)
    obtain ⟨u0, hu0, hγπ⟩ := hP W.gam
    have hπΛ : ∃ t, W.γA W.gam (W.π₀ * abelian₂ W A c (A.len c) ^ 2) =
        t * (W.π₀ * abelian₂ W A c (A.len c) ^ 2) ∧ t ∈ W.AΔ :=
      ⟨u0 * w₁ ^ 2, by rw [map_mul, map_pow, hγπ, hγΛ]; ring,
        W.AΔ.mul_mem hu0 (W.AΔ.pow_mem hw₁ _)⟩
    have hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - ((A.len c : ℕ) : ZMod n)) x' →
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (W.π₀ * abelian₂ W A c (A.len c) ^ 2)
          (((W.φD T₂) ^ A.len c) (W.π₀ ^ A.M PD.p • x')) :=
      fun x' hx' => jj_lam W hR h5 A hA c (A.len c) T₂ _ hx'
    have hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T₂ (c - ((A.len c : ℕ) : ZMod n)) b 0 (sol k) :=
      fun k => (hhor.2 k).1
    have hγ := repVV_γ W hsol hJJ hw₁ hw' hww hγΛ hπΛ hfR
    have hπy := repVV_smul W hgR hπ
    have hz := repVV_sub W hinj (repVV_sub W hinj hγ hfR) hπy
    have h0 : W.γ T₂ (lA W ^ A.σ PD.p • w) - lA W ^ A.σ PD.p • w -
        W.π₀ • (lA W ^ A.σ PD.p • y₀) = 0 := by
      rw [Relay2.γ_lsmul, ← smul_sub, hγw, smul_comm, sub_self]
    rw [h0] at hz
    have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
      obtain ⟨h3, -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
      obtain ⟨w, hw⟩ := hR.2.2.2.2.1
      rw [hw, Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀]
      exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W ((Formalism.MainNotions.UnusedSlot80.SatW.UPi.unit _ w).mul
        (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3).add_p)
    have hmod := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA T₂ hcrys).2
    have hz0 := sec_zero W hinj hO2 hR hTr hH hCA h5 A hA (c - ((A.len c : ℕ) : ZMod n)) (A.len c) hjL
      T₂ hcrys hmod hq b sol hhor hcc hz
    choose t ht hzt using hz0
    obtain ⟨U, hU⟩ := lam_unit W hR A c (A.len c)
    let g' : Fin d → W.EE := fun k =>
      algebraMap (LetA O n) W.EE (letE c * abelian₂ W A c (A.len c) * t k)
    have hg'NL := inNL_lam W A hA c hc T₂ hT hCA b (fun m => hhor.1.1 m) t ht
    refine ⟨g + g', Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T₂ A c (A.len c) b hgNL hg'NL, fun k => ?_⟩

    have hLf := letter_of_inFr W hR A c (A.len c) (hfF k)
    have hLg := letter_of_inFr W hR A c (A.len c) (hgNL.1 k)
    have hLγ : algebraMap (LetA O n) W.EE (letE c) * W.γE W.gam (f k) = W.γE W.gam (f k) := by
      have := congrArg (W.γE W.gam) hLf
      rw [map_mul, W.γE_ext] at this
      rw [← this]
      congr 2
      exact (Formalism.MainNotions.LiftingTheory.frame_γA_letE W W.gam c).symm
    have hk := hzt k
    simp only [Pi.sub_apply] at hk
    have hLh : algebraMap (LetA O n) W.EE (letE c) *
        (algebraMap (LetA O n) W.EE (abelian₂ W A c (A.len c)) *
          (W.γE W.gam (f k) - f k - algebraMap (LetA O n) W.EE W.π₀ * g k)) =
        algebraMap (LetA O n) W.EE (abelian₂ W A c (A.len c)) *
          (W.γE W.gam (f k) - f k - algebraMap (LetA O n) W.EE W.π₀ * g k) := by
      have e1 : algebraMap (LetA O n) W.EE (letE c) *
          (W.γE W.gam (f k) - f k - algebraMap (LetA O n) W.EE W.π₀ * g k) =
          W.γE W.gam (f k) - f k - algebraMap (LetA O n) W.EE W.π₀ * g k := by
        rw [mul_sub, mul_sub, hLγ, hLf, mul_left_comm, hLg]
      rw [mul_left_comm, e1]
    rw [hLh] at hk
    have hcan : (U : W.EE) * (W.γE W.gam (f k) - f k) =
        (U : W.EE) * (algebraMap (LetA O n) W.EE W.π₀ * (g + g') k) := by
      rw [hU]
      simp only [Pi.add_apply, g']
      have : algebraMap (LetA O n) W.EE (abelian₂ W A c (A.len c)) * (W.γE W.gam (f k) - f k) =
          algebraMap (LetA O n) W.EE (abelian₂ W A c (A.len c)) *
            (W.γE W.gam (f k) - f k - algebraMap (LetA O n) W.EE W.π₀ * g k) +
          algebraMap (LetA O n) W.EE (abelian₂ W A c (A.len c)) *
            (algebraMap (LetA O n) W.EE W.π₀ * g k) := by ring
      rw [this, hk]
      simp only [map_mul, map_pow]
      ring
    have := congrArg (fun z => ((U⁻¹ : W.EEˣ) : W.EE) * z) hcan
    simpa [← mul_assoc] using this
  exact ⟨f, hfF, hfR, hRest A m T₂ c ⟨hCA, h5, hA, hT, hlow, hc⟩ d b sol Rst hFO w hwI hwP hwPole
    f hfF hfR hinv, hinv⟩

end SecR

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32a

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem dv_single' (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (j : Fin d) :
    dv W T e b (Pi.single j 1) = ((φVB PD (LL := LL) (V := T.V)) ^ e) (cmpD W T (b j)) := by
  simp [dv, Pi.single_apply]

theorem dvO_eq (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T e b c₀ = ∑ j, algebraMap O LL (c₀ j) • dv W T e b (Pi.single j 1) := by
  simp only [dvO, dv_single']
  rfl

theorem coord_zero (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (hli : LinearIndependent LL (fun k => dv W T e b (Pi.single k 1)))
    (hinj : Function.Injective (algebraMap O LL)) (Rst : Finset (Fin d)) (c₀ : Fin d → O)
    (hc : dvO W T e b c₀ ∈ Submodule.span LL ((fun k => dv W T e b (Pi.single k 1)) '' (Rst : Set (Fin d)))) :
    ∀ k ∉ Rst, c₀ k = 0 := by
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := LL)).1 hc
  have h0 : ∑ j, (algebraMap O LL (c₀ j) - if j ∈ Rst then cc j else 0) •
      dv W T e b (Pi.single j 1) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
    rw [← dvO_eq, Finset.sum_ite_mem, Finset.univ_inter, hcc, sub_self]
  intro k hk
  have := Fintype.linearIndependent_iff.1 hli _ h0 k
  rw [if_neg hk, sub_zero] at this
  exact hinj (by rw [this, map_zero])

theorem coord_zero' (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (hli : LinearIndependent LL (fun k => dv W T e b (Pi.single k 1)))
    (hinj : Function.Injective (algebraMap O LL)) (c₀ : Fin d → O) (hc : dvO W T e b c₀ = 0) :
    ∀ k, c₀ k = 0 := by
  intro k
  rw [dvO_eq] at hc
  have h := Fintype.linearIndependent_iff.1 hli (fun j => algebraMap O LL (c₀ j)) hc k
  exact hinj (by rw [h, map_zero])

theorem filCris_bot (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (i : ZMod n) (u : ℤ)
    (hj : ∀ a, IsJumpV PD T.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i) a → a < u) :
    FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb i) = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨hyF, hyD⟩ := Submodule.mem_inf.1 hy
  have h1 := Formalism.MainNotions.UnusedSlot80.UnivC.ι_DdRE T.ρ (W.emb i) (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i)
    (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_alg W hCA.1 i) hCA.1.2 hyD
  have h2 : ιV PD (LL := LL) (V := T.V) y ∈ FildR PD T.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i) u :=
    Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 hyF).2⟩
  rw [fildR_eq_bot_of PD T.ρ _ u hj] at h2
  have h3 : ιV PD (LL := LL) (V := T.V) y = 0 := (Submodule.mem_bot LL).1 h2
  rw [Submodule.mem_bot]
  exact ιV_inj PD (by rw [h3, map_zero])

theorem filCris_le (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (i : ZMod n) (u w : ℤ)
    (huw : u ≤ w)
    (hj : ∀ a, IsJumpV PD T.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i) a → u ≤ a → w ≤ a) :
    FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb i) ≤ FilCris PD T.ρ w ⊓ DcrisL PD T.ρ (W.emb i) := by
  intro y hy
  obtain ⟨hyF, hyD⟩ := Submodule.mem_inf.1 hy
  have h1 := Formalism.MainNotions.UnusedSlot80.UnivC.ι_DdRE T.ρ (W.emb i) (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i)
    (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_alg W hCA.1 i) hCA.1.2 hyD
  have h2 : ιV PD (LL := LL) (V := T.V) y ∈ FildR PD T.ρ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver W hCA.1 i) u :=
    Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 hyF).2⟩
  rw [← fildR_const PD T.ρ _ u w huw hj] at h2
  exact Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hyF).1,
    (Submodule.mem_inf.1 h2).2⟩, hyD⟩

theorem filS_mono_le (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) {u w : ℤ}
    (h : FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) ≤
      FilCris PD T.ρ w ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))) :
    FilS W T c s u ≤ FilS W T c s w := by
  unfold FilS
  exact Submodule.map_mono h

theorem filS_bot (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) {u : ℤ}
    (h : FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) = ⊥) :
    FilS W T c s u = ⊥ := by
  unfold FilS; rw [h, Submodule.map_bot]

end L32a

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

def eMM {n : ℕ} (A : ArcP n) : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .thin => A.G₀
  | .up b => b + A.S
  | .down _ => 0

def eDB : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .thin => 0
  | .up _ => 0
  | .down b => b

section L32b

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem mmDen_eq (A : ArcP n) (c : ZMod n) :
    mmDen W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ eMM A (A.ty (c - (s : ZMod n))) := by
  rfl

theorem downB_eq (A : ArcP n) (c : ZMod n) :
    downB W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ eDB (A.ty (c - (s : ZMod n))) := by
  rfl

theorem eMM_le (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (s : ℕ) (hs : s < A.len c) :
    eMM A (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hthick := hA.2.2.2.2.2.2.2.1 (c - (s : ZMod n))
  have hcut := (hA.2.2.1 c hc).2.2.1
  have hlet : c - (s : ZMod n) = (c - ((A.len c : ℕ) : ZMod n)) + ((A.len c - s : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hs.le]; ring
  unfold ArcP.Hs
  by_cases h1 : A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin ∨ A.len c - s ≤ A.j
  · rw [if_pos h1]
    rcases hty : A.ty (c - (s : ZMod n)) with _ | b | b
    · simp [eMM]
    · have h1' : A.len c - s ≤ A.j := h1.resolve_left (by rw [hty]; simp)
      rcases hA.2.2.2.2.2.2.2.2 with hthin | ⟨hj1, -, hG⟩
      · have := hthin _ hcut (A.len c - s) (by omega) h1'
        rw [← hlet, hty] at this
        exact absurd this (by simp)
      · have := hG _ hcut
        have e1 : A.len c - s = 1 := by omega
        rw [e1, Nat.cast_one] at hlet
        rw [← hlet, hty] at this
        simpa [eMM, Formalism.MainNotions.LocalTheoryWindows.LT.size] using this
    · simp [eMM]
  · rw [if_neg h1]
    rcases hty : A.ty (c - (s : ZMod n)) with _ | b | b
    · simp [eMM]; exact hA.2.2.2.2.2.1
    · rw [hty] at hthick
      simpa [eMM, Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size] using hthick
    · simp [eMM]

theorem inId_bound (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (E : ℕ → ℕ) (hαE : ∀ s < e, -(E s : ℤ) ≤ α s)
    {g : W.EE} (hg : InId W a e α g) :
    ∃ z ∈ W.AΔ, algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ E s) * g =
      algebraMap (LetA O n) W.EE (letE a * (∏ s ∈ Finset.range e, ps W s ^ (α s + E s).toNat) * z) := by
  obtain ⟨u, hu, hgu⟩ := hg
  refine ⟨u, hu, ?_⟩
  have hsplit : ∏ s ∈ Finset.range e, ps W s ^ E s =
      (∏ s ∈ Finset.range e, ps W s ^ (E s - (-(α s)).toNat)) *
        ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    have := hαE s (Finset.mem_range.1 hs)
    rw [← pow_add]
    congr 1
    omega
  have hnum : (∏ s ∈ Finset.range e, ps W s ^ (E s - (-(α s)).toNat)) *
      ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat =
      ∏ s ∈ Finset.range e, ps W s ^ (α s + E s).toNat := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    have := hαE s (Finset.mem_range.1 hs)
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, map_mul, mul_assoc, hgu, ← map_mul, ← hnum]
  congr 1
  ring

end L32b

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32c

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def qQ (A : ArcP n) (c : ZMod n) : LetA O n :=
  ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - eMM A (A.ty (c - (s : ZMod n))))

theorem qQ_def (A : ArcP n) (c : ZMod n) : qQ W A c =
    ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - eMM A (A.ty (c - (s : ZMod n)))) := rfl

theorem lam_split (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) :
    abelian₂ W A c (A.len c) = qQ W A c * mmDen W A c := by
  rw [mmDen_eq, qQ_def, ← Finset.prod_mul_distrib]
  unfold abelian₂
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [← pow_add, Nat.sub_add_cancel (eMM_le A hA c hc s (Finset.mem_range.1 hs))]

theorem upi_prod (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (e : ℕ) (E : ℕ → ℕ) :
    Formalism.MainNotions.UnusedSlot80.SatW.UPi PD.p (∏ s ∈ Finset.range e, ps W s ^ E s) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact Formalism.MainNotions.UnusedSlot80.SatW.UPi.prod _ _ fun s _ => (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s).pow _

theorem prod_mem (e : ℕ) (E : ℕ → ℕ) : (∏ s ∈ Finset.range e, ps W s ^ E s) ∈ W.AΔ :=
  W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s) _

theorem exists_eq_prod_mul_of_pow_mul [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (e : ℕ) (E : ℕ → ℕ) (κ : ℕ)
    {x Z : LetA O n} (hZ : Z ∈ W.AΔ)
    (h : ((PD.p : ℕ) : LetA O n) ^ κ * x = (∏ s ∈ Finset.range e, ps W s ^ E s) * Z) :
    ∃ Z' ∈ W.AΔ, x = (∏ s ∈ Finset.range e, ps W s ^ E s) * Z' := by
  have hO := Formalism.MainNotions.UnusedSlot80.SatW.p_nzd_O W hinj
  obtain ⟨Z', hZ'⟩ := Formalism.MainNotions.UnusedSlot80.SatW.dvd_of_UPi hO (upi_prod W hR e E) κ Z x h
  refine ⟨Z', Formalism.MainNotions.UnusedSlot80.SatW.mem_AΔ_of_p_pow W hO κ (hZ' ▸ hZ), ?_⟩
  apply Formalism.MainNotions.UnusedSlot80.SatW.p_pow_cancel hO κ
  rw [h, hZ']
  ring

theorem unit_prod (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) (e : ℕ) (E : ℕ → ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ E s)) :=
  Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (upi_prod W hR e E)

theorem cancel_unit {q : LetA O n} (hq : IsUnit (algebraMap (LetA O n) W.EE q)) {x y : W.EE}
    (h : algebraMap (LetA O n) W.EE q * x = algebraMap (LetA O n) W.EE q * y) : x = y := by
  exact hq.mul_left_cancel h

end L32c

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32d

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem sat_frac [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (F : ℕ → ℕ) {x : W.EE}
    (hx : InFr W c 1 (abelian₂ W A c (A.len c)) x) (κ : ℕ) {z : LetA O n} (hz : z ∈ W.AΔ)
    (h : ιE ((PD.p : ℕ) : LetA O n) ^ κ * (ιE (mmDen W A c) * x) =
      ιE (letE c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s) * z)) :
    ∃ Z' ∈ W.AΔ, ιE (mmDen W A c) * x =
      ιE (letE c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s) * Z') := by
  obtain ⟨u, hu, hxu⟩ := hx
  have hQF : qQ W A c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s) =
      ∏ s ∈ Finset.range (A.len c), ps W s ^
        ((A.Hs c (A.len c) s - eMM A (A.ty (c - (s : ZMod n)))) + F s) := by
    rw [qQ_def, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => by rw [pow_add]
  have hLQ := lam_split W A hA c hc
  have h1 : ιE (qQ W A c) * (ιE (mmDen W A c) * x) = ιE (letE c * 1 * u) := by
    rw [← mul_assoc, ← map_mul, ← hLQ]; exact hxu
  have hA1 : ((PD.p : ℕ) : LetA O n) ^ κ * (letE c * u) =
      (qQ W A c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s)) * (letE c * z) := by
    apply W.EE_inj
    calc ιE (((PD.p : ℕ) : LetA O n) ^ κ * (letE c * u))
        = ιE ((PD.p : ℕ) : LetA O n) ^ κ * ιE (letE c * 1 * u) := by simp [map_mul, map_pow]
      _ = ιE ((PD.p : ℕ) : LetA O n) ^ κ * (ιE (qQ W A c) * (ιE (mmDen W A c) * x)) := by rw [h1]
      _ = ιE (qQ W A c) * (ιE ((PD.p : ℕ) : LetA O n) ^ κ * (ιE (mmDen W A c) * x)) := by ring
      _ = ιE (qQ W A c) * ιE (letE c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s) * z) := by rw [h]
      _ = ιE ((qQ W A c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s)) * (letE c * z)) := by
          simp only [map_mul]; ring
  rw [hQF] at hA1
  obtain ⟨Z', hZ', hZe⟩ := exists_eq_prod_mul_of_pow_mul W hinj hR (A.len c) _ κ
    (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c) hz) hA1
  rw [← hQF] at hZe
  refine ⟨letE c * Z', W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c) hZ', ?_⟩
  have hQunit : IsUnit (ιE (qQ W A c)) := by rw [qQ_def]; exact unit_prod W hR _ _
  refine cancel_unit W hQunit ?_
  rw [h1]
  have hLL := letE_mul_self (O := O) c
  have e2 : letE c * 1 * u = letE c * (letE c * u) := by rw [mul_one, ← mul_assoc, hLL]
  rw [e2, hZe, ← map_mul]
  congr 1
  linear_combination (-(qQ W A c * (∏ s ∈ Finset.range (A.len c), ps W s ^ F s) * Z')) * hLL

end L32d

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32e

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def KillWinCore {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ f : W.EE,
    InFr W c 1 (abelian₂ W A c (A.len c)) f → InFr W c 1 (mmDen W A c) f →
    InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam f - f) →
    InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
        (W.γE W.gam (PPγ W (A.len c) (A.JS c) f) - PPγ W (A.len c) (A.JS c) f) ∧
      InFr W c 1 (nnDen W A c) (PPγ W (A.len c) (A.JS c) f) ∧
      ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
        ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
          (lE W κ * PPγ W (A.len c) (A.JS c) f -
            algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)

variable {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem section_restriction_first [IsDomain O] [Fintype (K →ₐ[Qp] LL)] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n)
    (hsit : Formalism.MainNotions.UnusedSlot80.UnivC.Situ PD W A m T₂ c) (d : ℕ) (b : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d))
    (hFO : Formalism.MainNotions.UnusedSlot80.UnivC.FrameOK W A m T₂ c b sol Rst) (w : W.DD T₂)
    (hwPole : PoleOK W A T₂ c b sol w) (f : Fin d → W.EE)
    (hfF : ∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (f k))
    (hfR : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (lA W ^ A.σ PD.p • w) f) :
    ∀ k ∉ Rst, InFr W c 1 (mmDen W A c) (f k) := by
  obtain ⟨hCA, h5, hA, hT, hlow, hc⟩ := hsit
  have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hcrys : IsCrys PD T₂.ρ := hT.1
  have hTr : Formalism.MainNotions.LiftingTheory.coreTr W := Formalism.MainNotions.LiftingTheory.coreTr_of W (fun _ => hR) hO2
  have hcc : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hAC := (hArc hCA h5 A hA c hc (A.len c) hjL le_rfl).2 T₂ hT
  simp only [hcc] at hAC
  obtain ⟨-, -, -, hF⟩ := hAC
  obtain ⟨⟨hLI, -⟩, -⟩ := hF d b sol hFO.1
  obtain ⟨κ, fp, hfpR, hfpS⟩ := hwPole
  have h1 := repVV_smul W hfpR (W.AΔ.pow_mem (lA_mem W) (A.σ PD.p))
  have h2 := repVV_smul W hfR (W.AΔ.pow_mem (lA_mem W) κ)
  have h3 := repVV_sub W hinj h2 h1
  rw [smul_comm (lA W ^ κ) (lA W ^ A.σ PD.p) w, sub_self] at h3
  have hq : IsUnit (ιE W.q) := by
    obtain ⟨h3', -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
    obtain ⟨u, hu⟩ := hR.2.2.2.2.1
    rw [hu, Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀]
    exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W ((Formalism.MainNotions.UnusedSlot80.SatW.UPi.unit _ u).mul
      (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3').add_p)
  have hmod := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA T₂ hcrys).2
  have hz := sec_zero W hinj hO2 hR hTr hH hCA h5 A hA _ (A.len c) hjL T₂ hcrys hmod hq b sol
    hFO.1 hcc h3
  obtain ⟨I, g, c₀, α, hgi, hfpk⟩ := hfpS
  intro k hk
  obtain ⟨t, ht, hkt⟩ := hz k

  have hterm : ∀ i, ∃ z ∈ W.AΔ, ιE (mmDen W A c) * (g i * algebraMap O W.EE (c₀ i k)) =
      ιE (letE c * z) := by
    intro i
    by_cases hc0 : c₀ i k = 0
    · exact ⟨0, W.AΔ.zero_mem, by simp [hc0]⟩
    · have hb : ∀ s < A.len c, -((eMM A (A.ty (c - (s : ZMod n))) : ℕ) : ℤ) ≤ α i s := by
        intro s hs
        have hp := (hgi i).2 s hs
        rcases hty : A.ty (c - (s : ZMod n)) with _ | bs | bs
        · simp only [hty] at hp; simpa [eMM] using hp
        · simp only [hty] at hp; simp only [eMM]; push_cast; linarith
        · simp only [hty] at hp
          rcases hp with hp | hp
          · simp only [eMM]; push_cast; linarith
          · exact absurd (coord_zero W T₂ (A.len c) b hLI hinj Rst (c₀ i)
              (hFO.2.2.2 s hs bs hty hp) k hk) hc0
      obtain ⟨z, hzm, hgz⟩ := inId_bound W c (A.len c) (α i) (fun s => eMM A (A.ty (c - (s : ZMod n))))
        hb (hgi i).1
      refine ⟨(∏ s ∈ Finset.range (A.len c), ps W s ^ (α i s + (eMM A (A.ty (c - (s : ZMod n))) : ℤ)).toNat)
        * z * algebraMap O (LetA O n) (c₀ i k), W.AΔ.mul_mem (W.AΔ.mul_mem (prod_mem W _ _) hzm)
          (W.AΔ.algebraMap_mem _), ?_⟩
      rw [mmDen_eq, ← mul_assoc, hgz, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
      congr 1
      ring
  choose zz hzzm hzz using hterm
  have hfpm : ιE (mmDen W A c) * fp k = ιE (letE c) * ιE (∑ i, zz i) := by
    rw [hfpk k, Finset.mul_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hzz i, map_mul]
  have hL := letter_of_inFr W hR A c (A.len c) (hfF k)
  have hLQ' : ιE (abelian₂ W A c (A.len c)) = ιE (qQ W A c) * ιE (mmDen W A c) := by
    rw [lam_split W A hA c hc, map_mul]
  have hLL' : ιE (letE c) * ιE (letE c) = ιE (letE c) := by rw [← map_mul, letE_mul_self]
  simp only [Pi.sub_apply, map_mul, map_pow] at hkt
  unfold lA at hkt
  have hzm : ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ i, zz i) + W.π₀ * abelian₂ W A c (A.len c) *
      mmDen W A c * t ∈ W.AΔ :=
    W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) (W.AΔ.sum_mem fun i _ => hzzm i))
      (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
        (lam_mem W A c (A.len c))) (by rw [mmDen_eq]; exact prod_mem W _ _)) ht)
  have hEq : ιE ((PD.p : ℕ) : LetA O n) ^ κ * (ιE (mmDen W A c) * f k) =
      ιE (letE c * (∏ s ∈ Finset.range (A.len c), ps W s ^ (0 : ℕ)) *
        (((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * (∑ i, zz i) + W.π₀ * abelian₂ W A c (A.len c) *
          mmDen W A c * t)) := by
    apply cancel_unit W (unit_prod W hR (A.len c)
      (fun s => A.Hs c (A.len c) s - eMM A (A.ty (c - (s : ZMod n)))))
    rw [← qQ_def]
    simp only [pow_zero, Finset.prod_const_one, mul_one, map_mul, map_add, map_pow]
    linear_combination (-(ιE ((PD.p : ℕ) : LetA O n)) ^ κ * f k +
        ιE (letE c) * ιE ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * fp k +
        ιE (letE c) * ιE W.π₀ * ιE (abelian₂ W A c (A.len c)) * ιE t) * hLQ' -
      ιE ((PD.p : ℕ) : LetA O n) ^ κ * ιE (abelian₂ W A c (A.len c)) * hL + hkt +
      ιE (qQ W A c) * ιE ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * ιE (∑ i, zz i) * hLL' +
      ιE (letE c) * ιE (qQ W A c) * ιE ((PD.p : ℕ) : LetA O n) ^ A.σ PD.p * hfpm
  obtain ⟨Z', hZ', hZe⟩ := sat_frac W hinj hR A hA c hc (fun _ => 0) (hfF k) κ hzm hEq
  refine ⟨Z', hZ', ?_⟩
  simpa using hZe

end L32e

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32f

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem filCris_anti (T : LocLat G Qp LL O) (τ₀ : K₀ →ₐ[Qp] LL) {u w : ℤ} (h : w ≤ u) :
    FilCris PD T.ρ u ⊓ DcrisL PD T.ρ τ₀ ≤ FilCris PD T.ρ w ⊓ DcrisL PD T.ρ τ₀ :=
  inf_le_inf_right _ (inf_le_inf_left _ (Submodule.comap_mono (filV_anti PD h)))

theorem nn_bounds [Fintype (K →ₐ[Qp] LL)] (hinj : Function.Injective (algebraMap O LL))
    (A : ArcP n) (hA : A.OK) (c : ZMod n) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (m : ℕ) (T₂ : LocLat G Qp LL O)
    (hT : Win W A T₂) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)
    (Rst : Finset (Fin d)) (hFO : Formalism.MainNotions.UnusedSlot80.UnivC.FrameOK W A m T₂ c b sol Rst)
    (hLI : LinearIndependent LL (fun k => dv W T₂ (A.len c) b (Pi.single k 1)))
    (α : ℕ → ℤ) (c₀ : Fin d → O) (hN : condNN W T₂ c (A.len c) b α c₀) (k : Fin d) (hk : k ∉ Rst)
    (hc0 : c₀ k ≠ 0) (s : ℕ) (hs : s < A.len c) :
    -((eMM A (A.ty (c - (s : ZMod n))) : ℕ) : ℤ) ≤ α s ∧
      ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs → (bs : ℤ) ≤ α s := by
  have hNs := hN s hs
  have hJ := hT.2 (c - (s : ZMod n)) _ (Formalism.MainNotions.UnusedSlot80.UnivC.τOver_over W hCA.1 (c - (s : ZMod n)))
  have hok := hA.2.2.2.2.1 (c - (s : ZMod n))
  have hzero : FilS W T₂ c s (-(α s)) = ⊥ → False := by
    intro hb
    rw [hb] at hNs
    have h0 : dvO W T₂ (A.len c) b c₀ = 0 := (Submodule.mem_bot LL).1 hNs
    exact hc0 (coord_zero' W T₂ (A.len c) b hLI hinj c₀ h0 k)
  rcases hty : A.ty (c - (s : ZMod n)) with _ | bs | bs
  · rw [hty] at hJ
    refine ⟨?_, fun bs h => absurd h (by simp)⟩
    simp only [eMM]
    by_contra hlt
    push_neg at hlt
    refine hzero (filS_bot W T₂ c s (filCris_bot W hCA T₂ _ _ fun a ha => ?_))
    have := hJ a ha
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at this
    omega
  · rw [hty] at hJ hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    refine ⟨?_, fun bs' h => absurd h (by simp)⟩
    simp only [eMM]
    by_contra hlt
    push_neg at hlt
    refine hzero (filS_bot W T₂ c s (filCris_bot W hCA T₂ _ _ fun a ha => ?_))
    have := hJ a ha
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at this
    push_cast at hlt
    omega
  · rw [hty] at hJ hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    have hb : (bs : ℤ) ≤ α s := by
      by_contra hlt
      push_neg at hlt
      have hle : FilS W T₂ c s (-(α s)) ≤ FilS W T₂ c s (-(A.η : ℤ)) := by
        apply filS_mono_le
        rcases le_or_gt (-(α s)) (-(A.η : ℤ)) with h | h
        · refine filCris_le W hCA T₂ _ _ _ h fun a ha hua => ?_
          have := hJ a ha
          simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at this
          omega
        · exact filCris_anti T₂ _ h.le
      exact hc0 (coord_zero W T₂ (A.len c) b hLI hinj Rst c₀
        ((hFO.2.2.2 s hs bs hty) (hle hNs)) k hk)
    refine ⟨?_, fun bs' h => ?_⟩
    · simp only [eMM]; push_cast; omega
    · cases h; exact hb

end L32f

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section L32g

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem section_restriction_second [IsDomain O] [Fintype (K →ₐ[Qp] LL)] (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n)
    (hsit : Formalism.MainNotions.UnusedSlot80.UnivC.Situ PD W A m T₂ c) (d : ℕ) (b : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d))
    (hFO : Formalism.MainNotions.UnusedSlot80.UnivC.FrameOK W A m T₂ c b sol Rst) (f : Fin d → W.EE)
    (hinv : InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f) :
    ∀ k ∉ Rst, InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam (f k) - f k) := by
  obtain ⟨hCA, h5, hA, hT, hlow, hc⟩ := hsit
  have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hcc : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hAC := (hArc hCA h5 A hA c hc (A.len c) hjL le_rfl).2 T₂ hT
  simp only [hcc] at hAC
  obtain ⟨-, -, -, hF⟩ := hAC
  obtain ⟨⟨hLI, -⟩, -⟩ := hF d b sol hFO.1
  obtain ⟨Gs, ⟨hGF, κ, I, g, c₀, α, hgi, hGk⟩, hG⟩ := hinv
  intro k hk
  have hterm : ∀ i, ∃ z ∈ W.AΔ, ιE (mmDen W A c) * (g i * algebraMap O W.EE (c₀ i k)) =
      ιE (letE c * downB W A c * z) := by
    intro i
    by_cases hc0 : c₀ i k = 0
    · exact ⟨0, W.AΔ.zero_mem, by simp [hc0]⟩
    · have hbd := fun s hs => nn_bounds W hinj A hA c hCA m T₂ hT b sol Rst hFO hLI (α i) (c₀ i)
        (hgi i).2 k hk hc0 s hs
      obtain ⟨z, hzm, hgz⟩ := inId_bound W c (A.len c) (α i) (fun s => eMM A (A.ty (c - (s : ZMod n))))
        (fun s hs => (hbd s hs).1) (hgi i).1
      have hsplit : (∏ s ∈ Finset.range (A.len c),
          ps W s ^ (α i s + (eMM A (A.ty (c - (s : ZMod n))) : ℤ)).toNat) =
          downB W A c * ∏ s ∈ Finset.range (A.len c), ps W s ^
            ((α i s + (eMM A (A.ty (c - (s : ZMod n))) : ℤ)).toNat - eDB (A.ty (c - (s : ZMod n)))) := by
        rw [downB_eq, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun s hs => ?_
        rw [← pow_add]
        congr 1
        have h1 := (hbd s (Finset.mem_range.1 hs)).1
        have h2 := (hbd s (Finset.mem_range.1 hs)).2
        rcases hty : A.ty (c - (s : ZMod n)) with _ | bs | bs
        · simp [eDB]
        · simp [eDB]
        · have := h2 bs hty
          simp only [eDB, eMM] at *
          omega
      refine ⟨(∏ s ∈ Finset.range (A.len c), ps W s ^
            ((α i s + (eMM A (A.ty (c - (s : ZMod n))) : ℤ)).toNat - eDB (A.ty (c - (s : ZMod n))))) *
          z * algebraMap O (LetA O n) (c₀ i k),
        W.AΔ.mul_mem (W.AΔ.mul_mem (prod_mem W _ _) hzm) (W.AΔ.algebraMap_mem _), ?_⟩
      rw [mmDen_eq, ← mul_assoc, hgz, hsplit, IsScalarTower.algebraMap_apply O (LetA O n) W.EE,
        ← map_mul]
      congr 1
      ring
  choose zz hzzm hzz using hterm
  have hsum : ιE ((PD.p : ℕ) : LetA O n) ^ κ * (ιE (mmDen W A c) * Gs k) =
      ιE (letE c * (∏ s ∈ Finset.range (A.len c), ps W s ^ eDB (A.ty (c - (s : ZMod n)))) *
        ∑ i, zz i) := by
    have h1 : lE W κ * Gs k = ∑ i, g i * algebraMap O W.EE (c₀ i k) := hGk k
    have h2 : ιE ((PD.p : ℕ) : LetA O n) ^ κ = lE W κ := by unfold lE; rw [map_natCast]
    rw [h2, mul_left_comm, h1, Finset.mul_sum, ← downB_eq, Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hzz i
  obtain ⟨Z', hZ', hZe⟩ := sat_frac W hinj hR A hA c hc (fun s => eDB (A.ty (c - (s : ZMod n))))
    (hGF k) κ (W.AΔ.sum_mem fun i _ => hzzm i) hsum
  refine ⟨Z', hZ', ?_⟩
  rw [hG k, mul_left_comm, hZe, ← downB_eq, ← map_mul]
  congr 1
  ring

theorem secRest_of [IsDomain O] [Fintype (K →ₐ[Qp] LL)] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hKW : KillWinCore W) :
    SecRestCore PD W := by
  intro A m T₂ c hsit d b sol Rst hFO w hwI hwP hwPole f hfF hfR hinv k hk
  have ha := section_restriction_first W hinj hO2 hArc hR h9 hH A m T₂ c hsit d b sol Rst hFO w hwPole f hfF hfR k hk
  have hb := section_restriction_second W hinj hArc hR A m T₂ c hsit d b sol Rst hFO f hinv k hk
  obtain ⟨hCA, h5, hA, -, -, hc⟩ := hsit
  exact ⟨ha, hb, hKW hCA h5 A hA c hc (f k) (hfF k) ha hb⟩

end L32g

end Formalism.MainNotions.UnusedSlot80.UnivF

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.UnivC

theorem univFrameL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) : UnivFrameL D HW := by
  intro l _ K LL hG hA h5 _
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  exact UnivF.univFrame_of _ (hAdm.2.2.2 l K LL hG hA h5).1 (h9 l K 1 LL hG) (hH l K 1 LL hG)
    (hDR l K LL)

theorem univLiftL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    UnivLiftL D HW := by
  intro l _ K LL hG hA h5 _
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hA
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  exact UnivF.univLift_of _ (IsFractionRing.injective _ _) (hAdm.2.2.2 l K LL hG hA h5).1 hR
    (KF.psStable_of _ hR) (hAdm.2.2.1 l K LL hA h5)

theorem universal_general_of_sections (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) (hSec : UnivSecL D HW)
    (hGen : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_frame_sections D HW F Cm hAdm h9 hH (univFrameL_of D HW F Cm hAdm h9 hH hDR) hSec hGen
    (univLiftL_of D HW F Cm hAdm h9)

end Formalism.MainNotions.UnusedSlot80

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.UnivC

def SecRestL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    UnivF.SecRestCore ((D.loc l).PD K) ((HW l).W K 1 LL hG)

theorem univSecL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hRest : SecRestL D HW) : UnivSecL D HW := by
  intro l _ K LL hG hA h5 _
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hA
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  exact UnivF.univSec_of _ (IsFractionRing.injective _ _) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL).2.1
    (hAdm.2.2.2 l K LL hG hA h5).1 hR (KF.psStable_of _ hR) (hAdm.2.2.1 l K LL hA h5)
    (h9 l K 1 LL hG) (hH l K 1 LL hG) (hRest l K LL hG hA h5)

theorem universal_general_of_restriction (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) (hRest : SecRestL D HW)
    (hGen : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_sections D HW F Cm hAdm h9 hH hDR (univSecL_of D HW F Cm hAdm h9 hH hRest) hGen

end Formalism.MainNotions.UnusedSlot80

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.UnivC

def KillWinL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => UnivF.KillWinCore ((HW l).W K 1 LL hG)

theorem secRestL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hKW : KillWinL D HW) : SecRestL D HW := by
  intro l _ K LL hG hA h5 _
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hA
  exact UnivF.secRest_of _ (IsFractionRing.injective _ _) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL).2.1
    (hAdm.2.2.2 l K LL hG hA h5).1 hR (h9 l K 1 LL hG) (hH l K 1 LL hG) (hKW l K LL hG hA h5)

theorem universal_general_of_window (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) (hKW : KillWinL D HW)
    (hGen : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_restriction D HW F Cm hAdm h9 hH hDR (secRestL_of D HW F Cm hAdm h9 hH hKW) hGen

end Formalism.MainNotions.UnusedSlot80
