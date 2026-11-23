import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubquot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubquot

set_option linter.unusedSectionVars false

theorem iSupIndep_comap {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (p j).comap g) ≤ (⨆ (j) (_ : j ≠ i), p j).comap g :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  have h0 := (Submodule.disjoint_def.mp (hp i)) (g x) (Submodule.mem_comap.mp hx) (Submodule.mem_comap.mp (hle hx'))
  exact hg (by rw [h0, map_zero])

theorem iSupIndep_map_of_ker_le {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨x, hx, rfl⟩ := hy
  have hy2 : f x ∈ (⨆ (j) (_ : j ≠ i), p j).map f := by
    simpa only [Submodule.map_iSup] using hy'
  obtain ⟨z, hz, hzx⟩ := hy2
  have hk : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  have hk' := hL hk
  rw [iSup_split_single (fun c => LinearMap.ker f ⊓ p c) i, Submodule.mem_sup] at hk'
  obtain ⟨l, hl, w, hw, hlw⟩ := hk'
  have hw1 : w ∈ ⨆ (j) (_ : j ≠ i), p j :=
    (show (⨆ (j) (_ : j ≠ i), LinearMap.ker f ⊓ p j) ≤ ⨆ (j) (_ : j ≠ i), p j from
      iSup₂_mono fun j _ => inf_le_right) hw
  have hxl : x - l ∈ p i := sub_mem hx (Submodule.mem_inf.mp hl).2
  have hxl' : x - l ∈ ⨆ (j) (_ : j ≠ i), p j := by
    have e : x - l = z + w := by
      calc x - l = (x - z) - l + z := by abel
        _ = z + w := by rw [← hlw]; abel
    rw [e]
    exact Submodule.add_mem _ hz hw1
  have h0 := (Submodule.disjoint_def.mp (hp i)) (x - l) hxl hxl'
  rw [sub_eq_zero.mp h0]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k

variable (S ι) in

def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}

theorem monTimes_subset_span (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by
  rintro _ ⟨u, h, hh, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hh)

theorem span_monTimes_le (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S :=
  Submodule.span_le.mpr (monTimes_subset_span H)

theorem monomial_smul_mem (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx

theorem span_le_span_monTimes (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by
  let T : Submodule (MRingOver S ι) M :=
    { carrier := Submodule.span S (monTimes S ι H)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro p y hy
        refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
        · have e : (monomial u a : MRingOver S ι) = a • monomial u (1 : S) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [e, smul_assoc]
          exact Submodule.smul_mem _ a (monomial_smul_mem H u hy)
        · rw [add_smul]
          exact Submodule.add_mem _ hp hq }
  have hT : Submodule.span (MRingOver S ι) H ≤ T := by
    rw [Submodule.span_le]
    intro h hh
    have e : h = (monomial 0 (1 : S) : MRingOver S ι) • h := by
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_smul]
    exact Submodule.subset_span ⟨0, h, hh, e⟩
  exact fun x hx => hT hx

theorem monTimes_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩

theorem mem_iSup_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN

end GradedSubquot

open GradedSubquot in

theorem GradedSubquot.proof : GradedSubquot.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 G H hM hG hH hGH

  have hind : iSupIndep (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) :=
    iSupIndep_comap hM.1.submodule_iSupIndep ((Submodule.span (MRingOver S ι) H).subtype.restrictScalars S)
      (fun a b h => Subtype.ext h)
  have hsup : ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    exact (show (⨆ c, ((Submodule.span (MRingOver S ι) H).comap (Submodule.span (MRingOver S ι) H).subtype).restrictScalars S ⊓
        subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) ≤ ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c from
      iSup_mono fun c => inf_le_right) (mem_iSup_inf hM hH le_rfl x x.2)
  refine ⟨⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup,
    fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩, ?_⟩

  set L := (Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype with hLdef
  set f := L.mkQ.restrictScalars S with hfdef
  have hker : LinearMap.ker f = L.restrictScalars S := by
    ext x
    simp [hfdef]
  have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) := by
    rw [hker]
    intro x hx
    exact mem_iSup_inf hM hG hGH x hx
  have hind2 := iSupIndep_map_of_ker_le hind f hL
  have hsup2 : ⨆ c, quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) L c = ⊤ := by
    change ⨆ c, (subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c).map f = ⊤
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective L
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
  rintro a c p _ hp ⟨x, hx, rfl⟩
  exact ⟨p • x, hM.2 a c p (x : M) hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
