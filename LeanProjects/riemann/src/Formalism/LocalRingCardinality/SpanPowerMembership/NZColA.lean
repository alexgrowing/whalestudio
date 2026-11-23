import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField Formalism.MainNotions.G

structure GatBasis (D : D7) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  bas : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).ι → (D.gat u w hg).Fn
  bas_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (bas u w hg)
  bas_span : ∀ u w hg, Submodule.span (D.gat u w hg).O (Set.range (bas u w hg)) = (D.gat u w hg).M

namespace GatBasis

variable {D : D7} (B : GatBasis D)

def cmp (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn where
  toFun x := ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem cmp_apply (u w hg) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg x = ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a := rfl

theorem cmp_smul (u w hg) (r : D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg (r • x) = B.embW u w hg r • B.cmp u w hg x := by
  rw [cmp_apply, cmp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]

theorem cmp_basis (u w hg) (a : ((D.fm u).lat 0).ι) : B.cmp u w hg (((D.fm u).lat 0).b a) = B.bas u w hg a := by
  rw [cmp_apply, Finset.sum_eq_single a]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_smul]
  · intro c _ hc
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hc, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem int_mem (u w hg) (r : 𝓞 D.what₂.LL) :
    B.embW u w hg (r : D.what₂.LL) ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
  rw [← B.embW_int, D.val_nonneg_iff]
  exact (D.plEq w).valuation_le_one r

def toCmp (hstd : ∀ u, ((D.fm u).lat 0).L = Submodule.span (𝓞 D.what₂.LL) (Set.range ((D.fm u).lat 0).b)) :
    LatCmp D where
  embW := B.embW
  embW_int := B.embW_int
  cmp := B.cmp
  cmp_smul := B.cmp_smul
  cmp_li u w hg := by
    have : (fun a => B.cmp u w hg (((D.fm u).lat 0).b a)) = B.bas u w hg := funext (B.cmp_basis u w hg)
    rw [this]; exact B.bas_li u w hg
  cmp_M u w hg := by
    rw [← B.bas_span u w hg]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hstd u] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [B.cmp_basis]; exact Submodule.subset_span ⟨a, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        obtain ⟨o, ho⟩ := B.int_mem u w hg r
        have h1 : r • y = (r : D.what₂.LL) • y := (algebraMap_smul D.what₂.LL r y).symm
        rw [h1, B.cmp_smul, ← ho, algebraMap_smul]
        exact Submodule.smul_mem _ o hy
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨((D.fm u).lat 0).b a, ?_, B.cmp_basis u w hg a⟩
      rw [SetLike.mem_coe, hstd u]
      exact Submodule.subset_span ⟨a, rfl⟩

include B in

theorem d_eq (u w hg) (hinj : Function.Injective (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)) :
    (D.gat u w hg).d = Fintype.card ((D.fm u).lat 0).ι := by
  unfold GAtP.d
  rw [← B.bas_span u w hg]
  refine finrank_span_eq_card ?_
  have : FaithfulSMul (D.gat u w hg).O (D.gat u w hg).Kf := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact (B.bas_li u w hg).restrict_scalars' (D.gat u w hg).O

end GatBasis

end Formalism.BasicNotions.Examples₂.NZ
