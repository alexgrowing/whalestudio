import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IndepOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem span_pi_iff (hR : RedData ϖ k r n b Λ) (x : M.L.O) :
    (x : E) ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ r x = 0 := by
  rw [Submodule.mem_span_singleton, hR.ker]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, o.2, by rw [← ho]; show (o : E) * _ = _; ring⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by rw [hzx]; show z * _ = _; ring⟩

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Ph (r : M.L.O →+* k) (H : Loc.HermSp M V) (b : Fin n → V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O) :
    Matrix (Fin n) (Fin n) k := fun i j => r ⟨H.h (b i) (b j), hint i j⟩

theorem gram_mem (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) ∧ H.h x y ∈ M.L.O := by
  have he : H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) := by
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    exact h_expand H b _ _
  refine ⟨he, ?_⟩
  rw [he]
  exact M.L.O.sum_mem fun i _ => M.L.O.sum_mem fun j _ =>
    M.L.O.mul_mem (M.L.O.mul_mem (cO_mem hR x i) (cj_mem (cO_mem hR y j))) (hint i j)

theorem gram_red (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    r ⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ =
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q := by
  have h1 : (⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ : M.L.O) =
      ∑ i, ∑ j, (⟨cO hR x i, cO_mem hR x i⟩ : M.L.O) * ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ *
        ⟨H.h (b i) (b j), hint i j⟩ := by
    apply Subtype.ext
    show H.h x y = _
    rw [(gram_mem hR H hint hx hy).1]
    push_cast
    rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, rfrob ⟨cO hR y j, cO_mem hR y j⟩ ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ rfl]
  simp only [red, Ph]
  ring

theorem gram_cond_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (g : E) (hg : g ∈ M.L.O) :
    H.h x y - g ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q = r ⟨g, hg⟩ := by
  have hm := (gram_mem hR H hint hx hy).2
  have := span_pi_iff hR ⟨H.h x y - g, M.L.O.sub_mem hm hg⟩
  simp only at this
  rw [this, show (⟨H.h x y - g, M.L.O.sub_mem hm hg⟩ : M.L.O) = ⟨H.h x y, hm⟩ - ⟨g, hg⟩ from
    Subtype.ext rfl, map_sub, sub_eq_zero, gram_red hR H hint q rfrob hx hy]

end FC

end PI.UnitaryGroupMassFormula.CntFormula
