import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.MidLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (y : S.V) :
    prj e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a := by
  simp [prj, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable {e f : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← hconj, hef]; split_ifs <;> simp

include hee hef in
theorem prj_e (b : Fin r) : prj e f (e b) = 0 := by
  rw [prj_apply]; simp [hfe hef, hee]

include hff hef in
theorem prj_f (b : Fin r) : prj e f (f b) = 0 := by
  rw [prj_apply]; simp [hff, hef]

theorem prj_perp {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) : prj e f y = y := by
  rw [prj_apply]; simp [(hy _).1, (hy _).2]

theorem pair_prj {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) (x : S.V) :
    S.hT (prj e f x) y = S.hT x y := by
  rw [prj_apply]; simp [map_sub, map_sum, (hy _).1, (hy _).2]

include hee hef in
theorem prj_spanE {s : S.V} (hs : s ∈ Submodule.span E (Set.range e)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range e) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_e hee hef b)
  exact h hs

include hff hef in
theorem prj_spanF {s : S.V} (hs : s ∈ Submodule.span E (Set.range f)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range f) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_f hff hef b)
  exact h hs

theorem latSpanS_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpanS aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.St.G.MidLat

open GlobalTheory.St.G.MidLat in

theorem GlobalTheory.St.G.midLat_selfDual_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  intro D X u
  have hprjL : ∀ y ∈ (VS D).L0, prj X.eX X.fY y ∈ X.Lb := by
    intro y hy
    rw [X.Lam_split] at hy
    obtain ⟨y1, hy1, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
    have hs' := latSpanS_le_span _ _ hs
    have ht' := latSpanS_le_span _ _ ht
    rw [map_add, map_add, prj_spanE X.ee X.ef hs', prj_spanF X.ff X.ef ht', zero_add, add_zero,
      prj_perp (fun a => X.Lb_perp l hl a)]
    exact hl
  have hLbL : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]; exact le_sup_right.trans le_sup_left
  have h1 : ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
      ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧
        ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb)) := by
    intro y hy
    refine ⟨⟨fun h => ?_, fun h => hLbL h⟩, fun hint => ?_⟩
    · have := hprjL y h; rwa [prj_perp hy] at this
    · have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
      have hyL : y ∈ (VS D).L0 := by
        rw [← hU]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro x hx
        obtain ⟨o, ho⟩ := hint _ (hprjL x hx)
        exact ⟨o, by rw [ho, pair_prj hy]⟩
      have := hprjL y hyL; rwa [prj_perp hy] at this
  refine ⟨h1, ?_, fun y hy => ?_⟩

  · let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
    have hσ : ∀ o : 𝓞 D.host.E, ((σ o : 𝓞 D.host.E) : D.host.E) = star (o : D.host.E) := fun o => rfl
    let J : Ideal (𝓞 D.host.E) :=
      (LinearMap.range (((VS D).hT (X.zu u)).restrictScalars (𝓞 D.host.E) ∘ₗ X.Lb.subtype)).comap
        (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hJ : ∀ o, o ∈ J ↔ ∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = (o : D.host.E) := by
      intro o
      simp only [J, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Subtype.exists,
        exists_prop]
    by_cases hJt : J = ⊤
    · obtain ⟨x, hx, hx1⟩ := (hJ 1).1 (hJt ▸ Submodule.mem_top)
      exact ⟨x, hx, by rw [hx1]; simp⟩
    exfalso
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
    obtain ⟨c, hc, hc1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) hM0 hM.ne_top
    have hc' := (FractionalIdeal.mem_inv_iff (by rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero])).1 hc
    have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
    have hzL : X.zu u ∈ X.Lb := X.zu_Lb u
    have hwperp : ∀ a, (VS D).hT (X.eX a) (star c • X.zu u) = 0 ∧ (VS D).hT (X.fY a) (star c • X.zu u) = 0 := by
      intro a
      exact ⟨by rw [map_smul, smul_eq_mul, (X.zu_orth u a).1, mul_zero],
        by rw [map_smul, smul_eq_mul, (X.zu_orth u a).2, mul_zero]⟩
    have hwLb : star c • X.zu u ∈ X.Lb := by
      refine (h1 _ hwperp).2 ?_
      intro x hx
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hU]; exact hLbL hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hxd
      obtain ⟨o, ho⟩ := hxd (X.zu u) (hLbL hzL)
      have hoM : o ∈ M := hJM ((hJ o).2 ⟨x, hx, ho.symm⟩)
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨o, hoM, rfl⟩))
      refine ⟨σ o', ?_⟩
      change ((σ o' : 𝓞 D.host.E) : D.host.E) = _
      rw [hσ]
      change star (algebraMap (𝓞 D.host.E) D.host.E o') = _
      rw [ho', map_smul, smul_eq_mul, ← hconj (X.zu u) x, ← ho, star_mul, mul_comm]
    have hprim := (X.Fu_fixed u).2.2.2.2 (star c)
    dsimp only at hprim
    rw [X.flagZVector u] at hprim
    have horth : star c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (Formalism.MainNotions.S.Lat.hS D)
        (Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))) := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have hX : Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
          = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [hX] at hx
      have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT (star c • X.zu u)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨a, rfl⟩
          show (VS D).hT (star c • X.zu u) (X.eX a) = 0
          rw [← hconj, (hwperp a).1, star_zero])
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [← hconj, this, star_zero]
    obtain ⟨o, ho⟩ := hprim ⟨Submodule.mem_sup_left ⟨hLbL hwLb, horth⟩, horth⟩
    apply hc1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨σ o, ?_⟩
    change ((σ o : 𝓞 D.host.E) : D.host.E) = c
    rw [hσ, ho, star_star]
  · have := hprjL y hy; rwa [prj_apply] at this
