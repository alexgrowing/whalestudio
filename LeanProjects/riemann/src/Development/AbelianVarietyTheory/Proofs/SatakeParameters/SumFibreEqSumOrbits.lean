import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Formalism.LocalToGlobal.Columns.GSetLemmas

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

theorem sum_inv_eq_sum_orbits {K M H X : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group H] [Finite H]
    [MulAction H X] [Fintype X] [Fintype (MulAction.orbitRel.Quotient H X)] (F : X → M)
    (hF : ∀ (g : H) (x : X), F (g • x) = F x) :
    ((Nat.card H : K))⁻¹ • ∑ x, F x =
      ∑ q : MulAction.orbitRel.Quotient H X, ((Nat.card (MulAction.stabilizer H q.out) : K))⁻¹ • F q.out := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : ∀ x : X, (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q ↔ x ∈ MulAction.orbit H q.out := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply
  rw [Finset.sum_congr rfl (g := fun _ => F q.out) (by
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (Finset.mem_filter.1 hx).2
    exact hF g _), Finset.sum_const]
  have hc : (Finset.univ.filter fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q).card
      = Nat.card (MulAction.orbit H q.out) := by
    symm
    refine Nat.subtype_card _ fun x => ?_
    rw [Finset.mem_filter, ← hmem]
    simp
  have hm : Nat.card (MulAction.orbit H q.out) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H q.out)
  have h1 : (Nat.card (MulAction.stabilizer H q.out) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [hc, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have : (Nat.card (MulAction.orbit H q.out) : K) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hm
  field_simp
  rw [← this]

theorem card_stabilizer_smul {G D : Type} [Group G] [MulAction G D] (g : G) (d : D) :
    Nat.card (MulAction.stabilizer G (g • d)) = Nat.card (MulAction.stabilizer G d) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g) (a := d) (b := g • d) rfl).toEquiv).symm

theorem sum_fibre_eq_sum_orbits {K M G D D₀ : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group G]
    [MulAction G D] [MulAction G D₀] (pr : D → D₀) (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
    [Fintype (MulAction.orbitRel.Quotient G D₀)] [Fintype (MulAction.orbitRel.Quotient G D)]
    (hs : ∀ x : D₀, Finite (MulAction.stabilizer G x)) [∀ x : D₀, Fintype (fibre pr hpr x)] (F : D → M)
    (hF : ∀ (g : G) (x : D), F (g • x) = F x) :
    ∑ c : MulAction.orbitRel.Quotient G D₀, ((Nat.card (MulAction.stabilizer G c.out) : K))⁻¹ •
        ∑ y : fibre pr hpr c.out, F y =
      ∑ q : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G q.out) : K))⁻¹ • F q.out := by
  classical
  let _ : ∀ x : D₀, Fintype (MulAction.orbitRel.Quotient (MulAction.stabilizer G x) (fibre pr hpr x)) :=
    fun x => Fintype.ofFinite _
  rw [← (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hs c.out
  rw [sum_inv_eq_sum_orbits (H := MulAction.stabilizer G c.out) (fun y : fibre pr hpr c.out => F y)
    (fun g y => hF (g : G) (y : D))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩
      = (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) : MulAction.orbitRel.Quotient G D) := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  obtain ⟨g, hg⟩ : ∃ g : G, g • ((q.out : fibre pr hpr c.out) : D) =
      ((orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩).out := by
    rw [h1]
    exact Quotient.exact' (Quotient.out_eq' (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) :
      MulAction.orbitRel.Quotient G D))
  rw [← hg, hF, card_stabilizer_smul, fibre_card_stab]

section Pairs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}

def cplFibreEquiv (Y : Cpl S) (x : S.D) :
    fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x ≃ Y.ys x where
  toFun p := ⟨p.1.1.2, by
    have h1 : p.1.1.1 = x := p.2
    exact (congrArg (fun z => p.1.1.2 ∈ Y.ys z) h1).mp p.1.2⟩
  invFun y := ⟨⟨(x, y.1), y.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext (show p.1.1.1 = x from p.2).symm rfl))
  right_inv _ := rfl

theorem cplGSD_ok (Y : Cpl S) (h : S.Ok) : (cplGSD S Y).Ok where
  fin_orb := by
    have := h.fin_orb
    have : ∀ x : S.D, Finite (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
      have := (Y.fin x).to_subtype
      Finite.of_equiv _ (cplFibreEquiv Y x).symm
    exact Finite.of_equiv _ (orbitsFib (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) Quotient.out
      (fun c => Quotient.out_eq' c))
  fin_stab d := by
    have := h.fin_stab d.1.1
    have hle : MulAction.stabilizer S.G d ≤ MulAction.stabilizer S.G d.1.1 := fun g hg =>
      congrArg (fun p : Y.Pts => p.1.1) hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  nab_smul g d := h.nab_smul g d.1.1
  del_smul g d := h.del_smul g d.1.1
  inv := h.inv

def cplKer1 (A : CplKer S₀ S S₁ Y) : ClsKer S₀ (cplGSD S Y) where
  k d₀ d := A.k1 d₀ d.1.1 d.1.2
  equiv g₀ g d₀ d := A.equiv1 g₀ g d₀ d.1.1 d.1.2

def cplKer2 (A : CplKer S₀ S S₁ Y) : ClsKer (cplGSD S Y) S₁ where
  k d d₁ := A.k2 d.1.1 d.1.2 d₁
  equiv g g₁ d d₁ := A.equiv2 g g₁ d.1.1 d.1.2 d₁

theorem cpl_comp_k (A : CplKer S₀ S S₁ Y) (h : S.Ok) (d₀ : S₀.D) (d₁ : S₁.D) :
    (A.comp h S.outSec).k d₀ d₁ =
      letI := (cplGSD_ok Y h).fintypeCl
      ∑ q : (cplGSD S Y).Cl, ((((cplGSD S Y).toCSDOf (cplGSD_ok Y h) (cplGSD S Y).outSec).wt q : K))⁻¹ •
        ((cplKer2 A).k ((cplGSD S Y).outSec.rep q) d₁) ∘ₗ ((cplKer1 A).k d₀ ((cplGSD S Y).outSec.rep q)) := by
  let i1 : Fintype (MulAction.orbitRel.Quotient S.G S.D) := h.fintypeCl
  let i2 : Fintype (MulAction.orbitRel.Quotient S.G Y.Pts) := (cplGSD_ok Y h).fintypeCl
  let i3 : ∀ x : S.D, Fintype (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
    have := (Y.fin x).to_subtype
    have := Finite.of_equiv _ (cplFibreEquiv Y x).symm
    Fintype.ofFinite _
  have key := sum_fibre_eq_sum_orbits (K := K) (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) h.fin_stab
    (fun p : Y.Pts => (A.k2 p.1.1 p.1.2 d₁) ∘ₗ (A.k1 d₀ p.1.1 p.1.2)) (by
      intro g p
      have e1 := A.equiv1 1 g d₀ p.1.1 p.1.2
      have e2 := A.equiv2 g 1 p.1.1 p.1.2 d₁
      rw [one_smul, inv_one, map_one] at e1
      rw [one_smul, map_one] at e2
      show (A.k2 (g • p.1.1) (g • p.1.2) d₁) ∘ₗ (A.k1 d₀ (g • p.1.1) (g • p.1.2)) = _
      rw [e1, e2]
      ext x
      simp only [LinearMap.comp_apply, Module.End.one_apply]
      rw [← Module.End.mul_apply (S.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  refine Eq.trans ?_ key
  show ∑ c : S.Cl, _ = _
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  congr 1
  let _ : Fintype (Y.ys c.out) := (Y.fin c.out).fintype
  refine (Finset.sum_subtype (p := fun y => y ∈ Y.ys c.out) (F := inferInstance) _
    (fun y => (Y.fin _).mem_toFinset) _).trans ?_
  exact ((cplFibreEquiv Y c.out).symm.sum_comp
    (fun y => (A.k2 y.1.1.1 y.1.1.2 d₁) ∘ₗ (A.k1 d₀ y.1.1.1 y.1.1.2)))

theorem cpl_op_eq_comp {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}
    (A : CplKer S₀ S S₁ Y) (h₀ : S₀.Ok) (h : S.Ok) :
    ∃ (h' : (cplGSD S Y).Ok) (k1 : ClsKer S₀ (cplGSD S Y)) (k2 : ClsKer (cplGSD S Y) S₁),
      (∀ d₀ (d : Y.Pts), k1.k d₀ d = A.k1 d₀ d.1.1 d.1.2) ∧ (∀ (d : Y.Pts) d₁, k2.k d d₁ = A.k2 d.1.1 d.1.2 d₁) ∧
        (A.comp h S.outSec).op h₀ = (k2.op h').comp (k1.op h₀) := by
  refine ⟨cplGSD_ok Y h, cplKer1 A, cplKer2 A, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  ext φ d₁
  show (A.comp h S.outSec).appOf h₀ S₀.outSec φ d₁ =
    (cplKer2 A).appOf (cplGSD_ok Y h) (cplGSD S Y).outSec ((cplKer1 A).appOf h₀ S₀.outSec φ) d₁
  unfold ClsKer.appOf
  simp only [cpl_comp_k, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => ?_
  rw [smul_comm]

end Pairs

end GlobalTheory.GO
