import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfA

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfB

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem cspB_over {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) :
    x ≫ Xo.s = spMap (algebraMap c.F S) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [hx, sOf, ← Spec.map_comp]
  rfl

def cspB_lift {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift x (spMap (algebraMap c.F S)) (cspB_over hx)

theorem cspB_lift_fst {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.fst _ _ = x := by
  unfold cspB_lift
  exact pullback.lift_fst _ _ _

theorem cspB_lift_snd {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  unfold cspB_lift
  exact pullback.lift_snd _ _ _

theorem cspB_lift_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : cspB_lift z hz = spMap φ.toRingHom ≫ cspB_lift x hx := by
  apply pullback.hom_ext
  · rw [cspB_lift_fst, Category.assoc, cspB_lift_fst, hzx]
  · rw [cspB_lift_snd, Category.assoc, cspB_lift_snd, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (AlgHom.comp_algebraMap φ).symm

theorem cspB_idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have key : ∀ x y : S, IsIdempotentElem x → IsIdempotentElem y →
      (∀ q : PrimeSpectrum S, x ∉ q.asIdeal → y ∉ q.asIdeal) → x = x * y := by
    intro x y hx hy hxy
    have hid : x * (1 - y) * (x * (1 - y)) = x * (1 - y) := by
      linear_combination (1 - y) ^ 2 * hx.eq + x * hy.eq
    have hmem : x * (1 - y) ∈ nilradical S := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      by_cases hxJ : x ∈ J
      · exact J.mul_mem_right _ hxJ
      · have hyJ : y ∉ J := hxy ⟨J, hJ⟩ hxJ
        apply J.mul_mem_left
        have h0 : y * (1 - y) = 0 := by linear_combination -hy.eq
        have h1 : y * (1 - y) ∈ J := by rw [h0]; exact J.zero_mem
        exact (hJ.mem_or_mem h1).resolve_left hyJ
    obtain ⟨n, hn⟩ := mem_nilradical.mp hmem
    have hpow : ∀ k : ℕ, (x * (1 - y)) ^ (k + 1) = x * (1 - y) := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]
      | succ k ih => rw [pow_succ, ih, hid]
    have h0 : x * (1 - y) = 0 := by rw [← hpow n, pow_succ, hn, zero_mul]
    linear_combination h0
  calc a = a * b := key a b ha hb (fun q h => (hab q).mp h)
    _ = b * a := mul_comm a b
    _ = b := (key b a hb ha (fun q h => (hab q).mpr h)).symm

variable (C : Set (Xo.XF c)) (hC : IsClopen C)

def cspB_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : S :=
  ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩).1

theorem cspB_idem_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    IsIdempotentElem (cspB_idem C hC x hx) := by
  unfold cspB_idem
  exact ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm _).2

theorem cspB_idem_spec {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S)
    (q : PrimeSpectrum S) : cspB_idem C hC x hx ∉ q.asIdeal ↔ cspB_lift x hx q ∈ C := by
  have h1 := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).apply_symm_apply
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩
  have h2 : q ∈ ((((PrimeSpectrum.isIdempotentElemEquivClopens (R := S))
      ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
        ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩)) :
          TopologicalSpace.Clopens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) ↔
      q ∈ (cspB_lift x hx) ⁻¹' C := by
    rw [h1]
    rfl
  exact h2

theorem cspB_idem_congr {S : Type} [CommRing S] [Algebra c.F S] {x x' : Sp S ⟶ Xo.X}
    (hx : x ≫ Xo.s = sOf c S) (hx' : x' ≫ Xo.s = sOf c S) (h : x' = x) :
    cspB_idem C hC x' hx' = cspB_idem C hC x hx := by
  subst h
  rfl

theorem cspB_idem_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : φ (cspB_idem C hC x hx) = cspB_idem C hC z hz := by
  apply cspB_idem_eq_of ((cspB_idem_idem C hC x hx).map φ) (cspB_idem_idem C hC z hz)
  intro q
  rw [cspB_idem_spec C hC z hz q, cspB_lift_map φ hx hz hzx]
  exact cspB_idem_spec C hC x hx (PrimeSpectrum.comap φ.toRingHom q)

theorem cspB_idem_field_one {K' : Type} [Field K'] [Algebra c.F K'] (x : Sp K' ⟶ Xo.X)
    (hx : x ≫ Xo.s = sOf c K') (q : PrimeSpectrum K') (hq : cspB_lift x hx q ∈ C) :
    cspB_idem C hC x hx = 1 := by
  have hi := cspB_idem_idem C hC x hx
  have hne : cspB_idem C hC x hx ≠ 0 := by
    intro h0
    have h3 := (cspB_idem_spec C hC x hx q).mpr hq
    rw [h0] at h3
    exact h3 q.asIdeal.zero_mem
  have h2 : cspB_idem C hC x hx * (cspB_idem C hC x hx - 1) = 0 := by
    rw [mul_sub, mul_one, hi.eq, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

theorem cspB_idem_field_zero {K' : Type} [Field K'] [Algebra c.F K'] (x : Sp K' ⟶ Xo.X)
    (hx : x ≫ Xo.s = sOf c K') (q : PrimeSpectrum K') (hq : cspB_lift x hx q ∉ C) :
    cspB_idem C hC x hx = 0 := by
  have h1 : cspB_idem C hC x hx ∈ q.asIdeal := by
    by_contra h
    exact hq ((cspB_idem_spec C hC x hx q).mp h)
  by_contra hne
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (Ne.isUnit hne))

variable (Xo c) in

def cspB_rule : Rul Xo c := fun _ y => cspB_idem C hC y.x y.x_over

theorem cspB_rule_natural : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (cspB_rule Xo c C hC) := by
  intro p q φ y z hyz
  first
  | exact cspB_idem_map C hC φ y.x_over z.x_over hyz.1
  | exact (cspB_idem_map C hC φ y.x_over z.x_over hyz.1).symm

theorem cspB_rule_bor (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R) (hb : FrBor t y y') :
    cspB_rule Xo c C hC p y' = cspB_rule Xo c C hC p y := by
  exact cspB_idem_congr C hC y.x_over y'.x_over hb.1

theorem cspB_rule_mul_mem {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n) :
    cspB_rule Xo c C hC * g ∈ sec Xo c a n := by
  have hg' : _ ∧ _ := hg
  obtain ⟨hgN, hgW⟩ := hg'
  show _ ∧ _
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    show cspB_rule Xo c C hC q z * g q z = φ (cspB_rule Xo c C hC p y * g p y)
    rw [map_mul, ← cspB_rule_natural C hC p q φ y z hyz, ← hgN p q φ y z hyz]
  · intro p t y y' hb
    show cspB_rule Xo c C hC p y' * g p y' = wchar (ex Dw a n) t * (cspB_rule Xo c C hC p y * g p y)
    rw [cspB_rule_bor C hC p t y y' hb, hgW p t y y' hb]
    ring

theorem split_rule_mem_weight_zero : cspB_rule Xo c C hC ∈ sec Xo c 0 0 := by
  show _ ∧ _
  refine ⟨cspB_rule_natural C hC, ?_⟩
  intro p t y y' hb
  rw [cspB_rule_bor C hC p t y y' hb]
  unfold wchar ex
  rw [Finset.prod_eq_one (fun i _ => by cases i <;> simp), one_mul]

theorem cspB_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    evR Xo c (cspB_rule Xo c C hC) y = cspB_idem C hC y.x y.x_over := by
  unfold evR evalAt
  rw [dif_pos hy]
  first
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1.1

theorem cspB_evR_zero {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : ¬ FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt
  rw [dif_neg hy]

theorem cspB_evR_mul {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f g : Rul Xo c) :
    evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y := by
  exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y

theorem cspB_genPt_mem (Z : Comp Xo c) : genPt Z ∈ (Z : Set (Xo.XF c)) := by
  unfold genPt
  have hcl : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hS : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  have hg : IsGenericPoint hS.genericPoint (closure (Z : Set (Xo.XF c))) := by
    first
    | exact hS.isGenericPoint_genericPoint_closure
    | exact hS.genericPoint_spec
  rw [hcl.closure_eq] at hg
  exact hg.mem

theorem cspB_lift_genFr (hG : GenFrEx Xo c) (Z : Comp Xo c) (q : PrimeSpectrum (Om Z)) :
    cspB_lift (genFr hG Z).x (genFr hG Z).x_over q = genPt Z := by
  have e0 : Spec.map (CommRingCat.ofHom (algebraMap c.F (kap Z))) = genSp Z ≫ strK := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have e : cspB_lift (genFr hG Z).x (genFr hG Z).x_over = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [cspB_lift_fst, (isGenFr_genFr hG Z).1, Category.assoc]
      rfl
    · rw [cspB_lift_snd, Category.assoc]
      show _ = spMap (algebraMap (kap Z) (Om Z)) ≫ (genSp Z ≫ strK)
      rw [← e0]
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e]
  exact (Scheme.Hom.comp_apply (spMap (algebraMap (kap Z) (Om Z))) (genSp Z) q).trans
    (Scheme.fromSpecResidueField_apply (genPt Z) _)

theorem cspB_isClopen (hdisj : ∀ Z Z' : Comp Xo c, Z ≠ Z' → Disjoint (Z : Set (Xo.XF c)) Z')
    (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := CompFin.finite_comp Xo c
  refine ⟨isClosed_of_mem_irreducibleComponents _ Z.2, ?_⟩
  have hU : (Z : Set (Xo.XF c)) = (⋃ Z' : {Z' : Comp Xo c // Z' ≠ Z}, (Z'.1 : Set (Xo.XF c)))ᶜ := by
    ext p
    constructor
    · intro hp hp'
      obtain ⟨⟨Z', hne⟩, hZ'⟩ := Set.mem_iUnion.1 hp'
      exact Set.disjoint_left.1 (hdisj Z Z' (Ne.symm hne)) hp hZ'
    · intro hp
      have hall : p ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.1 hall
      by_contra hpZ
      refine hp (Set.mem_iUnion.2 ⟨⟨⟨W, hW⟩, fun hWZ => hpZ ?_⟩, hpW⟩)
      rw [← hWZ]
      exact hpW
  rw [hU]
  exact (isClosed_iUnion_of_finite fun Z' : {Z' : Comp Xo c // Z' ≠ Z} =>
    isClosed_of_mem_irreducibleComponents _ Z'.1.2).isOpen_compl

theorem cspB_chi_zero {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have h1 : X.χ 0 γ = X.χ 0 γ * X.χ 0 γ := by
    have h3 := X.χ_add 0 0 γ hγ
    rwa [add_zero] at h3
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have h4 := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at h4
    exact zero_ne_one h4
  have h2 : X.χ 0 γ * (X.χ 0 γ - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

open Classical in
theorem cspB_isIdemFn {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (k : U.Comp) :
    CompSplitPfA.IsIdemFn (U.X k) (rdU U (cspB_rule Xo c C hC) k) := by
  have hdom : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, ⟨0, rfl⟩⟩
  have hsec := hU.2.2.2.2.1 0 0 hdom _ (split_rule_mem_weight_zero C hC) k
  have hla : laU U 0 0 k = 0 := by
    funext τ j
    simp [laU]
  rw [hla] at hsec
  refine ⟨fun x hx => ?_, hsec.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · show (if h : x ∈ (U.X k).dom then toC (evR Xo c (cspB_rule Xo c C hC) (U.un k ⟨x, h⟩)) else 0) = 0 ∨
      (if h : x ∈ (U.X k).dom then toC (evR Xo c (cspB_rule Xo c C hC) (U.un k ⟨x, h⟩)) else 0) = 1
    rw [dif_pos hx]
    by_cases ht : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k ⟨x, hx⟩)
    · rw [cspB_evR C hC _ ht]
      have he := cspB_idem_idem C hC (U.un k ⟨x, hx⟩).x (U.un k ⟨x, hx⟩).x_over
      exact IsIdempotentElem.iff_eq_zero_or_one (G₀ := ℂ) |>.1 he
    · rw [cspB_evR_zero _ ht]
      left
      rfl
  · rw [hsec.2.1 x hx b hb]
    simp [bchar]
  · rw [hsec.2.2 γ hγ x hx, cspB_chi_zero _ hγ, one_mul]

open Classical in
theorem cspB_rdU_mul {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (g : Rul Xo c) :
    rdU U (cspB_rule Xo c C hC * g) = fun k => rdU U (cspB_rule Xo c C hC) k * rdU U g k := by
  funext k x
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  split_ifs with h
  · rw [cspB_evR_mul]
    rfl
  · simp

end Formalism.L2.Pj.CompSplitPfB
