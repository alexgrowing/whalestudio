import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.Enlarge

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {g : Ω} (hg : g ∈ Algebra.adjoin K gs) :
    ∃ d : O, d ≠ 0 ∧ algebraMap K Ω (algebraMap O K d) * g ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨(1 : O), one_ne_zero, ?_⟩
    rw [map_one, map_one, one_mul]
    exact Subring.subset_closure (Set.mem_union_right _ hx)
  | algebraMap x =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    have hb' : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    rw [← map_mul, mul_div_cancel₀ _ hb']
    exact hOS a
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x + y) =
        algebraMap K Ω (algebraMap O K d2) * (algebraMap K Ω (algebraMap O K d1) * x) +
          algebraMap K Ω (algebraMap O K d1) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.add_mem (S.mul_mem (hOS _) hx) (S.mul_mem (hOS _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x * y) =
        (algebraMap K Ω (algebraMap O K d1) * x) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.mul_mem hx hy

theorem clear_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {r : Ω} (hr : IsIntegral (Algebra.adjoin K gs) r) :
    ∃ κ : O, κ ≠ 0 ∧ ∃ q : Polynomial Ω, q.Monic ∧ q.eval (algebraMap K Ω (algebraMap O K κ) * r) = 0 ∧
      ∀ i, q.coeff i ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hr
  have hex := fun i => exists_den (O := O) gs (p.coeff i).2
  choose d hd0 hd using hex
  set κ : O := ∏ i ∈ Finset.range (p.natDegree + 1), d i with hκdef
  have hκ : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i)
  have hκc : ∀ i, algebraMap K Ω (algebraMap O K κ) * ((p.coeff i : Algebra.adjoin K gs) : Ω) ∈ S := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hκdef, ← Finset.mul_prod_erase _ _ hi, map_mul, map_mul, mul_comm (algebraMap K Ω (algebraMap O K (d i))),
        mul_assoc]
      exact S.mul_mem (hOS _) (hd i)
    · have : p.coeff i = 0 := p.coeff_eq_zero_of_natDegree_lt (by simp at hi; omega)
      rw [this]
      simp
  set k := algebraMap K Ω (algebraMap O K κ) with hk
  set pm := p.map (algebraMap (Algebra.adjoin K gs) Ω) with hpmdef
  have hpmm : pm.Monic := hpm.map _
  have hdeg : pm.natDegree = p.natDegree := hpm.natDegree_map _
  refine ⟨κ, hκ, pm.scaleRoots k, (monic_scaleRoots_iff k).mpr hpmm, ?_, ?_⟩
  · have h0 : eval₂ (RingHom.id Ω) r pm = 0 := by
      rw [eval₂_id, hpmdef, Polynomial.eval_map]; exact hp
    have := scaleRoots_eval₂_eq_zero (RingHom.id Ω) h0 (s := k)
    rwa [eval₂_id] at this
  · intro i
    rw [coeff_scaleRoots]
    have hci : pm.coeff i = ((p.coeff i : Algebra.adjoin K gs) : Ω) := by
      rw [hpmdef, coeff_map]; rfl
    rcases h : pm.natDegree - i with _ | m
    · rcases (show pm.natDegree ≤ i by omega).lt_or_eq with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt]; simp
      · rw [← heq, hpmm.coeff_natDegree]; simp
    · have : pm.coeff i * k ^ (m + 1) = k ^ m * (k * ((p.coeff i : Algebra.adjoin K gs) : Ω)) := by
        rw [hci]; ring
      rw [this]
      exact S.mul_mem (S.pow_mem (hOS κ) m) (hκc i)

theorem mem_of_root {K Ω L : Type} [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (A : Subalgebra K Ω)
    (Sb : Subring Ω) (hSA : ∀ x ∈ Sb, x ∈ A) (ψ : A →ₐ[K] L) (W : ValuationSubring L)
    (hW : ∀ x (hx : x ∈ Sb), ψ ⟨x, hSA x hx⟩ ∈ W) (q : Polynomial Ω) (hqm : q.Monic) (hqc : ∀ i, q.coeff i ∈ Sb)
    (t : Ω) (ht : t ∈ A) (h0 : q.eval t = 0) : ψ ⟨t, ht⟩ ∈ W := by
  let incl : Sb →+* A :=
    { toFun := fun x => ⟨x, hSA x x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let θ : Sb →+* W := ((ψ : A →+* L).comp incl).codRestrict W (fun x => hW x x.2)
  have hcs : (q.coeffs : Set Ω) ⊆ Sb := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact hqc n
  set q' := q.toSubring Sb hcs with hq'
  have hq'm : q'.Monic := (Polynomial.monic_toSubring q Sb hcs).mpr hqm
  have hroot : Polynomial.eval₂ incl ⟨t, ht⟩ q' = 0 := by
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ q' incl ((A.val : A →ₐ[K] Ω) : A →+* Ω) ⟨t, ht⟩
    rw [show ((A.val : A →ₐ[K] Ω) : A →+* Ω).comp incl = Sb.subtype from RingHom.ext fun _ => rfl,
      Polynomial.eval₂_eq_eval_map Sb.subtype, hq', Polynomial.map_toSubring] at key
    change ((A.val : A →ₐ[K] Ω) : A →+* Ω) _ = 0
    rw [key]
    exact h0
  have hint : IsIntegral W (ψ ⟨t, ht⟩) := by
    refine ⟨q'.map θ, hq'm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap W L).comp θ = (ψ : A →+* L).comp incl := RingHom.ext fun _ => rfl
    rw [hc]
    have h1 := Polynomial.hom_eval₂ q' incl (ψ : A →+* L) ⟨t, ht⟩
    rw [hroot, map_zero] at h1
    exact h1.symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hw]
  exact w.2

def trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) (y : FrPt Xo c A) :
    FrPt Xo c B :=
  h ▸ y

theorem frMap_trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) {T : Type} [CommRing T]
    [Algebra c.F T] (ψ : B →ₐ[c.F] T) (y : FrPt Xo c A) (z : FrPt Xo c T) :
    FrMap ψ (trPt h y) z ↔ FrMap (ψ.comp (Subalgebra.equivOfEq A B h).toAlgHom) y z := by
  subst h
  have : ψ.comp (Subalgebra.equivOfEq A A rfl).toAlgHom = ψ := AlgHom.ext fun _ => rfl
  rw [this]
  rfl

variable {O : Type} [CommRing O] {β : O →+* c.F}

attribute [local instance] Classical.propDecidable

theorem eqR (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) (e : P.Ω) (he : e ∈ P.es) :
    P.R e = Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω)) := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  · rw [Algebra.adjoin_le_iff, Finset.coe_insert]
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · exact hs e he
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

def enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) : PChart Xo c β where
  Ω := P.Ω
  fld := P.fld
  alg := P.alg
  gens := insert s P.gens
  frac := by
    rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  es := P.es
  es_ne := P.es_ne
  es_mem e he := ⟨(P.es_mem e he).1, Subring.closure_mono
    (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)) (P.es_mem e he).2⟩
  sm e he := by rw [← eqR P s hs e he]; exact P.sm e he
  yg := P.yg
  y e he := trPt (eqR P s hs e he) (P.y e he)
  gen e he := by
    rw [frMap_trPt]
    have : (Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω))).val.comp
        (Subalgebra.equivOfEq _ _ (eqR P s hs e he)).toAlgHom = (P.R e).val := AlgHom.ext fun _ => rfl
    rw [this]
    exact P.gen e he
  int e he T io := by
    intro ψ hO hg z hz
    letI : Algebra c.F T.Fr := io.toAlgebra
    exact P.int e he T io (ψ.comp (Subalgebra.equivOfEq (P.R e) _ (eqR P s hs e he)).toAlgHom) hO
      (fun g hgm => hg _ (Finset.mem_insert_of_mem hgm)) z ((frMap_trPt (eqR P s hs e he) ψ (P.y e he) z).mp hz)

theorem catches_enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) {L : Type} [Field L]
    [Algebra c.F L] (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (q : Polynomial P.Ω)
    (hqm : q.Monic) (hq0 : q.eval s = 0) (hqc : ∀ i, q.coeff i ∈ P.B) (y : FrPt Xo c L) (hy : P.Catches W y) :
    (enlarge P s hs).Catches W y := by
  obtain ⟨e, he, ψ, z, t, hg, hm, hb⟩ := hy
  have hR := eqR P s hs e he
  refine ⟨e, he, ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom, z, t, ?_, ?_, hb⟩
  · intro g hgm
    rcases Finset.mem_insert.mp hgm with h | h
    · have hBA : ∀ x ∈ P.B, x ∈ P.R e := by
        intro x hx
        refine (Subring.closure_le (t := (P.R e).toSubring)).mpr ?_ hx
        rintro x (⟨a, rfl⟩ | hx)
        · exact Subalgebra.algebraMap_mem _ _
        · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
      have hWB : ∀ x (hx : x ∈ P.B), ψ ⟨x, hBA x hx⟩ ∈ W := by
        intro x hx
        have hle : P.B ≤ ((W.toSubring.comap (ψ : P.R e →+* L)).map ((P.R e).val : P.R e →+* P.Ω)) := by
          rw [Subring.closure_le]
          rintro x (⟨a, rfl⟩ | hx)
          · refine ⟨algebraMap c.F (P.R e) (β a), ?_, rfl⟩
            show ψ (algebraMap c.F (P.R e) (β a)) ∈ W
            rw [AlgHom.commutes]; exact hW a
          · exact ⟨⟨x, Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)⟩, hg _ hx, rfl⟩
        obtain ⟨a, ha, hax⟩ := hle hx
        have : a = ⟨x, hBA x hx⟩ := Subtype.ext hax
        subst this
        exact ha
      have hgR : (show P.Ω from g.1) ∈ P.R e := by rw [hR]; exact g.2
      exact mem_of_root (P.R e) P.B hBA ψ W hWB q hqm hqc (show P.Ω from g.1) hgR (by rw [h]; exact hq0)
    · exact hg (Subalgebra.equivOfEq _ _ hR.symm g) h
  · have : (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom).comp (Subalgebra.equivOfEq _ _ hR).toAlgHom = ψ :=
      AlgHom.ext fun _ => rfl
    exact (frMap_trPt hR (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom) (P.y e he) z).mpr
      (by rw [this]; exact hm)

theorem enlarge_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ f P hR hI
  obtain ⟨κ, hκ, q, hqm, hq0, hqc⟩ := clear_den (O := O) (P.gens : Set P.Ω) hI
  have hk : algebraMap O c.F κ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hκ)
  set r := evR Xo c f P.yg with hr
  set s := algebraMap c.F P.Ω (algebraMap O c.F κ) * r with hsdef
  have hs : ∀ e ∈ P.es, s ∈ P.R e := fun e he =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hR e he)
  refine ⟨enlarge P s hs, ?_, fun L _ _ W hW y hy => catches_enlarge P s hs W hW q hqm hq0 hqc y hy⟩
  show r ∈ Algebra.adjoin c.F ((insert s P.gens : Finset P.Ω) : Set P.Ω)
  have : r = algebraMap c.F P.Ω (algebraMap O c.F κ)⁻¹ * s := by
    rw [hsdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
  rw [this]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (by simp))

end GlobalTheory.Reg.Enlarge
