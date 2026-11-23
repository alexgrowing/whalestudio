import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.ChartRed

theorem etale_of_quot {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] (f : R →+* S)
    (hf : f.Etale) (g : R →+* R') (hg : Function.Surjective g) (h : S →+* S') (hh : Function.Surjective h)
    (f' : R' →+* S') (comm : f'.comp g = h.comp f) (hk : RingHom.ker h = (RingHom.ker g).map f) : f'.Etale := by
  letI := f.toAlgebra
  haveI : Algebra.Etale R S := hf
  set P := RingHom.ker g with hP
  have het : Algebra.Etale (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S P).symm
  have h0 : (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S))).Etale := RingHom.etale_algebraMap.2 het
  let e1 : (R ⧸ P) ≃+* R' := RingHom.quotientKerEquivOfSurjective hg
  let e2 : (S ⧸ P.map (algebraMap R S)) ≃+* S' :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hh)
  have key : f' = (e2.toRingHom.comp (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S)))).comp e1.symm.toRingHom := by
    refine RingHom.ext fun r' => ?_
    obtain ⟨r, rfl⟩ := hg r'
    have h1 : e1.symm (g r) = Ideal.Quotient.mk P r := by
      rw [RingEquiv.symm_apply_eq]; rfl
    have h2 : f' (g r) = h (f r) := RingHom.congr_fun comm r
    change _ = e2 (algebraMap _ _ (e1.symm (g r)))
    rw [h1, h2]
    rfl
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e1.symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ h0 (RingHom.Etale.of_bijective e2.bijective))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l]

theorem ker_red (n : ℕ) : RingHom.ker (Wc.red l k n) =
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) ((l : WittVector l k) ^ n))} := by
  unfold Wc.red
  rw [Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]

theorem red_surj (n : ℕ) : Function.Surjective (Wc.red l k n) :=
  Ideal.Quotient.factor_surjective _

theorem map_Im (n : ℕ) : (Wc.Im l k (n + 1)).map (Wc.red l k n) = Wc.Im l k n := by
  unfold Wc.Im
  rw [Ideal.map_map]
  rfl

variable {O : Type} [CommRing O] {F : B.Fn O} {ρ : O →+* k} {n : ℕ}

theorem etale_q (T : Thick (Wc.L l F ρ (n + 1))) {d : ℕ} (t : Fin d → T.B)
    (h : (MvPolynomial.eval₂Hom T.i t : MvPolynomial (Fin d) (Wc.Wm l k (n + 1)) →+* T.B).Etale) :
    (MvPolynomial.eval₂Hom (qi T) (fun i => Ideal.Quotient.mk (lI n T) (t i)) :
      MvPolynomial (Fin d) (Wc.Wm l k n) →+* T.B ⧸ lI n T).Etale := by
  refine etale_of_quot _ h (MvPolynomial.map (Wc.red l k n)) (MvPolynomial.map_surjective _ (red_surj n))
    (Ideal.Quotient.mk (lI n T)) Ideal.Quotient.mk_surjective _ ?_ ?_
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [qi_red]
    · simp
  · rw [Ideal.mk_ker, MvPolynomial.ker_map, ker_red, Ideal.map_map, Ideal.map_span, Set.image_singleton]
    simp [lI]

theorem J_q (T : Thick (Wc.L l F ρ (n + 1))) (h : T.J = (Wc.Im l k (n + 1)).map T.i) :
    T.J.map (Ideal.Quotient.mk (lI n T)) = (Wc.Im l k n).map (qi T) := by
  have e : (Ideal.Quotient.mk (lI n T)).comp T.i = (qi T).comp (Wc.red l k n) :=
    RingHom.ext fun r => (qi_red T r).symm
  calc T.J.map (Ideal.Quotient.mk (lI n T))
      = ((Wc.Im l k (n + 1)).map T.i).map (Ideal.Quotient.mk (lI n T)) := by rw [← h]
    _ = (Wc.Im l k (n + 1)).map ((Ideal.Quotient.mk (lI n T)).comp T.i) := Ideal.map_map _ _
    _ = (Wc.Im l k (n + 1)).map ((qi T).comp (Wc.red l k n)) := by rw [e]
    _ = ((Wc.Im l k (n + 1)).map (Wc.red l k n)).map (qi T) := (Ideal.map_map _ _).symm
    _ = (Wc.Im l k n).map (qi T) := by rw [map_Im n]

abbrev rr (n : ℕ) : Wc.Wm l k (n + 1) ⧸ Wc.Im l k (n + 1) →+* Wc.Wm l k n ⧸ Wc.Im l k n :=
  Ideal.quotientMap _ (Wc.red l k n) (Ideal.map_le_iff_le_comap.1 (Wc.dp_red l k n).1)

theorem rr_surj (n : ℕ) : Function.Surjective (rr (l := l) (k := k) n) :=
  Ideal.quotientMap_surjective (red_surj n)

theorem qy_rr (T : Thick (Wc.L l F ρ (n + 1))) : (qy T).comp (rr n) = (qe T).comp T.y.1.1 := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have h := T.w r
  change qy T (rr n (Ideal.Quotient.mk _ r)) = qe T ((Wc.L l F ρ (n + 1)).str T.y (Ideal.Quotient.mk _ r))
  rw [h]
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

theorem qe_bij (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) : Function.Bijective (qe T) := by
  refine ⟨?_, Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : Ideal.Quotient.mk (lI n T) x ∈ T.J.map (Ideal.Quotient.mk (lI n T)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 ha
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (lI_le hn T)] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.2 h1

section Abs

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem map_eq_iff {κ' : Type} [CommRing κ'] {κ : O →+* κ'} {A : CommRingCat.{0}} {C : Type} [CommRing C]
    (φ : C →+* A) (z : PtOver X q κ C) (y : PtOver X q κ A) :
    (ptFun X q κ).map (CommRingCat.ofHom φ) z = y ↔
      φ.comp z.1.1 = y.1.1 ∧ Spec.map (CommRingCat.ofHom φ) ≫ z.1.2 = y.1.2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)

theorem rep_abs {K₁ K₂ C₁ C₂ : Type} [CommRing K₁] [CommRing K₂] [CommRing C₁] [CommRing C₂] {κ₁ : O →+* K₁}
    {κ₂ : O →+* K₂} (r : K₁ →+* K₂) (hr : Function.Surjective r) (hκ : r.comp κ₁ = κ₂) (e : C₁ →+* C₂)
    (he : Function.Bijective e) (z₁ : PtOver X q κ₁ C₁) (z₂ : PtOver X q κ₂ C₂) (h1 : z₂.1.1.comp r = e.comp z₁.1.1)
    (h2 : z₂.1.2 = Spec.map (CommRingCat.ofHom e) ≫ z₁.1.2) {V : X.Opens}
    (hrep : ∀ (A : CommRingCat.{0}) (y : PtOver X q κ₁ A), ⊤ ≤ y.1.2 ⁻¹ᵁ V →
      ∃! φ : C₁ →+* A, (ptFun X q κ₁).map (CommRingCat.ofHom φ) z₁ = y)
    (A : CommRingCat.{0}) (y : PtOver X q κ₂ A) (hy : ⊤ ≤ y.1.2 ⁻¹ᵁ V) :
    ∃! φ : C₂ →+* A, (ptFun X q κ₂).map (CommRingCat.ofHom φ) z₂ = y := by
  let y' : PtOver X q κ₁ A := ⟨(y.1.1.comp r, y.1.2), by
    have h := y.2
    rw [RingHom.comp_assoc, hκ]
    exact h⟩
  obtain ⟨φ', h', hu⟩ := hrep A y' hy
  rw [map_eq_iff] at h'
  let E := RingEquiv.ofBijective e he
  have hE : ∀ x, E.symm (e x) = x := fun x => E.symm_apply_apply x
  have hE' : ∀ x, e (E.symm x) = x := fun x => E.apply_symm_apply x
  have hcomp : (φ'.comp E.symm.toRingHom).comp e = φ' := RingHom.ext fun x => by simp [hE]
  have hsp : ∀ ψ : C₂ →+* A, Spec.map (CommRingCat.ofHom ψ) ≫ z₂.1.2 =
      Spec.map (CommRingCat.ofHom (ψ.comp e)) ≫ z₁.1.2 := fun ψ => by
    rw [h2, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨φ'.comp E.symm.toRingHom, ?_, fun ψ hψ => ?_⟩
  · refine (map_eq_iff _ _ _).2 ⟨?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := hr x
      have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
      have e2 : φ' (z₁.1.1 a) = y.1.1 (r a) := RingHom.congr_fun h'.1 a
      change φ' (E.symm (z₂.1.1 (r a))) = _
      rw [e1, hE, e2]
    · rw [hsp, hcomp]
      exact h'.2
  · obtain ⟨g1, g2⟩ := (map_eq_iff _ _ _).1 hψ
    have : ψ.comp e = φ' := by
      refine hu _ ((map_eq_iff _ _ _).2 ⟨?_, ?_⟩)
      · refine RingHom.ext fun a => ?_
        have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
        have e2 : ψ (z₂.1.1 (r a)) = y.1.1 (r a) := RingHom.congr_fun g1 (r a)
        change ψ (e (z₁.1.1 a)) = y.1.1 (r a)
        rw [← e1, e2]
      · rw [← hsp]
        exact g2
    rw [← this]
    refine RingHom.ext fun x => ?_
    change ψ x = ψ (e (E.symm x))
    rw [hE']

end Abs

abbrev tD {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k} {m : ℕ} {W : X.Opens}
    {d : ℕ} (c' : Chart (Wc.pd l k m) l q ((Wc.res l k m).comp ρ) W d) : Thick (Wc.L l (B.schFn q) ρ m) := c'.D

def cq {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d where
  D := qT (F := B.schFn q) (ρ := ρ) hn (tD c')
  t := fun i => Ideal.Quotient.mk (lI n (tD c')) (c'.t i)
  etale := etale_q (tD c') c'.t c'.etale
  J_eq := J_q (tD c') c'.J_eq
  inV := inU_qT q ρ hn (tD c') c'.inV
  rep := rep_abs (rr n) (rr_surj n) (Wc.red_res l ρ n) (qe (tD c')) (qe_bij hn (tD c')) (tD c').y
    (qT (F := B.schFn q) (ρ := ρ) hn (tD c')).y (qy_rr (tD c')) rfl c'.rep

theorem chart_q {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d)
      (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D),
      (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧
        (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) :=
  ⟨cq q ρ hn c', Iso.refl _, fun i => rfl, id⟩

end GlobalTheory.CompanionTheory.ChartRed

end
