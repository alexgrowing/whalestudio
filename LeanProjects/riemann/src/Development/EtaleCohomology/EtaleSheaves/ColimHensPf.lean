import Development.EtaleCohomology.EtaleSheaves.HensCut

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.ColimHensPf

variable {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
  (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) {c : Cocone D}

lemma beta_nat {j j' : J} (f : j ⟶ j') (b : B) : (D.map f).hom ((β.app j).hom b) = (β.app j').hom b := by
  have h := congrArg (fun g => g.hom b) (β.naturality f)
  simpa using h.symm

lemma iota_nat (c : Cocone D) {j j' : J} (f : j ⟶ j') (x : D.obj j) :
    (c.ι.app j').hom ((D.map f).hom x) = (c.ι.app j).hom x := by
  have h := congrArg (fun g => g.hom x) (c.w f)
  simpa using h

lemma mapI (I : Ideal B) {j j' : J} (f : j ⟶ j') {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (D.map f).hom x ∈ I.map (β.app j').hom := by
  have h : (D.map f).hom.comp (β.app j).hom = (β.app j').hom := RingHom.ext (beta_nat β f)
  have := Ideal.mem_map_of_mem (D.map f).hom hx
  rwa [Ideal.map_map, h] at this

def phi (c : Cocone D) : B →+* c.pt :=
  (c.ι.app (IsFiltered.nonempty (C := J)).some).hom.comp (β.app (IsFiltered.nonempty (C := J)).some).hom

lemma phi_eq (c : Cocone D) (j : J) (b : B) : (c.ι.app j).hom ((β.app j).hom b) = phi β c b := by
  let j0 := (IsFiltered.nonempty (C := J)).some
  show _ = (c.ι.app j0).hom ((β.app j0).hom b)
  rw [← iota_nat c (IsFiltered.leftToMax j j0), ← iota_nat c (IsFiltered.rightToMax j j0), beta_nat, beta_nat]

lemma KofI (c : Cocone D) (I : Ideal B) {j : J} {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (c.ι.app j).hom x ∈ I.map (phi β c) := by
  have h : (c.ι.app j).hom.comp (β.app j).hom = phi β c := RingHom.ext (phi_eq β c j)
  have := Ideal.mem_map_of_mem (c.ι.app j).hom hx
  rwa [Ideal.map_map, h] at this

variable (hc : IsColimit c)
include hc

lemma rep (z : c.pt) : ∃ j, ∃ y : D.obj j, (c.ι.app j).hom y = z :=
  Concrete.isColimit_exists_rep D hc z

lemma rep_above (j : J) (z : c.pt) : ∃ (j' : J) (_ : j ⟶ j') (y : D.obj j'), (c.ι.app j').hom y = z := by
  obtain ⟨j1, y, rfl⟩ := rep hc z
  exact ⟨IsFiltered.max j j1, IsFiltered.leftToMax j j1, (D.map (IsFiltered.rightToMax j j1)).hom y, iota_nat c _ y⟩

lemma eq_later {j : J} (x y : D.obj j) (h : (c.ι.app j).hom x = (c.ι.app j).hom y) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = (D.map f).hom y := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x y h
  refine ⟨_, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom x = (D.map g).hom y := hfg
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom x
        = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom x) := by simp
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom y) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom y := by simp
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom y := by rw [IsFiltered.coeq_condition]

lemma zero_later {j : J} (x : D.obj j) (h : (c.ι.app j).hom x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = 0 := by
  obtain ⟨j', f, hf⟩ := eq_later hc x 0 (by rw [h, map_zero])
  exact ⟨j', f, by rw [hf, map_zero]⟩

lemma Krep (I : Ideal B) {k : c.pt} (hk : k ∈ I.map (phi β c)) :
    ∃ j, ∃ x : D.obj j, x ∈ I.map (β.app j).hom ∧ (c.ι.app j).hom x = k := by
  have hk' : k ∈ Ideal.span (phi β c '' I) := hk
  clear hk
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨(IsFiltered.nonempty (C := J)).some, _, Ideal.mem_map_of_mem _ hi, phi_eq β c _ i⟩
  | zero => exact ⟨(IsFiltered.nonempty (C := J)).some, 0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨j1, x1, h1, rfl⟩ := hx
    obtain ⟨j2, x2, h2, rfl⟩ := hy
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom x1 +
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, add_mem (mapI β I _ h1) (mapI β I _ h2), ?_⟩
    rw [map_add, iota_nat, iota_nat]
  | smul a x _ hx =>
    obtain ⟨j2, x2, h2, rfl⟩ := hx
    obtain ⟨j1, y, rfl⟩ := rep hc a
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom y *
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, Ideal.mul_mem_left _ _ (mapI β I _ h2), ?_⟩
    rw [map_mul, iota_nat, iota_nat, smul_eq_mul]

lemma memK_descend (I : Ideal B) {j : J} (y : D.obj j) (hy : (c.ι.app j).hom y ∈ I.map (phi β c)) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom y ∈ I.map (β.app j').hom := by
  obtain ⟨j1, x, hx, hxe⟩ := Krep β hc I hy
  let l := IsFiltered.leftToMax j j1
  let r := IsFiltered.rightToMax j j1
  obtain ⟨j', g, hg⟩ := zero_later hc ((D.map l).hom y - (D.map r).hom x)
    (by rw [map_sub, iota_nat, iota_nat, hxe, sub_self])
  refine ⟨j', l ≫ g, ?_⟩
  rw [map_sub, sub_eq_zero] at hg
  have : (D.map (l ≫ g)).hom y = (D.map (r ≫ g)).hom x := by simpa using hg
  rw [this]
  exact mapI β I _ hx

lemma poly_lift (g : Polynomial c.pt) : ∃ j, g ∈ Polynomial.lifts (c.ι.app j).hom := by
  have mono : ∀ {j j' : J} (f : j ⟶ j') (g : Polynomial c.pt),
      g ∈ Polynomial.lifts (c.ι.app j).hom → g ∈ Polynomial.lifts (c.ι.app j').hom := by
    intro j j' f g ⟨q, hq⟩
    refine ⟨q.map (D.map f).hom, ?_⟩
    have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
    simp only [Polynomial.coe_mapRingHom] at hq ⊢
    rw [Polynomial.map_map, h, hq]
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, h1⟩ := hp
    obtain ⟨j2, h2⟩ := hq
    exact ⟨_, add_mem (mono (IsFiltered.leftToMax j1 j2) _ h1)
      (mono (IsFiltered.rightToMax j1 j2) _ h2)⟩
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := rep hc a
    exact ⟨j, Polynomial.monomial_mem_lifts n ⟨y, hy⟩⟩

omit hc in
lemma ev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R) (b : R) :
    φ (p.eval b) = (p.map φ).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

omit hc in
lemma pmap (c : Cocone D) {j j' : J} (f : j ⟶ j') (p : Polynomial (D.obj j)) :
    (p.map (D.map f).hom).map (c.ι.app j').hom = p.map (c.ι.app j).hom := by
  have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
  rw [Polynomial.map_map, h]

end LateralTheory.E.ColimHensPf

namespace LateralTheory.E.ColimHensPf
open LateralTheory.E.ColimHensPf

theorem ColimHens_of : LateralTheory.E.HensCut.ColimHens := by
  intro B _ I J _ _ D β c hc ha hb hcc
  refine ⟨I.map (phi β c), ⟨?_, ?_⟩, ⟨RingEquiv.ofBijective
    (Ideal.quotientMap (I.map (phi β c)) (phi β c) Ideal.le_comap_map) ⟨?_, ?_⟩⟩⟩
  ·
    intro k hk
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I (Ideal.mul_mem_right y _ hk)
    obtain ⟨j', f, hu⟩ := hb j x hx
    have := hu.map (c.ι.app j').hom
    rw [iota_nat, map_add, map_one, hxe, add_comm] at this
    exact this
  ·
    intro g hg a₀ hev hder
    by_cases hnt : Nontrivial c.pt
    swap
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨a₀, Subsingleton.elim _ _, by rw [sub_self]; exact zero_mem _⟩
    obtain ⟨j1, hj1⟩ := poly_lift hc g
    haveI : Nontrivial (((Functor.const J).obj c.pt).obj j1) := hnt
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic hj1 hg
    obtain ⟨w, hw⟩ := hder.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (phi β c))), Ideal.Quotient.eq] at hw
    obtain ⟨j2, f12, b0, hb0⟩ := rep_above hc j1 a₀
    obtain ⟨j3, f23, v, hv⟩ := rep_above hc j2 u
    set p3 := p.map (D.map (f12 ≫ f23)).hom with hp3
    set b3 := (D.map f23).hom b0 with hb3
    have hp3g : p3.map (c.ι.app j3).hom = g := by rw [hp3, pmap, hp]
    have hb3a : (c.ι.app j3).hom b3 = a₀ := by rw [hb3, iota_nat, hb0]
    have hy1 : (c.ι.app j3).hom (p3.eval b3) ∈ I.map (phi β c) := by
      rw [ev_map, hp3g, hb3a]; exact hev
    have hy2 : (c.ι.app j3).hom (p3.derivative.eval b3 * v - 1) ∈ I.map (phi β c) := by
      rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map, hp3g, hb3a, hv]; exact hw
    obtain ⟨j4, f34, h4⟩ := memK_descend β hc I _ hy1
    obtain ⟨j5, f45, h5⟩ := memK_descend β hc I ((D.map f34).hom (p3.derivative.eval b3 * v - 1))
      (by rw [iota_nat]; exact hy2)
    let h := f34 ≫ f45
    set P := p3.map (D.map h).hom with hP
    set b := (D.map h).hom b3 with hb
    have hPm : P.Monic := (hpm.map _).map _
    have hPe : P.eval b ∈ I.map (β.app j5).hom := by
      rw [hP, hb, ← ev_map]
      have := mapI β I f45 h4
      simpa [h] using this
    have hPd : IsUnit (Ideal.Quotient.mk (I.map (β.app j5).hom) (P.derivative.eval b)) := by
      have e : (D.map h).hom (p3.derivative.eval b3 * v - 1) = P.derivative.eval b * (D.map h).hom v - 1 := by
        rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map]
      have h5' : P.derivative.eval b * (D.map h).hom v - 1 ∈ I.map (β.app j5).hom := by
        rw [← e]; simpa [h] using h5
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ ((D.map h).hom v)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact h5'
    obtain ⟨j6, f56, a, ha1, ha2⟩ := hcc j5 P b hPm hPe hPd
    refine ⟨(c.ι.app j6).hom a, ?_, ?_⟩
    · have hr := ha1.map (f := (c.ι.app j6).hom)
      rwa [pmap, hP, pmap, hp3g] at hr
    · have := KofI β c I ha2
      rwa [map_sub, iota_nat, hb, iota_nat, hb3a] at this
  ·
    rw [injective_iff_map_eq_zero]
    intro a ha0
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha0
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I ha0
    obtain ⟨j', f, hf⟩ := zero_later hc ((β.app j).hom b - x)
      (by rw [map_sub, hxe, phi_eq, sub_self])
    rw [map_sub, sub_eq_zero, beta_nat] at hf
    have hm : (β.app j').hom b ∈ I.map (β.app j').hom := by rw [hf]; exact mapI β I f hx
    apply (ha j').1
    rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  ·
    intro z
    obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨j, y, rfl⟩ := rep hc z'
    obtain ⟨w, hw⟩ := (ha j).2 (Ideal.Quotient.mk _ y)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    rw [Ideal.quotientMap_mk] at hw ⊢
    rw [Ideal.Quotient.eq] at hw ⊢
    have := KofI β c I hw
    rwa [map_sub, phi_eq] at this

end LateralTheory.E.ColimHensPf
