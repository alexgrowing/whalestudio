import Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_prim_locPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

def AlgRoot : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ : Prim q A) (x : A), x ^ q = 1 →
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ a n : ℕ, f ^ n * (x - ζ.1 ^ a) = 0

def EtRoot : Prop := ∀ (U : Scheme.{0}) (p : Polynomial Γ(U, ⊤)), p.Monic → (Nontrivial Γ(U, ⊤) → 0 < p.natDegree) → p.Separable →
  Loc U fun V g => ∃ t : Γ(V, ⊤), (p.map g.appTop.hom).IsRoot t

section Alg
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (Polynomial.aeval ζ.1) hr
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h2
  exact sub_eq_zero.1 h2

theorem prim_isPrim {B : Type} [CommRing B] [IsDomain B] (φ : A →+* B) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hq : IsUnit (q : B) := by simpa using ζ.2.1.map φ
  haveI : NeZero (q : B) := ⟨hq.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := (Prim.map φ ζ).2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact h

theorem unit_sub (ζ : Prim q A) {j : ℕ} (hj0 : 0 < j) (hjq : j < q) : IsUnit (ζ.1 ^ j - 1) := by
  by_contra h
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
  have hp := prim_isPrim (Ideal.Quotient.mk m) ζ
  have h0 : Ideal.Quotient.mk m (ζ.1 ^ j - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  exact hp.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.1 hj0) hjq h0

end Alg

section Idem
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (x : A)

def yy (a : ℕ) : A := x * ζ.1 ^ (a * (q - 1))
def ee (a : ℕ) : A := (ζ.2.1.unit⁻¹ : Aˣ) * ∑ j ∈ Finset.range q, (yy ζ x a) ^ j

theorem zeta_mul_yy (a : ℕ) : ζ.1 ^ a * yy ζ x a = x := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  unfold yy
  rw [show q - 1 = k by omega]
  calc ζ.1 ^ a * (x * ζ.1 ^ (a * k)) = x * ζ.1 ^ (a + a * k) := by rw [pow_add]; ring
    _ = x * (ζ.1 ^ (k + 1)) ^ a := by rw [← pow_mul]; ring_nf
    _ = x := by rw [hz, one_pow, mul_one]

theorem ee_kill (hx : x ^ q = 1) (a : ℕ) : ee ζ x a * (x - ζ.1 ^ a) = 0 := by
  have h1 : x - ζ.1 ^ a = ζ.1 ^ a * (yy ζ x a - 1) := by
    rw [mul_sub, zeta_mul_yy, mul_one]
  have hy : (yy ζ x a) ^ q = 1 := by
    unfold yy
    rw [mul_pow, hx, ← pow_mul, mul_comm (a * (q - 1)) q, pow_mul, prim_pow_q, one_pow, one_mul]
  unfold ee
  rw [h1]
  calc _ = ((ζ.2.1.unit⁻¹ : Aˣ) : A) * ζ.1 ^ a * ((∑ j ∈ Finset.range q, (yy ζ x a) ^ j) * (yy ζ x a - 1)) := by ring
    _ = 0 := by rw [geom_sum_mul, hy, sub_self, mul_zero]

theorem inner_sum {j : ℕ} (hj0 : 0 < j) (hjq : j < q) :
    ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  have hik : i < k := by omega
  have e1 : (q - 1) * (i + 1) = (k + 1) * i + (k - i) := by
    rw [show q - 1 = k by omega]; zify [hik.le]; ring
  have hw : ζ.1 ^ ((q - 1) * (i + 1)) = ζ.1 ^ (k - i) := by
    rw [e1, pow_add, pow_mul, hz, one_pow, one_mul]
  have hu : IsUnit (ζ.1 ^ (k - i) - 1) := unit_sub ζ (by omega) (by omega)
  have hwq : (ζ.1 ^ (k - i)) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, prim_pow_q, one_pow]
  rw [hw]
  have h2 := geom_sum_mul (ζ.1 ^ (k - i)) q
  rw [hwq, sub_self] at h2
  exact (hu.mul_left_eq_zero).1 h2

theorem ee_sum : ∑ a ∈ Finset.range q, ee ζ x a = 1 := by
  unfold ee yy
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range q, ∑ a ∈ Finset.range q, (x * ζ.1 ^ (a * (q - 1))) ^ j =
      x ^ j * ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [inner_sum ζ (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne q))) h

end Idem

theorem ee_nil {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : ℕ) (ha : ¬ a.Coprime q) :
    IsNilpotent (ee ζ ξ.1 a) := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  intro p hp
  haveI : Ideal.IsPrime p := hp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  by_contra hne
  have hk := congrArg (Ideal.Quotient.mk p) (ee_kill ζ ξ.1 (prim_pow_q ξ) a)
  rw [map_mul, map_zero, map_sub, map_pow] at hk
  have he : Ideal.Quotient.mk p ξ.1 = (Ideal.Quotient.mk p ζ.1) ^ a :=
    sub_eq_zero.1 ((mul_eq_zero.1 hk).resolve_left hne)
  have hξ := prim_isPrim (Ideal.Quotient.mk p) ξ
  have hζ := prim_isPrim (Ideal.Quotient.mk p) ζ
  rw [he] at hξ
  exact ha ((hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 hξ)

theorem algPow : AlgPow := by
  intro q _ A _ ζ ξ
  refine ⟨Set.range fun a : Fin q => ee ζ ξ.1 a, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← ee_sum ζ ξ.1, Finset.sum_range]
    exact Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨a, rfl⟩
  · rintro f ⟨a, rfl⟩
    by_cases hc : (a : ℕ).Coprime q
    · refine ⟨ZMod.unitOfCoprime a hc, 1, ?_⟩
      have hv : ((ZMod.unitOfCoprime (a : ℕ) hc : (ZMod q)ˣ) : ZMod q).val = a := by
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt a.2]
      rw [hv, pow_one]
      exact ee_kill ζ ξ.1 (prim_pow_q ξ) a
    · obtain ⟨n, hn⟩ := ee_nil ζ ξ a hc
      exact ⟨1, n, by rw [hn, zero_mul]⟩

theorem loc_of_span {U : Scheme.{0}} (s : Set Γ(U, ⊤)) (hs : Ideal.span s = ⊤) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ f ∈ s, ∀ (V : Scheme.{0}) (g : V ⟶ U), IsUnit (g.appTop.hom f) → P V g) : Loc U P := by
  let O : s → U.Opens := fun f => U.basicOpen f.1
  have hO : TopologicalSpace.IsOpenCover O := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, U.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := U.openCoverOfIsOpenCover O hO
  let S : Sieve U := {
    arrows := fun V g => ∃ f ∈ s, IsUnit (g.appTop.hom f)
    downward_closed := by
      rintro V W g ⟨f, hf, hu⟩ k
      exact ⟨f, hf, (show IsUnit (k.appTop.hom (g.appTop.hom f)) from hu.map _)⟩ }
  have hgen : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ≤ S := by
    rintro W g ⟨Y, k, _, ⟨i⟩, rfl⟩
    refine (S.downward_closed ?_ k)
    refine ⟨i.1, i.2, ?_⟩
    have hle : (O i).ι ''ᵁ ⊤ ≤ U.basicOpen i.1 := by simp [O]
    have := (U.toRingedSpace.isUnit_res_basicOpen i.1).map (U.presheaf.map (homOfLE hle).op).hom
    have e : U.presheaf.map (homOfLE (x := (O i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        U.presheaf.map (homOfLE (U.basicOpen_le i.1)).op ≫ U.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    show IsUnit ((O i).ι.appTop.hom i.1)
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  refine ⟨S, Scheme.etaleTopology.superset_covering hgen
    (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)), ?_⟩
  rintro V g ⟨f, hf, hu⟩
  exact h f hf V g hu

theorem eq_of_unit_kill {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {f x y : A} {n : ℕ}
    (hn : f ^ n * (x - y) = 0) (hu : IsUnit (φ f)) : φ x = φ y := by
  have h0 : φ (f ^ n * (x - y)) = 0 := by rw [hn, map_zero]
  rw [map_mul, map_pow, map_sub] at h0
  exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem c1 (hE : EtRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) :
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤)) := by
  have hsep : (Polynomial.cyclotomic q Γ(U, ⊤)).Separable := by
    have h1 := Polynomial.separable_X_pow_sub_C_unit (1 : (Γ(U, ⊤))ˣ) hq
    rw [Units.val_one, map_one] at h1
    exact h1.of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : Nontrivial Γ(U, ⊤) → 0 < (Polynomial.cyclotomic q Γ(U, ⊤)).natDegree := by
    intro _; rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  refine loc_mono' (hE U _ (Polynomial.cyclotomic.monic q _) hdeg hsep) fun V g ⟨t, ht⟩ => ?_
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  refine ⟨⟨t, hqV, ?_⟩⟩
  rw [Polynomial.map_cyclotomic] at ht
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ht

theorem c4 (hE : EtRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  have hq0 : q ≠ 0 := NeZero.ne q
  refine loc_mono' (hE U _ (Polynomial.monic_X_pow_sub_C _ hq0) (fun _ => by rw [Polynomial.natDegree_X_pow_sub_C]; omega)
    (Polynomial.separable_X_pow_sub_C_unit u hq)) fun V g ⟨t, ht⟩ => ?_
  have ht' : t ^ q = g.appTop.hom u := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using ht
  have htu : IsUnit t := (isUnit_pow_iff hq0).1 (by rw [ht']; exact (u.isUnit.map _))
  refine ⟨htu.unit, Units.ext ?_⟩
  simp [ht']

theorem c2 (hA : AlgPow) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨s, hs, hf⟩ := hA q Γ(U, ⊤) ζ ξ
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

theorem c3 (hR : AlgRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)) (hx : x ^ q = 1) :
    Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  obtain ⟨s, hs, hf⟩ := hR q Γ(U, ⊤) ζ x hx
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

end LateralTheory.E.L_prim_locPf
