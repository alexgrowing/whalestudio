import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFieldAutActsHarishChandraCharactersStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.GalSer

open Formalism.CyclotomicNorms

variable {g : ℕ} [Fact g.Prime]

theorem finOrder {x : Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  obtain ⟨n, hn, h2⟩ := isOfFinOrder_iff_pow_eq_one.1 h1
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩
  have h3 : y ^ n = 1 := by simpa using congrArg Units.val h2
  simpa [y] using congrArg Subtype.val h3

theorem teich_zero (L : LabelDatum g) : L.teich 0 = 0 := by
  by_contra h
  have h1 : ∀ x, L.teich x = 1 := fun x => by
    have h2 : L.teich 0 * L.teich x = L.teich 0 * 1 := by rw [← map_mul, zero_mul, mul_one]
    exact mul_left_cancel₀ h h2
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact hx.2 (L.teich_inj x 1 hx.1 one_ne_zero (by rw [h1, h1]))

theorem teich_ne_zero (L : LabelDatum g) {x : Fbar g} (hx : x ≠ 0) : L.teich x ≠ 0 := by
  intro h
  have h2 : L.teich x * L.teich x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

theorem teich_injective (L : LabelDatum g) : Function.Injective L.teich := by
  intro x y h
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd (by rw [← h, hx, teich_zero]) (teich_ne_zero L hy)
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, teich_zero]) (teich_ne_zero L hx)
    · exact L.teich_inj x y hx hy h

theorem map_eq_pow {R : Type} [CommRing R] [IsDomain R] (s : R →* R) {x : R} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, s x = x ^ a := by
  haveI : NeZero (orderOf x) := ⟨hx.orderOf_pos.ne'⟩
  have h1 : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := (IsPrimitiveRoot.orderOf x).eq_pow_of_pow_eq_one h1
  exact ⟨a, ha.symm⟩

def phi (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) : Fbar g :=
  Function.invFun L.teich (τ (L.teich x))

theorem phi_pow (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) :
    ∃ a : ℕ, phi L τ x = x ^ a ∧ τ (L.teich x) = L.teich (x ^ a) := by
  have h : ∃ a : ℕ, τ (L.teich x) = L.teich (x ^ a) := by
    by_cases hx : x = 0
    · exact ⟨1, by rw [hx, pow_one, teich_zero, map_zero]⟩
    · obtain ⟨a, ha⟩ := map_eq_pow (τ : ℂ →* ℂ) (L.teich.isOfFinOrder (finOrder hx))
      exact ⟨a, by rw [map_pow]; exact ha⟩
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by rw [phi, ha]; exact Function.leftInverse_invFun (teich_injective L) _, ha⟩

theorem teich_phi (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) :
    L.teich (phi L τ x) = τ (L.teich x) := by
  obtain ⟨a, h1, h2⟩ := phi_pow L τ x
  rw [h1, h2]

theorem phi_symm (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) : phi L τ.symm (phi L τ x) = x :=
  teich_injective L (by rw [teich_phi, teich_phi, RingEquiv.symm_apply_apply])

theorem phi_injective (L : LabelDatum g) (τ : ℂ ≃+* ℂ) : Function.Injective (phi L τ) :=
  Function.LeftInverse.injective (phi_symm L τ)

theorem phi_zero (L : LabelDatum g) (τ : ℂ ≃+* ℂ) : phi L τ 0 = 0 :=
  teich_injective L (by rw [teich_phi, teich_zero, map_zero])

theorem phi_pow' (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) (n : ℕ) : phi L τ (x ^ n) = phi L τ x ^ n :=
  teich_injective L (by rw [teich_phi, map_pow, map_pow, map_pow, teich_phi])

theorem phi_gal (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (s : Fbar g ≃ₐ[ZMod g] Fbar g) (x : Fbar g) :
    phi L τ (s x) = s (phi L τ x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero, phi_zero, map_zero]
  · obtain ⟨b, hb⟩ := map_eq_pow (s : Fbar g →* Fbar g) (finOrder hx)
    have hb' : s x = x ^ b := hb
    obtain ⟨a, ha, -⟩ := phi_pow L τ x
    rw [hb', phi_pow', ha, map_pow, hb', ← pow_mul, ← pow_mul, mul_comm]

theorem mem_rootsBar {f : (ZMod g)[X]} (hf : f ≠ 0) {x : Fbar g} : x ∈ rootsBar f ↔ aeval x f = 0 := by
  have := mem_aroots (p := f) (S := Fbar g) (a := x)
  rw [aroots_def] at this
  rw [rootsBar, this]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩

theorem mem_roots_minpoly {x y : Fbar g} :
    y ∈ rootsBar (minpoly (ZMod g) x) ↔ ∃ s : Fbar g ≃ₐ[ZMod g] Fbar g, s x = y := by
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  rw [mem_rootsBar (minpoly.ne_zero hi)]
  constructor
  · exact minpoly.exists_algEquiv_of_root' hi.isAlgebraic
  · rintro ⟨s, rfl⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]

theorem nodup_minpoly (x : Fbar g) : (rootsBar (minpoly (ZMod g) x)).Nodup := by
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  exact nodup_roots (PerfectField.separable_of_irreducible (minpoly.irreducible hi)).map

theorem roots_minpoly_phi (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) :
    rootsBar (minpoly (ZMod g) (phi L τ x)) = (rootsBar (minpoly (ZMod g) x)).map (phi L τ) := by
  rw [Multiset.Nodup.ext (nodup_minpoly _) ((nodup_minpoly x).map (phi_injective L τ))]
  intro y
  rw [mem_roots_minpoly, Multiset.mem_map]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s x, mem_roots_minpoly.2 ⟨s, rfl⟩, phi_gal L τ s x⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨s, rfl⟩ := mem_roots_minpoly.1 hz
    exact ⟨s, (phi_gal L τ s x).symm⟩

theorem rootsBar_mul {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    rootsBar (f * h) = rootsBar f + rootsBar h := by
  rw [rootsBar, rootsBar, rootsBar, Polynomial.map_mul, roots_mul]
  exact mul_ne_zero (Polynomial.map_ne_zero hf) (Polynomial.map_ne_zero hh)

theorem eq_of_rootsBar {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic) (e : rootsBar f = rootsBar h) :
    f = h := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Fbar g)) (algebraMap (ZMod g) (Fbar g)).injective
  rw [(IsAlgClosed.splits (f.map _)).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (h.map _)).eq_prod_roots_of_monic (hh.map _)]
  exact congrArg (fun m : Multiset (Fbar g) => (m.map fun a => X - C a).prod) e

theorem card_rootsBar (f : (ZMod g)[X]) : (rootsBar f).card = f.natDegree := by
  rw [rootsBar, ← (IsAlgClosed.splits (f.map _)).natDegree_eq_card_roots, natDegree_map]

theorem exists_minpoly {P : (ZMod g)[X]} (hm : P.Monic) (hP : Irreducible P) :
    ∃ x : Fbar g, P = minpoly (ZMod g) x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) P (degree_pos_of_irreducible hP).ne'
  exact ⟨x, minpoly.eq_of_irreducible_of_monic hP hx hm⟩

def Rel (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (f f' : (ZMod g)[X]) : Prop :=
  f'.Monic ∧ rootsBar f' = (rootsBar f).map (phi L τ)

theorem Rel.mul {L : LabelDatum g} {τ : ℂ ≃+* ℂ} {f f' h h' : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0)
    (h1 : Rel L τ f f') (h2 : Rel L τ h h') : Rel L τ (f * h) (f' * h') :=
  ⟨h1.1.mul h2.1, by
    rw [rootsBar_mul h1.1.ne_zero h2.1.ne_zero, rootsBar_mul hf hh, h1.2, h2.2, Multiset.map_add]⟩

theorem Rel.unique {L : LabelDatum g} {τ : ℂ ≃+* ℂ} {f f' f'' : (ZMod g)[X]}
    (h1 : Rel L τ f f') (h2 : Rel L τ f f'') : f' = f'' :=
  eq_of_rootsBar h1.1 h2.1 (h1.2.trans h2.2.symm)

theorem Rel.symm {L : LabelDatum g} {τ : ℂ ≃+* ℂ} {f f' : (ZMod g)[X]} (hf : f.Monic)
    (h1 : Rel L τ f f') : Rel L τ.symm f' f :=
  ⟨hf, by rw [h1.2, Multiset.map_map]; simp [phi_symm]⟩

theorem rel_minpoly (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (x : Fbar g) :
    Rel L τ (minpoly (ZMod g) x) (minpoly (ZMod g) (phi L τ x)) :=
  ⟨minpoly.monic (Algebra.IsIntegral.isIntegral _), roots_minpoly_phi L τ x⟩

theorem rel_one (L : LabelDatum g) (τ : ℂ ≃+* ℂ) : Rel L τ 1 1 :=
  ⟨monic_one, by simp [rootsBar]⟩

theorem exists_rel (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (n : ℕ) :
    ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → ∃ f', Rel L τ f f' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
    by_cases h1 : f = 1
    · exact ⟨1, h1 ▸ rel_one L τ⟩
    · have hu : ¬ IsUnit f := fun hu => h1 (hf.isUnit_iff.1 hu)
      obtain ⟨P, hPm, hP, h, rfl⟩ := exists_monic_irreducible_factor f hu
      have hh : h.Monic := hPm.of_mul_monic_left hf
      have hd : h.natDegree < n := by
        rw [← hn, hPm.natDegree_mul hh]
        have := hP.natDegree_pos
        omega
      obtain ⟨h', hh'⟩ := ih _ hd h hh rfl
      obtain ⟨x, rfl⟩ := exists_minpoly hPm hP
      exact ⟨_, (rel_minpoly L τ x).mul hPm.ne_zero hh.ne_zero hh'⟩

theorem theta_phi (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (d : ℕ) (x z : Fbar g) :
    thetaOf L d (phi L τ x) z = τ (thetaOf L d x z) := by
  unfold thetaOf
  split_ifs with h
  · rw [teich_phi, map_pow]
  · rw [map_zero]

theorem isCuspOf_map (L : LabelDatum g) (τ : ℂ ≃+* ℂ) {P : (ZMod g)[X]} {d : ℕ} {χ : Gn g d → ℂ}
    (h : IsCuspOf L P χ) : ∃ P', Rel L τ P P' ∧ IsCuspOf L P' (τ ∘ χ) := by
  obtain ⟨⟨hm, hi, h0, hd⟩, hc, hv⟩ := h
  obtain ⟨x, rfl⟩ := exists_minpoly hm hi
  have hr := rel_minpoly L τ x
  have hint : IsIntegral (ZMod g) (phi L τ x) := Algebra.IsIntegral.isIntegral _
  refine ⟨_, hr, ⟨hr.1, minpoly.irreducible hint, ?_, ?_⟩, (GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ).2.2 d χ hc, ?_⟩
  · intro h
    have h2 : (0 : Fbar g) ∈ rootsBar (minpoly (ZMod g) (phi L τ x)) := by
      rw [mem_rootsBar hr.1.ne_zero, ← coeff_zero_eq_aeval_zero', h, map_zero]
    rw [hr.2, Multiset.mem_map] at h2
    obtain ⟨y, hy, hy0⟩ := h2
    have hy1 : y = 0 := phi_injective L τ (hy0.trans (phi_zero L τ).symm)
    rw [hy1, mem_rootsBar hm.ne_zero, ← coeff_zero_eq_aeval_zero'] at hy
    exact h0 ((map_eq_zero _).1 hy)
  · rw [← card_rootsBar, hr.2, Multiset.card_map, card_rootsBar, hd]
  · intro x' hx' y hy z hz
    rw [hr.2, Multiset.mem_map] at hx'
    obtain ⟨w, hw, rfl⟩ := hx'
    rw [Function.comp_apply, hv w hw y hy z hz]
    simp only [theta_phi, map_mul, map_pow, map_neg, map_one, map_sum]

theorem list_map (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ p ∈ Q, IsCuspOf L p.1 p.2.2) :
    ∃ Q' : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q', IsCuspOf L p.1 p.2.2) ∧
      Q'.map Prod.snd = (Q.map Prod.snd).map (fun p => (⟨p.1, τ ∘ p.2⟩ : Pc g)) ∧
      (Q.map Prod.fst).prod.Monic ∧ Rel L τ (Q.map Prod.fst).prod (Q'.map Prod.fst).prod := by
  induction Q with
  | nil => exact ⟨[], by simp, rfl, monic_one, rel_one L τ⟩
  | cons p Q ih =>
    obtain ⟨Q', h1, h2, h3, h4⟩ := ih (fun q hq => hQ q (List.mem_cons_of_mem _ hq))
    have hp := hQ p List.mem_cons_self
    obtain ⟨P', hP1, hP2⟩ := isCuspOf_map L τ hp
    refine ⟨(P', ⟨p.2.1, τ ∘ p.2.2⟩) :: Q', ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hP2
      · exact h1 q hq
    · simp only [List.map_cons, h2]
    · simp only [List.map_cons, List.prod_cons]
      exact hp.1.1.mul h3
    · simp only [List.map_cons, List.prod_cons]
      exact hP1.mul hp.1.1.ne_zero h3.ne_zero h4

theorem hasLabel_map (L : LabelDatum g) (τ : ℂ ≃+* ℂ) {n : ℕ} {χ : Gn g n → ℂ} {f f' : (ZMod g)[X]}
    (hr : Rel L τ f f') (h : HasLabel L χ f) : HasLabel L (τ ∘ χ) f' := by
  obtain ⟨Q, hQ, hd, rfl, hip⟩ := h
  obtain ⟨Q', h1, h2, -, h4⟩ := list_map L τ Q hQ
  refine ⟨Q', h1, ?_, hr.unique h4, ?_⟩
  · rw [h2, ← hd, degL, degL, List.map_map]
    rfl
  · rw [h2, (GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ).2.1, ((GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ).1 _ χ).2.2]
    exact fun h => hip ((map_eq_zero τ).1 h)

theorem eSerC_map (L : LabelDatum g) (τ : ℂ ≃+* ℂ) (n : ℕ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hr : Rel L τ f f') :
    (eSerC L n f).coeff.mapRange τ (map_zero τ) = (eSerC L n f').coeff := by
  have hset : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f'} =
      (fun χ : Gn g n → ℂ => τ ∘ χ) '' {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} := by
    ext χ
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨τ.symm ∘ χ, ⟨((GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ.symm).1 _ χ).1 h1, hasLabel_map L τ.symm (hr.symm hf) h2⟩, ?_⟩
      funext x
      simp
    · rintro ⟨χ, ⟨h1, h2⟩, rfl⟩
      exact ⟨((GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ).1 _ χ).1 h1, hasLabel_map L τ hr h2⟩
  let E := MonoidAlgebra.mapAddEquiv (Gn g n) τ.toAddEquiv
  have hE : ∀ a : MonoidAlgebra ℂ (Gn g n), (E a).coeff = a.coeff.mapRange τ (map_zero τ) := fun a => by
    ext x
    rw [MonoidAlgebra.coeff_mapAddEquiv, Finsupp.mapRange_apply]
    rfl
  have hz : ∀ χ : Gn g n → ℂ, E (zOf χ) = zOf (τ ∘ χ) := fun χ => by
    ext x
    rw [hE, ((GlobalTheory.T.complexFieldAut_acts_harishChandra_characters g τ).1 _ χ).2.1]
  rw [← hE, eSerC, eSerC, hset, finsum_mem_image (τ.injective.comp_left.injOn)]
  congr 1
  rw [E.map_finsum]
  refine finsum_congr fun χ => ?_
  rw [E.map_finsum]
  exact finsum_congr fun _ => hz χ

theorem eSer_galois : Green → ∀ D : Formalism.BasicNotions.D7, ESerTie D → ∀ (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f → (D.ntypes.eSer k f).coeff.mapRange τ (map_zero τ) = (D.ntypes.eSer k (labAct D τ k f)).coeff := by
  intro _ D hD τ k f hf
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, hL, he⟩ := hD k
  rw [he, he]
  apply eSerC_map L τ _ hf.1
  have h := Classical.epsilon_spec (exists_rel L τ _ f hf.1 rfl)
  have e : labAct D τ k f = Classical.epsilon (Rel L τ f) := by
    unfold labAct Rel phi
    rw [hL]
  rw [e]
  exact h

end GlobalTheory.GLq.GalSer
