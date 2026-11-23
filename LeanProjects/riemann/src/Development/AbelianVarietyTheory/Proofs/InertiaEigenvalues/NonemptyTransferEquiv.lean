import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteSurjectiveOfPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

noncomputable section
namespace GlobalTheory.HeckeCount
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pLat (D : Datum H) (p : ℕ) : AddSubgroup D.La := (DistribMulAction.toAddMonoidHom D.La p).range

theorem mem_pLat {D : Datum H} {p : ℕ} {a : D.La} : a ∈ pLat D p ↔ ∃ b, a = p • b := by
  simp [pLat, eq_comm]

def LatCount (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) : Type :=
  {N : AddSubgroup D.La // pLat D p ≤ N ∧ (∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) ∧
    (∀ a ∈ J, ∀ x ∈ N, a • x ∈ pLat D p) ∧ (pLat D p).relIndex N = m}

section Alg
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

def evA (p : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev p a)) fun a b => by rw [I.add]; rfl

theorem ker_evA {p : ℕ} (hp : 0 < p) : (evA I p).ker = pLat D p := by
  ext a
  rw [AddMonoidHom.mem_ker, mem_pLat, ← I.ker p hp a]
  exact ofMul_eq_zero

theorem relIndex_eq {p : ℕ} (hp : 0 < p) (N : AddSubgroup D.La) :
    (pLat D p).relIndex N = Nat.card (N.map (evA I p)) := by
  rw [← ker_evA I hp, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]

end Alg
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
section Alg2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

theorem card_toAdd (C : Subgroup Q) : Nat.card C.toAddSubgroup = Nat.card C :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun _ => Iff.rfl)

def datumEquiv {p : ℕ} (hp : 0 < p) (hnat : ∀ x, act (p : 𝓞 E) x = x ^ p) {J : Ideal (𝓞 E)}
    (hpJ : (p : 𝓞 E) ∈ J) {m : ℕ} (hm : m ≠ 0) :
    {C₀ : Subgroup Q // (∀ a, ∀ x ∈ C₀, act a x ∈ C₀) ∧ (∀ x ∈ C₀, ∀ a ∈ J, act a x = 1) ∧ Finite C₀ ∧
      Nat.card C₀ = m} ≃ LatCount D p J m where
  toFun C := ⟨C.1.toAddSubgroup.comap (evA I p), by
      rw [← ker_evA I hp]; exact AddMonoidHom.ker_le_comap _ _,
    fun a x hx => by
      show (I.ev p (a • x)) ∈ C.1
      rw [I.lin]; exact C.2.1 a _ hx,
    fun a ha x hx => by
      rw [← ker_evA I hp, AddMonoidHom.mem_ker]
      show Additive.ofMul (I.ev p (a • x)) = 0
      rw [I.lin, show act a (I.ev p x) = 1 from C.2.2.1 _ hx a ha]; rfl,
    by
      have hle : C.1.toAddSubgroup ≤ (evA I p).range := fun x hx => by
        have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
        obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
        exact ⟨a, ha⟩
      rw [relIndex_eq I hp, AddSubgroup.map_comap_eq, inf_eq_right.2 hle, card_toAdd]
      exact C.2.2.2.2⟩
  invFun N := ⟨Subgroup.toAddSubgroup.symm (N.1.map (evA I p)), by
      rintro a _ ⟨x, hx, rfl⟩
      exact ⟨a • x, N.2.2.1 a x hx, I.lin p a x⟩,
    by
      rintro _ ⟨x, hx, rfl⟩ a ha
      have h := N.2.2.2.1 a ha x hx
      rw [← ker_evA I hp, AddMonoidHom.mem_ker] at h
      show act a (I.ev p x) = 1
      rw [← I.lin]; exact h,
    by
      have : Nat.card (Subgroup.toAddSubgroup.symm (N.1.map (evA I p))) ≠ 0 := by
        rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp, N.2.2.2.2]; exact hm
      exact Nat.finite_of_card_ne_zero this,
    by rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp]; exact N.2.2.2.2⟩
  left_inv C := by
    apply Subtype.ext
    show Subgroup.toAddSubgroup.symm _ = C.1
    rw [AddSubgroup.map_comap_eq, OrderIso.symm_apply_eq]
    refine inf_eq_right.2 fun x hx => ?_
    have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
    obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
    exact ⟨a, ha⟩
  right_inv N := by
    apply Subtype.ext
    show AddSubgroup.comap (evA I p) (Subgroup.toAddSubgroup (Subgroup.toAddSubgroup.symm (N.1.map (evA I p)))) = N.1
    rw [OrderIso.apply_symm_apply, AddSubgroup.comap_map_eq, ker_evA I hp]
    exact sup_eq_left.2 N.2.1

end Alg2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}

include hL in

theorem map_pow_eq (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) {C₀ : Subgroup (Pts o.t)} (h₀ : IsHeckeDatum o.t P i C₀)
    (e : (C : Set (Pts o.t)) = heckeKernel o.t p P C₀) : C.map (powMonoidHom p) = C₀ := by
  have hcard : Nat.card (C.map (powMonoidHom p)) = Ideal.absNorm P ^ i := by
    obtain ⟨-, -, -, -, c₅, c₆⟩ := hC
    obtain ⟨-, -, hp, -, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨-, -, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₁ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact mul_left_cancel₀ h₁.1 (hm.symm.trans c₆)
  have : Finite C₀ := h₀.2.2.1
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, h₀.2.2.2])
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ heckeKernel o.t p P C₀ := e ▸ hx
  obtain ⟨x₁, x₂, x₃, rfl, ⟨t₁, -⟩, ⟨-, k₂⟩, ⟨t₃, -⟩⟩ := hx'
  show (x₁ * x₂ * x₃) ^ p ∈ C₀
  rw [mul_pow, mul_pow, t₁, t₃, _root_.one_mul, _root_.mul_one]
  exact k₂

include hL in
theorem isHeckeDatum_map_pow (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) : IsHeckeDatum o.t P i (C.map (powMonoidHom p)) := by
  obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C).1 hC
  rw [map_pow_eq hL o h hC h₀ e]
  exact h₀

def heckeKerEquivDatum (h : IsSplitPrimeOff l p P) (i : ℕ) :
    {C : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C} ≃
      {C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} where
  toFun C := ⟨C.1.map (powMonoidHom p), isHeckeDatum_map_pow hL o h C.2⟩
  invFun C₀ := ⟨(exists_heckeKer_of_datum hL o h C₀.2).choose,
    (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2⟩
  left_inv C := by
    apply Subtype.ext
    apply SetLike.coe_injective
    obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C.1).1 C.2
    have hm := map_pow_eq hL o h C.2 h₀ e
    refine (exists_heckeKer_of_datum hL o h (isHeckeDatum_map_pow hL o h C.2)).choose_spec.1.trans ?_
    simp only [hm]
    exact e.symm
  right_inv C₀ := by
    apply Subtype.ext
    exact map_pow_eq hL o h (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2 C₀.2
      (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.1

end Fibre
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}

include hL in
theorem nonempty_datum_equiv (h : IsSplitPrimeOff l p P) (i : ℕ) :
    Nonempty ({C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} ≃
      LatCount D p (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  obtain ⟨hP, -, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, -, -⟩ := tate_facts hL o
  have h0 : Ideal.absNorm P ≠ 0 := fun e => by
    rw [Ideal.absNorm_eq_zero_iff.1 e] at hpP
    exact Nat.cast_ne_zero.2 hp.pos.ne' (Ideal.mem_bot.1 hpP)
  exact ⟨(Equiv.subtypeEquivRight fun C₀ => Iff.rfl).trans
    (datumEquiv I hp.pos (fun x => (isAct_ptAct o.t _).nat p x) (natCast_mem_conj hpP) (pow_ne_zero i h0))⟩

end Fibre2

section Transfer2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem nonempty_transfer_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    (P : Ideal (𝓞 E)) (p i : ℕ) :
    Nonempty ({C' : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C'} ≃
      {C : Subgroup (Over.mk y ⟶ u.t.G) // u.t.HeckeKer (Over.mk y) D P p i C}) := by
  obtain ⟨ρ, -, e₀, -⟩ := exists_fibre_equiv u m
  have hx : ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → x₀ = ρ x := fun x x₀ h =>
    Over.OverMorphism.ext (h.trans (e₀ x).symm)
  have same : ∀ C : Subgroup (Over.mk y ⟶ u.t.G), SamePoints m (C.comap ρ.toMonoidHom : Set (Pts o.t)) C :=
    fun C x x₀ h => by rw [hx x x₀ h]; rfl
  refine ⟨{ toFun := fun C' => ⟨C'.1.map ρ.toMonoidHom, ?_⟩
            invFun := fun C => ⟨C.1.comap ρ.toMonoidHom, (heckeKer_transfer m (same C.1) P p i).1 C.2⟩
            left_inv := fun C' => Subtype.ext (Subgroup.comap_map_eq_self_of_injective ρ.injective _)
            right_inv := fun C => Subtype.ext (Subgroup.map_comap_eq_self_of_surjective ρ.surjective _) }⟩
  refine (heckeKer_transfer m (same _) P p i).2 ?_
  rw [Subgroup.comap_map_eq_self_of_injective ρ.injective]
  exact C'.2

end Transfer2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

theorem card_hkKer_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q → ∃ n : ℕ, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
      (z : FrPt Xo c Ω), Nonempty (Fin n ≃ hkKer (Xo := Xo) P q i Ω z) := by
  intro E _ _ _ H Dw l Xo c P q i hP
  refine ⟨Nat.card (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)), fun Ω _ _ _ z => ?_⟩
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  let e : hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i) :=
    eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)
  have : Finite (hkKer (Xo := Xo) P q i Ω z) :=
    GlobalTheory.HeckePointLaw.finite_heckeKer hs.1.pos hs.2.2.1 i z.x
  have : Finite (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := Finite.of_equiv _ e
  exact ⟨(Finite.equivFin _).symm.trans e.symm⟩

end GlobalTheory.HeckeCount
