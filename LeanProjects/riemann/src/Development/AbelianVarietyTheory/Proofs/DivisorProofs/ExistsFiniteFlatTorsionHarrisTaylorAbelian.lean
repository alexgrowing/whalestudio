import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeIntActionHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProductStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTTors

open GlobalTheory.IwLevel GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

def actF (o : Obj b N s) : Out.RingAct o.A (𝓞 D.F) :=
  ⟨fun c => o.act.act (algebraMap (𝓞 D.F) D.O c), fun _ => o.act.hom _,
   by rw [map_one]; exact o.act.one,
   fun _ _ => by rw [map_mul]; exact o.act.mul _ _,
   fun _ _ => by rw [map_add]; exact o.act.add _ _⟩

theorem killedBy_map (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    KilledBy (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy (actF o) w x := by
  rw [Ideal.map, killedBy_span]
  exact Set.forall_mem_image

theorem inSub_ker {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {T : Over S} (x : T ⟶ A) :
    InSub (pullback.fst f η[B]) x ↔ x ≫ f = 1 := by
  refine ⟨?_, fun h => ⟨KerGrp.lift f x h, KerGrp.lift_fst _ _ _⟩⟩
  rintro ⟨y, rfl⟩
  rw [Category.assoc, KerGrp.fst_comp, MonObj.comp_one]

theorem comp_lift_eq_one {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) (a c : A ⟶ A) :
    x ≫ lift a c = 1 ↔ x ≫ a = 1 ∧ x ≫ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (· ≫ fst A A) h
    have h2 := congrArg (· ≫ snd A A) h
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.one_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, MonObj.one_comp]
    · rw [Category.assoc, lift_snd, h2, MonObj.one_comp]

theorem killedBy_pair {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A (𝓞 D.F)) (g e : 𝓞 D.F)
    {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span {g, e}) x ↔ x ≫ lift (ρ.act g) (ρ.act e) = 1 := by
  rw [killedBy_span, comp_lift_eq_one]
  simp

theorem htTorsion : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o w hw
  obtain ⟨g, e, 𝔟, hg0, he, hf, hmul, hp⟩ := GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField D.F p (Fact.out) w hw
  have hI2 := fun c hc => GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor p D R b N S s o c hc
  let ρ := actF o
  have hρ : ∀ c, IsMonHom (ρ.act c) := ρ.hom

  have hgw : g ∈ w * 𝔟 := by rw [hmul]; exact Ideal.mem_span_singleton_self g
  have hgw1 : g ∈ w := Ideal.mul_le_left (I := w) (J := 𝔟) hgw
  have hgw2 : g ∈ 𝔟 := Ideal.mul_le_right (I := w) (J := 𝔟) hgw
  have hw' : w = Ideal.span {g, e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = a * (1 - e) + a * e := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : a * (1 - e) ∈ w * 𝔟 := Ideal.mul_mem_mul ha hf
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw1, Set.singleton_subset_iff.2 he⟩)
  have h𝔟' : 𝔟 = Ideal.span {g, 1 - e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = e * a + a * (1 - e) := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : e * a ∈ w * 𝔟 := Ideal.mul_mem_mul he ha
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw2, Set.singleton_subset_iff.2 hf⟩)
  have hcop : w ⊔ 𝔟 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 D.F) = e + (1 - e) := by ring
    rw [h1]
    exact Submodule.add_mem_sup he hf
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmul
    exact hg0 hmul

  let f₁ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act e)
  let f₂ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act (1 - e))
  letI := KerGrp.grp f₁
  have h₁ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₁ η[o.A ⊗ o.A]) x ↔ KilledBy ρ w x := by
    intro T x; rw [inSub_ker, hw', killedBy_pair]
  have h₂ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₂ η[o.A ⊗ o.A]) x ↔ KilledBy ρ 𝔟 x := by
    intro T x; rw [inSub_ker, h𝔟', killedBy_pair]
  have h₃ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst (ρ.act g) η[o.A]) x ↔ KilledBy ρ (w * 𝔟) x := by
    intro T x; rw [inSub_ker, hmul, killedBy_span]; simp
  have d₃ : IsIsogDeg (toUnit (ker (ρ.act g)))
      (Ideal.absNorm w ^ (D.m * D.n) * Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
    rw [← mul_pow, ← map_mul, hmul, Ideal.absNorm_span_singleton]
    exact (hI2 g hg0).ker
  have d₂ : IsIsogDeg (toUnit (ker f₂)) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) :=
    GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor p D R b N S s o hI2 𝔟 hp _ (pullback.fst f₂ η[o.A ⊗ o.A]) inferInstance
      (fun T x => by rw [h₂, killedBy_map])
  have hpos : 0 < Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have d₁ := GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product S o.A (𝓞 D.F) ρ w 𝔟 hcop _ _ _ (pullback.fst f₁ η[o.A ⊗ o.A])
    (pullback.fst f₂ η[o.A ⊗ o.A]) (pullback.fst (ρ.act g) η[o.A]) inferInstance inferInstance inferInstance
    h₁ h₂ h₃ _ _ hpos d₃ d₂
  refine ⟨ker f₁, KerGrp.grp f₁, pullback.fst f₁ η[o.A ⊗ o.A], KerGrp.isMonHom_fst f₁, inferInstance,
    by rw [← pow_mul]; exact d₁, fun T x => by rw [h₁, killedBy_map]⟩

end GlobalTheory.HTTors
