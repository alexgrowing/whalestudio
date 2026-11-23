import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSumStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftDiff

theorem spMap_fst_surjective {B : Type} [CommRing B] (f : DualNumber B →+* B) (hf : ∀ c, f c = c.fst) :
    Function.Surjective (spMap f) := by
  intro q
  refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap B (DualNumber B) (f c) ∈ q.asIdeal ↔ c ∈ q.asIdeal
  rw [hf]
  have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem le_preimage_of_red {B : Type} [CommRing B] {X : Scheme.{0}} (f : DualNumber B →+* B)
    (hf : ∀ c, f c = c.fst) {y : Sp (DualNumber B) ⟶ X} {x : Sp B ⟶ X} (e : spMap f ≫ y = x) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_fst_surjective f hf p
  have := h (Set.mem_univ q)
  rw [← e] at this
  exact this

theorem ev_eq_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (ω : Form s)
    {T₁ T₂ T : Thick (dp0 R) s} (a : T₁ ⟶ T₂) (ψ : T₂ ⟶ T) (φ : T₁ ⟶ T) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (e : a ≫ ψ = φ) : ev ω.1 φ = ev ω.1 ψ := by
  rw [← e, ev_comp, show ev ω.1 a = 0 from ω.2 a h₁ h₂, map_zero, zero_add]

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem ev_sec_sub_ev_tan (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) :
    ∃ (hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
        spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
        ((fibMor h).isMor.obj P.ext).x)
      (ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x),
      ev ((fibMor h).isMor.pullForm ω).1 P.sec - ev ((fibMor h).isMor.pullForm ω).1 (P.tan hv) =
        ev ω.1 (idLift _ _ hc ec) - ev ω.1 (idLift _ _ ht et) := by
  let g : DualNumber K →+* P.B := (algebraMap K P.B).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have w : (P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap g := ((fibMor h).isMor.obj P.triv).w
  have hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) := by
    rw [Category.assoc, w]
    exact (Cris.spMap_comp g (algebraMap P.B (DualNumber P.B))).symm.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))
  have ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
      ((fibMor h).isMor.obj P.ext).x := by
    let π' : DualNumber P.B →+* P.B := TrivSqZeroExt.fstHom K P.B P.B
    have e : π'.comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := RingHom.ext fun _ ↦ rfl
    show spMap π' ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i = P.x ≫ i
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  have ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) :=
    ((fibMor h).isMor.obj (P.tr v).triv).w
  have et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) ((P.isTransl_trx v).red hv))
  refine ⟨hc, ec, ht, et, ?_⟩
  refine congrArg₂ (· - ·) (ev_eq_of_triv ω ?a (idLift _ _ hc ec) ((fibMor h).isMor.functor.map P.sec) rfl rfl ?ea)
    (ev_eq_of_triv ω ?b (idLift _ _ ht et) ((fibMor h).isMor.functor.map (P.tan hv)) rfl rfl ?eb)
  case a =>
    exact { φ := { algebraMap P.B (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := algebraMap P.B (DualNumber P.B)
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := rfl }
  case b =>
    exact { φ := { RingHom.id (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := RingHom.id _
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := by
              show spMap (RingHom.id (DualNumber P.B)) ≫ P.trx v ≫ i = P.trx v ≫ i
              rw [Cris.spMap_id, Category.id_comp] }
  case ea => exact Thick.hom_ext fun _ ↦ rfl
  case eb => exact Thick.hom_ext fun _ ↦ rfl

theorem liftVal_sub_snd : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  intro K _ A _ A' _ i h hA ω U hU P hP y₁ y₂ h₁ h₂ n u c hu hdiff
  obtain ⟨m, r, t, H⟩ := GlobalTheory.T.exists_crystallineForm_lift_difference_eq_sum (DualNumber K) A'.left (A'.hom ≫ 𝟙 _) ω U hU
  have hPU : ⊤ ≤ (P.x ≫ i) ⁻¹ᵁ U := hP
  have red : ∀ c : DualNumber P.B, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) c = c.fst :=
    fun _ ↦ rfl
  have hU₁ : ⊤ ≤ y₁ ⁻¹ᵁ U := le_preimage_of_red _ red h₁.2 hPU
  have hU₂ : ⊤ ≤ y₂ ⁻¹ᵁ U := le_preimage_of_red _ red h₂.2 hPU
  have k1 := H ((liftMor (epsDP K) h).isMor.obj P.eps) (SqExt.ofModule K P.B P.B).sq rfl y₁ y₂ h₁.1 h₂.1
    h₁.2 h₂.2 hU₁ hU₂
  have e1 : liftVal h ω.1 h₁ - liftVal h ω.1 h₂ =
      -∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
    rw [← neg_sub]; exact congrArg Neg.neg k1
  have f2 : ∀ f, (valR y₂ U f).fst = valR P.x (i ⁻¹ᵁ U) ((i.app U).hom f) := fun f ↦ by
    rw [← GlobalTheory.Points.valR_comp, ← h₂.2, GlobalTheory.Points.valR_spMap_comp _ _ _ hU₂]; exact (red _).symm
  have step2 : ∀ a, ∑ k, valR P.x (i ⁻¹ᵁ U) ((i.app U).hom (r k)) *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd =
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
    intro a
    have X := ev_sec_sub_ev_tan (K := K) (A := A) (A' := A') (i := i) h ω P (hu a)
    obtain ⟨hc, ec, ht, et, E⟩ := X
    have F := GlobalTheory.T.invariantForm_abelianVariety_translate_value K A hA (u a) (hu a) ((fibMor h).isMor.pullForm ω) P
    have hUt : ⊤ ≤ (P.trx (u a) ≫ i) ⁻¹ᵁ U := fun p hp ↦ hP.tr (hu a) hp
    have hUc : ⊤ ≤ (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ⁻¹ᵁ U :=
      fun _ _ ↦ hPU (Set.mem_univ _)
    have k2 := H ((fibMor h).isMor.obj P.ext) (SqExt.ofModule K P.B P.B).sq rfl _ _ ht hc et ec hUt hUc
    have F3 : (∑ k, valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (r k) *
        (valR (P.trx (u a) ≫ i) U (t k) - valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (t k))) =
        TrivSqZeroExt.inr (algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω))) := k2.symm.trans (E.symm.trans F)
    have F' := congrArg (fun z : DualNumber P.B ↦ z.snd) F3
    simp only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sum] at F'
    rw [← F']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_comp,
      GlobalTheory.Points.valR_comp, GlobalTheory.Points.valR_comp]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have D : ∀ k, valR y₁ U (t k) - valR y₂ U (t k) = TrivSqZeroExt.inr (∑ a, c a *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd) := fun k ↦ hdiff (t k)
  refine (congrArg (fun z : DualNumber P.B ↦ z.snd) e1).trans ?_
  have G := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ congrArg (valR y₂ U (r k) * ·) (D k)
  refine (congrArg (fun z : DualNumber P.B ↦ (-z).snd) G).trans ?_
  simp only [TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, f2, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.op_zero,
    MulOpposite.unop_zero, mul_zero, zero_smul, add_zero, neg_inj]
  simp only [← step2, Finset.mul_sum]
  clear H k1 e1 hdiff D G step2 f2 red
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.CechKS.LiftDiff
