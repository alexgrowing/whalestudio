import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelTheta

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {ψ : Y ⟶ X} (φ : Z ⟶ Y) {χ : Z ⟶ X}
    (H : LBIso M (L.pull ψ)) (e : χ = φ ≫ ψ) : LBIso (M.pull φ) (L.pull χ) :=
  H.chartPull (chartPullPull M φ φ rfl)
    (chartPullSame L (fun _ : PUnit => χ) (fun _ : PUnit => ψ) (fun _ => 1) φ (fun _ => e))

theorem pow_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x' : Out.baseOver S' ⟶ G') (x : Out.baseOver S ⟶ G)
    (e : x'.left ≫ φ = f ≫ x.left) (m : ℕ) : (x' ^ m).left ≫ φ = f ≫ (x ^ m).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e₁ : pushHom h _ x' = preHom U x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ m) = preHom U (x ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e₂

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def Above {S S' : Scheme.{0}} (P : Out.PolAV S) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (m : ℕ) {s' : S' ⟶ Sp o} (t : TObj g k J b s') (f : S' ⟶ S) (ψ : t.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback t.A P.A f ψ ∧ LBIso t.L (P.L.pull ψ) ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ m).left ≫ ψ = f ≫ (Q i).left

theorem Above.comp {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s'}
    {u : TObj g k J b s''} {f : S' ⟶ S} {ψ : t.A.left ⟶ P.A.left} (h : Above P act Q m t f ψ) {f' : S'' ⟶ S'}
    {φ : u.A.left ⟶ t.A.left} (h₁ : IsGrpPullback u.A t.A f' φ) (h₂ : LBIso u.L (t.L.pull φ))
    (h₃ : ∀ i, (u.pt i).left ≫ φ = f' ≫ (t.pt i).left) (h₄ : ∀ j, (u.act j).left ≫ φ = φ ≫ (t.act j).left) :
    Above P act Q m u (f' ≫ f) (φ ≫ ψ) := by
  refine ⟨h₁.comp h.1, LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB P.isLB _) h₂
    (lbIso_pull_comp φ h.2.1 rfl), fun i => ?_, fun i => ?_⟩
  · rw [← Category.assoc, h₄, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, pow_push h₁ _ _ (h₃ i), Category.assoc, h.2.2.2, Category.assoc]

theorem Above.compare {S S' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {u u' : TObj g k J b s'}
    {f : S' ⟶ S} {ψ : u.A.left ⟶ P.A.left} {ψ' : u'.A.left ⟶ P.A.left} (h : Above P act Q m u f ψ)
    (h' : Above P act Q m u' f ψ') :
    ∃ χ : u'.A.left ⟶ u.A.left, χ ≫ ψ = ψ' ∧ IsGrpPullback u'.A u.A (𝟙 _) χ ∧ LBIso u'.L (u.L.pull χ) ∧
      (∀ i, (u'.pt i ^ m).left ≫ χ = (u.pt i ^ m).left) ∧ ∀ j, (u'.act j).left ≫ χ = χ ≫ (u.act j).left := by
  have hp := h.1.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom h'.1.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  refine ⟨χ, e₁, h.1.cancel (h'.1.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id]),
    LBIso.trans u'.isLB (pull_isLB P.isLB _) (pull_isLB u.isLB _) h'.2.1
      (lbIso_pull_comp χ h.2.1 e₁.symm).symm, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.2, h.2.2.2]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.1, Category.assoc, h.2.2.1, ← Category.assoc, e₁]
    · rw [Category.assoc, e₂, Over.w, Category.assoc, Over.w, e₂]

theorem exists_level_with_theta_point : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  intro hL hL2 g n j J hn hodd hj o _ b R _ _ _ β v P act Q hP hdense
  have hn2 : 2 ≤ n := hn.two_le
  have hpos : 0 < n ^ j := pow_pos hn.pos j
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h3 : 3 ≤ n ^ j := by
    have h4 : 2 ^ 2 ≤ n ^ j := (Nat.pow_le_pow_left hn2 2).trans (Nat.pow_le_pow_right hn.pos hj)
    omega
  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, hab, huniv⟩ := GlobalTheory.exists_finiteEtale_level_cover hL hL2 o g (n ^ j) J b R β P act Q hpos hP
  have hab' : Above P act Q (n ^ j) t₁ (spMap (algebraMap R R₁)) ψ₁ := hab
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨K, _, _, x, t', ψ, hker, hth, -⟩, -, hqp, -⟩ :=
      hdense q 1 hq.isPrime (fun h => hq.ne_top ((Ideal.eq_top_iff_one _).2 h))
    obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh hL hL2 o g (n ^ j) J b _ _ t' n K (𝟙 _) _ ⊥ hn2 hdvd hth Ideal.isPrime_bot 0
    apply hc
    have : v (0 + (n ^ j / n) • c) ∈ RingHom.ker x := hker ▸ hqp (hle (Ideal.subset_span ⟨_, rfl⟩))
    exact this
  have hspan₁ : Ideal.span (Set.range fun a => algebraMap R R₁ (v a)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R₁)) hspan
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff hL hL2 o g (n ^ j) J b R₁ _ t₁ _ hodd.pow h3 hspan₁

  have hth : ∀ (R' : Type) [CommRing R'] (x : R →+* R') (y : R₁ →+* R') (s' : Sp R' ⟶ Sp o)
      (t' : TObj g ((n ^ j) ^ 2) J b s'), y.comp (algebraMap R R₁) = x → TMap t' t₁ (spMap y) →
      (t'.HasTh (𝟙 _) (fun a => x (v a)) ↔ ∀ r ∈ 𝔞, y r = 0) := by
    intro R' _ x y s' t' e hm
    subst e
    rw [GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ t' _ R' _ _ hm, Category.id_comp]
    exact h𝔞 R' y

  have huniq : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = x → y'.comp (algebraMap R R₁) = x → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) →
      y = y' := by
    intro K _ _ x y y' e e' k k'
    have d : spMap y ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e]
    have d' : spMap y' ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e']
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y) t₁ (by rw [← Category.assoc, d])
    obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y') t₁ (by rw [← Category.assoc, d'])
    have T := (hth K x y _ u e hu).2 k
    have T' := (hth K x y' _ u' e' hu').2 k'
    obtain ⟨φ, a₁, a₂, a₃, a₄⟩ := id hu
    obtain ⟨φ', a₁', a₂', a₃', a₄'⟩ := id hu'
    have A := hab'.comp a₁ a₂ a₃ a₄
    have A' := hab'.comp a₁' a₂' a₃' a₄'
    rw [d] at A
    rw [d'] at A'
    obtain ⟨χ, c₀, c₁, c₂, c₃, c₄⟩ := A.compare A'
    have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ T T'
    have hχ : TMap u' u (𝟙 _) := ⟨χ, c₁, c₂, fun i => by rw [c₅, Category.id_comp], c₄⟩
    have hm : TMap u' t₁ (spMap y) := by
      have := ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ u u').2 _ _ hu).1 hχ
      rwa [Category.id_comp] at this
    refine (huniv K x u' (φ' ≫ ψ₁) A').unique ⟨e, fun i => ?_, hm⟩ ⟨e', fun i => ?_, hu'⟩
    · rw [← c₀, ← Category.assoc, c₅, ← Category.assoc, a₃, Category.assoc]
    · rw [← Category.assoc, a₃', Category.assoc]
  have hcomp : (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) = algebraMap R (R₁ ⧸ 𝔞) := rfl
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R 𝔞) Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap R (R₁ ⧸ 𝔞)) := by
    refine GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point R (R₁ ⧸ 𝔞) _ hdense ?_
    rintro q ⟨K, _, _, x, t', ψ, hker, T, A⟩
    obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y k, ?_, fun z hz => ?_⟩
    · exact e
    · have := huniq K x (z.comp (Ideal.Quotient.mk 𝔞)) y hz e
        (fun r hr => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]) k
      exact Ideal.Quotient.ringHom_ext (this.trans (by ext r; rfl))
  let ε : R ≃+* R₁ ⧸ 𝔞 := RingEquiv.ofBijective _ hbij
  let ρ : R₁ →+* R := (ε.symm : R₁ ⧸ 𝔞 →+* R).comp (Ideal.Quotient.mk 𝔞)
  have hρ : ρ.comp (algebraMap R R₁) = RingHom.id R := RingHom.ext fun r => ε.symm_apply_apply r
  have hρ' : ∀ r, r - algebraMap R R₁ (ρ r) ∈ 𝔞 := fun r =>
    Ideal.Quotient.eq.1 (ε.apply_symm_apply (Ideal.Quotient.mk 𝔞 r)).symm
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap β) (spMap ρ) t₁
    (by rw [← Category.assoc, spMap_comp, hρ, spMap_id, Category.id_comp])
  refine ⟨t, (hth R (RingHom.id R) ρ _ t hρ ht).2 fun r hr => ?_, fun K _ _ x t' ψ T A => ?_⟩
  · show ε.symm (Ideal.Quotient.mk 𝔞 r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  · obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    have hy : x.comp ρ = y := RingHom.ext fun r => by
      have := k _ (hρ' r)
      rw [map_sub, sub_eq_zero] at this
      rw [this, ← e]; rfl
    refine ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ t t').2 _ _ ht).2 ?_
    rwa [spMap_comp ρ x, hy]

end GlobalTheory.LevelTheta
