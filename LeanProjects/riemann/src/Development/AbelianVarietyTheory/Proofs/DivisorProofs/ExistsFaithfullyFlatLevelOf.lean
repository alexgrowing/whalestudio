import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFlatUniversalTorsionTuple
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.LevFlat

section Alg

variable {M O : Type} [CommGroup M] [CommRing O] (ρ : O → M →* M)

structure IsAct : Prop where
  add : ∀ a b x, ρ (a + b) x = ρ a x * ρ b x
  one : ∀ x, ρ 1 x = x
  mul : ∀ a b x, ρ (a * b) x = ρ b (ρ a x)

variable {ρ}

theorem IsAct.zero (h : IsAct ρ) (x : M) : ρ 0 x = 1 := by
  have := h.add 0 0 x
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem IsAct.natCast (h : IsAct ρ) (n : ℕ) (x : M) : ρ (n : O) x = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, h.zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, h.add, ih, h.one, pow_succ]

theorem IsAct.add_mul_eq (h : IsAct ρ) {N : ℕ} {x : M} (hx : x ^ N = 1) (a c : O) :
    ρ (a + (N : O) * c) x = ρ a x := by
  rw [h.add, h.mul, h.natCast, hx, map_one, _root_.mul_one]

theorem IsAct.sub (h : IsAct ρ) (a b : O) (x : M) : ρ (a - b) x = ρ a x * (ρ b x)⁻¹ := by
  have := h.add (a - b) b x
  rw [sub_add_cancel] at this
  rw [this, mul_inv_cancel_right]

def comb (ρ : O → M →* M) (u : Fin 2 → M) (a b : O) : M := ρ a (u 0) * ρ b (u 1)

theorem comb_pow (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1) (a b : O) :
    comb ρ u a b ^ N = 1 := by
  rw [comb, mul_pow, ← map_pow, ← map_pow, hu, hu, map_one, map_one, _root_.mul_one]

theorem comb_sub (h : IsAct ρ) (u : Fin 2 → M) (a b a' b' : O) :
    comb ρ u (a - a') (b - b') = comb ρ u a b * (comb ρ u a' b')⁻¹ := by
  simp only [comb]
  rw [h.sub, h.sub, mul_inv, _root_.mul_mul_mul_comm]

variable (O) in

def rep (N : ℕ) : O ⧸ Ideal.span {(N : O)} → O :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : O)}))

theorem mk_rep (N : ℕ) (q : O ⧸ Ideal.span {(N : O)}) : Ideal.Quotient.mk _ (rep O N q) = q :=
  Function.surjInv_eq _ q

theorem exists_rep_eq (N : ℕ) (a : O) : ∃ c, rep O N (Ideal.Quotient.mk _ a) = a + (N : O) * c := by
  have h := mk_rep N (Ideal.Quotient.mk (Ideal.span {(N : O)}) a)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc]; ring⟩

theorem comb_rep (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1) (a b : O) :
    comb ρ u (rep O N (Ideal.Quotient.mk _ a)) (rep O N (Ideal.Quotient.mk _ b)) = comb ρ u a b := by
  obtain ⟨c, hc⟩ := exists_rep_eq N a
  obtain ⟨d, hd⟩ := exists_rep_eq N b
  rw [comb, comb, hc, hd, h.add_mul_eq (hu 0), h.add_mul_eq (hu 1)]

theorem mk_eq_zero_iff (N : ℕ) (a : O) : Ideal.Quotient.mk (Ideal.span {(N : O)}) a = 0 ↔ (N : O) ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem inj_of_ne (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1)
    (hne : ∀ q : (O ⧸ Ideal.span {(N : O)}) × (O ⧸ Ideal.span {(N : O)}), q ≠ 0 →
      comb ρ u (rep O N q.1) (rep O N q.2) ≠ 1) (a b : O) (hab : comb ρ u a b = 1) :
    (N : O) ∣ a ∧ (N : O) ∣ b := by
  by_contra hn
  refine hne (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b) (fun h0 => hn ?_) ((comb_rep h hu a b).trans hab)
  rw [Prod.ext_iff] at h0
  exact ⟨(mk_eq_zero_iff N a).1 h0.1, (mk_eq_zero_iff N b).1 h0.2⟩

def combQ (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1)
    (q : (O ⧸ Ideal.span {(N : O)}) × (O ⧸ Ideal.span {(N : O)})) : {y : M // y ^ N = 1} :=
  ⟨comb ρ u (rep O N q.1) (rep O N q.2), comb_pow h hu _ _⟩

theorem combQ_injective (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1)
    (hinj : ∀ a b, comb ρ u a b = 1 → (N : O) ∣ a ∧ (N : O) ∣ b) : Function.Injective (combQ h hu) := by
  intro q q' hqq
  have e : comb ρ u (rep O N q.1 - rep O N q'.1) (rep O N q.2 - rep O N q'.2) = 1 := by
    rw [comb_sub h, mul_inv_eq_one]
    exact congrArg Subtype.val hqq
  obtain ⟨h1, h2⟩ := hinj _ _ e
  rw [← mk_eq_zero_iff, map_sub, mk_rep, mk_rep, sub_eq_zero] at h1 h2
  exact Prod.ext h1 h2

theorem combQ_surjective (h : IsAct ρ) {N : ℕ} {u : Fin 2 → M} (hu : ∀ i, u i ^ N = 1)
    (hsurj : ∀ y, y ^ N = 1 → ∃ a b, y = comb ρ u a b) : Function.Surjective (combQ h hu) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, b, rfl⟩ := hsurj y hy
  exact ⟨(Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b), Subtype.ext (comb_rep h hu a b)⟩

theorem surj_of_basis (h : IsAct ρ) {N : ℕ} [Finite (O ⧸ Ideal.span {(N : O)})] {u p : Fin 2 → M}
    (hu : ∀ i, u i ^ N = 1) (hp : ∀ i, p i ^ N = 1)
    (huinj : ∀ a b, comb ρ u a b = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (hpinj : ∀ a b, comb ρ p a b = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (hpsurj : ∀ y, y ^ N = 1 → ∃ a b, y = comb ρ p a b) :
    ∀ y, y ^ N = 1 → ∃ a b, y = comb ρ u a b := by
  have hg : Function.Bijective (combQ h hp) := ⟨combQ_injective h hp hpinj, combQ_surjective h hp hpsurj⟩
  let e := Equiv.ofBijective _ hg
  haveI : Finite {y : M // y ^ N = 1} := Finite.of_equiv _ e
  have hf : Function.Bijective (combQ h hu) :=
    (combQ_injective h hu huinj).bijective_of_nat_card_le (Nat.card_congr e).ge
  intro y hy
  obtain ⟨q, hq⟩ := hf.2 ⟨y, hy⟩
  exact ⟨_, _, (congrArg Subtype.val hq).symm⟩

end Alg

end GlobalTheory.RealMult.LevFlat

namespace GlobalTheory.RealMult

def TorsionFreeRankTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b)

namespace LevFlat

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def ptAct {S : Scheme.{0}} (X : Obj F 𝔠 S) (T : Over S) (a : 𝓞 F) : (T ⟶ X.A) →* (T ⟶ X.A) where
  toFun x := x ≫ X.rm.act a
  map_one' := by
    haveI := X.rm.hom a
    exact MonObj.one_comp _
  map_mul' x y := by
    haveI := X.rm.hom a
    exact MonObj.mul_comp x y _

theorem ptAct_apply {S : Scheme.{0}} (X : Obj F 𝔠 S) (T : Over S) (a : 𝓞 F) (x : T ⟶ X.A) :
    ptAct X T a x = x ≫ X.rm.act a := rfl

theorem isAct_ptAct {S : Scheme.{0}} (X : Obj F 𝔠 S) (T : Over S) : IsAct (ptAct X T) where
  add a b x := by
    rw [ptAct_apply, ptAct_apply, ptAct_apply, X.rm.add, MonObj.comp_mul]
  one x := by rw [ptAct_apply, X.rm.one, Category.comp_id]
  mul a b x := by rw [ptAct_apply, ptAct_apply, ptAct_apply, X.rm.mul, Category.assoc]

theorem comp_comb {S : Scheme.{0}} (X : Obj F 𝔠 S) {T T' : Over S} (g : T' ⟶ T) (u : Fin 2 → (T ⟶ X.A))
    (a b : 𝓞 F) : g ≫ comb (ptAct X T) u a b = comb (ptAct X T') (fun i => g ≫ u i) a b := by
  simp only [comb, ptAct_apply]
  rw [MonObj.comp_mul, Category.assoc, Category.assoc]

theorem finEt {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) {N : ℕ} (hN : IsUnit (N : R)) :
    (IsFinite (Out.mulA X.A N).left ∧ Flat (Out.mulA X.A N).left) ∧
      IsFinite (torsion X.A N).hom ∧ Etale (torsion X.A N).hom := by
  haveI := X.ab
  have hu : IsUnit (N : Γ(Sp R, ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion X.A hu
  have e : Out.mulA X.A N = mulN X.A N := (GlobalTheory.GrpTangent.mulN_eq_pow X.A N).symm
  rw [e]
  haveI := h2
  exact ⟨⟨h1, inferInstance⟩, h3, h4⟩

theorem exists_idem {R B : Type} [CommRing R] [CommRing B] (X : Obj F 𝔠 (Sp R)) {N : ℕ}
    [IsFinite (torsion X.A N).hom] [Etale (torsion X.A N).hom] (φ : R →+* B)
    (a b : Over.mk (spMap φ ≫ 𝟙 (Sp R)) ⟶ X.A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T),
      χ e = 1 ↔ spMap χ ≫ a.left = spMap χ ≫ b.left := by
  obtain ⟨U, hU, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq ha hb
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_isIdempotentElem_range_spMap_subset (B := B)
    (U := (U : Set (Over.mk (spMap φ ≫ 𝟙 (Sp R))).left)) ⟨hU, U.isOpen⟩
  refine ⟨e, he, fun T _ χ => (H T χ).trans ?_⟩
  refine (HU (Over.mk (spMap χ ≫ spMap φ ≫ 𝟙 (Sp R))) (Over.homMk (spMap χ) rfl)).symm.trans ?_
  exact ⟨fun h => congrArg CommaMorphism.left h, fun h => Over.OverMorphism.ext h⟩

theorem ptEquiv {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩

end LevFlat

end GlobalTheory.RealMult

namespace GlobalTheory.RealMult.LevFlat

variable {R B R' Ω : Type} [CommRing R] [CommRing B] [CommRing R'] [CommRing Ω]

theorem spMap_eq₁ (φ : R →+* B) (lo : B →+* R') :
    spMap lo ≫ spMap φ ≫ 𝟙 (Sp R) = 𝟙 (Sp R') ≫ spMap (lo.comp φ) := by
  rw [spMap_comp, Category.comp_id, Category.id_comp]

theorem spMap_eq₂ (φ : R →+* B) (lo : B →+* R') (χ : R' →+* Ω) :
    spMap (χ.comp lo) ≫ spMap φ ≫ 𝟙 (Sp R) = spMap χ ≫ spMap (lo.comp φ) := by
  rw [spMap_comp, spMap_comp, Category.comp_id, Category.assoc]

theorem spMap_eq₃ {Y : Scheme.{0}} (lo : B →+* R') (χ : R' →+* Ω) (x : Sp B ⟶ Y) :
    spMap χ ≫ spMap lo ≫ x = spMap (χ.comp lo) ≫ x := by
  rw [spMap_comp, Category.assoc]

end GlobalTheory.RealMult.LevFlat

namespace GlobalTheory.RealMult

open LevFlat

theorem exists_faithfullyFlat_level_of (hT : TorsionFreeRankTwo) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N) := by
  intro F _ _ _ 𝔠 N hN1 R _ hN X
  classical
  obtain ⟨⟨hf1, hf2⟩, ht1, ht2⟩ := finEt X hN
  haveI := hf1
  haveI := hf2
  haveI := ht1
  haveI := ht2
  haveI : Finite (𝓞 F ⧸ Ideal.span {((N : ℕ) : 𝓞 F)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (by omega : N ≠ 0))
  obtain ⟨B, _, φ, w, hφ, hw, hU⟩ := GlobalTheory.TorsTuple.exists_tuple X.A N R (𝟙 (Sp R)) (Fin 2)
  have hρ := isAct_ptAct X (Over.mk (spMap φ ≫ 𝟙 (Sp R)))
  let J := {q : (𝓞 F ⧸ Ideal.span {((N : ℕ) : 𝓞 F)}) × (𝓞 F ⧸ Ideal.span {((N : ℕ) : 𝓞 F)}) // q ≠ 0}
  haveI : Fintype J := Fintype.ofFinite J
  let c : J → (Over.mk (spMap φ ≫ 𝟙 (Sp R)) ⟶ X.A) := fun q =>
    comb (ptAct X _) w (rep (𝓞 F) N q.1.1) (rep (𝓞 F) N q.1.2)
  have hc : ∀ q, c q ^ N = 1 := fun q => comb_pow hρ hw _ _
  choose f hf Hf using fun q : J => exists_idem X φ (c q) 1 (hc q) (one_pow N)
  let e : B := ∏ q, (1 - f q)

  have hne : ∀ (K : Type) [Field K] (χ : B →+* K), IsUnit (χ e) → ∀ q : J,
      ¬ spMap χ ≫ (c q).left = spMap χ ≫ (1 : Over.mk (spMap φ ≫ 𝟙 (Sp R)) ⟶ X.A).left := by
    intro K _ χ hu q hq
    have h1 : IsUnit (χ (1 - f q)) :=
      isUnit_of_dvd_unit (map_dvd χ (Finset.dvd_prod_of_mem (fun q => 1 - f q) (Finset.mem_univ q))) hu
    rw [map_sub, map_one, (Hf q K χ).2 hq, sub_self] at h1
    exact not_isUnit_zero h1
  have hunit : ∀ (K : Type) [Field K] (χ : B →+* K), (∀ q : J,
      ¬ spMap χ ≫ (c q).left = spMap χ ≫ (1 : Over.mk (spMap φ ≫ 𝟙 (Sp R)) ⟶ X.A).left) → IsUnit (χ e) := by
    intro K _ χ H
    rw [isUnit_iff_ne_zero, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun q _ => ?_
    rw [map_sub, map_one, sub_ne_zero]
    intro h
    exact H q ((Hf q K χ).1 h.symm)

  have hind : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R) (g : Over.mk s ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp R)))
      (χ : B →+* K), IsUnit (χ e) → g.left = spMap χ → ∀ q : J,
        comb (ptAct X (Over.mk s)) (fun i => g ≫ w i) (rep (𝓞 F) N q.1.1) (rep (𝓞 F) N q.1.2) ≠ 1 := by
    intro K _ s g χ hu hg q h1
    refine hne K χ hu q ?_
    have h2 : g ≫ c q = g ≫ 1 := by rw [MonObj.comp_one, comp_comb]; exact h1
    have h3 : g.left ≫ (c q).left = g.left ≫ (1 : Over.mk (spMap φ ≫ 𝟙 (Sp R)) ⟶ X.A).left :=
      congrArg CommaMorphism.left h2
    rw [hg] at h3
    exact h3
  let R' := Localization.Away e
  let lo : B →+* R' := algebraMap B R'
  have hlo : IsUnit (lo e) := IsLocalization.Away.algebraMap_isUnit e
  let σ : R →+* R' := lo.comp φ
  have hff : σ.FaithfullyFlat := by
    refine GlobalTheory.faithfullyFlat_points_baseChange_descent.1 _ _ _
      (GlobalTheory.faithfullyFlat_points_baseChange_descent.2.1 _ _ φ e hφ) fun K _ _ ψ => ?_
    have hK : (N : K) ≠ 0 := by simpa using (hN.map ψ).ne_zero
    obtain ⟨p, hp, hpinj, -⟩ := hT F 𝔠 (Sp R) X N K (spMap ψ ≫ 𝟙 (Sp R)) hK
    obtain ⟨χ, hχ, hu⟩ := hU K ψ p hp
    subst hχ
    let g : Over.mk (spMap (χ.comp φ) ≫ 𝟙 (Sp R)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp R)) :=
      Over.homMk (spMap χ) (by
        show spMap χ ≫ spMap φ ≫ 𝟙 (Sp R) = spMap (χ.comp φ) ≫ 𝟙 (Sp R)
        rw [spMap_comp, Category.assoc])
    have hgw : (fun i => g ≫ w i) = p := funext fun i => Over.OverMorphism.ext (hu i).symm
    have hχe : IsUnit (χ e) := by
      refine hunit K χ fun q hq => q.2 ?_
      have h1 : comb (ptAct X _) (fun i => g ≫ w i) (rep (𝓞 F) N q.1.1) (rep (𝓞 F) N q.1.2) = 1 := by
        rw [← comp_comb]
        have : g ≫ c q = g ≫ 1 := Over.OverMorphism.ext hq
        rw [this, MonObj.comp_one]
      rw [hgw] at h1
      obtain ⟨d1, d2⟩ := hpinj _ _ h1
      rw [← mk_eq_zero_iff, mk_rep] at d1 d2
      exact Prod.ext d1 d2
    refine ⟨IsLocalization.Away.lift e hχe, ?_⟩
    show (IsLocalization.Away.lift e hχe).comp ((algebraMap B (Localization.Away e)).comp φ) = χ.comp φ
    rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  obtain ⟨X', φ', hX'⟩ := Obj.exists_isPullBy X (spMap σ)
  refine ⟨R', inferInstance, σ, X', φ', hff, hX', ?_⟩
  have hEact : ∀ (Z : Over (Sp R')) (E : (Z ⟶ X'.A) ≃* (Over.mk (Z.hom ≫ spMap σ) ⟶ X.A)),
      (∀ x, (E x).left = x.left ≫ φ') → ∀ x a, E (x ≫ X'.rm.act a) = E x ≫ X.rm.act a := by
    intro Z E hE x a
    apply Over.OverMorphism.ext
    rw [hE, Over.comp_left, Over.comp_left, hE, Category.assoc, hX'.act a, Category.assoc]
  obtain ⟨E1, hE1⟩ := ptEquiv hX'.grp (𝟙_ (Over (Sp R')))
  let g0 : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap σ) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp R)) :=
    Over.homMk (spMap lo) (by
      exact spMap_eq₁ φ lo)
  let pt : Fin 2 → (𝟙_ (Over (Sp R')) ⟶ X'.A) := fun i => E1.symm (g0 ≫ w i)
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    show E1.symm (g0 ≫ w i) ^ N = 1
    rw [← map_pow, ← MonObj.comp_pow, hw, MonObj.comp_one, map_one]
  have hpt0 : ∀ i, (pt i).left ≫ φ' = spMap lo ≫ (w i).left := fun i => by
    rw [← hE1, MulEquiv.apply_symm_apply]
    rfl

  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp R'),
      ∃ E : (Over.mk t ⟶ X'.A) ≃* (Over.mk (t ≫ spMap σ) ⟶ X.A),
        (∀ x a, E (x ≫ X'.rm.act a) = E x ≫ X.rm.act a) ∧
        (∀ a b, comb (ptAct X _) (fun i => E (toUnit (Over.mk t) ≫ pt i)) a b = 1 →
          (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
        ∀ y, y ^ N = 1 → ∃ a b, y = comb (ptAct X _) (fun i => E (toUnit (Over.mk t) ≫ pt i)) a b := by
    intro Ω _ _ t
    obtain ⟨E, hE⟩ := ptEquiv hX'.grp (Over.mk t)
    obtain ⟨χ', rfl⟩ : ∃ χ' : R' →+* Ω, spMap χ' = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
    let gt : Over.mk (spMap χ' ≫ spMap σ) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp R)) :=
      Over.homMk (spMap (χ'.comp lo)) (by
        exact spMap_eq₂ φ lo χ')
    have hu : (fun i => E (toUnit (Over.mk (spMap χ')) ≫ pt i)) = fun i => gt ≫ w i := funext fun i => by
      apply Over.OverMorphism.ext
      rw [hE, Over.comp_left, Over.toUnit_left, Category.assoc, hpt0, Over.comp_left]
      exact spMap_eq₃ lo χ' (w i).left
    have hρ' := isAct_ptAct X (Over.mk (spMap χ' ≫ spMap σ))
    have huN : ∀ i, (fun i => E (toUnit (Over.mk (spMap χ')) ≫ pt i)) i ^ N = 1 := fun i => by
      show E (toUnit _ ≫ pt i) ^ N = 1
      rw [← map_pow, ← MonObj.comp_pow, hpt, MonObj.comp_one, map_one]
    have huinj : ∀ a b, comb (ptAct X _) (fun i => E (toUnit (Over.mk (spMap χ')) ≫ pt i)) a b = 1 →
        (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
      refine inj_of_ne hρ' huN fun q hq => ?_
      rw [hu]
      exact hind Ω _ gt (χ'.comp lo) (hlo.map χ') rfl ⟨q, hq⟩
    have hΩ : (N : Ω) ≠ 0 := by simpa using (hN.map (χ'.comp σ)).ne_zero
    obtain ⟨p, hp, hpinj, hpsurj⟩ := hT F 𝔠 (Sp R) X N Ω (spMap χ' ≫ spMap σ) hΩ
    exact ⟨E, hEact _ E hE, huinj, surj_of_basis hρ' huN hp huinj hpinj hpsurj⟩
  refine ⟨⟨pt, hpt, fun Ω _ _ t a b hab => ?_, fun Ω _ _ t y hy => ?_⟩⟩
  · obtain ⟨E, hEa, hinj, -⟩ := key Ω t
    refine hinj a b ?_
    have := congrArg E hab
    rw [map_mul, map_one, ← Category.assoc, ← Category.assoc, hEa, hEa] at this
    exact this
  · obtain ⟨E, hEa, -, hsurj⟩ := key Ω t
    obtain ⟨a, b, hab⟩ := hsurj (E y) (by rw [← map_pow, hy, map_one])
    refine ⟨a, b, E.injective ?_⟩
    rw [hab, map_mul, ← Category.assoc, ← Category.assoc, hEa, hEa]
    rfl

end GlobalTheory.RealMult
