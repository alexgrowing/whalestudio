import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

noncomputable section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinOf

lemma finOf_idem {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
  · right
    exact hu.mul_left_cancel (by rw [_root_.mul_one]; exact h.eq)
  · left
    exact hu.mul_left_cancel (by rw [mul_zero]; exact h.one_sub_mul_self)

lemma finOf_local_of_comp {O Q S : Type} [CommRing O] [CommRing Q] [CommRing S] [IsLocalRing O]
    [IsLocalRing Q] [IsLocalRing S] [Algebra O Q] [Algebra.IsIntegral O Q] (g : Q →+* S)
    (h : IsLocalHom (g.comp (algebraMap O Q))) : IsLocalHom g := by
  have h1 : (maximalIdeal S).comap (g.comp (algebraMap O Q)) = maximalIdeal O :=
    ((local_hom_TFAE (g.comp (algebraMap O Q))).out 0 4).1 h
  have h2 : (((maximalIdeal S).comap g).comap (algebraMap O Q)).IsMaximal := by
    rw [Ideal.comap_comap, h1]; infer_instance
  have h3 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h2
  exact ((local_hom_TFAE g).out 4 0).1 (eq_maximalIdeal h3)

lemma finOf_local_algebraMap {O Q : Type} [CommRing O] [CommRing Q] [IsLocalRing O]
    [IsLocalRing Q] [Algebra O Q] [Algebra.IsIntegral O Q] : IsLocalHom (algebraMap O Q) :=
  ((local_hom_TFAE (algebraMap O Q)).out 4 0).1
    (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal Q)))

variable {R₀ : Type} [CommRing R₀]

def finOf_fst (C : Type) [Field C] [Algebra R₀ C] :
    LHom (R₀ := R₀) ⟨DualNumber C⟩ ⟨C⟩ :=
  ⟨TrivSqZeroExt.fstHom R₀ C C, ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

lemma finOf_fst_sqZero (C : Type) [Field C] [Algebra R₀ C] : (finOf_fst (R₀ := R₀) C).SqZero := by
  refine ⟨fun c => ⟨TrivSqZeroExt.inl c, rfl⟩, ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : TrivSqZeroExt.fst (a : DualNumber C) = 0 := ha
  have hb' : TrivSqZeroExt.fst (b : DualNumber C) = 0 := hb
  change (a * b : DualNumber C) = 0
  ext
  · simp [ha']
  · simp [ha', hb']

lemma finOf_tangent (B : BX R₀) (p : ℕ) (hp : p ≠ 0) (C : Type) [Field C] [CharZero C]
    [Algebra R₀ C] (z z' : B.G ⟨DualNumber C⟩) (hz : p • z = 0) (hz' : p • z' = 0)
    (h : B.map (finOf_fst C) z = B.map (finOf_fst C) z') : z = z' := by
  obtain ⟨v, hv⟩ := (B.tg_ker (finOf_fst C) (finOf_fst_sqZero C) (z - z')).1
    (by rw [map_sub, h, sub_self])
  have h1 : p • v = 0 := B.tg_inj (finOf_fst C) (finOf_fst_sqZero C)
    (by rw [map_nsmul, hv, smul_sub, hz, hz', sub_self, map_zero])
  have hinj : Function.Injective
      (p • LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : p • (a.1 : DualNumber C) = 0 := congrArg Subtype.val ha
    apply Subtype.ext
    have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
    rw [← Nat.cast_smul_eq_nsmul C] at ha'
    exact (smul_eq_zero.1 ha').resolve_left hpC
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := B.gg) _ hinj
  have h3 : v = 0 := h2 (by
    rw [map_zero, ← h1]
    have := map_nsmul (LinearMap.lTensorHom (R := R₀) B.gg) p
      (LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker)
    simp only [LinearMap.coe_lTensorHom, LinearMap.lTensor_id] at this
    rw [this]; rfl)
  rw [h3, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

lemma finOf_free {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] {n : ℕ} (ε : Fin n → A)
    (hε : CompleteOrthogonalIdempotents ε) :
    (∀ i, Module.Free O (A ⧸ Ideal.span {1 - ε i})) ∧
      (∑ i, Module.finrank O (A ⧸ Ideal.span {1 - ε i})) = Module.finrank O A := by
  let Q : Fin n → Type := fun i => A ⧸ Ideal.span {1 - ε i}
  let E : A ≃ₗ[O] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (Ideal.Quotient.mkₐ O _).toLinearMap)
      hε.bijective_pi
  haveI hfree : ∀ i, Module.Free O (Q i) := fun i => by
    haveI : Module.Projective O (Q i) :=
      Module.Projective.of_split (M := A)
        (E.symm.toLinearMap ∘ₗ LinearMap.single O Q i) (LinearMap.proj i ∘ₗ E.toLinearMap)
        (LinearMap.ext fun x => by simp)
    exact Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype]

section Split

variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]

def finOf_sO [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    LHom O ⟨A ⧸ I⟩ :=
  ⟨IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ I), finOf_local_algebraMap (O := O) (Q := A ⧸ I)⟩

lemma finOf_algOf [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    algOf (finOf_sO O I) = (inferInstance : Algebra (O : Type) (A ⧸ I)) :=
  Algebra.algebra_ext _ _ fun _ => rfl

lemma finOf_lift [Module.Finite (O : Type) A] (ε : A) [IsLocalRing (A ⧸ Ideal.span {1 - ε})]
    (S : LAlg R₀) (s : LHom O S) (φ : A →ₐ[R₀] S)
    (hφ : φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s.1) (hε : φ ε = 1) :
    ∃ ψ : LHom ⟨A ⧸ Ideal.span {1 - ε}⟩ S, ψ.comp (finOf_sO O _) = s ∧
      ψ.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
  have hk : ∀ a ∈ Ideal.span {1 - ε}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, map_one, hε, sub_self, mul_zero]
  let ψ : (A ⧸ Ideal.span {1 - ε}) →ₐ[R₀] S := Ideal.Quotient.liftₐ _ φ hk
  have hψ : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ Ideal.span {1 - ε})) = s.1 := by
    rw [← hφ]; rfl
  refine ⟨⟨ψ, finOf_local_of_comp (O := O) (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S) ?_⟩,
    Subtype.ext hψ, by ext a; rfl⟩
  have : (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S).comp (algebraMap (O : Type) _) = (s.1 : O →+* S) := by
    rw [← hψ]; rfl
  rw [this]; exact s.2

lemma finOf_split (B : BX R₀) (p : ℕ) [Module.Free (O : Type) A] [Module.Finite (O : Type) A]
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (hsep : ∀ f : A, (∀ φ : A →ₐ[(O : Type)] O, φ f = 0) → f = 0)
    (hrank : Module.finrank (O : Type) A = Nat.card (A →ₐ[(O : Type)] O))
    {n : ℕ} (ε : Fin n → A) (hε : CompleteOrthogonalIdempotents ε)
    [hloc : ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})] : Nonempty (FIN B O p) := by
  obtain ⟨hfree, h1⟩ := finOf_free (O := O) ε hε
  have hone : ∀ (S : LAlg R₀) (φ : A →ₐ[R₀] S), ∃ i, φ (ε i) = 1 := by
    intro S φ
    by_contra hcon
    have h0 : ∀ i, φ (ε i) = 0 := fun i =>
      (finOf_idem ((hε.idem i).map φ)).resolve_right fun h => hcon ⟨i, h⟩
    have h1 := congrArg φ hε.complete
    rw [map_sum, map_one, Finset.sum_eq_zero fun i _ => h0 i] at h1
    exact zero_ne_one h1
  have hmk : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε i) = 1 := fun i => by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - ε i})), eq_comm, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _
  refine ⟨FIN.mk (Fin n) (fun i => ⟨A ⧸ Ideal.span {1 - ε i}⟩) (fun i => finOf_sO O _)
    (fun i => ?_) (fun i => pt _ (Ideal.Quotient.mkₐ R₀ _)) (fun i => pt_p _ _)
    (fun S s z hz => ?_) (fun i f hf => ?_) ?_⟩
  · rw [finOf_algOf]
    exact ⟨hfree i, inferInstance⟩
  · obtain ⟨φ, ⟨hφs, hφz⟩, huniq⟩ := pt_univ S s.1 z hz
    obtain ⟨i, hi⟩ := hone S φ
    obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) S s φ hφs hi
    refine ⟨i, ψ, hψs, by rw [pt_nat, hψφ, hφz], fun j φ' h1 h2 => ?_⟩
    have h3 : φ'.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
      refine huniq _ ⟨?_, ?_⟩
      · rw [← h1]; rfl
      · rw [← h2, pt_nat]
    have hj : φ (ε j) = 1 := by
      rw [← h3]
      change φ'.1 (Ideal.Quotient.mk _ (ε j)) = 1
      rw [hmk, map_one]
    have hji : j = i := by
      by_contra hne
      have h4 := congrArg φ (hε.ortho hne)
      rw [map_mul, hi, hj, map_zero, _root_.mul_one] at h4
      exact one_ne_zero h4
    subst hji
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    exact Ideal.Quotient.algHom_ext R₀ (h3.trans hψφ.symm)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
    have h0 : a * ε i = 0 := by
      refine hsep _ fun φ => ?_
      rw [map_mul]
      rcases finOf_idem ((hε.idem i).map φ) with h | h
      · rw [h, mul_zero]
      · obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) O (LHom.id O) (φ.restrictScalars R₀)
          (by ext r; exact φ.commutes r) h
        have h1 := hf ψ hψs
        have h2 : φ a = 0 := (AlgHom.congr_fun hψφ a).symm.trans h1
        rw [h2, zero_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    rw [mul_sub, h0, sub_zero, _root_.mul_one]
  · have h2 : Nat.card (A →ₐ[(O : Type)] O) = Nat.card {t : B.G O // p • t = 0} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun φ => ⟨pt O (φ.restrictScalars R₀), pt_p _ _⟩) ⟨fun φ φ' h => ?_, fun t => ?_⟩)
      · have h' : pt O (φ.restrictScalars R₀) = pt O (φ'.restrictScalars R₀) :=
          congrArg Subtype.val h
        have := (pt_univ O (AlgHom.id R₀ O) _ (pt_p O (φ'.restrictScalars R₀))).unique
          (y₁ := φ.restrictScalars R₀) (y₂ := φ'.restrictScalars R₀)
          ⟨by ext r; exact φ.commutes r, h'⟩ ⟨by ext r; exact φ'.commutes r, rfl⟩
        exact AlgHom.restrictScalars_injective R₀ this
      · obtain ⟨φ, ⟨h1, h2⟩, -⟩ := pt_univ O (AlgHom.id R₀ O) t.1 t.2
        exact ⟨⟨φ.toRingHom, fun r => AlgHom.congr_fun h1 r⟩, Subtype.ext h2⟩
    rw [← h2, ← hrank, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finOf_algOf]

lemma finOf_unram (B : BX R₀) (p : ℕ) (hp : p ≠ 0)
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (C : Type) [Field C] [CharZero C] [Algebra (O : Type) C] [Algebra R₀ C]
    [IsScalarTower R₀ (O : Type) C] (φ φ' : A →ₐ[(O : Type)] DualNumber C)
    (h : ∀ a, (φ a).fst = (φ' a).fst) : φ = φ' := by
  let ψ : A →ₐ[R₀] DualNumber C := φ.restrictScalars R₀
  let ψ' : A →ₐ[R₀] DualNumber C := φ'.restrictScalars R₀
  have h1 : pt ⟨DualNumber C⟩ ψ = pt ⟨DualNumber C⟩ ψ' := by
    refine finOf_tangent B p hp C _ _ (pt_p _ _) (pt_p _ _) ?_
    rw [pt_nat, pt_nat]
    congr 1
    ext a
    exact h a
  have h2 : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) =
      ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) :=
    AlgHom.ext fun r => (φ.commutes r).trans (φ'.commutes r).symm
  have h3 : ψ = ψ' := (pt_univ ⟨DualNumber C⟩ (ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A)) _
    (pt_p ⟨DualNumber C⟩ ψ')).unique ⟨h2, h1⟩ ⟨rfl, rfl⟩
  exact AlgHom.ext fun a => AlgHom.congr_fun h3 a

end Split

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) →
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) →
  (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
    (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
    Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧ Module.finrank O A = Nat.card (A →ₐ[O] O)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C], v.Integers (O : Type) → p ≠ 0 →
    Nonempty (FIN B O p)) := by
  intro REP SPLIT ETA R₀ _ G _ _ O p B e hbij hadd hnat hfin hflat hsm C _ _ _ v _ hv hp
  obtain ⟨A, _, _, _, _, hAfree, hAfin, y, hy, huniv⟩ := REP G O p hfin hflat hsm
  have he0 : ∀ R, e R 0 = 1 := fun R => by
    have h := hadd R 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hen : ∀ R (x : B.G R) (n : ℕ), e R (n • x) = e R x ^ n := fun R x n => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, he0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have htor : ∀ R (x : B.G R), p • x = 0 ↔ e R x ^ p = 1 := fun R x => by
    rw [← hen, ← he0 R, (hbij R).1.eq_iff]
  let pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).symm (spMap φ ≫ y)
  have hpt : ∀ S φ, e S (pt S φ) = spMap φ ≫ y := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).apply_symm_apply _
  have pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ) := fun {S S'} f φ => (hbij S').1 (by
    rw [hnat, hpt, hpt, ← Category.assoc, spMap_comp])
  have pt_p : ∀ S φ, p • pt S φ = 0 := fun S φ => by
    rw [htor, hpt, ← MonObj.comp_pow, hy, MonObj.comp_one]
  have pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z := by
    intro S s z hz
    letI : Algebra (O : Type) S := s.toRingHom.toAlgebra
    haveI : IsScalarTower R₀ (O : Type) S :=
      IsScalarTower.of_algebraMap_eq fun r => (s.commutes r).symm
    obtain ⟨φ, hφ, hu⟩ := huniv S (e S z) ((htor S z).1 hz)
    refine ⟨φ.restrictScalars R₀, ⟨by ext r; exact φ.commutes r, (hbij S).1 (by rw [hpt, hφ])⟩,
      fun φ' ⟨h1, h2⟩ => ?_⟩
    have h3 := hu ⟨φ'.toRingHom, fun r => AlgHom.congr_fun h1 r⟩ (by rw [← h2, hpt]; rfl)
    rw [← h3]; rfl
  letI : Algebra R₀ C := ((algebraMap (O : Type) C).comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfinite, hsep, hrank⟩ := ETA C O A v hv
    (finOf_unram O B p hp pt pt_nat pt_p pt_univ C)
  obtain ⟨n, ε, hε, hloc⟩ := SPLIT O A hsep
  exact finOf_split O B p pt pt_nat pt_p pt_univ hsep hrank ε hε

end GlobalTheory.FinOf
