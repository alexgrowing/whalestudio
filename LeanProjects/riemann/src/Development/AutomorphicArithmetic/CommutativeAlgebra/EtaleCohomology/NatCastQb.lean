import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open PAlg

variable {l : ℕ} [Fact l.Prime]

private theorem natCast_qb (A : PAlg l) : (l : Qb A) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})), A.natCast_l, map_zero]

private def frQ (A : PAlg l) : Qb A →+* Qb A where
  toFun x := x ^ l
  map_one' := one_pow _
  map_mul' x y := mul_pow x y l
  map_zero' := zero_pow (Fact.out : l.Prime).ne_zero
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) x y
    rw [hr, natCast_qb A]; simp

private def pw (A : PAlg l) : ℕ → (Qb A →+* Qb A)
  | 0 => RingHom.id _
  | m + 1 => (frQ A).comp (pw A m)

private theorem pw_apply (A : PAlg l) (m : ℕ) (x : Qb A) : pw A m x = x ^ l ^ m := by
  induction m with
  | zero => simp [pw]
  | succ m ih =>
    change (pw A m x) ^ l = _
    rw [ih, ← pow_mul, pow_succ]

private theorem mapQ_pw {A B : PAlg l} (f : A ⟶ B) (m : ℕ) (x : Qb A) :
    PAlg.mapQ f (pFlat l) (pw A m x) = pw B m (PAlg.mapQ f (pFlat l) x) := by
  rw [pw_apply, pw_apply, map_pow]

private theorem coeff_xi (A : PAlg l) : A.xi.coeff 0 = - A.s (pFlat l) := by
  have h : (xi0 l).coeff 0 = - pFlat l := by
    change WittVector.constantCoeff (xi0 l) = _
    rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    congr 1
  change (WittVector.map A.s (xi0 l)).coeff 0 = _
  rw [WittVector.map_coeff, h, map_neg]

private def rd (A : PAlg l) (m : ℕ) : A.U →+* Qb A :=
  Ideal.Quotient.lift _ ((pw A m).comp ((Ideal.Quotient.mk _).comp WittVector.constantCoeff)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have h0 : (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})) (WittVector.constantCoeff A.xi) = 0 := by
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      change A.xi.coeff 0 ∈ _
      rw [coeff_xi]
      exact neg_mem (Ideal.mem_span_singleton_self _)
    simp only [RingHom.comp_apply, map_mul, h0, mul_zero, map_zero]

private theorem rd_th (A : PAlg l) (m : ℕ) (x : A.W) :
    rd A m (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m :=
  pw_apply A m _

private theorem rd_ext (A : PAlg l) (m : ℕ) (ψ : A.U →+* Qb A)
    (h : ∀ x : A.W, ψ (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m) : ψ = rd A m :=
  RingHom.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (h y).trans (rd_th A m y).symm

private theorem rd_mapU {A B : PAlg l} (f : A ⟶ B) (m : ℕ) (x : A.U) :
    rd B m (mapU f x) = PAlg.mapQ f (pFlat l) (rd A m x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change rd B m (B.th (mapW f y)) = PAlg.mapQ f (pFlat l) (rd A m (A.th y))
  rw [rd_th, rd_th, map_pow]
  congr 1

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

private def frT (f : ℕ) {g : O →+* Qo l} (hg : ∀ x, g x ^ l ^ f = g x) : PQ q g ⟶ PQ q g where
  app A := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (pw A f)) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [pw_apply, ← map_pow, hg]⟩
  naturality A B φ := by
    ext y
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (pw B f)) ≫ Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ Spec.map (CommRingCat.ofHom (pw A f)) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => (mapQ_pw φ f x).symm

private def rdT (m : ℕ) {κ : O →+* OC l} {g : O →+* Qo l}
    (hg : ∀ (x : O) (w : Ainf l), theta0 l w = κ x → g x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ m) :
    PX q κ ⟶ PQ q g where
  app A := TypeCat.ofHom fun y => ⟨Spec.map (CommRingCat.ofHom (rd A m)) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (κ x)
    simp only [RingHom.comp_apply]
    rw [← hw, oC_theta0, rd_th, hg x w hw, map_pow]
    congr 1⟩
  naturality A B φ := by
    ext y
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom (rd B m)) ≫ Spec.map (CommRingCat.ofHom (mapU φ)) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (PAlg.mapQ φ (pFlat l))) ≫ Spec.map (CommRingCat.ofHom (rd A m)) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => (rd_mapU φ m x)

private theorem pull_sq {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {σ : R →+* R} (a : CH.Mor F F σ) (a' : CH.Mor F' F' σ)
    (b : CH.Mor F F' (RingHom.id R)) (j : ℕ)
    (h : ∀ c : CH.Cn F j, a'.pullC j (b.pullC j c) = b.pullC j (a.pullC j c)) (x : CH.H F j) :
    a'.pull j (b.pull j x) = b.pull j (a.pull j x) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F').B j).submoduleOf ((CH.cx F').Z j))) (Subtype.ext (h c.1))

private theorem phi_pull {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j : ℕ) (x : MH P' n j) :
    phiH P n j (pullH u n j x) = pullH u n j (phiH P' n j x) :=
  pull_sq (phiMor P' n) (phiMor P n) (pullMor u n) j (fun c => funext fun s => rfl) x

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.frEx :
    UpperTheory.Ru.crystallineComparison.FrEx := by
  intro l _ O _ X q κ g m f hg
  refine ⟨⟨frT f hg, fun A φ hφ y => ?_⟩, fun h => ⟨rdT m h, fun A ψ hψ y => ?_⟩, fun P P' u n j x => phi_pull u n j x⟩
  · have e : φ = pw A f := RingHom.ext fun x => (hφ x).trans (pw_apply A f x).symm
    rw [e]; rfl
  · rw [rd_ext A m ψ hψ]; rfl
