import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.RedShDefs
import Development.AutomorphicArithmetic.CommutativeAlgebra.CochainPullbackBijectiveOfTermwiseBijectiveInjec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

section SlopeTestRemainingChoices
variable {R : Type} [CommRing R]

private theorem cpull_comp' {A B C : Cx R} (f : A ⟶ B) (g : B ⟶ C) (I : Cx R) (n : ℤ)
    (x : CohomologyClass C I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_id' {A : Cx R} (I : Cx R) (n : ℤ) (x : CohomologyClass A I n) :
    cpull (𝟙 A) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem cpull_homotopy {A B : Cx R} {f g : A ⟶ B} (h : Homotopy f g) (I : Cx R) (n : ℤ)
    (x : CohomologyClass B I n) : cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  rw [cpre_mk, cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 _ 0 (n + 1) n (by omega) (by omega) rfl]
  simp [zcomp, smul_smul, hz, Cochain.add_comp]

private theorem cpull_bij {A B : Cx R} (e : HomotopyEquiv A B) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp', cpull_homotopy e.homotopyInvHomId, cpull_id']
  · rw [← cpull_comp', cpull_homotopy e.homotopyHomInvId, cpull_id']

private theorem transfer {A B A' B' : Cx R} (g : A ⟶ B) (g' : A' ⟶ B') (a : HomotopyEquiv A A')
    (b : HomotopyEquiv B B') (w : g ≫ b.hom = a.hom ≫ g') (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull g' I n) → Function.Bijective (cpull g I n)) ∧
      (Function.Injective (cpull g' I n) → Function.Injective (cpull g I n)) := by
  have ha := cpull_bij a I n
  have hb := cpull_bij b I n
  have key : ⇑(cpull g I n) = cpull a.hom I n ∘ cpull g' I n ∘ (Equiv.ofBijective _ hb).symm := by
    funext x
    obtain ⟨y, rfl⟩ := hb.2 x
    have : (Equiv.ofBijective _ hb).symm (cpull b.hom I n y) = y :=
      (Equiv.ofBijective _ hb).symm_apply_apply y
    simp only [Function.comp_apply, this]
    rw [← cpull_comp', ← cpull_comp', w]
  rw [key]
  exact ⟨fun h => ha.comp (h.comp (Equiv.bijective _)),
    fun h => ha.1.comp (h.comp (Equiv.injective _))⟩

private theorem subsingleton_of_isZero {A : Cx R} (h : IsZero A) (I : Cx R) (n : ℤ) :
    Subsingleton (CohomologyClass A I n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_))
  exact ((HomologicalComplex.eval _ _ p).map_isZero h).eq_of_src _ _

private theorem bij_of_isZero {A B : Cx R} (hA : IsZero A) (hB : IsZero B) (g : A ⟶ B) (I : Cx R)
    (n : ℤ) : Function.Bijective (cpull g I n) := by
  have := subsingleton_of_isZero hA I n
  have := subsingleton_of_isZero hB I n
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem core (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ)
    (e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)))
    (he : ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
      (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom)
    (h : ∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) :
    UpperTheory.RedSh.Conn p F m := by
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  have := hle E
  have := hle E'
  refine UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective R (res R F) hinj ((chains R).map p) m fun q => ?_
  rcases lt_or_ge 0 q with hq | hq
  · have hz : ∀ K : Cx R, K.IsStrictlyLE 0 →
        IsZero ((CochainComplex.singleFunctor (Shv R) 0).obj (K.X q)) := fun K _ =>
      (CochainComplex.singleFunctor (Shv R) 0).map_isZero (K.isZero_of_isStrictlyLE 0 q hq)
    exact ⟨fun n _ => bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _,
      (bij_of_isZero (hz _ (hle E')) (hz _ (hle E)) _ _ _).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
    let S := CochainComplex.singleFunctor (Shv R) 0
    let φ := p.app (op (SimplexCategory.mk k))
    let a : HomotopyEquiv (S.obj (((chains R).obj E').X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E' k))).trans (e _)
    let b : HomotopyEquiv (S.obj (((chains R).obj E).X (-(k : ℤ)))) _ :=
      (HomotopyEquiv.ofIso (S.mapIso (chainsXIso R E k))).trans (e _)
    have w : S.map (((chains R).map p).f (-(k : ℤ))) ≫ b.hom =
        a.hom ≫ (chains R).map (disc.map φ) := by
      change S.map _ ≫ S.map (chainsXIso R E k).hom ≫ (e _).hom =
        (S.map (chainsXIso R E' k).hom ≫ (e _).hom) ≫ _
      rw [Category.assoc, he, ← Category.assoc, ← S.map_comp, hnat, S.map_comp, Category.assoc]
    have hm : m + -(k : ℤ) = m - k := by ring
    rw [hm]
    refine ⟨fun n hn => (transfer _ _ a b w _ n).1 ((h k).1 n hn),
      (transfer _ _ a b w _ _).2 (h k).2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.sheafConnected_of_levelwise_connected :
    ∀ (R : Type) [CommRing R] (F : Shv R) {E' E : Spc} (p : E' ⟶ E) (m : ℤ), (∀ k : ℕ, UpperTheory.RedSh.Conn (disc.map (p.app (op (SimplexCategory.mk k)))) F (m - k)) → UpperTheory.RedSh.Conn p F m := by
  intro R _ F E' E p m h
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact core R F p m e he h
