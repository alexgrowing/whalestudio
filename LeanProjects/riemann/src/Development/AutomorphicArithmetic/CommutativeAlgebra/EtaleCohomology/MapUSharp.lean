import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackDecomposition
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsSubordinateOfEtaleSec
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsLiftThroughSharp
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsFiniteSectionsDeterminingRingHomOfSmooth
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsMatchingOfSameNorm
import Development.AutomorphicArithmetic.EtaleIdempotents.CorrespondenceNormBoundOfAffineOpens
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSameNormRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PInjSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PRankDeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsEquiv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCoeffInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLiftP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtsProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCongrRad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseSmooth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSmoothClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSmoothRed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem normOfPt' : NormOfPt :=
  normPt_of (sameNormRing_of (normRead_of (normInt_of (normEx_of matRep_of detSplit_of) splitsBC_of
    (injSplit_of (rankDeg_of splitsField_of) splitsEquiv_of) coeffInt_of liftingProperty) etUnit_of splitsField_of valPts_of)
    valLift_of ptsProd_of congrRad_of) (baseChart_of (baseSmooth_of smoothClosed_of smoothRed_of)) secChart_of
    (etAway_of secChart_of etChart_of) genChart_of ptChart_of

private theorem wzSum {P : Type} (q n : ℕ) {I : Fin (n + 1) → Type} [∀ j, Fintype (I j)] (v : ∀ j, I j → P)
    (h : pts (wEv q) v = pts (wOd q) v) :
    ∑ x : (Σ j, I j), Finsupp.single (v x.1 x.2) ((-1 : ℤ) ^ (x.1 : ℕ) * ((q ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = 0 := by
  classical
  let Φ : Multiset P →+ (P →₀ ℤ) := (Multiset.sumAddMonoidHom).comp (Multiset.mapAddMonoidHom fun p => Finsupp.single p (1 : ℤ))
  let G : Fin (n + 1) → (P →₀ ℤ) := fun j => ∑ i, Finsupp.single (v j i) (1 : ℤ)
  have hG : ∀ j, Φ (Finset.univ.val.map (v j)) = G j := fun j => by
    change ((Finset.univ.val.map (v j)).map fun p => Finsupp.single p (1 : ℤ)).sum = _
    rw [Multiset.map_map]
    rfl
  have key : ∀ a : Fin (n + 1) → ℕ, Φ (pts a v) = ∑ j, a j • G j := fun a => by
    simp only [pts, map_sum, map_nsmul, hG]
  have h0 : ∑ j, wEv q j • G j = ∑ j, wOd q j • G j := by rw [← key, ← key, h]
  rw [Fintype.sum_sigma]
  have e : ∀ j : Fin (n + 1), ∑ i, Finsupp.single (v j i) ((-1 : ℤ) ^ (j : ℕ) * ((q ^ ((j : ℕ).choose 2) : ℕ) : ℤ)) =
      ((wEv q j : ℤ) - (wOd q j : ℤ)) • G j := fun j => by
    have : (-1 : ℤ) ^ (j : ℕ) * ((q ^ ((j : ℕ).choose 2) : ℕ) : ℤ) = (wEv q j : ℤ) - (wOd q j : ℤ) := by
      by_cases hj : Even (j : ℕ)
      · simp [wEv, wOd, hj, hj.neg_one_pow]
      · simp [wEv, wOd, hj, (Nat.not_even_iff_odd.1 hj).neg_one_pow]
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finsupp.smul_single]
  simp only [e, sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
  rw [h0, sub_self]

private theorem wzPts {J P : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ) (v : ∀ j, I j → P) :
    pts a v = Finset.univ.val.map (fun x : (Σ j, Fin (a j) × I j) => v x.1 x.2.2) := by
  have hm : ∀ {K : Type} [Fintype K] (g : K → P), Finset.univ.val.map g = ∑ x, ({g x} : Multiset P) := fun {K} _ g => by
    have := Multiset.sum_map_singleton (Finset.univ.val.map g)
    rw [Multiset.map_map] at this
    exact this.symm
  simp only [pts, hm]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  simp

private theorem frob_pow' (A : PAlg l) (k : ℕ) (a : A.A) : (A.frob ^ k) a = a ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih]
    change (a ^ l ^ k) ^ l = _
    rw [← pow_mul, pow_succ]

private theorem wzPhi (A : PAlg l) (m : ℕ) : ∃ φ : Qb A →+* Qb A, ∀ x, φ x = x ^ l ^ m := by
  refine ⟨Ideal.quotientMap _ (A.frob ^ m) ?_, fun x => ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, frob_pow']
    exact Ideal.mem_span_singleton.2 (dvd_pow_self _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, frob_pow', map_pow]

private theorem wzPsi (A : PAlg l) (m : ℕ) : ∃ ψ : A.U →+* Qb A, ∀ x : A.W,
    ψ (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m := by
  obtain ⟨φ, hφ⟩ := wzPhi A m
  have hxi : (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})).comp WittVector.constantCoeff A.xi = 0 := by
    have e : WittVector.constantCoeff A.xi = - A.s (pFlat l) := by
      rw [PAlg.xi, PAlg.sW, xi0, map_sub, map_sub, map_natCast, map_natCast, PAlg.natCast_l, WittVector.map_teichmuller]
      simp [WittVector.constantCoeff_apply]
    rw [RingHom.comp_apply, e, map_neg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), neg_zero]
  let ψ₀ : A.U →+* Qb A := Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hxi, mul_zero])
  refine ⟨φ.comp ψ₀, fun x => ?_⟩
  rw [RingHom.comp_apply, hφ]
  rfl

private theorem ptOf_pre {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {B C : Type} [CommRing B] [CommRing C]
    (ρ : B →+* C) (f : Γ(Y, V) →+* B) :
    Spec.map (CommRingCat.ofHom ρ) ≫ ptOf hV B f = ptOf hV C (ρ.comp f) := by
  simp only [ptOf, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem wzFr {O : Type} [CommRing O] {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {g : O →+* Qo l}
    {f : ℕ} {F : PQ q g ⟶ PQ q g} (hF : IsFr f F) (A : PAlg l) (φ : Qb A →+* Qb A) (hφ : ∀ x, φ x = x ^ l ^ f)
    {V : Y.Opens} (hV : IsAffineOpen V) (β : Γ(Y, V) →+* Qb A) (P : (PQ q g).obj A) (hP : P.1 = ptOf hV _ β) (k : ℕ) :
    ((itE F k).app A P).1 = ptOf hV _ ((φ ^ k).comp β) := by
  induction k with
  | zero =>
    simpa [itE, RingHom.one_def] using hP
  | succ k ih =>
    have e : itE F (k + 1) = itE F k ≫ F := by
      simp only [itE, pow_succ']
      rfl
    rw [e]
    change (F.app A ((itE F k).app A P)).1 = _
    rw [hF A φ hφ, ih, ptOf_pre, pow_succ', RingHom.mul_def, RingHom.comp_assoc]

private theorem wzPhiPow {B : Type} [CommRing B] (φ : B →+* B) (Q : ℕ) (hφ : ∀ x, φ x = x ^ Q) (k : ℕ) (x : B) :
    (φ ^ k) x = x ^ Q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ]

private theorem wzNontriv (A : PAlg l) (h : ¬ Subsingleton A.A) : Nontrivial (Qb A) := by
  refine Ideal.Quotient.nontrivial_iff.2 fun ht => h ⟨fun a b => ?_⟩
  have hz : ∀ x : A.A, x = 0 := fun x => by
    have := A.compl.toIsHausdorff
    refine this.haus' x fun n => ?_
    rw [ht]
    simp [SModEq.zero, Ideal.top_pow]
  rw [hz a, hz b]

private theorem wzCore (f n : ℕ) {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (g : O →+* Qo l)
    {V : Y.Opens} (hV : IsAffineOpen V) (d : Fin (n + 1) → ℕ) (N : ℕ)
    (hN : ((∑ j, wEv (l ^ f) j * d j) + 1) ^ (∑ j, wEv (l ^ f) j * d j) ≤ (l ^ f) ^ N)
    (A : Test l) (β : ∀ j, Fin (d j) → (Γ(Y, V) →+* Qb A.obj)) (φ : Qb A.obj →+* Qb A.obj)
    (hφ : ∀ x, φ x = x ^ l ^ f) (v : ∀ j, Fin (d j) → (PQ q g).obj A.obj)
    (hv : ∀ j i, (v j i).1 = ptOf hV _ ((φ ^ (n - j + N)).comp (β j i)))
    {ι : Type} [Fintype ι] (x : ι → Γ(Y, V))
    (hx : ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
      ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂)
    (hS : SameNorm (pts (wEv (l ^ f)) fun j i k => β j i (x k) ^ (l ^ f) ^ (n - j))
      (pts (wOd (l ^ f)) fun j i k => β j i (x k) ^ (l ^ f) ^ (n - j))) :
    ∃ S : Fam A, IsDec S ∧ ∀ s,
      pts (wEv (l ^ f)) (fun j i => (PQ q g).map (S.f s).hom (v j i)) =
        pts (wOd (l ^ f)) (fun j i => (PQ q g).map (S.f s).hom (v j i)) ∨ Subsingleton (S.B s).obj.A := by
  classical
  by_cases hsub : Subsingleton A.obj.A
  · refine ⟨⟨Unit, fun _ => A, fun _ => 𝟙 A⟩, ⟨fun a b hab => congrFun hab (), fun b => ⟨b (), funext fun _ => rfl⟩⟩,
      fun _ => Or.inr hsub⟩
  have hnt := wzNontriv A.obj hsub
  let c : (Σ j, Fin (wEv (l ^ f) j) × Fin (d j)) → ι → Qb A.obj := fun e k => β e.1 e.2.2 (x k) ^ (l ^ f) ^ (n - e.1)
  let c' : (Σ j, Fin (wOd (l ^ f) j) × Fin (d j)) → ι → Qb A.obj := fun e k => β e.1 e.2.2 (x k) ^ (l ^ f) ^ (n - e.1)
  have hS' : SameNorm (Finset.univ.val.map c) (Finset.univ.val.map c') := by
    rw [wzPts, wzPts] at hS
    exact hS
  have hcI : Fintype.card (Σ j, Fin (wEv (l ^ f) j) × Fin (d j)) = ∑ j, wEv (l ^ f) j * d j := by
    simp [Fintype.card_sigma]
  have hcI' : Fintype.card (Σ j, Fin (wOd (l ^ f) j) × Fin (d j)) = ∑ j, wEv (l ^ f) j * d j := by
    have := (snBasic_of (Qb A.obj) ι).2.2.1 hnt _ _ hS'
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ] at this
    rw [← this, hcI]
  have hL : (l ^ f) ^ N = l ^ (f * N) := by rw [pow_mul]
  obtain ⟨e, he, hm⟩ := UpperTheory.exists_orthogonalIdempotents_matching_of_sameNorm l A.obj A.property (f * N) _ hcI hcI' (by rw [← hL]; exact hN) c c' hS'
  obtain ⟨B, fσ, hd, h1⟩ := decEx l A _ e he
  refine ⟨⟨_, B, fσ⟩, hd, fun σ => Or.inl ?_⟩
  rw [wzPts, wzPts]
  rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  have hi := hm σ i
  let f₀ := (fσ σ).hom
  change (PQ q g).map f₀ (v i.1 i.2.2) = (PQ q g).map f₀ (v (σ i).1 (σ i).2.2)
  apply Subtype.ext
  have hpt : ∀ (j) (t), ((PQ q g).map f₀ (v j t)).1 =
      ptOf hV _ ((PAlg.mapQ f₀ (pFlat l)).comp ((φ ^ (n - j + N)).comp (β j t))) := fun j t => by
    change Spec.map (CommRingCat.ofHom (PAlg.mapQ f₀ (pFlat l))) ≫ (v j t).1 = _
    rw [hv, ptOf_pre]
  rw [hpt, hpt]
  refine congrArg _ (hx _ _ _ ?_ fun k => ?_)
  · rw [← hpt, ← hpt, ((PQ q g).map f₀ (v i.1 i.2.2)).2, ((PQ q g).map f₀ (v (σ i).1 (σ i).2.2)).2]
  · have a : ∀ (j : Fin (n + 1)) t, (φ ^ (n - j + N)) (β j t (x k)) = (β j t (x k) ^ (l ^ f) ^ (n - j)) ^ l ^ (f * N) := fun j t => by
      rw [wzPhiPow φ (l ^ f) hφ, pow_add, pow_mul, ← hL]
    have h1' : PAlg.mapQ f₀ (pFlat l) (Ideal.Quotient.mk _ (e σ)) = 1 := by
      rw [PAlg.mapQ, Ideal.quotientMap_mk]
      change Ideal.Quotient.mk _ (PAlg.Hom.f (fσ σ).hom (e σ)) = 1
      rw [h1 σ, map_one]
    have := congrArg (PAlg.mapQ f₀ (pFlat l)) (hi k)
    rw [map_mul, map_mul, h1', one_mul, one_mul] at this
    simp only [RingHom.comp_apply]
    rw [a, a]
    exact this

private theorem mapU_sharp' {A B : PAlg l} (f : A ⟶ B) (a : A.A) : PAlg.mapU f (A.sharp a) = B.sharp (PAlg.Hom.f f a) := by
  change B.th (PAlg.mapW f (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (PAlg.Hom.f f a))
  rw [PAlg.mapW, WittVector.map_teichmuller]

private theorem wzChart {Y : Scheme.{0}} (hY : AffFin Y) {J : Type} [Finite J] (T : J → Corr l Y) (A : Test l)
    (y : Spec (CommRingCat.of A.obj.U) ⟶ Y) :
    ∃ S : Fam A, IsDec S ∧ ∀ s, ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧
      (∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) ∧
      ⊤ ≤ (Spec.map (CommRingCat.ofHom (PAlg.mapU (S.f s).hom)) ≫ y) ⁻¹ᵁ U := by
  classical
  have hT := testFacts l A.obj A.property
  choose U V hU hV hx hUV using charts_of l Y hY J T
  obtain ⟨I, _, e, a, he, hea⟩ := UpperTheory.exists_orthogonalIdempotents_subordinate_of_etale_sections A.obj.U hT.2.2.2.1 Y (fun x => y ⁻¹' (U x : Set Y))
    (fun x => (U x).isOpen.preimage y.continuous) (fun p => ⟨y p, hx _⟩)
  obtain ⟨e₀, he₀, hs⟩ := UpperTheory.exists_orthogonalIdempotents_lift_through_sharp l A I e he
  obtain ⟨B, f, hd, h1⟩ := decEx l A I e₀ he₀
  refine ⟨⟨I, B, f⟩, hd, fun s => ⟨U (a s), V (a s), hU _, hV _, hUV _, fun p _ => ?_⟩⟩
  have h2 : PAlg.mapU (f s).hom (e s) = 1 := by
    rw [← hs, mapU_sharp']
    change (B s).obj.sharp (PAlg.Hom.f (f s).hom (e₀ s)) = 1
    rw [h1 s]
    simp [PAlg.sharp]
  have := hea s (PrimeSpectrum.comap (PAlg.mapU (f s).hom) p) (fun hmem => by
    have h3 : PAlg.mapU (f s).hom (e s) ∈ p.asIdeal := hmem
    rw [h2] at h3
    exact p.2.ne_top ((Ideal.eq_top_iff_one _).2 h3))
  exact this

private theorem wzNat {C : Type 1} [Category.{0} C] {F G : C ⥤ Type} (u : F ⟶ G) {A B : C} (f : A ⟶ B) (y : F.obj A) :
    u.app B (F.map f y) = G.map f (u.app A y) := FunctorToTypes.naturality u f y

private theorem wzLocal {O : Type} [CommRing O] (f n : ℕ) {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (hq : Smooth q)
    (ϖ : O) (T : Fin (n + 1) → Corr l Y) (hr : ∀ j, (T j).r ≫ q = (T j).p ≫ q) (κ : O →+* OC l) (g : O →+* Qo l)
    (hg : g ϖ = 0) (m : ℕ) (F : PQ q g ⟶ PQ q g) (ρ : PX q κ ⟶ PQ q g) (hF : IsFr f F) (hρ : IsRd m ρ) (D : WDat l T)
    (N : ℕ) (hN : ((∑ j, wEv (l ^ f) j * (T j).d) + 1) ^ (∑ j, wEv (l ^ f) j * (T j).d) ≤ (l ^ f) ^ N)
    (A : Test l) (y : (PX (D.π ≫ q) κ).obj A.obj) {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) (hy : ⊤ ≤ (y.1 ≫ D.π) ⁻¹ᵁ U)
    (hn : NormOn l (l ^ f) n (fn q ϖ) T U V h) :
    ∃ S : Fam A, IsDec S ∧ ∀ s,
      ∑ x : (Σ j : Fin (n + 1), Fin (T j).d), Finsupp.single
        ((pxMap (p := D.π ≫ q) κ (D.s x.1 x.2 ≫ (T x.1).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]) ≫
          ρ ≫ itE F (n - x.1 + N)).app _ ((PX (D.π ≫ q) κ).map (S.f s).hom y))
        ((-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = 0 ∨ Subsingleton (S.B s).obj.A := by
  obtain ⟨φ, hφ⟩ := wzPhi A.obj f
  obtain ⟨ψ, hψ⟩ := wzPsi A.obj m
  let y' : (PX q κ).obj A.obj := ⟨y.1 ≫ D.π, by rw [Category.assoc]; exact y.2⟩
  have hc : ∀ x : O, ψ (A.obj.oC (κ x)) = qs A.obj (g x) := by
    have h1 := (ρ.app A.obj y').2
    rw [hρ A.obj ψ hψ y', Category.assoc, y'.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := Spec.map_injective h1
    intro x
    exact RingHom.congr_fun (CommRingCat.hom_ext_iff.1 h2) x
  obtain ⟨α, hα, hnorm⟩ := UpperTheory.correspondence_norm_bound_of_affine_opens l q ϖ (l ^ f) n T κ D A y hU hV h hy hn ψ (by rw [hc, hg, map_zero])
  obtain ⟨k, x, hx⟩ := UpperTheory.exists_finite_sections_determining_ringHom_of_smooth q hq hV
  let u : ∀ j, Fin (T j).d → (PX (D.π ≫ q) κ ⟶ PQ q g) := fun j i =>
    pxMap (p := D.π ≫ q) κ (D.s j i ≫ (T j).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]) ≫
          ρ ≫ itE F (n - j + N)
  have hv : ∀ j i, ((u j i).app A.obj y).1 = ptOf hV _ ((φ ^ (n - j + N)).comp (ψ.comp (α j i))) := fun j i => by
    let yy : (PX q κ).obj A.obj := (pxMap (p := D.π ≫ q) κ (D.s j i ≫ (T j).r)
      (by rw [Category.assoc, hr, ← Category.assoc, D.hs])).app A.obj y
    have e1 : (ρ.app A.obj yy).1 = ptOf hV _ (ψ.comp (α j i)) := by
      rw [hρ A.obj ψ hψ yy, ← ptOf_pre, ← hα]
      rfl
    exact wzFr hF A.obj φ hφ hV (ψ.comp (α j i)) (ρ.app A.obj yy) e1 _
  obtain ⟨S, hS, hs⟩ := wzCore f n q g hV (fun j => (T j).d) N hN A (fun j i => ψ.comp (α j i)) φ hφ
    (fun j i => (u j i).app A.obj y) hv x hx (hnorm _ x)
  refine ⟨S, hS, fun s => (hs s).imp (fun e => ?_) id⟩
  have nat : ∀ j i, (u j i).app (S.B s).obj ((PX (D.π ≫ q) κ).map (S.f s).hom y) =
      (PQ q g).map (S.f s).hom ((u j i).app A.obj y) :=
    fun j i => wzNat (u j i) (S.f s).hom y
  have e3 := wzSum (l ^ f) n (I := fun j => Fin (T j).d)
    (fun j i => (PQ q g).map (S.f s).hom ((u j i).app A.obj y)) e
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) e3
  exact congrArg (fun w => Finsupp.single w ((-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ))) (nat x.1 x.2)

theorem wZero : UpperTheory.Ru.crystallineComparison.WZero := by
  intro l _ f n O _ _ _ ϖ hϖ hl0 hlu Y q hq hqc hY hf T hr hpt κ g hg m F ρ hF hρ _ D
  have hl2 : 2 ≤ l ^ f := by
    have h2 := (Fact.out : l.Prime).two_le
    exact h2.trans (Nat.le_self_pow hf.ne' l)
  refine ⟨((∑ j, wEv (l ^ f) j * (T j).d) + 1) ^ (∑ j, wEv (l ^ f) j * (T j).d), ?_⟩
  intro A y
  obtain ⟨S, hS, hch⟩ := wzChart hY T A (y.1 ≫ D.π)
  choose U V hU hV h hy using hch
  have hpar := fun s => wzLocal f n q hq ϖ T hr κ g hg m F ρ hF hρ D _ (Nat.lt_pow_self (by omega)).le (S.B s)
    ((PX (D.π ≫ q) κ).map (S.f s).hom y) (hU s) (hV s) (h s)
    (by
      have e : ((PX (D.π ≫ q) κ).map (S.f s).hom y).1 ≫ D.π =
          Spec.map (CommRingCat.ofHom (PAlg.mapU (S.f s).hom)) ≫ y.1 ≫ D.π := Category.assoc _ _ _
      rw [e]; exact hy s) (normOfPt' l f n (Fact.out) O ϖ hϖ hl0 hlu Y q hq T hpt _ _ (hU s) (hV s) (h s))
  choose R hR hz using hpar
  obtain ⟨Pa, hPa⟩ := partsEx l
  have hd := (hPa A _).1 (Pa.trans S R ((hPa A S).2 hS) fun s => (hPa _ _).2 (hR s))
  refine ⟨_, hd, ?_⟩
  rintro ⟨s, t⟩
  have e := hz s t
  have e2 : (PX (D.π ≫ q) κ).map (S.f s ≫ (R s).f t).hom y =
      (PX (D.π ≫ q) κ).map ((R s).f t).hom ((PX (D.π ≫ q) κ).map (S.f s).hom y) :=
    FunctorToTypes.map_comp_apply _ _ _ _
  change (∑ i, _) = 0 ∨ _
  simp only [e2]
  exact e

end UpperTheory.Ru.crystallineComparison
