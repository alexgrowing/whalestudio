import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem reduced_of_finite_etale {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Sp K) [IsFinite f] [Etale f] : IsReduced X := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  have hE : (Scheme.Hom.appTop f).hom.Etale := HasRingHomProperty.appTop @Etale f inferInstance
  have hF : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  letI : Field Γ(Sp K, ⊤) := hF.toField
  letI := (Scheme.Hom.appTop f).hom.toAlgebra
  haveI : Algebra.Etale Γ(Sp K, ⊤) Γ(X, ⊤) := hE.toAlgebra
  haveI : _root_.IsReduced Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

private theorem half_pt (hRead : PulledRead) (hKer : PullKer) {p : ℕ} [Fact p.Prime] {D : Datum p} {O : Type} [CommRing O]
    {b : Base D O} {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c)
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y)
    (hy : y ≫ T.s = x) (hy' : y' ≫ T.s = x)
    (hag : ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → KerAt T y g.left → KerAt T y' g.left)
    {o₁ : Obj b N (x ≫ M.s)} (m₁ : ObjMap o₁ M.univ x) (P : Pulled T m₁ y) (P' : Pulled T m₁ y')
    (a : 𝟙_ (Over (Sp K)) ⟶ o₁.A) (ha : UKer r o₁ P.ψ _ a) : a ≫ P'.ψ = 1 := by
  have hR := (hRead p D O b N M r w j c T (Sp K) x (x ≫ M.s) o₁ m₁ y hy P a).1
  have hR' := (hRead p D O b N M r w j c T (Sp K) x (x ≫ M.s) o₁ m₁ y' hy' P' a).1
  have hkw : KilledBy o₁ w a := (P.tj K (𝟙 _)).1 a ha.1 ha.2
  have hw : (Over.Hom.left a ≫ m₁.φ) ≫ M.univ.A.hom = x := by
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
    exact Category.id_comp x
  obtain ⟨g, hg⟩ : ∃ g : Over.mk x ⟶ M.univ.A, Over.Hom.left g = Over.Hom.left a ≫ m₁.φ :=
    ⟨@Over.homMk _ _ _ (Over.mk x) M.univ.A (Over.Hom.left a ≫ m₁.φ : Sp K ⟶ M.univ.A.left) hw, rfl⟩
  have hK := (hKer p D O b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁ (𝟙 _) (𝟙 _)
    (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a g (by rw [hg, eqToHom_refl, Category.id_comp])
  have hkg : KilledBy M.univ w g := (hK.2.2 w).1 hkw
  have h1 := hag g hkg (by rw [hg]; exact hR.1 ha.1)
  rw [hg] at h1
  exact hR'.2 h1

private theorem half_ker (hRead : PulledRead) (hKer : PullKer) {p : ℕ} [Fact p.Prime] {D : Datum p} {O : Type} [CommRing O]
    {b : Base D O} {N : ℕ} (hN : 3 ≤ N) (hNp : N.Coprime p) (hm : D.m = 1) {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)}
    (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) {j c : ℕ} (hj : j ≤ D.n) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (T : TjD M r w j c)
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (hpU : IsUnit ((p : ℕ) : Γ(Sp K, ⊤))) (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y)
    (hy : y ≫ T.s = x) (hy' : y' ≫ T.s = x)
    (hag : ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → KerAt T y g.left → KerAt T y' g.left)
    {o₁ : Obj b N (x ≫ M.s)} (m₁ : ObjMap o₁ M.univ x) (P : Pulled T m₁ y) (P' : Pulled T m₁ y')
    (U : Over (Sp K)) (g : U ⟶ o₁.A) (hg : UKer r o₁ P.ψ U g) : UKer r o₁ P'.ψ U g := by
  obtain ⟨Ks, e, i, -, -, hfin, het, -, -, hiff⟩ := GlobalTheory.UPel.HT.ES.KerUPart.exists_kerUPart p D O b N hN hNp hm r w j c
    hw hu hj hc (Sp K) (x ≫ M.s) hpU o₁ P.o' P.ψ P.isog P.tj
  refine ⟨?_, hg.2⟩
  obtain ⟨z, rfl⟩ := (hiff U g).1 hg
  suffices hi : i ≫ P'.ψ = 1 by
    rw [Category.assoc, hi]
    simp
  haveI : IsFinite Ks.hom := hfin
  haveI : Etale Ks.hom := het
  haveI : IsReduced Ks.left := reduced_of_finite_etale Ks.hom
  haveI : IsProper P'.o'.A.hom := IsAbelianScheme.proper (self := P'.o'.ab)
  haveI : Smooth P'.o'.A.hom := IsAbelianScheme.smooth (self := P'.o'.ab)
  have hw1 : Over.Hom.left (i ≫ P'.ψ) ≫ P'.o'.A.hom = Ks.hom := Over.w _
  haveI : LocallyOfFiniteType (Over.Hom.left (i ≫ P'.ψ) ≫ P'.o'.A.hom) := by
    rw [hw1]
    infer_instance
  apply Over.OverMorphism.ext
  refine ext_of_apply_eq P'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
  · intro pt _ hpt
    obtain ⟨aK, haK⟩ : ∃ aK : 𝟙_ (Over (Sp K)) ⟶ Ks, Over.Hom.left aK = pointOfClosedPoint Ks.hom pt hpt :=
      ⟨Over.homMk (pointOfClosedPoint Ks.hom pt hpt) (pointOfClosedPoint_comp Ks.hom pt hpt), rfl⟩
    have h0 : (aK ≫ i) ≫ P'.ψ = 1 :=
      half_pt hRead hKer T x y y' hy hy' hag m₁ P P' (aK ≫ i) ((hiff _ _).2 ⟨aK, rfl⟩)
    have hp1 : pt = (pointOfClosedPoint Ks.hom pt hpt) (IsLocalRing.closedPoint K) :=
      (pointOfClosedPoint_apply Ks.hom pt hpt _).symm
    have e1 : (pointOfClosedPoint Ks.hom pt hpt ≫ Over.Hom.left (i ≫ P'.ψ)) (IsLocalRing.closedPoint K) =
        (pointOfClosedPoint Ks.hom pt hpt ≫ Over.Hom.left (1 : Ks ⟶ P'.o'.A)) (IsLocalRing.closedPoint K) := by
      rw [← haK, ← Over.comp_left, ← Over.comp_left, ← Category.assoc, h0]
      simp
    rw [hp1]
    exact e1
  · rw [Over.w, Over.w]

private theorem charZero_of_pt {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {p : ℕ}
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O) {K : Type} [Field K] (hK : (p : K) ≠ 0) (s : Sp K ⟶ Sp O) : CharZero K := by
  let φ : O →+* K := (Spec.preimage s).hom
  have hφp : φ p = (p : K) := map_natCast φ p
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  by_cases hb : RingHom.ker φ = ⊥
  · exact charZero_of_injective_ringHom ((RingHom.injective_iff_ker_eq_bot φ).2 hb)
  · exfalso
    have hmax : (RingHom.ker φ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hb
    have hm : RingHom.ker φ = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
    apply hK
    rw [← hφp, ← RingHom.mem_ker, hm]
    exact hp

theorem UpperTheory.Gal.crystallineComparison.Mod.secInj_of :
    PulledEx → PulledRead → PullKer → KerFromU → IsoOfKer → SecInj := by
  intro hEx hRead hKer hKF hIso p _ D O _ _ _ _ f b N r w _ hStd M j hj T K _ _ hp x y y' hy hy' hag
  haveI : CharZero K := charZero_of_pt hStd.pmem hp (x ≫ M.s)
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have hcard := hStd.card
      rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hcard
      exact (not_subsingleton_iff_nontrivial.2 inferInstance hcard.1).elim
    · exact h
  have hpU : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 _ hp).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) := ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hEx p D O b N hStd.three hStd.cop M r w j _ T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hEx p D O b N hStd.three hStd.cop M r w j _ T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hU : ∀ U g, UKer r o₁ P.ψ U g ↔ UKer r o₁ P'.ψ U g := fun U g =>
    ⟨half_ker hRead hKer hStd.three hStd.cop hStd.m1 inferInstance hStd.ule hj hc T hpU x y y' hy hy'
        (fun g h => (hag g h).1) m₁ P P' U g,
      half_ker hRead hKer hStd.three hStd.cop hStd.m1 inferInstance hStd.ule hj hc T hpU x y' y hy' hy
        (fun g h => (hag g h).2) m₁ P' P U g⟩
  have hne : w ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := fun U g =>
    ⟨hKF p D O b N r w hne hStd.ule K (x ≫ M.s) _ o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hU U g,
      hKF p D O b N r w hne hStd.ule K (x ≫ M.s) _ o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog (fun U g => (hU U g).symm) U g⟩
  obtain ⟨m, hmφ⟩ := hIso p D O b N K (x ≫ M.s) _ o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨n, hn⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hex : ∃ n' : ObjMap P.o' T.o' y', n'.φ = m.φ ≫ P'.m'.φ := by
    revert n hn
    rw [Category.id_comp]
    exact fun n hn => ⟨n, hn⟩
  obtain ⟨n', hn'⟩ := hex
  exact (T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpU P.isog P.tj).unique ⟨hy, P.m₀, P.m', P.sq⟩
    ⟨hy', P'.m₀, n', by rw [P'.sq, hn', ← hmφ, Category.assoc]⟩
