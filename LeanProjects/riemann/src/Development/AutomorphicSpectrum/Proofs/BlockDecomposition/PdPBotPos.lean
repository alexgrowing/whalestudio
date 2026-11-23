import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplitRangeIsoOfIntervalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcLoc

theorem dividedPowerFiltration_dividedPowersBot' (O : Type) [CommRing O] {r : ℕ} (hr : r ≠ 0) : pdP (dividedPowersBot O) r = ⊥ := by
  classical
  rw [eq_bot_iff]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have hq : ∃ q ∈ l, q.1 ≠ 0 := by
    by_contra h
    push_neg at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h q hq)
    omega
  obtain ⟨q, hq, h0⟩ := hq
  refine List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)
  rw [dividedPowersBot_dpow_eq]
  simp [h0]

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem sub_of_bot (a b : IdF F) (T : C) (h : a.S T = ⊥) : Subsingleton (sqM a b T) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := x.2
  have hy := y.2
  simp only [sqM, h, Ideal.map_bot] at hx hy
  exact (show (x.1 : F.obj T ⧸ b.S T) = 0 from hx).trans (show (y.1 : F.obj T ⧸ b.S T) = 0 from hy).symm

theorem sub_of_top (a b : IdF F) (T : C) (h : b.S T = ⊤) : Subsingleton (sqM a b T) := by
  haveI : Subsingleton (F.obj T ⧸ b.S T) := Ideal.Quotient.subsingleton_iff.2 h
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

theorem pi_ex (a b : IdF F) (T : C) {Y : Type} [CommRing Y] {P Q : Ideal Y} (e : Y ≃+* F.obj T)
    (hP : ∀ z, e z ∈ a.S T ↔ z ∈ P) (hQ : ∀ z, e z ∈ b.S T ↔ z ∈ Q) :
    ∃ π : P →+ sqM a b T, Function.Surjective π ∧ (∀ x, π x = 0 ↔ x.1 ∈ Q) ∧
      ∀ x, (π x).1 = Ideal.Quotient.mk _ (e x.1) := by
  refine ⟨AddMonoidHom.mk' (fun x => ⟨Ideal.Quotient.mk _ (e x.1), Ideal.mem_map_of_mem _ ((hP _).2 x.2)⟩)
    (fun x y => Subtype.ext (by simp)), ?_, fun x => ?_, fun x => rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    refine ⟨⟨e.symm w, (hP _).1 (by simpa using hw)⟩, Subtype.ext ?_⟩
    simp
  · rw [← hQ, ← Ideal.Quotient.eq_zero_iff_mem]
    exact Subtype.ext_iff

theorem theta_ex {G : Type} [CommRing G] [Algebra R G] (a b : IdF F) (T : C) (ht : a.S T = ⊤) (hb : b.S T = ⊥)
    (e : R ⊗[R] G ≃+* F.obj T) (he : ∀ r, e (r ⊗ₜ 1) = algebraMap R (F.obj T) r) :
    ∃ θ : G ≃ₗ[R] sqM a b T, ∀ x, (θ x).1 = Ideal.Quotient.mk _ (e (1 ⊗ₜ x)) := by
  let f : G →ₗ[R] sqM a b T :=
    { toFun := fun x => ⟨Ideal.Quotient.mk _ (e (1 ⊗ₜ x)), Ideal.mem_map_of_mem _ (by rw [ht]; trivial)⟩
      map_add' := fun x y => Subtype.ext (by simp [TensorProduct.tmul_add])
      map_smul' := fun r x => Subtype.ext (by
        have h1 : (1 : R) ⊗ₜ[R] (r • x) = (r ⊗ₜ[R] (1 : G)) * ((1 : R) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] (r • x))) = r • Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] x))
        rw [h1, map_mul, he, map_mul, Algebra.smul_def]
        rfl) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun x y h => ?_, ?_⟩, fun x => rfl⟩
  · have h1 := congrArg Subtype.val h
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb, Ideal.mem_bot, ← map_sub, map_eq_zero_iff _ e.injective, ← TensorProduct.tmul_sub] at h2
    have h3 := congrArg (TensorProduct.lid R G) h2
    simpa [sub_eq_zero] using h3
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨TensorProduct.lid R G (e.symm w), Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w))) = _
    have : (1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w) = e.symm w := by
      refine TensorProduct.induction_on (e.symm w) (by simp) (fun r x => ?_) (fun u v hu hv => ?_)
      · simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      · simp only [map_add, TensorProduct.tmul_add, hu, hv]
    rw [this, e.apply_symm_apply]

end Sq

theorem crit_of {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (P : Poly Φ)
    {F a : ℤ → IdF Φ.A} {r r₀ : ℤ} (h : P.Crit F r₀) (h0 : a r = F r₀)
    (hk : ∀ k : ℕ, a (r - k) = F (r₀ - k)) : P.Crit a r := by
  intro T b
  rw [h0]
  simp only [hk]
  exact h T b

theorem chart_tens : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) (l s m : ℕ)
    (S : GrSplit O γ m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B)
      (hD : TO q l s {V} cO.D) (hD' : TS γ q l s {V} cA.D)
      (e : (⟨cO.D, hD⟩ : (TO q l s {V}).FullSubcategory) ⟶ (smO γ q l s {V}).G.obj ⟨cA.D, hD'⟩),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, e.hom.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f)) →
      ∀ (c t : ℤ), 0 ≤ c →
      ∀ (ha : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - c - i)) (sFil _ (t - c)))
        (hb : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - i)) (sFil _ t)),
      Tens O (N := S.N) (M := fun i => (sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).obj ⟨cO.D, hD⟩)
        (M' := (sq (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t)).obj ⟨cA.D, hD'⟩)
        fun i n x => ((smO γ q l s {V}).sqC (S.ν i n) (ha i n) (hb i n)).τ ⟨cA.D, hD'⟩
          (((sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).map e).hom x) := by
  intro O A _ _ _ I γ l s m S X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hD hD' e hiO hiA he c t hc ha hb
  haveI hF : Module.Flat O Γ(X, V) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale cV.t cV.etale
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have pO := (GlobalTheory.T.chart_divided_powers_graded_constant cO (GlobalTheory.T.chart_is_good cO) (TO q l s {V}) hQ hD).1
  have pA := (GlobalTheory.T.chart_divided_powers_graded_constant cA (GlobalTheory.T.chart_is_good cA) (TS γ q l s {V}) hQ' hD').1
  have bot1 : ∀ r : ℕ, r ≠ 0 → cO.D.pdPow r = ⊥ := fun r hr => by
    rw [pO, dividedPowerFiltration_dividedPowersBot' O hr, Ideal.map_bot]
  have mA : ∀ (r : ℕ) (z : A ⊗[O] Γ(X, V)), eA z ∈ cA.D.pdPow r ↔
      z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) := fun r z => by
    have h1 : cA.D.i = (eA : A ⊗[O] Γ(X, V) →+* cA.D.B).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) :=
      RingHom.ext fun a => (hiA a).symm
    rw [pA, h1, ← Ideal.map_map]
    constructor
    · intro h
      obtain ⟨w, hw, h2⟩ := (Ideal.mem_map_iff_of_surjective _ eA.surjective).1 h
      have h3 := eA.injective h2
      rwa [← h3]
    · exact fun h => Ideal.mem_map_of_mem _ h
  have fa : ∀ (i : Fin m) (hu : (t - c).toNat ≤ (i : ℕ)) (hv : (i : ℕ) < t.toNat),
      ∃ θ : Γ(X, V) ≃ₗ[O] sqM (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩,
        ∀ x, (θ x).1 = Ideal.Quotient.mk _ (eO (1 ⊗ₜ x)) := fun i hu hv =>
    theta_ex (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩
      (by
        change cO.D.pdPow _ = ⊤
        rw [show (t - c - i).toNat = 0 by omega]
        exact cO.D.pdPow_zero)
      (by
        change cO.D.pdPow _ = ⊥
        exact bot1 _ (by omega)) eO hiO
  choose θ hθ using fa
  obtain ⟨π, hs, hk, hπ⟩ := pi_ex (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t) ⟨cA.D, hD'⟩ eA (mA _) (mA _)
  refine GlobalTheory.T.graded_split_range_iso_of_interval (O := O) (A := A) (G := Γ(X, V)) γ m S (t - c).toNat t.toNat θ ?_ π hs hk _ ?_ ?_
  · intro i hi
    by_cases hu : (t - c).toNat ≤ (i : ℕ)
    · refine sub_of_top _ _ _ ?_
      change cO.D.pdPow _ = ⊤
      rw [show (t - i).toNat = 0 by
        have : ¬ (i : ℕ) < t.toNat := fun h => hi ⟨hu, h⟩
        omega]
      exact cO.D.pdPow_zero
    · refine sub_of_bot _ _ _ ?_
      change cO.D.pdPow _ = ⊥
      exact bot1 _ (by omega)
  · intro i n
    simp only [map_zero]
  · intro i n x hu hv hx
    refine Subtype.ext ?_
    rw [hπ]
    have hz := hθ i hu hv x
    generalize θ i hu hv x = z at hz ⊢
    obtain ⟨z, hz'⟩ := z
    change z = _ at hz
    subst hz
    have key : ∀ w : cA.D.B, w = eA (1 ⊗ₜ x) → cA.D.i (S.ν i n) * w = eA (S.ν i n ⊗ₜ x) := by
      rintro _ rfl
      rw [← hiA, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (Ideal.Quotient.mk _) (key _ (he x))

theorem bc_single : KH.LocBc → KH.PolyTf → BcOn True := by
  intro hLoc hPoly O A _ _ _ I γ l s m hO hA S X q 𝒱 h r r' hrr hrs ha hb j
  obtain ⟨-, V, d, rfl, ⟨cV⟩⟩ | ⟨hF, -⟩ := h
  swap
  · exact absurd trivial hF
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℤ, 0 ≤ c ∧ r = r' - c := ⟨r' - r, by omega, by ring⟩
  obtain ⟨cO, eO, tfO, hiO, htO, hevO⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (dividedPowersBot O) l s hO q
    (Ideal.Quotient.mk ⊥) (fun _ => rfl) cV
  obtain ⟨cA, eA, tfA, hiA, htA, hevA⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := A) γ l s hA q (κA O I) (fun _ => rfl) cV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chart_tensor_base_compat γ q cV cO cA eO eA hiO hiA hevO hevA
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hD : TO q l s {V} cO.D := ⟨tfO, V, rfl, cO.inV⟩
  have hD' : TS γ q l s {V} cA.D := ⟨tfA, V, rfl, cA.inV⟩
  have gO := GlobalTheory.T.chart_is_good cO
  have gA := GlobalTheory.T.chart_is_good cA
  let E := cO.frame gO (TO q l s {V}) hQ hD
  let E' := cA.frame gA (TS γ q l s {V}) hQ' hD'
  let e : E.D ⟶ (smO γ q l s {V}).G.obj E'.D := ObjectProperty.homMk e₀
  have he : (smO γ q l s {V}).Fr E E' e := by
    intro i T σ σ'
    have h1 : e₀.φ (cO.t i) = cA.t i := by
      rw [← htO, ← htA]; exact he₀ _
    change (σ'.hom.φ (e₀.φ (cO.t i)) - σ.hom.φ (e₀.φ (cO.t i)) : T.obj.B) = σ'.hom.φ (cA.t i) - σ.hom.φ (cA.t i)
    rw [h1]
  have fil := GlobalTheory.T.sheaf_filtration_property (TO q l s {V})
  have fil' := GlobalTheory.T.sheaf_filtration_property (TS γ q l s {V})
  obtain ⟨PO, hPO⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {V}
  obtain ⟨PA, hPA⟩ := hPoly γ q (κA O I) l s {V}
  have lem : ∀ (i : ℕ) (a : A), a ∈ pdP γ i → ∀ t : ℤ, (smO γ q l s {V}).LeC a (sFil _ (t - i)) (sFil _ t) :=
    fun i a h t => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s {V} i a h t
  refine hLoc (smO γ q l s {V}) PO PA E E' e he (fun _ => Function.injective_id) S.N S.ν
    (fun i t => sFil _ (t - c - i)) (fun i t => sFil _ (t - i)) (fun t => sFil _ (t - c)) (fun t => sFil _ t) r'
    (fun i => ⟨fun t T => fil.anti (by omega) T, fun t ht => crit_of PO (hPO (t - c - i) (by omega)).1 rfl
        (fun k => by congr 1; ring),
      fun t ht => crit_of PO (hPO (t - i) (by omega)).1 rfl (fun k => by congr 1; ring)⟩)
    ⟨fun t T => fil'.anti (by omega) T, fun t ht => crit_of PA (hPA (t - c) (by omega)).1 rfl (fun k => by congr 1; ring),
      fun t ht => (hPA t (by omega)).1⟩
    (fun i n t => lem i _ (S.mem i n) _) (fun i n t => lem i _ (S.mem i n) _) ?_ j
  intro t _ _
  exact chart_tens γ l s m S q cV cO cA eO eA hD hD' e hiO hiA he₀ c t hc _ _

end GlobalTheory.CompanionTheory.BcLoc
