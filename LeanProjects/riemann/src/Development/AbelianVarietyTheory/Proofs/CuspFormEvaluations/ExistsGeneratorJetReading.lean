import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValJetEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_point_eq {K : Type} [Field K] {I : Type} {m : ℕ} (p : PrimeSpectrum (Jet K I m)) :
    p = IsLocalRing.closedPoint (Jet K I m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K I m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_id' {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (h' : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (b : Γ(Y, ⊤)ˣ) (hb : (f.appLE U ⊤ h').hom a.val = b.val) :
    res h (pullU f U a) = res (le_top : W ≤ ⊤) b := by
  have : b = res h' (pullU f U a) := Units.ext hb.symm
  rw [this, res_res']

theorem exists_gen_of_units {X Y : Scheme.{0}} (L : LB X) (hY : ∀ p q : Y, p = q) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : K → L.ι → Γ(Y, ⊤)ˣ)
    (hu : ∀ k j j' (h : ⊤ ≤ φ k ⁻¹ᵁ (L.U j ⊓ L.U j')),
      (u k j).val = ((φ k).appLE _ ⊤ h).hom (L.g j j').val * (u k j').val) :
    ∃ τ : LB.Gen (LB.LinComb L φ ε), τ.IsGen ∧ ∀ (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j),
      (Y.presheaf.map (homOfLE h).op).hom (τ.s j).val = (∏ k, u k (j k) ^ ε k).val := by
  refine ⟨⟨fun j => res le_top (∏ k, u k (j k) ^ ε k)⟩, fun (i : K → L.ι) (j : K → L.ι) => ?_, fun j h => ?_⟩
  · by_cases hne : ∃ p, p ∈ LB.wchart L φ i ⊓ LB.wchart L φ j
    · obtain ⟨p, hp⟩ := hne
      have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k q _ => by
        rw [hY q p]
        exact ⟨LB.wchart_le L φ i k hp.1, LB.wchart_le L φ j k hp.2⟩
      have hle : ∀ k, LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k =>
        le_top.trans (hk k)
      show res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) (res le_top (∏ k, u k (i k) ^ ε k)) =
        (∏ k, (res (hle k) (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k)) *
          res (inf_le_right : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) (res le_top (∏ k, u k (j k) ^ ε k))
      rw [res_res', res_res', map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [res_pullU (φ k) _ _ (hk k) (L.g (i k) (j k)) (u k (i k) * (u k (j k))⁻¹)
        (by rw [Units.val_mul, hu k _ _ (hk k), Units.mul_inv_cancel_right]), map_zpow, map_zpow, ← mul_zpow,
        ← map_mul, inv_mul_cancel_right]
    · have hb : LB.wchart L φ i ⊓ LB.wchart L φ j = ⊥ :=
        le_bot_iff.1 fun p hp => (hne ⟨p, hp⟩).elim
      have : Subsingleton Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j) := by
        rw [hb]; infer_instance
      exact Units.ext (this.elim _ _)
  · exact congrArg Units.val ((res_res' le_top h _).trans (res_id' _ _))

theorem jetOf_one {d : ℕ} (m : ℕ) : jetOf m (fun _ : Fin d → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) :
    jetOf m (fun z => f z ^ k) = jetOf m f ^ k := by
  induction k with
  | zero => simpa using jetOf_one m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hf.pow k) hf]
    congr 1

theorem contDiffAt_zpow' {d : ℕ} {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0) (k : ℤ) :
    ContDiffAt ℂ ω (fun z => f z ^ k) 0 := by
  cases k with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)

theorem jetOf_zpow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin d) m)ˣ) (hu : u.val = jetOf m f) (k : ℤ) :
    jetOf m (fun z => f z ^ k) = (u ^ k).val := by
  cases k with
  | ofNat k => simpa [hu] using jetOf_pow m hf k
  | negSucc k =>
    rw [zpow_negSucc]
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow m hf,
      ← jetOf_mul m (hf.pow (k + 1)) (contDiffAt_zpow' hf h0 _), ← jetOf_one m]
    refine jetOf_congr m ((hf.continuousAt.eventually_ne h0).mono fun z hz => ?_)
    show f z ^ (k + 1) * f z ^ (Int.negSucc k) = 1
    rw [zpow_negSucc, mul_inv_cancel₀ (pow_ne_zero _ hz)]

theorem jetOf_prod {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hf a) (contDiffAt_prod fun k _ => hf k)]
    congr 1
    funext z
    simp [Finset.prod_insert ha]

theorem appLE_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by
  have h1 : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U := fun p _ => by
    rw [jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) p]
    show jetPt e hol m (IsLocalRing.closedPoint _) ∈ U
    rwa [jetPt_closedPoint]
  have e1 : (spMap r ≫ jetPt e hol m).appLE U ⊤ h = (jetPt e hol m).appLE U ⊤ h1 ≫ (spMap r).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap r) (jetPt e hol m) U ⊤ ⊤ h1 le_rfl).symm
  rw [e1, jetPt_appLE e hol m U hU h1, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {I : Type} (r : Jet ℂ (Fin 1 × Fin d) m →+* Jet ℂ I m) (U : Y.Opens)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) : e 0 cpt ∈ U := by
  let p : Sp (Jet ℂ I m) := IsLocalRing.closedPoint (Jet ℂ I m)
  have h2 : (spMap r ≫ jetPt e hol m) p ∈ U := h (show p ∈ (⊤ : (Sp (Jet ℂ I m)).Opens) from trivial)
  rw [Scheme.Hom.comp_apply] at h2
  rw [← jetPt_closedPoint e hol m, ← jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) (spMap r p)]
  exact h2

theorem contDiffAt_fr {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n : ℕ} (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (j : L.L.ι)
    (h : (Φ.e (Λ (colsOf n g 0))).left cpt ∈ L.L.U j) :
    ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0 := by
  have h1 : ContDiffAt ℂ ω (Φ.fr j) (Λ (colsOf n g 0)) :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} (Φ.fr j) (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) _
      (top_le_of_mem h)).contDiffAt
  have h2 : ContDiff ℂ ω (colsOf n g) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))
  have h3 : ContDiff ℂ ω (fun v => Λ (colsOf n g v)) :=
    (LinearMap.toContinuousLinearMap Λ).contDiff.comp h2
  exact h1.comp 0 h3.contDiffAt

theorem exists_gen_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  intro S A _ _ L x0 g Φ n m K _ φ ε Λ hφ
  classical
  have hφ' := hφ
  choose hol hφe using hφ'
  let r : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m := renN n g m
  let F : K → L.L.ι → (Fin (n * g) → ℂ) → ℂ := fun k j v => Φ.fr j (Λ k (colsOf n g v))
  let u0 : K → L.L.ι → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k j =>
    if h : IsUnit (jetOf m (F k j)) then h.unit else 1
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ φ k ⁻¹ᵁ U → (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ U := fun k U h =>
    mem_of_spMap_jetPt _ (hol k) m r U (by rw [hφe k] at h; exact h)
  have hF0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → F k j 0 ≠ 0 := fun k j h =>
    Φ.fr_ne j _ (top_le_of_mem h)
  have hu0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → (u0 k j).val = jetOf m (F k j) := fun k j h => by
    have hu : IsUnit (jetOf m (F k j)) := isUnit_of_jetAug _ (by rw [jetAug_jetOf]; exact hF0 k j h)
    simp only [u0, dif_pos hu, IsUnit.unit_spec]
  let ρ : (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ →* Γ(Sp (Jet ℂ (Fin n × Fin g) m), ⊤)ˣ :=
    Units.map ((toΓ (Jet ℂ (Fin n × Fin g) m)).comp r).toMonoidHom
  have hρ : ∀ a, (ρ a).val = toΓ _ (r a.val) := fun _ => rfl
  obtain ⟨τ, h1, h2⟩ := exists_gen_of_units L.L (Y := Sp (Jet ℂ (Fin n × Fin g) m))
    (fun p q => (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) p).trans
      (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) q).symm) φ ε (fun k j => ρ (u0 k j)) (fun k j j' h => by
      have hm := hmem k _ h
      have key : ∀ (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (h : ⊤ ≤ ψ ⁻¹ᵁ (L.L.U j ⊓ L.L.U j')),
          ψ = spMap r ≫ jetPt _ (hol k) m → (ψ.appLE _ ⊤ h).hom (L.L.g j j').val = toΓ _ (r (jetOf m fun z =>
            valAt' (Φ.e (Λ k (colsOf n g z))).left (L.L.U j ⊓ L.L.U j') (L.L.g j j').val)) := by
        rintro _ h rfl
        exact appLE_spMap_jetPt _ (hol k) m r _ hm h _
      rw [key _ h (hφe k), hρ, hρ, ← map_mul, ← map_mul, hu0 k j hm.1, hu0 k j' hm.2,
        ← jetOf_mul m (contDiffAt_val _ (hol k) hm _) (contDiffAt_fr Φ (Λ k) j' hm.2)]
      exact congrArg (fun x => toΓ _ (r x))
        (jetOf_congr m ((eventually_mem _ (hol k) hm).mono fun z hz => Φ.fr_g j j' _ hz)))
  refine ⟨τ, h1, hφ, fun j h => ?_⟩
  have hm : ∀ k, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U (j k) := fun k =>
    hmem k _ (h.trans (LB.wchart_le L.L φ j k))
  rw [h2 j h]
  have e1 : (∏ k, ρ (u0 k (j k)) ^ ε k) = ρ (∏ k, u0 k (j k) ^ ε k) := by
    simp only [map_prod, map_zpow]
  rw [e1, hρ]
  show toΓ _ (r _) = toΓ _ (r (jetOf m fun v => ∏ k, F k (j k) v ^ ε k))
  refine congrArg (fun x => toΓ _ (r x)) ?_
  rw [jetOf_prod m Finset.univ (f := fun k v => F k (j k) v ^ ε k)
    (fun k => contDiffAt_zpow' (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _), Units.coe_prod]
  exact Finset.prod_congr rfl fun k _ =>
    (jetOf_zpow m (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _ (hu0 k _ (hm k)) _).symm

end GlobalTheory.AnValJetEx
