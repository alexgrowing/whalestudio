import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DenseBasis

variable {Z S : Scheme.{0}}

theorem isOpenImmersion_section (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) :
    IsOpenImmersion σ := by
  have : Etale (σ ≫ p) := by rw [hσ]; infer_instance
  have : Etale σ := Etale.of_comp σ p
  have : IsSplitMono σ := IsSplitMono.mk' ⟨p, hσ⟩
  exact IsOpenImmersion.of_flat_of_mono σ

theorem comp_section_eq_iff (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S)
    {K : Type} [Field K] (y : Spec (.of K) ⟶ Z) (w : Spec (.of K)) :
    (y ≫ p) ≫ σ = y ↔ y w ∈ Set.range σ := by
  have := isOpenImmersion_section p σ hσ
  constructor
  · intro h
    refine ⟨(y ≫ p) w, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec (.of K) ⟶ Z => f w) h
  · intro h
    have hr : Set.range y ⊆ Set.range σ := by
      rintro _ ⟨v, rfl⟩
      rwa [Subsingleton.elim v w]
    rw [← IsOpenImmersion.lift_fac σ y hr]
    simp only [Category.assoc, reassoc_of% hσ]

theorem exists_lift (p : Z ⟶ S) [IsFinite p] [Etale p] {K : Type} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ S) (w : Spec (.of K)) (z : Z) (hz : p z = x w) :
    ∃ y : Spec (.of K) ⟶ Z, y ≫ p = x ∧ y w = z := by
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z w hz
  obtain ⟨n, e, he⟩ := GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed (pullback.snd p x)
  obtain ⟨⟨j, v⟩, hv⟩ : ∃ a, AlgebraicGeometry.sigmaMk _ a = e.inv q :=
    ⟨(AlgebraicGeometry.sigmaMk _).symm (e.inv q), by simp⟩
  rw [AlgebraicGeometry.sigmaMk_mk] at hv
  refine ⟨Sigma.ι (fun _ : Fin n => Spec (.of K)) j ≫ e.hom ≫ pullback.fst p x, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he]
    simp
  · rw [Subsingleton.elim w v, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply]
    simpa using hq₁

theorem existsUnique_section_of_dense (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by
  have hO : ∀ i, IsOpenImmersion (σ i) := fun i => isOpenImmersion_section p (σ i) (hσ i)
  have hCl : ∀ i, IsClosedImmersion (σ i) := fun i => by
    have : IsClosedImmersion (σ i ≫ p) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) p
  have hp : ∀ i s, p (σ i s) = s := fun i s => by
    rw [← Scheme.Hom.comp_apply, hσ i]; rfl

  have hdisj : ∀ i j s s', σ i s = σ j s' → i = j := by
    intro i j s s' hss
    have hE : IsOpen ((σ i).base ⁻¹' Set.range (σ j)) :=
      (σ j).isOpenEmbedding.isOpen_range.preimage (σ i).continuous
    obtain ⟨t, htE, htD⟩ := hD.inter_open_nonempty _ hE ⟨s, s', hss.symm⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h t htD
    obtain ⟨t', ht'⟩ := htE
    have hsec : ((x' ≫ σ i) ≫ p) ≫ σ j = x' ≫ σ i := by
      rw [comp_section_eq_iff p (σ j) (hσ j)]
      exact ⟨t', by rw [Scheme.Hom.comp_apply, hw']; exact ht'⟩
    simp only [Category.assoc] at hsec
    rw [reassoc_of% (hσ i)] at hsec
    have hl : (x' ≫ σ i) ≫ p = x' := by rw [Category.assoc, hσ i, Category.comp_id]
    exact (hu _ hl).unique rfl hsec

  have hcov : ∀ z : Z, ∃ i, z ∈ Set.range (σ i) := by
    by_contra hne
    push Not at hne
    set C : Set Z := (⋃ i, Set.range (σ i))ᶜ with hCdef
    have hCo : IsOpen C :=
      (isClosed_iUnion_of_finite fun i => (σ i).isClosedEmbedding.isClosed_range).isOpen_compl
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀C : z₀ ∈ C := by simpa [hCdef] using hz₀
    obtain ⟨t, ⟨z, hzC, rfl⟩, htD⟩ :=
      hD.inter_open_nonempty _ (p.isOpenMap C hCo) ⟨p z₀, z₀, hz₀C, rfl⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h (p z) htD
    obtain ⟨y', hy'p, hy'w⟩ := exists_lift p x' w' z hw'.symm
    obtain ⟨i, hi, -⟩ := hu y' hy'p
    apply hzC
    rw [Set.mem_iUnion]
    exact ⟨i, x' w', by rw [← hy'w, ← hi, Scheme.Hom.comp_apply]⟩
  let w : Spec (.of K) := default
  obtain ⟨i, hi⟩ := hcov (y w)
  have hyi : (y ≫ p) ≫ σ i = y := (comp_section_eq_iff p (σ i) (hσ i) y w).2 hi
  rw [hy] at hyi
  refine ⟨i, hyi, fun j hj => ?_⟩
  obtain ⟨s, hs⟩ := hi
  refine hdisj j i (x w) s ?_
  rw [hs, ← hj, Scheme.Hom.comp_apply]

theorem comp_linComb {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  let φ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => f ≫ g, map_one' := MonObj.comp_one f, map_mul' := MonObj.comp_mul f }
  have hφ := map_list_prod φ (List.ofFn fun i => y i ^ a i)
  simpa [φ, List.map_ofFn, Function.comp_def, MonObj.comp_pow] using hφ

theorem linComb_pow_eq_one {A T : Over S} [GrpObj A] [IsCommMonObj A] {n k : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ k = 1) (a : Fin n → ℕ) :
    Out.linComb y a ^ k = 1 := by
  unfold Out.linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hy i, one_pow]

end GlobalTheory.DenseBasis

namespace GlobalTheory

open DenseBasis LatticeTorsion in

theorem torsion_basis_of_dense :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A)) (Sg : Set S), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → (∀ i, pt i ^ k = 1) → Dense Sg → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ ∀ y : Over.mk x ⟶ A, y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y := by
  intro S A _ k r pt Sg hA hk hku hpt hD hSg K _ _ x y hy
  have : IsCommMonObj A := hA.comm
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨Z, et, hZf, hZe, hadd, hkill, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom S A k ℤ hA hku
  have := hZf
  have := hZe

  have het : ∀ m : ℤ, et m = et 1 ^ m := by
    have h0 : et 0 = 1 := by
      have h00 := hadd 0 0
      rw [add_zero] at h00
      exact left_eq_mul.mp h00
    intro m
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ n ih => rw [hadd, ih, zpow_add_one]
    | pred n ih =>
      have hn := hadd (-(n : ℤ) - 1) 1
      rw [sub_add_cancel, ih] at hn
      rw [zpow_sub_one, hn, mul_inv_cancel_right]

  have hfac : ∀ (T : Over S) (a : T ⟶ A), a ^ k = 1 → ∃! g : T ⟶ Z, g ≫ et 1 = a := by
    intro T a ha
    obtain ⟨g, hg, hgu⟩ := huniv T (fun m => a ^ m) (fun m c => zpow_add a m c) (fun m => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow])
    refine ⟨g, by simpa using hg 1, fun g' hg' => hgu g' fun m => ?_⟩
    rw [het m, GrpObj.comp_zpow, hg']
  have hktor : ∀ (T : Over S) (g : T ⟶ Z), (g ≫ et 1) ^ k = 1 := fun T g => by
    rw [← MonObj.comp_pow, hkill 1, MonObj.comp_one]

  have hP : ∀ c : Fin r → ZMod k, Out.linComb pt (fun i => (c i).val) ^ k = 1 :=
    fun c => linComb_pow_eq_one pt hpt _
  choose h hh using fun c => (hfac _ _ (hP c)).exists
  have hsec : ∀ c, (h c).left ≫ Z.hom = 𝟙 S := fun c => by
    rw [Over.w (h c)]
    rfl
  have key : ∀ (K' : Type) [Field K'] (x' : Sp K' ⟶ S) (Y' : Over.mk x' ⟶ Z)
      (c : Fin r → ZMod k),
      Out.linComb (fun i => (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (c i).val) = Y' ≫ et 1 ↔ x' ≫ (h c).left = Y'.left := by
    intro K' _ x' Y' c
    rw [← comp_linComb, ← hh c, ← Category.assoc]
    constructor
    · intro he
      have he' := (hfac _ (Y' ≫ et 1) (hktor _ Y')).unique he rfl
      rw [← he']
      simp
    · intro he
      have he' : (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ h c = Y' := by
        ext
        simpa using he
      rw [he']
  have hdense : ∀ t ∈ Sg, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K')
      (x' : Spec (.of K') ⟶ S), t ∈ Set.range x' ∧
        ∀ y' : Spec (.of K') ⟶ Z.left, y' ≫ Z.hom = x' →
          ∃! c, x' ≫ (fun c => (h c).left) c = y' := by
    intro t ht
    obtain ⟨K', _, _, x', hx', H⟩ := hSg t ht
    refine ⟨K', inferInstance, inferInstance, x', hx', fun y' hy' => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := H _ (hktor _ (Over.homMk y' hy' : Over.mk x' ⟶ Z))
    exact ⟨c, (key K' x' _ c).1 hc1, fun c' hc' => hc2 c' ((key K' x' _ c').2 hc')⟩
  obtain ⟨Y', hY', -⟩ := hfac (Over.mk x) y hy
  obtain ⟨c, hc1, hc2⟩ := existsUnique_section_of_dense Z.hom (fun c => (h c).left) hsec Sg hD
    hdense K x Y'.left (by simp [Over.w Y'])
  refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
  · rw [← hY']
    exact (key K x Y' c).2 hc1
  · rw [← hY'] at hc'
    exact (key K x Y' c').1 hc'

end GlobalTheory
