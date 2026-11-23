import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv

noncomputable section

namespace GlobalTheory.ShortVal.Halves

open scoped TensorProduct in

theorem nonempty_equiv_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] (r : ℕ)
    (hr : Module.finrank R N = r) :
    Nonempty ((N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[R] (Fin r → R ⧸ I)) := by
  classical
  haveI : Module.Flat R N := inferInstance
  have hrk : ∀ P : MaximalSpectrum (R ⧸ I),
      Module.finrank ((R ⧸ I) ⧸ P.1) (((R ⧸ I) ⧸ P.1) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] N)) = r := by
    intro P
    letI := Ideal.Quotient.field P.1
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1)
      ((R ⧸ I) ⧸ P.1) N).finrank_eq]
    let p₀ : PrimeSpectrum ((R ⧸ I) ⧸ P.1) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := (R ⧸ I) ⧸ P.1)
      (M := ((R ⧸ I) ⧸ P.1) ⊗[R] N)) p₀
    have h2 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.1) p₀
    have h3 := (Ideal.finrank_fiber_eq_rankAtStalk (M := N)
      (p₀.comap (algebraMap R ((R ⧸ I) ⧸ P.1))).asIdeal).symm.trans
      (Ideal.finrank_fiber_eq_finrank (M := N) (p₀.comap (algebraMap R ((R ⧸ I) ⧸ P.1))).asIdeal)
    exact h1.symm.trans (h2.trans (h3.trans hr))
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) r hrk
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul N I).symm.trans (b.equivFun.restrictScalars R)⟩

theorem exists_equiv_of_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ ψ : (Fin r → R ⧸ I) ≃ₗ[R] Q, ∀ b, ψ (Pi.single b 1) = x b := by
  classical
  have hsur : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let y : Fin r → (Fin r → R ⧸ I) := fun b => e (x b)
  have hy : Submodule.span (R ⧸ I) (Set.range y) = ⊤ := by
    have h1 : Submodule.span R (Set.range y) = ⊤ := by
      have h0 : Set.range y = (e : Q →ₗ[R] (Fin r → R ⧸ I)) '' Set.range x := by
        rw [← Set.range_comp]; rfl
      rw [h0, Submodule.span_image, hx, Submodule.map_top, LinearEquiv.range]
    rw [← Submodule.restrictScalars_eq_top_iff R, Submodule.restrictScalars_span R (R ⧸ I) hsur]
    exact h1
  let L : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I) :=
    ∑ b, (LinearMap.proj b : (Fin r → R ⧸ I) →ₗ[R ⧸ I] R ⧸ I).smulRight (y b)
  have hL : ∀ b, L (Pi.single b 1) = y b := by
    intro b
    simp [L, LinearMap.sum_apply, LinearMap.smulRight_apply, Pi.single_apply]
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hy, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨Pi.single b 1, hL b⟩
  have hbij : Function.Bijective L := OrzechProperty.bijective_of_surjective_endomorphism L hsurj
  refine ⟨((LinearEquiv.ofBijective L hbij).restrictScalars R).trans e.symm, fun b => ?_⟩
  simp [hL, y]

theorem exists_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) : ∃ x : Fin r → Q, Submodule.span R (Set.range x) = ⊤ := by
  classical
  have hsur : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  refine ⟨fun b => e.symm (Pi.single b 1), ?_⟩
  have hfun : (fun b : Fin r => (Pi.single b (1 : R ⧸ I) : Fin r → R ⧸ I)) =
      ⇑(Pi.basisFun (R ⧸ I) (Fin r)) := funext fun b => (Pi.basisFun_apply _ _ b).symm
  have h1 : Submodule.span R (Set.range fun b : Fin r => (Pi.single b (1 : R ⧸ I) : Fin r → R ⧸ I)) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) hsur, Submodule.restrictScalars_eq_top_iff, hfun]
    exact (Pi.basisFun (R ⧸ I) (Fin r)).span_eq
  have h2 : (Set.range fun b => e.symm (Pi.single b 1)) =
      (e.symm : (Fin r → R ⧸ I) →ₗ[R] Q) '' Set.range fun b : Fin r => (Pi.single b (1 : R ⧸ I) : Fin r → R ⧸ I) := by
    rw [← Set.range_comp]; rfl
  rw [h2, Submodule.span_image, h1, Submodule.map_top, LinearEquiv.range]

theorem existsUnique_equiv {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x x' : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤)
    (hx' : Submodule.span R (Set.range x') = ⊤) : ∃! g : Q ≃ₗ[R] Q, ∀ b, g (x b) = x' b := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_span I r e x hx
  obtain ⟨ψ', hψ'⟩ := exists_equiv_of_span I r e x' hx'
  refine ⟨ψ.symm.trans ψ', fun b => ?_, fun g hg => ?_⟩
  · rw [LinearEquiv.trans_apply, ← hψ b, LinearEquiv.symm_apply_apply, hψ' b]
  · apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on_range hx
    intro b
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hg b, LinearEquiv.trans_apply, ← hψ b,
      LinearEquiv.symm_apply_apply, hψ' b]

theorem exists_adjoint {R P Q Z : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Z] (s : R → R) (B : P → Q → Z) (hadd : ∀ u v w, B u (v + w) = B u v + B u w)
    (hbal : ∀ a u v, B u (a • v) = B (s a • u) v)
    (hnd : ∀ v w, (∀ u, B u v = B u w) → v = w)
    (hrep : ∀ (g : P →ₗ[R] P) (v : Q), ∃ w, ∀ u, B (g u) v = B u w) :
    ∃ adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q), (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : Q ≃ₗ[R] Q) (g : P ≃ₗ[R] P), (∀ u v, B (g u) v = B u (k v)) ↔ k = adj g := by
  classical
  choose st hst using hrep
  have hsm : ∀ (g : P →ₗ[R] P) (a : R) (v : Q), st g (a • v) = a • st g v := by
    intro g a v
    refine hnd _ _ fun u => ?_
    rw [← hst g (a • v) u, hbal, ← map_smul g, hst g v (s a • u), ← hbal]
  have had : ∀ (g : P →ₗ[R] P) (v w : Q), st g (v + w) = st g v + st g w := by
    intro g v w
    refine hnd _ _ fun u => ?_
    rw [← hst g (v + w) u, hadd, hadd, ← hst g v u, ← hst g w u]
  have hcomp : ∀ (g h : P →ₗ[R] P) (v : Q), st (g ∘ₗ h) v = st h (st g v) := by
    intro g h v
    refine hnd _ _ fun u => ?_
    rw [← hst (g ∘ₗ h) v u, LinearMap.comp_apply, hst g v (h u), hst h (st g v) u]
  have hid : ∀ v : Q, st LinearMap.id v = v := by
    intro v
    refine hnd _ _ fun u => ?_
    rw [← hst LinearMap.id v u, LinearMap.id_apply]
  let T : (P →ₗ[R] P) → (Q →ₗ[R] Q) := fun g => ⟨⟨st g, had g⟩, hsm g⟩
  have hT : ∀ g v, T g v = st g v := fun _ _ => rfl
  have hinv : ∀ g : P ≃ₗ[R] P, ∀ v, T g (T g.symm v) = v := by
    intro g v
    rw [hT, hT, ← hcomp]
    have h1 : (g.symm : P →ₗ[R] P) ∘ₗ (g : P →ₗ[R] P) = LinearMap.id := LinearMap.ext fun x => by simp
    rw [h1, hid]
  have hinv' : ∀ g : P ≃ₗ[R] P, ∀ v, T g.symm (T g v) = v := by
    intro g v
    rw [hT, hT, ← hcomp]
    have h1 : (g : P →ₗ[R] P) ∘ₗ (g.symm : P →ₗ[R] P) = LinearMap.id := LinearMap.ext fun x => by simp
    rw [h1, hid]
  let adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q) := fun g =>
    LinearEquiv.ofLinear (T g) (T g.symm) (LinearMap.ext (hinv g)) (LinearMap.ext (hinv' g))
  have hadj : ∀ g v, adj g v = st g v := fun _ _ => rfl
  refine ⟨adj, fun g g' => ?_, fun k g => ⟨fun h => ?_, ?_⟩⟩
  · refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, hadj, hadj, hadj, ← hcomp]
    congr 1
  · refine LinearEquiv.ext fun v => hnd _ _ fun u => ?_
    rw [hadj, ← h u v]
    exact hst _ v u
  · rintro rfl u v
    rw [hadj]
    exact hst _ v u

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem cHalf_spec (I : Ideal (𝓞 E)) (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) :
    cHalf H I ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ cHalf H I - 1 ∈ I := by
  classical
  have h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I := by
    have h1 : (1 : 𝓞 E) ∈ I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [hI]; exact Submodule.mem_top
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
    refine ⟨c, hc, ?_⟩
    have h2 : c - 1 = -a := by rw [← hac]; ring
    rw [h2]; exact neg_mem ha
  unfold cHalf
  rw [dif_pos h]
  exact h.choose_spec

theorem ef_swap (x y : Dw.La) : Dw.EF y x = -Dw.EF x y := by
  have h := Dw.alt (x + y)
  simp only [map_add, LinearMap.add_apply, Dw.alt] at h
  linarith

theorem qRep_mk {K : Submodule (𝓞 E) Dw.La} (q : Dw.La ⧸ K) : Submodule.Quotient.mk (qRep q) = q := by
  unfold qRep
  exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

private theorem host_bar_bar' (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

private theorem dvd_EF_cHalf_sub_of_sub_mem {N : ℕ} {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (a a' b b' : Dw.La)
    (hab : a - a' ∈ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La))
    (hbb : b - b' ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (N : ℤ) ∣ Dw.EF a' (cHalf H I • b') - Dw.EF a (cHalf H I • b) := by
  obtain ⟨hcJ, -⟩ := cHalf_spec (H := H) I hI
  have e1 : Dw.EF a' (cHalf H I • b') - Dw.EF a (cHalf H I • b) =
      -(Dw.EF (a - a') (cHalf H I • b) + Dw.EF a' (cHalf H I • (b - b'))) := by
    simp only [map_sub, LinearMap.sub_apply, smul_sub]; ring
  rw [e1, dvd_neg]
  exact dvd_add (GlobalTheory.DatumInverseCharacter.dvd_left Dw hp hcJ b hab)
    (GlobalTheory.DatumInverseCharacter.dvd_right Dw hp hcJ a' hbb)

private theorem mem_ideal_smul_of_forall_dvd_EF_cHalf {N : ℕ} (hN : N ≠ 0) {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (z : Dw.La)
    (h : ∀ x : Dw.La, (N : ℤ) ∣ Dw.EF x (cHalf H I • z)) :
    z ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨-, hc1⟩ := cHalf_spec (H := H) I hI
  have h1 : ∀ x : Dw.La, (N : ℤ) ∣ Dw.EF (cHalf H I • z) x := fun x => by
    rw [ef_swap, dvd_neg]; exact h x
  have hmod := GlobalTheory.DatumInverseCharacter.modN_of_dvd Dw (Nat.pos_of_ne_zero hN) h1
  have hNmem : (N : 𝓞 E) ∈ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hp]; exact Ideal.mem_span_singleton_self _
  have hmem := GlobalTheory.DatumInverseCharacter.mem_of_modN Dw hNmem hmod
  have hle : ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E)) • ⊤ : Submodule (𝓞 E) Dw.La) ≤ I • ⊤ :=
    Submodule.smul_mono_left Ideal.mul_le_left
  have h2 : (cHalf H I - 1) • z ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hc1 Submodule.mem_top
  have h3 : z = cHalf H I • z - (cHalf H I - 1) • z := by
    rw [sub_smul, one_smul, sub_sub_cancel]
  rw [h3]
  exact Submodule.sub_mem _ (hle hmem) h2

private theorem exists_forall_dvd_EF_cHalf_sub_of_linearMap {N : ℕ} {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (G : Dw.La →ₗ[𝓞 E] Dw.La) (t : Dw.La) :
    ∃ m : Dw.La, ∀ a : Dw.La,
      (N : ℤ) ∣ Dw.EF a (cHalf H I • m) - Dw.EF (G a) (cHalf H I • t) := by
  obtain ⟨hcJ, hc1⟩ := cHalf_spec (H := H) I hI
  obtain ⟨G', hG'⟩ := GlobalTheory.DatumInverseCharacter.exists_adjoint Dw G
  refine ⟨G' (cHalf H I • t), fun a => ?_⟩
  have h1 : ∀ a', Dw.EF (G a') (cHalf H I • t) = Dw.EF a' (G' (cHalf H I • t)) := fun a' => by
    rw [ef_swap (cHalf H I • t) (G a'), ← hG' (cHalf H I • t) a', ef_swap a' (G' (cHalf H I • t)),
      neg_neg]
  have hbar1 : H.bar (cHalf H I - 1) ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hc1
  have h2 : Dw.EF a (cHalf H I • G' (cHalf H I • t)) - Dw.EF (G a) (cHalf H I • t) =
      Dw.EF (G (H.bar (cHalf H I - 1) • a)) (cHalf H I • t) := by
    rw [h1, h1, Dw.adj, host_bar_bar', sub_smul, one_smul, map_sub]
  rw [h2]
  exact GlobalTheory.DatumInverseCharacter.dvd_left Dw hp hcJ t
    (by rw [map_smul]; exact Submodule.smul_mem_smul hbar1 Submodule.mem_top)

theorem exists_adjoint_halves (N : ℕ) (hN : N ≠ 0) (I : Ideal (𝓞 E))
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (KJ KI : Submodule (𝓞 E) Dw.La)
    (hKJ : KJ = I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤) (hKI : KI = I • ⊤) :
    ∃ adj : ((Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)) → ((Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)),
      (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : (Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)) (kst : (Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)),
        (∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H I • v) -
          Dw.EF u (cHalf H I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by
  classical
  subst hKJ hKI
  let B : (Dw.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) →
      (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) → ZMod N :=
    fun p q => ((Dw.EF (qRep p) (cHalf H I • qRep q) : ℤ) : ZMod N)
  have key : ∀ a a' b b' : Dw.La,
      (Submodule.Quotient.mk a : Dw.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) =
        Submodule.Quotient.mk a' →
      (Submodule.Quotient.mk b : Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) = Submodule.Quotient.mk b' →
      ((Dw.EF a (cHalf H I • b) : ℤ) : ZMod N) = ((Dw.EF a' (cHalf H I • b') : ℤ) : ZMod N) := by
    intro a a' b b' hab hbb
    rw [Submodule.Quotient.eq] at hab hbb
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_EF_cHalf_sub_of_sub_mem hp hI a a' b b' hab hbb)
  have hB : ∀ a b : Dw.La, B (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      ((Dw.EF a (cHalf H I • b) : ℤ) : ZMod N) :=
    fun a b => key _ _ _ _ (qRep_mk _) (qRep_mk _)
  have hadd : ∀ p q q', B p (q + q') = B p q + B p q' := by
    intro p q q'
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, smul_add, map_add, Int.cast_add]
  have hbal : ∀ (r : 𝓞 E) p q, B p (r • q) = B (H.bar r • p) q := by
    intro r p q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hB, hB, Dw.adj, host_bar_bar',
      smul_comm]
  have hnd : ∀ q q', (∀ p, B p q = B p q') → q = q' := by
    intro q q' h
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [Submodule.Quotient.eq]
    refine mem_ideal_smul_of_forall_dvd_EF_cHalf hN hp hI _ fun x => ?_
    have h0 := h (Submodule.Quotient.mk x)
    rw [hB, hB, ZMod.intCast_eq_intCast_iff_dvd_sub] at h0
    rw [smul_sub, map_sub]
    exact dvd_sub_comm.mp h0
  have hrep : ∀ (g : (Dw.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) →ₗ[𝓞 E]
      (Dw.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)))
      (v : Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)), ∃ w, ∀ u, B (g u) v = B u w := by
    intro g v
    haveI := Dw.proj
    obtain ⟨G, hG⟩ := Module.projective_lifting_property
      ((I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La).mkQ)
      (g ∘ₗ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La).mkQ)
      (Submodule.mkQ_surjective _)
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨m, hm⟩ := exists_forall_dvd_EF_cHalf_sub_of_linearMap hp hI G t
    refine ⟨Submodule.Quotient.mk m, fun u => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have hGa : g (Submodule.Quotient.mk a) = Submodule.Quotient.mk (G a) := by
      have h0 := LinearMap.congr_fun hG a
      simpa using h0.symm
    rw [hGa, hB, hB]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hm a)
  obtain ⟨adj, hmul, hiff⟩ := exists_adjoint (⇑H.bar) B hadd hbal hnd hrep
  refine ⟨adj, hmul, fun k kst => ?_⟩
  rw [← hiff k kst]
  have e1 : ∀ u v : Dw.La, B (kst (Submodule.Quotient.mk u)) (Submodule.Quotient.mk v) =
      ((Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H I • v) : ℤ) : ZMod N) :=
    fun u v => key _ _ _ _ rfl (qRep_mk _)
  have e2 : ∀ u v : Dw.La, B (Submodule.Quotient.mk u) (k (Submodule.Quotient.mk v)) =
      ((Dw.EF u (cHalf H I • qRep (k (Submodule.Quotient.mk v))) : ℤ) : ZMod N) :=
    fun u v => key _ _ _ _ (qRep_mk _) rfl
  constructor
  · intro h p q
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [e1, e2]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h u v)).symm
  · intro h u v
    have h0 := h (Submodule.Quotient.mk u) (Submodule.Quotient.mk v)
    rw [e1, e2] at h0
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h0.symm

end

theorem halves_free_and_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → (∃ x₀ : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x₀) = ⊤) ∧ (∀ x x' : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x) = ⊤ → Submodule.span (𝓞 E) (Set.range x') = ⊤ → ∃! g : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d, ∀ b, g (x b) = x' b) ∧ ∃ adj : (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) → (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d), (∀ g g', adj (g * g') = adj g' * adj g) ∧ ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by
  intro E _ _ _ H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  have hp : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} :=
    GlobalTheory.DatumInverseCharacter.half_prod hM hMb
  have hpd : d.pd ≠ 0 := by
    intro h0
    have h3 := d.l₂.three_le
    rw [hM, h0, mul_zero] at h3
    omega
  have hJne : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h0
    have h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [hp]; exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mul_bot, Ideal.mem_bot] at h1
    exact hpd (by exact_mod_cast h1)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hJne
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := nonempty_equiv_quot (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) (Dw.p + Dw.q) Dw.rank
  exact ⟨exists_span _ _ e, fun x x' hx hx' => existsUnique_equiv _ _ e x x' hx hx',
    exists_adjoint_halves d.pd hpd d.I hp hI _ _ rfl rfl⟩

end GlobalTheory.ShortVal.Halves

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ShortVal.Coeff

theorem norm_of_pow {F : Type} [Field F] (σ : F →+* ℂ) {z : F} {N : ℕ} (hN : N ≠ 0) (hz : z ^ N = 1) :
    ‖σ z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hN

theorem absNorm_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (I : Ideal (𝓞 E)) (N : ℕ)
    (hI : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)}) :
    Nat.card (𝓞 E ⧸ I.map (H.bar : 𝓞 E →+* 𝓞 E)) = N ^ fdeg E := by
  have hc : Nat.card (𝓞 E ⧸ I.map (H.bar : 𝓞 E →+* 𝓞 E)) = Nat.card (𝓞 E ⧸ I) :=
    (Nat.card_congr (Ideal.quotientEquiv I (I.map (H.bar : 𝓞 E →+* 𝓞 E)) H.bar rfl).toEquiv).symm
  have hn := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply, ← hc] at hn
  have hnorm : (Algebra.norm ℤ (N : 𝓞 E)).natAbs = N ^ Module.finrank ℚ E := by
    rw [← map_natCast (algebraMap ℤ (𝓞 E)) N, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have hdeg : Module.finrank ℚ E = 2 * fdeg E := by
    have h2 : Module.finrank ℚ E = Module.finrank ℚ (NumberField.maximalRealSubfield E) * 2 := by
      rw [← Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield E) E,
        Algebra.IsQuadraticExtension.finrank_eq_two (NumberField.maximalRealSubfield E) E]
    unfold fdeg
    omega
  rw [hnorm, hdeg] at hn
  exact Nat.mul_self_inj.mp (hn.trans (by rw [two_mul, pow_add]))

private theorem norm_embedding_zpow_eq_one_of_pow_eq_one {F : Type} [Field F] (σ : F →+* ℂ) {z : F} {N : ℕ} (hN : N ≠ 0)
    (hz : z ^ N = 1) (k : ℤ) : ‖σ (z ^ k)‖ = 1 :=
  norm_of_pow σ hN (by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow])

private theorem norm_embedding_inv_character_eq_one {G K F : Type} [Group G] [Finite G] [Field K] [Field F]
    (ψ : G →* Kˣ) (f : K →+* F) (σ : F →+* ℂ) (k : G) : ‖σ (f (((ψ k)⁻¹ : Kˣ) : K))‖ = 1 :=
  norm_of_pow σ (Nat.card_pos (α := G)).ne' (by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, pow_card_eq_one', map_one,
      inv_one, Units.val_one, map_one])

private theorem ideal_mul_map_bar_eq_span_pd_of_isLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    {d : DeltaDat Xo c n} (hd : d.IsLev) :
    d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} ∧ d.pd ≠ 0 := by
  obtain ⟨-, hM, -, hMb, -, -⟩ := hd
  refine ⟨GlobalTheory.DatumInverseCharacter.half_prod hM hMb, fun h0 => ?_⟩
  have h3 := d.l₂.three_le
  rw [hM, h0, mul_zero] at h3
  omega

private theorem finite_quotient_I_and_map_bar_of_isLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    {d : DeltaDat Xo c n} (hd : d.IsLev) :
    Finite (𝓞 E ⧸ d.I) ∧ Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
  obtain ⟨hp, hpd⟩ := ideal_mul_map_bar_eq_span_pd_of_isLev hd
  have hpd0 : (d.pd : 𝓞 E) ≠ 0 := by exact_mod_cast hpd
  have hne : ∀ K : Ideal (𝓞 E), (d.pd : 𝓞 E) ∈ K → K ≠ ⊥ := by
    intro K hK h0
    rw [h0, Ideal.mem_bot] at hK
    exact hpd0 hK
  have hpIJ : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hp]; exact Ideal.mem_span_singleton_self _
  exact ⟨Ideal.finiteQuotientOfFreeOfNeBot _ (hne _ (Ideal.mul_le_left hpIJ)),
    Ideal.finiteQuotientOfFreeOfNeBot _ (hne _ (Ideal.mul_le_right hpIJ))⟩

private theorem finite_linearEquiv_laI_of_isLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    {d : DeltaDat Xo c n} (hd : d.IsLev) : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) := by
  haveI := (finite_quotient_I_and_map_bar_of_isLev hd).1
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨eI⟩ := GlobalTheory.ShortVal.Halves.nonempty_equiv_quot d.I (Dw.p + Dw.q) Dw.rank
  haveI : Finite (LaI Xo c d) := Finite.of_equiv _ eI.toEquiv.symm
  exact Finite.of_injective (fun g : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (g : LaI Xo c d → LaI Xo c d))
    (fun g g' h => LinearEquiv.ext (congrFun h))

private theorem card_laJ_eq_pd_pow_of_isLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    {d : DeltaDat Xo c n} (hd : d.IsLev) :
    Nat.card (LaJ Xo c d) = d.pd ^ (fdeg E * (Dw.p + Dw.q)) := by
  haveI := (finite_quotient_I_and_map_bar_of_isLev hd).2
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨eJ⟩ := GlobalTheory.ShortVal.Halves.nonempty_equiv_quot (d.I.map (H.bar : 𝓞 E →+* 𝓞 E))
    (Dw.p + Dw.q) Dw.rank
  rw [Nat.card_congr eJ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin, absNorm_conj H d.I d.pd (ideal_mul_map_bar_eq_span_pd_of_isLev hd).1, ← pow_mul]

private theorem norm_eF_ph_le_one_of_phiPin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    {d : DeltaDat Xo c n} (hd : d.IsLev)
    {ph : (Fin n → LaJ Xo c d) → c.F} {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ}
    {x₀ : Fin n → LaJ Xo c d} (hpin : d.PhiPin ph ψ x₀) (hn : Dw.p + Dw.q ≤ n)
    (σ : d.c₂.F →+* ℂ) (x : Fin n → LaJ Xo c d) : ‖σ (d.eF (ph x))‖ ≤ 1 := by
  classical
  haveI := finite_linearEquiv_laI_of_isLev hd
  obtain ⟨-, huniq, adj, -, hadj⟩ :=
    GlobalTheory.ShortVal.Halves.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨hph1, hph2, hph3, hph4, hph5, -⟩ := hpin
  by_cases h0 : ph x = 0
  · simp [h0]
  have hspan := hph2 x h0
  let y : Fin (Dw.p + Dw.q) → LaJ Xo c d := fun i => x ⟨i, lt_of_lt_of_le i.2 hn⟩
  let y₀ : Fin (Dw.p + Dw.q) → LaJ Xo c d := fun i => x₀ ⟨i, lt_of_lt_of_le i.2 hn⟩
  have hr : ∀ z : Fin n → LaJ Xo c d,
      Set.range (fun i : Fin (Dw.p + Dw.q) => z ⟨i, lt_of_lt_of_le i.2 hn⟩) =
        z '' {b | b.val < Dw.p + Dw.q} := by
    intro z
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, i.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hy : Submodule.span (𝓞 E) (Set.range y) = ⊤ := by
    rw [show Set.range y = _ from hr x]; exact hspan
  have hy₀ : Submodule.span (𝓞 E) (Set.range y₀) = ⊤ := by
    rw [show Set.range y₀ = _ from hr x₀]; exact hph5
  obtain ⟨g, hg, -⟩ := huniq y₀ y hy₀ hy
  let x₁ : Fin n → LaJ Xo c d := fun b => if b.val < Dw.p + Dw.q then x₀ b else g.symm (x b)
  have hx₁ : ph x₁ = 1 := by
    rw [hph1 x₁ x₀ fun b hb => by simp [x₁, hb]]
    exact hph4
  have hgx : (fun b => g (x₁ b)) = x := by
    funext b
    by_cases hb : b.val < Dw.p + Dw.q
    · simpa [x₁, hb, y, y₀] using hg ⟨b, hb⟩
    · simp [x₁, hb]
  have h3 := hph3 (adj g) g ((hadj (adj g) g).mpr rfl) x₁
  rw [hgx, hx₁, _root_.mul_one] at h3
  rw [h3]
  exact (norm_embedding_inv_character_eq_one ψ (d.eF : c.F →+* d.c₂.F) σ (adj g)).le

theorem norm_coeff_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → 0 < d.pd → ∀ ph ψ x₀, d.PhiPin ph ψ x₀ → Dw.p + Dw.q ≤ n → ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂) (σ : d.c₂.F →+* ℂ), ‖σ (d.w x0 q)‖ ≤ (d.pd : ℝ) ^ (fdeg E * (Dw.p + Dw.q) * n) := by
  classical
  intro E _ _ _ H Dw l Xo c n d hd hpd ph ψ x₀ hpin hn x0 q σ
  have hM : d.l₂.M = l.M * d.pd := hd.2.1
  have hph6 := hpin.2.2.2.2.2
  have hz1 : ∀ k : ℤ, ‖σ (d.eF (zetaM c ^ k))‖ = 1 := by
    intro k
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have hz : zetaM c ^ l.M = 1 := by
      unfold zetaM
      exact GlobalTheory.DatumInverseCharacter.root_pow c dvd_rfl
    rw [map_zpow₀]
    exact norm_embedding_zpow_eq_one_of_pow_eq_one σ hM0 (by rw [← map_pow, hz, map_one]) k
  have hζ : ∀ k : ℤ,
      ‖σ (((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^ k)‖ = 1 :=
    norm_embedding_zpow_eq_one_of_pow_eq_one σ hpd.ne'
      (GlobalTheory.DatumInverseCharacter.root_pow d.c₂ (by rw [hM]; exact dvd_mul_left _ _))
  haveI : Finite (LaJ Xo c d) :=
    Nat.finite_of_card_ne_zero (by rw [card_laJ_eq_pd_pow_of_isLev hd]; exact pow_ne_zero _ hpd.ne')
  haveI : Fintype (Fin n → LaJ Xo c d) := Fintype.ofFinite _
  simp only [DeltaDat.w, map_mul, norm_mul, hz1, _root_.one_mul]
  rw [hph6 q, finsum_eq_sum_of_fintype, map_sum]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun x _ => ?_).trans ?_)
  · rw [map_mul, norm_mul, hζ, _root_.mul_one]
    exact norm_eF_ph_le_one_of_phiPin hd hpin hn σ x
  · rw [Finset.card_univ, nsmul_eq_mul, _root_.mul_one, ← Nat.card_eq_fintype_card, Nat.card_fun,
      card_laJ_eq_pd_pow_of_isLev hd, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, ← pow_mul]
    push_cast
    exact le_rfl

end GlobalTheory.ShortVal.Coeff
