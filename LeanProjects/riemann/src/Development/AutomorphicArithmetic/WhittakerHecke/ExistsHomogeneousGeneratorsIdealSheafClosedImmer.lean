import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.HomogeneousExtension

private lemma exists_pow_mul_mem {Z : Scheme.{0}} (I : Z.IdealSheafData) (U : Z.affineOpens)
    (t g : Γ(Z, U))
    (hg : Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op g ∈ I.ideal (Z.affineBasicOpen t)) :
    ∃ e : ℕ, t ^ e * g ∈ I.ideal U := by
  have inst := U.2.isLocalization_basicOpen t
  rw [← I.map_ideal_basicOpen U t] at hg
  have h1 : (Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op).hom = algebraMap _ _ := rfl
  rw [h1] at hg
  change algebraMap _ _ g ∈ _ at hg
  obtain ⟨_, ⟨e, rfl⟩, he⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers t) _ _ _).1 hg
  exact ⟨e, he⟩

variable {R : Type} [CommRing R] {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace R N)

private noncomputable def phi (a : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) R →+* Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
  (i.appLE _ _ le_rfl).hom.comp (chartHom a)

private lemma phi_X_self (a : Fin (N + 1)) : phi i a (X a) = 1 := by
  simp [phi, chartHom_X_self]

private lemma isAffineOpen_U [IsClosedImmersion i] (a : Fin (N + 1)) :
    IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) := by
  have h : IsAffineOpen (Proj.basicOpen (grading R N) (X a)) :=
    Proj.isAffineOpen_basicOpen (grading R N) (X a) (X_mem a) one_pos
  exact h.preimage i

private lemma exists_homog_chartHom (a : Fin (N + 1))
    (s : Γ(PSpace R N, Proj.basicOpen (grading R N) (X a))) :
    ∃ (d : ℕ) (G : MvPolynomial (Fin (N + 1)) R), G ∈ grading R N d ∧ chartHom a G = s := by
  let e := Proj.basicOpenIsoAway (grading R N) (X a) (X_mem a) one_pos
  obtain ⟨d, G, hG, hx⟩ := HomogeneousLocalization.Away.mk_surjective (grading R N) (X_mem a) (e.inv s)
  have hG' : G ∈ grading R N d := by simpa using hG
  refine ⟨d, G, hG', ?_⟩
  rw [chartHom_of_mem a hG']
  have h1 : (Proj.awayToSection (grading R N) (X a)).hom (e.inv s) = s := by
    have := e.inv_hom_id_apply s
    exact this
  rw [← h1, ← hx]

private lemma exists_homog_phi [IsClosedImmersion i] (a : Fin (N + 1))
    (h : Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))) :
    ∃ (d : ℕ) (G : MvPolynomial (Fin (N + 1)) R), G ∈ grading R N d ∧ phi i a G = h := by
  obtain ⟨s, hs⟩ := i.app_surjective _
    (Proj.isAffineOpen_basicOpen (grading R N) (X a) (X_mem a) one_pos) h
  obtain ⟨d, G, hG, hGs⟩ := exists_homog_chartHom a s
  refine ⟨d, G, hG, ?_⟩
  simp only [phi, RingHom.comp_apply, hGs, ← Scheme.Hom.app_eq_appLE]
  exact hs

private lemma phi_surjective [IsClosedImmersion i] (a : Fin (N + 1)) :
    Function.Surjective (phi i a) := fun h => by
  obtain ⟨_, G, _, hG⟩ := exists_homog_phi i a h
  exact ⟨G, hG⟩

private lemma basicOpen_phi_X (a b : Fin (N + 1)) :
    Z.basicOpen (phi i b (X a)) = i ⁻¹ᵁ Proj.basicOpen (grading R N) (X b) ⊓
      i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := by
  simp only [phi, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.basicOpen_res,
    ← Scheme.preimage_basicOpen]
  have e := basicOpen_chartHom_X (A := R) (n := N) b a
  erw [e]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, Scheme.Hom.mem_preimage,
    SetLike.mem_coe, TopologicalSpace.Opens.mem_inf]
  tauto

private lemma phi_res (a b : Fin (N + 1)) {d : ℕ} {G : MvPolynomial (Fin (N + 1)) R}
    (hG : G ∈ grading R N d) (ha : Z.basicOpen (phi i b (X a)) ≤
      i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :
    Z.presheaf.map (homOfLE (Z.basicOpen_le (phi i b (X a)))).op (phi i b G) =
      Z.presheaf.map (homOfLE ha).op (phi i a G) *
        Z.presheaf.map (homOfLE (Z.basicOpen_le (phi i b (X a)))).op (phi i b (X a)) ^ d := by
  set V := Z.basicOpen (phi i b (X a)) with hV
  have hWV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [hV, basicOpen_phi_X, Proj.basicOpen_mul]
    intro x hx
    simpa using hx
  have nat : ∀ (k : Fin (N + 1)) (s : Γ(PSpace R N, Proj.basicOpen (grading R N) (X k)))
      (hk : V ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X k))
      (hW : Proj.basicOpen (grading R N) (X b * X a) ≤ Proj.basicOpen (grading R N) (X k)),
      Z.presheaf.map (homOfLE hk).op ((i.appLE _ _ le_rfl).hom s) =
        (i.appLE _ V hWV).hom ((PSpace R N).presheaf.map (homOfLE hW).op s) := by
    intro k s hk hW
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have ci := chart_identity (A := R) (n := N) a b (t := d) (a := G) (by simpa using hG)
  rw [← chartHom_of_mem a hG] at ci
  have e1 := nat b (chartHom b G) (Z.basicOpen_le _) (basicOpen_mul_le_left a b)
  have e2 := nat a (chartHom a G) ha (basicOpen_mul_le_right a b)
  have e3 := nat b (chartHom b (X a)) (Z.basicOpen_le _) (basicOpen_mul_le_left a b)
  change Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom b G)) =
    Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom a G)) *
      Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom b (X a))) ^ d
  rw [e1, e2, e3, ← map_pow, ← map_mul]
  exact congrArg (i.appLE _ V hWV).hom ci.symm

private lemma exists_pow_mul_phi_mem [IsClosedImmersion i] (I : Z.IdealSheafData)
    (a b : Fin (N + 1)) {d : ℕ} {G : MvPolynomial (Fin (N + 1)) R} (hG : G ∈ grading R N d)
    (hI : phi i a G ∈ I.ideal ⟨_, isAffineOpen_U i a⟩) :
    ∃ e : ℕ, phi i b (X a) ^ e * phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
  have ha : Z.basicOpen (phi i b (X a)) ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := by
    rw [basicOpen_phi_X]
    exact inf_le_right
  refine exists_pow_mul_mem I ⟨_, isAffineOpen_U i b⟩ (phi i b (X a)) (phi i b G) ?_
  have hle : Z.affineBasicOpen (U := ⟨_, isAffineOpen_U i b⟩) (phi i b (X a)) ≤ ⟨_, isAffineOpen_U i a⟩ := ha
  have hmem := I.ideal_le_comap_ideal hle hI
  rw [Ideal.mem_comap] at hmem
  rw [phi_res i a b hG ha, mul_comm]
  exact Ideal.mul_mem_left _ _ hmem

private lemma exists_extension [IsClosedImmersion i] (I : Z.IdealSheafData) (a : Fin (N + 1))
    (h : Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))
    (hI : h ∈ I.ideal ⟨_, isAffineOpen_U i a⟩) :
    ∃ d₀ : ℕ, ∀ n, d₀ ≤ n → ∃ G : MvPolynomial (Fin (N + 1)) R, G.IsHomogeneous n ∧
      phi i a G = h ∧ ∀ b, phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
  obtain ⟨d, G, hG, rfl⟩ := exists_homog_phi i a h
  have key : ∀ b, ∃ e : ℕ, phi i b (X a) ^ e * phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ :=
    fun b => exists_pow_mul_phi_mem i I a b hG hI
  choose e he using key
  refine ⟨d + Finset.univ.sup e, fun n hn => ⟨X a ^ (n - d) * G, ?_, ?_, ?_⟩⟩
  · have hGd : G.IsHomogeneous d := (mem_homogeneousSubmodule d G).mp hG
    have hmul := (isHomogeneous_X_pow a (n - d) : (X a ^ (n - d) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (n - d)).mul hGd
    rwa [Nat.sub_add_cancel (by omega)] at hmul
  · simp [phi_X_self]
  · intro b
    have hle : e b ≤ n - d := by
      have : e b ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ b)
      omega
    rw [map_mul, map_pow, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (he b)

end UpperTheory.HomogeneousExtension

open UpperTheory.HomogeneousExtension in
theorem UpperTheory.exists_homogeneous_generators_idealSheaf_closedImmersion :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace R N) [IsClosedImmersion i] (I : Z.IdealSheafData),
      ∃ (n M : ℕ) (F : Fin (M + 1) → MvPolynomial (Fin (N + 1)) R), (∀ m, (F m).IsHomogeneous n) ∧
        ∀ (a : Fin (N + 1)) (hU : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))),
          Ideal.span (Set.range fun m => i.appLE _ _ le_rfl (chartHom a (F m))) = I.ideal ⟨_, hU⟩ := by
  intro R _ _ N Z i _ I
  have hfg : ∀ a : Fin (N + 1), (I.ideal ⟨_, isAffineOpen_U i a⟩).FG := by
    intro a
    haveI : IsNoetherianRing Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
      isNoetherianRing_of_surjective _ _ (phi i a) (phi_surjective i a)
    exact IsNoetherian.noetherian _
  choose gens hgens using hfg
  have hext : ∀ p : (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))),
      ∃ d₀ : ℕ, ∀ n, d₀ ≤ n → ∃ G : MvPolynomial (Fin (N + 1)) R, G.IsHomogeneous n ∧
        phi i p.1 G = p.2.1 ∧ ∀ b, phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
    rintro ⟨a, h, hh⟩
    exact exists_extension i I a h (hgens a ▸ Ideal.subset_span hh)
  choose d₀ hd₀ using hext
  let n := Finset.univ.sup d₀
  have hG := fun p => hd₀ p n (Finset.le_sup (Finset.mem_univ p))
  choose G hGh hGa hGb using hG
  let M := Fintype.card (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))))
  let e := Fintype.equivFin (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))))
  let F : Fin (M + 1) → MvPolynomial (Fin (N + 1)) R := fun m =>
    if hm : (m : ℕ) < M then G (e.symm ⟨m, hm⟩) else 0
  refine ⟨n, M, F, ?_, ?_⟩
  · intro m
    by_cases hm : (m : ℕ) < M
    · simp only [F, dif_pos hm]
      exact hGh _
    · simp only [F, dif_neg hm]
      exact MvPolynomial.isHomogeneous_zero _ _ _
  · intro a hU
    change Ideal.span (Set.range fun m => phi i a (F m)) = I.ideal ⟨_, isAffineOpen_U i a⟩
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨m, rfl⟩
      by_cases hm : (m : ℕ) < M
      · simp only [F, dif_pos hm]
        exact hGb _ a
      · simp only [F, dif_neg hm, map_zero]
        exact Ideal.zero_mem _
    · rw [← hgens a, Ideal.span_le]
      intro h hh
      let p : (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))) :=
        ⟨a, h, hh⟩
      refine Ideal.subset_span ⟨⟨e p, by omega⟩, ?_⟩
      have hlt : ((⟨e p, by omega⟩ : Fin (M + 1)) : ℕ) < M := (e p).2
      simp only [F, dif_pos hlt]
      simp only [Fin.eta, Equiv.symm_apply_apply]
      exact hGa p
