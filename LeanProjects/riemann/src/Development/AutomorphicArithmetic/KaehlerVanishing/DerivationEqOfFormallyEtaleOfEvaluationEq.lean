import Mathlib

open KaehlerDifferential

namespace UpperTheory.EtaleExpansion

private abbrev D := TrivSqZeroExt ℂ ℂ

private noncomputable def tw {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) : S →+* D where
  toFun a := TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (η a)
  map_one' := by
    have h1 : η 1 = 0 := by
      have := h 1 1
      simp only [mul_one, map_one, one_mul] at this
      linear_combination -this
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
  map_zero' := by simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp <;> ring
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [h]; ring

private lemma tw_fst {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) (a : S) : (tw ev η h a).fst = ev a := by
  simp [tw]

private lemma tw_snd {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) (a : S) : (tw ev η h a).snd = η a := by
  simp [tw]

end UpperTheory.EtaleExpansion

private theorem exists_point_derivation_eq_on_image {A S : Type} [CommRing A] [CommRing S] [Algebra ℂ A] [Algebra ℂ S]
    [Algebra A S] [IsScalarTower ℂ A S] [Algebra.FormallySmooth A S] (a2 : A →ₐ[ℂ] S)
    (ev : S →ₐ[ℂ] ℂ) (hev : ∀ f : A, ev (algebraMap A S f) = ev (a2 f)) (η : S →ₗ[ℂ] ℂ)
    (hη : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) :
    ∃ η' : S →ₗ[ℂ] ℂ, (∀ a b : S, η' (a * b) = ev a * η' b + ev b * η' a) ∧
      ∀ f : A, η' (algebraMap A S f) = η (a2 f) := by
  classical
  let T : S →+* TrivSqZeroExt ℂ ℂ := UpperTheory.EtaleExpansion.tw ev η hη
  let χ : A →+* TrivSqZeroExt ℂ ℂ := T.comp a2.toRingHom
  let fs : TrivSqZeroExt ℂ ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  letI iD : Algebra A (TrivSqZeroExt ℂ ℂ) := χ.toAlgebra
  letI iC : Algebra A ℂ := (fs.comp χ).toAlgebra
  have hT1 : ∀ s, (T s).fst = ev s := fun s => UpperTheory.EtaleExpansion.tw_fst ev η hη s
  have hT2 : ∀ s, (T s).snd = η s := fun s => UpperTheory.EtaleExpansion.tw_snd ev η hη s
  let f : S →ₐ[A] ℂ :=
    { ev.toRingHom with
      commutes' := fun x => by
        change ev (algebraMap A S x) = (T (a2 x)).fst
        rw [hT1, hev] }
  let g : TrivSqZeroExt ℂ ℂ →ₐ[A] ℂ :=
    { fs with commutes' := fun x => rfl }
  have hg : Function.Surjective g := fun z => ⟨TrivSqZeroExt.inl z, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (g : TrivSqZeroExt ℂ ℂ →+* ℂ)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff]
    refine Ideal.mul_le.2 fun r hr s hs => ?_
    rw [RingHom.mem_ker] at hr hs
    change r.fst = 0 at hr
    change s.fst = 0 at hs
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hr, hs]
    · simp [hr, hs]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hnil
  have hL1 : ∀ s, (L s).fst = ev s := fun s =>
    Algebra.FormallySmooth.liftOfSurjective_apply f g hg hnil s
  have hL2 : ∀ x : A, L (algebraMap A S x) = T (a2 x) := fun x => L.commutes x
  have hη1 : η 1 = 0 := by
    have := hη 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination -this
  have hLc : ∀ c : ℂ, L (algebraMap ℂ S c) = TrivSqZeroExt.inl c := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℂ A S, hL2, a2.commutes]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hT1]
      simp
    · rw [hT2, Algebra.algebraMap_eq_smul_one, map_smul, hη1]
      simp
  refine ⟨{ toFun := fun s => (L s).snd
            map_add' := fun a b => by simp
            map_smul' := fun c s => by
              simp only [RingHom.id_apply, smul_eq_mul]
              rw [Algebra.smul_def, map_mul, hLc]
              simp }, ?_, ?_⟩
  · intro a b
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, hL1]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  · intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hL2, hT2]

theorem UpperTheory.derivation_eq_of_formallyEtale_of_evaluation_eq :
    ∀ {A S : Type} [CommRing A] [CommRing S] [Algebra ℂ A] [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S] [Algebra.FormallyEtale A S] (a2 : A →ₐ[ℂ] S) (ev : S →ₐ[ℂ] ℂ), (∀ f : A, ev (algebraMap A S f) = ev (a2 f)) → ∀ (d : ℕ) (δ δ' : S →ₗ[ℂ] (Fin d → ℂ)), (∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a) → (∀ a b : S, δ' (a * b) = ev a • δ' b + ev b • δ' a) → (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a)) → (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ' a)) → ∀ (τ τ' : Fin d → A) (M M' : Matrix (Fin d) (Fin d) ℂ), (∀ l, δ (algebraMap A S (τ l)) = Pi.single l 1) → (∀ j, δ (a2 (τ j)) = fun l => M j l) → (∀ l, δ' (algebraMap A S (τ' l)) = Pi.single l 1) → (∀ j, δ' (a2 (τ' j)) = fun l => M' j l) → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ M' = P * M * P⁻¹ := by
  intro A S _ _ _ _ _ _ _ a2 ev hev d δ δ' hδ hδ' uδ uδ' τ τ' M M' hτ hM hτ' hM'
  classical
  have F1 : ∀ (ε : S →ₗ[ℂ] (Fin d → ℂ)) (σ : Fin d → A),
      (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
        ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (ε a)) →
      (∀ l, ε (algebraMap A S (σ l)) = Pi.single l 1) →
      ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
        ∀ a, η a = ∑ l, η (algebraMap A S (σ l)) * ε a l := by
    intro ε σ uε hσ η hη a
    obtain ⟨r, hr⟩ := uε η hη
    have hsum : ε a = ∑ l, ε a l • (Pi.single l (1 : ℂ) : Fin d → ℂ) := by
      ext j
      simp [Pi.single_apply]
    simp only [hr, hσ]
    conv_lhs => rw [hsum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have Fδ := F1 δ τ uδ hτ
  have Fδ' := F1 δ' τ' uδ' hτ'
  have hproj : ∀ (ε : S →ₗ[ℂ] (Fin d → ℂ)), (∀ a b : S, ε (a * b) = ev a • ε b + ev b • ε a) →
      ∀ k : Fin d, ∀ a b : S, ((LinearMap.proj k).comp ε) (a * b) =
        ev a * ((LinearMap.proj k).comp ε) b + ev b * ((LinearMap.proj k).comp ε) a := by
    intro ε hε k a b
    simp [hε]
  let Q : Matrix (Fin d) (Fin d) ℂ := fun j l => δ (algebraMap A S (τ' j)) l
  let Q' : Matrix (Fin d) (Fin d) ℂ := fun j l => δ' (algebraMap A S (τ j)) l
  have hQQ' : Q * Q' = 1 := by
    ext j k
    have := Fδ ((LinearMap.proj k).comp δ') (hproj δ' hδ' k) (algebraMap A S (τ' j))
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, hτ'] at this
    have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) j k = (Pi.single j (1 : ℂ) : Fin d → ℂ) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [Matrix.mul_apply, h1, this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Q, Q']
    ring
  have hQM : Q * M = M' * Q := by
    ext j k
    obtain ⟨η', hη', hη'a⟩ := exists_point_derivation_eq_on_image a2 ev hev ((LinearMap.proj k).comp δ) (hproj δ hδ k)
    have e1 := Fδ η' hη' (algebraMap A S (τ' j))
    have e2 := Fδ' ((LinearMap.proj k).comp δ) (hproj δ hδ k) (a2 (τ' j))
    rw [hη'a] at e1
    simp only [hη'a, LinearMap.comp_apply, LinearMap.proj_apply, hM, hM'] at e1 e2
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ l, Q j l * M l k = ∑ l, M l k * δ (algebraMap A S (τ' j)) l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Q]
          ring
      _ = δ (a2 (τ' j)) k := e1.symm
      _ = ∑ l, M' j l * Q l k := by
          rw [e2]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Q]
          ring
  refine ⟨Q, Matrix.isUnit_det_of_right_inverse hQQ', ?_⟩
  rw [Matrix.inv_eq_right_inv hQQ', hQM, Matrix.mul_assoc, hQQ', Matrix.mul_one]
