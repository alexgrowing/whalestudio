import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohDefs

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem coc_inj (n : ℕ) {x y : cocycles A n}
    (h : cochainOf A (cocycleι A n x) = cochainOf A (cocycleι A n y)) : x = y :=
  cocycleι_injective (cochainOf_injective h)

theorem exists_coc (n : ℕ) (c : (Fin n → G) → A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = c := by
  refine ⟨(cochainsComplex A).cyclesMk (mkCochain A c hc) (n + 1) (by simp) ?_, ?_⟩
  · apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans hd
  · exact congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

theorem pi_succ_eq_zero_iff (n : ℕ) (x : cocycles A (n + 1)) :
    cohomologyπ A (n + 1) x = 0 ↔ ∃ w : (Fin n → G) → A, IsLocallyConstant w ∧
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleι A (n + 1) x) := by
  change ((cochainsComplex A).homologyπ (n + 1)).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w, isLocallyConstant_cochainOf w, ?_⟩
    rw [← cochainOf_d]
    exact congrArg (cochainOf A) hw
  · rintro ⟨w, hw, h⟩
    refine ⟨mkCochain A w hw, ?_⟩
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans h

theorem pi_zero_eq_zero_iff (x : cocycles A 0) :
    cohomologyπ A 0 x = 0 ↔ cochainOf A (cocycleι A 0 x) = 0 := by
  change ((cochainsComplex A).homologyπ 0).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_zero]
  have h0 : (cochainsComplex A).d 0 0 = 0 := (cochainsComplex A).shape 0 0 (by simp)
  rw [h0]
  constructor
  · rintro ⟨w, hw⟩
    exact (congrArg (cochainOf A) hw).symm
  · intro h
    refine ⟨0, ?_⟩
    apply cochainOf_injective (A := A)
    exact h.symm

theorem core_hom {Z : Type} [AddCommGroup Z] (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z) :
    ∃ f : Z →+ cohomology A n, Function.Surjective f ∧
      ∀ z x, cochainOf A (cocycleι A n x) = φ z → f z = cohomologyπ A n x := by
  choose ψ hψ using hex
  have hadd : ∀ z z', ψ (z + z') = ψ z + ψ z' := fun z z' => coc_inj A n (by
    rw [map_add, cochainOf_add, hψ, hψ, hψ, map_add])
  let f : Z →+ cohomology A n := AddMonoidHom.mk' (fun z => cohomologyπ A n (ψ z))
    (fun z z' => by rw [hadd, map_add])
  have hf : ∀ z x, cochainOf A (cocycleι A n x) = φ z → f z = cohomologyπ A n x := fun z x h => by
    have : ψ z = x := coc_inj A n ((hψ z).trans h.symm)
    change cohomologyπ A n (ψ z) = _
    rw [this]
  refine ⟨f, fun y => ?_, hf⟩
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A n y
  obtain ⟨z, hz⟩ := hsurj x
  exact ⟨z, hf z x hz⟩

theorem core_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (B : Submodule R Z)
    (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z)
    (hB : ∀ z x, cochainOf A (cocycleι A n x) = φ z → (cohomologyπ A n x = 0 ↔ z ∈ B)) :
    ∃ e : (Z ⧸ B) ≃+ cohomology A n,
      ∀ z x, cochainOf A (cocycleι A n x) = φ z →
        e (Submodule.Quotient.mk z) = cohomologyπ A n x := by
  obtain ⟨f, hs, hf⟩ := core_hom A n φ hex hsurj
  have hk : ∀ z, f z = 0 ↔ z ∈ B := fun z => by
    obtain ⟨x, hx⟩ := hex z
    rw [hf z x hx, hB z x hx]
  let g : (Z ⧸ B) →+ cohomology A n :=
    QuotientAddGroup.lift B.toAddSubgroup f (fun z hz => (hk z).2 hz)
  have hg : ∀ z, g (Submodule.Quotient.mk z) = f z := fun z => rfl
  refine ⟨AddEquiv.ofBijective g ⟨?_, ?_⟩, fun z x h => (hg z).trans (hf z x h)⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective B q
    rw [hg, hk] at hq
    exact (Submodule.Quotient.mk_eq_zero B).2 hq
  · intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨_, hg z⟩

end Core

theorem neg_one_pow_smul' {S V : Type} [Ring S] [AddCommGroup V] [Module S V] (j : ℕ) (v : V) :
    (-1 : S) ^ j • v = (-1 : ℤ) ^ j • v := by
  rw [← Int.cast_smul_eq_zsmul S]
  simp

section Cmp

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  (rho : Representation R G M) (A : Rep.{0} k G) (e : M ≃+ A.V)
  (he : ∀ g m, e (rho g m) = A.ρ g (e m))

theorem dn_app (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

include he in
theorem d_comp (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  funext s
  rw [inhomogeneousCochains.d_hom_apply, dn_app, map_add, map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]

theorem dn_zero (f : (Fin 0 → G) → M) (s : Fin 1 → G) :
    dn rho 0 f s = rho (s 0) (f default) - f default := by
  have h : ∀ t, f t = f default := fun t => congrArg f (Subsingleton.elim _ _)
  rw [dn_app]
  simp [h, sub_eq_add_neg]

theorem dn_one (f : G → M) (s : Fin 2 → G) :
    dn rho 1 (fun t => f (t 0)) s = rho (s 0) (f (s 1)) - f (s 0 * s 1) + f (s 0) := by
  rw [dn_app]
  simp [Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

theorem dn_two (f : G × G → M) (s : Fin 3 → G) :
    dn rho 2 (fun t => f (t 0, t 1)) s =
      rho (s 0) (f (s 1, s 2)) - f (s 0 * s 1, s 2) + f (s 0, s 1 * s 2) - f (s 0, s 1) := by
  rw [dn_app]
  have h3 : (-1 : R) ^ 3 = -1 := by norm_num
  simp [h3, Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

end Cmp

end CompanionTheory.LocalTateOrthogonality.Gcoh
