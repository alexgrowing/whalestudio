import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LocRegDesc

theorem exists_unit_mul_eq_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    (ρ : A →+* R) (hρ : ρ.Flat) (s b : A) (r : R) (hs : ρ s = ρ b * r) :
    ∃ g a : A, IsUnit (ρ g) ∧ g * s = b * a := by
  letI := ρ.toAlgebra
  haveI : Module.Flat A R := hρ
  have hrel : ∑ i, (![s, -b] : Fin 2 → A) i • (![1, r] : Fin 2 → R) i = 0 := by
    simp [Fin.sum_univ_two, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hs]
  have ht : Module.IsTrivialRelation (![s, -b] : Fin 2 → A) (![1, r] : Fin 2 → R) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, a, y, hx, hf⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ρ (a 0 j)) := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have := hx 0
      simp only [Matrix.cons_val_zero] at this
      rw [this]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hne j))
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨a 0 j, a 1 j, hj, ?_⟩
  have := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linear_combination this

end LocRegDesc

namespace LocRegDesc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill_on_basicOpen (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0)
    (f : Γ(X, U.1)) (hf : X.basicOpen f ≤ W) :
    ∃ g, IsUnit (ρ g) ∧
      (X.presheaf.map (homOfLE hf).op).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0 := by
  haveI hloc := U.2.isLocalization_basicOpen f
  set δV := (X.presheaf.map (homOfLE hf).op).hom δ with hδV
  set hV := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom h with hhV
  have key : X.basicOpen hV = X.basicOpen f ⊓ X.basicOpen h := Scheme.basicOpen_res _ _ _
  have hB : X.basicOpen hV ≤ X.basicOpen h := key ▸ inf_le_right
  have hzero : (X.presheaf.map (homOfLE (X.basicOpen_le hV)).op).hom δV = 0 := by
    rw [hδV, res_res, ← res_res hh hB, hδ, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U.2.basicOpen f).isCompact δV hV hzero
  obtain ⟨⟨e, m⟩, hem⟩ := IsLocalization.surj (Submonoid.powers f) δV
  simp only at hem
  have h0 : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (h ^ n * e) = 0 := by
    rw [map_mul, ← hem, map_pow]
    change hV ^ n * (δV * _) = 0
    rw [← _root_.mul_assoc, hn, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
  simp only at hj
  have hc : ρ (f ^ j * e) = 0 := by
    have : ρ h ^ n * ρ (f ^ j * e) = 0 := by
      rw [← map_pow, ← map_mul, show h ^ n * (f ^ j * e) = f ^ j * (h ^ n * e) by ring, hj, map_zero]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hρh)
  obtain ⟨g, a, hu, hg⟩ := exists_unit_mul_eq_of_flat ρ hρ (f ^ j * e) 0 0 (by simp [hc])
  refine ⟨g, hu, ?_⟩
  rw [map_mul, res_res]
  change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * δV = 0
  have u1 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (m : Γ(X, U.1))) :=
    IsLocalization.map_units _ m
  have u2 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (f ^ j)) :=
    IsLocalization.map_units _ (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)
  rw [← u1.mul_left_eq_zero, ← u2.mul_left_eq_zero, _root_.mul_assoc _ δV, hem, ← map_mul, ← map_mul,
    show g * e * f ^ j = g * (f ^ j * e) by ring, hg, zero_mul, map_zero]

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0) :
    ∃ g, IsUnit (ρ g) ∧ (X.presheaf.map (homOfLE hWU).op).hom g * δ = 0 := by
  let p : Set X → Prop := fun t => ∃ g, IsUnit (ρ g) ∧ ∀ y (hy : y ∈ W), y ∈ t →
    (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0
  have hp : p (W : Set X) := by
    refine hW.induction_on ?_ ?_ ?_ ?_
    · exact ⟨1, by simp, fun y _ hy => hy.elim⟩
    · rintro s t hst ⟨g, hg, H⟩
      exact ⟨g, hg, fun y hy hs => H y hy (hst hs)⟩
    · rintro s t ⟨g₁, hg₁, H₁⟩ ⟨g₂, hg₂, H₂⟩
      refine ⟨g₁ * g₂, by rw [map_mul]; exact hg₁.mul hg₂, fun y hy hyst => ?_⟩
      rw [map_mul (X.presheaf.map (homOfLE hWU).op).hom g₁ g₂]
      rcases hyst with hs | ht
      · rw [mul_right_comm, map_mul (X.presheaf.germ W y hy).hom, H₁ y hy hs, zero_mul]
      · rw [_root_.mul_assoc, map_mul (X.presheaf.germ W y hy).hom, H₂ y hy ht, mul_zero]
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      obtain ⟨g, hg, H⟩ := exists_unit_kill_on_basicOpen X U W hWU R ρ hρ h hh hρh δ hδ f hf
      refine ⟨X.basicOpen f, mem_nhdsWithin_of_mem_nhds ((X.basicOpen f).isOpen.mem_nhds hxf),
        g, hg, fun y hy hyf => ?_⟩
      rw [← X.presheaf.germ_res_apply (homOfLE hf) y hyf, H, map_zero]
  obtain ⟨g, hg, H⟩ := hp
  refine ⟨g, hg, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf W _ 0 fun y hy => ?_
  exact (H y hy hy).trans (map_zero (X.presheaf.germ W y hy).hom).symm

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_one (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (θ : Γ(X, W))
    (H : ∀ (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) *
        (X.presheaf.map (homOfLE hh).op).hom θ → ρ h ^ N ∣ ρ s) :
    ∃ g, IsUnit (ρ g) ∧ ∃ s : Γ(X, U.1),
      (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ := by
  haveI hloc := U.2.isLocalization_basicOpen h
  obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hsm⟩ :=
    IsLocalization.surj (Submonoid.powers h) ((X.presheaf.map (homOfLE hh).op).hom θ)
  simp only at hsm
  obtain ⟨r, hr⟩ := H s N (by
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) s =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) * _
    rw [← hsm, mul_comm])
  obtain ⟨g₁, a, hu₁, hga⟩ := exists_unit_mul_eq_of_flat ρ hρ s (h ^ N) r (by rw [map_pow, hr])
  set δ := (X.presheaf.map (homOfLE hWU).op).hom a - (X.presheaf.map (homOfLE hWU).op).hom g₁ * θ
    with hδdef
  have hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0 := by
    have u : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N)) :=
      IsLocalization.map_units _ (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
    rw [← u.mul_left_eq_zero, hδdef, map_sub, map_mul, res_res, res_res]
    change (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) a - algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) g₁ *
      (X.presheaf.map (homOfLE hh).op).hom θ) * algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) = 0
    rw [sub_mul, _root_.mul_assoc, hsm, ← map_mul, ← map_mul, hga, mul_comm a, sub_self]
  obtain ⟨g₂, hu₂, hk⟩ := exists_unit_kill X U W hWU hW R ρ hρ h hh hρh δ hδ
  refine ⟨g₂ * g₁, by rw [map_mul]; exact hu₂.mul hu₁, g₂ * a, ?_⟩
  rw [map_mul, map_mul]
  rw [hδdef] at hk
  linear_combination hk

end LocRegDesc

theorem LocRegDesc.descent : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  intro X U W hWU hW R _ _ _ ρ hρ mm hmm h hh hρh J _ θ H
  choose g hg s hs using fun i => LocRegDesc.exists_unit_one X U W hWU hW R ρ hρ h hh hρh (θ i) (H i)
  haveI := Fintype.ofFinite J
  classical
  refine ⟨∏ i, g i, ?_, fun i => ⟨s i * ∏ j ∈ Finset.univ.erase i, g j, ?_⟩⟩
  · rw [← hmm, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hg i)
  · rw [map_mul, hs i, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), map_mul]
    ring

end GlobalTheory
