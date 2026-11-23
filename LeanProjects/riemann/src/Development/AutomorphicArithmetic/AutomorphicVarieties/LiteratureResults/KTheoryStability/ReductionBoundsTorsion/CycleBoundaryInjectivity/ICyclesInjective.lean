import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.Chains

noncomputable section

open CategoryTheory groupHomology UpperTheory.V.KL Finsupp

namespace PositivityTheory.KB.NaturalTheta

variable (G : Type) [Group G]

def Dz (n : ℕ) : ((Fin (n + 1) → G) →₀ ℤ) →ₗ[ℤ] ((Fin n → G) →₀ ℤ) :=
  (inhomogeneousChains.d (Rep.trivial ℤ G ℤ) n).hom

theorem Dz_eq_bdZ (n : ℕ) : Dz G n = bdZ G n := by
  apply Finsupp.lhom_ext
  intro g a
  unfold Dz bdZ
  rw [inhomogeneousChains.d_single, Finsupp.linearCombination_single, smul_add, Finset.smul_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_comm, Finsupp.smul_single_one]

theorem d_hom (n : ℕ) : ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (n + 1) n).hom = Dz G n := by
  rw [inhomogeneousChains.d_def]; rfl

theorem Dz_Dz (n : ℕ) : Dz G n ∘ₗ Dz G (n + 1) = 0 := by
  have := congrArg ModuleCat.Hom.hom (inhomogeneousChains.d_comp_d (Rep.trivial ℤ G ℤ) n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at this
  exact this

variable (k : ℕ)

theorem hnext : (ComplexShape.down ℕ).next (k + 1) = k := by simp

theorem hlift : (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype :
      ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ (inhomogeneousChains (Rep.trivial ℤ G ℤ)).X (k + 1)) ≫
      (inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (k + 1) k = 0 := by
  rw [inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.mem_ker.mp x.2

def cz : LinearMap.ker (Dz G k) →ₗ[ℤ] cycles (Rep.trivial ℤ G ℤ) (k + 1) :=
  ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).liftCycles
    (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype : ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ _)
    k (hnext k) (hlift G k)).hom

theorem i_cz (x : LinearMap.ker (Dz G k)) :
    (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom (cz G k x) = x.1 := by
  have h := HomologicalComplex.liftCycles_i (inhomogeneousChains (Rep.trivial ℤ G ℤ))
    (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype :
      ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ (inhomogeneousChains (Rep.trivial ℤ G ℤ)).X (k + 1))
    k (hnext k) (hlift G k)
  have h2 := congrArg (fun φ => φ.hom x) h
  exact h2

theorem iCycles_injective (n : ℕ) : Function.Injective (iCycles (Rep.trivial ℤ G ℤ) n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

def pz : LinearMap.ker (Dz G k) →ₗ[ℤ] grpH G (k + 1) :=
  (π (Rep.trivial ℤ G ℤ) (k + 1)).hom ∘ₗ cz G k

set_option backward.isDefEq.respectTransparency false in
theorem pz_surjective : Function.Surjective (pz G k) := by
  intro y
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (π (Rep.trivial ℤ G ℤ) (k + 1))).1 inferInstance y
  have hc : (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom c ∈ LinearMap.ker (Dz G k) := by
    rw [LinearMap.mem_ker, ← d_hom]
    have := congrArg (fun φ => φ.hom c)
      ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).iCycles_d (k + 1) k)
    simpa [ModuleCat.hom_comp] using this
  refine ⟨⟨_, hc⟩, ?_⟩
  simp only [pz, LinearMap.coe_comp, Function.comp_apply]
  congr 1
  exact iCycles_injective G (k + 1) (i_cz G k _)

theorem pz_eq_zero_iff (x : LinearMap.ker (Dz G k)) :
    pz G k x = 0 ↔ x.1 ∈ LinearMap.range (Dz G (k + 1)) := by
  set K := inhomogeneousChains (Rep.trivial ℤ G ℤ) with hK
  have hex := ShortComplex.exact_of_g_is_cokernel
    (S := ShortComplex.mk (K.toCycles (k + 2) (k + 1)) (K.homologyπ (k + 1))
      (K.toCycles_comp_homologyπ (k + 2) (k + 1)))
    (K.homologyIsCokernel (k + 2) (k + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hti : ∀ w, (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom ((K.toCycles (k + 2) (k + 1)).hom w)
      = Dz G (k + 1) w := by
    intro w
    have h0 := congrArg (fun φ => φ.hom w) (K.toCycles_i (k + 2) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
    rw [← d_hom]
    exact h0
  constructor
  · intro h0
    obtain ⟨w, hw⟩ := hex (cz G k x) h0
    refine ⟨w, ?_⟩
    rw [← hti, ← i_cz G k x]
    exact congrArg _ hw
  · rintro ⟨w, hw⟩
    have hc : (K.toCycles (k + 2) (k + 1)).hom w = cz G k x := by
      apply iCycles_injective
      rw [hti, i_cz, hw]
    simp only [pz, LinearMap.comp_apply, ← hc]
    have h1 := congrArg (fun φ => φ.hom w) (K.toCycles_comp_homologyπ (k + 2) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    exact h1

variable {G} {H : Type} [Group H] (f : G →* H)

theorem chainsMap_hom (n : ℕ) :
    ((chainsMap f (trivHom f)).f n).hom = Finsupp.lmapDomain ℤ ℤ (fun (g : Fin n → G) i => f (g i)) := by
  rw [chainsMap_f_hom]
  apply Finsupp.lhom_ext
  intro g a
  simp [trivHom]
  rfl

theorem map_mem_ker (x : (Fin (k + 1) → G) →₀ ℤ) (hx : x ∈ LinearMap.ker (Dz G k)) :
    Finsupp.lmapDomain ℤ ℤ (fun (g : Fin (k + 1) → G) i => f (g i)) x ∈ LinearMap.ker (Dz H k) := by
  rw [LinearMap.mem_ker] at hx ⊢
  have := congrArg (fun φ => φ.hom x) ((chainsMap f (trivHom f)).comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [d_hom, d_hom, chainsMap_hom, chainsMap_hom] at this
  rw [this, hx, map_zero]

theorem pz_natural (x : LinearMap.ker (Dz G k)) :
    pz H k ⟨_, map_mem_ker k f x.1 x.2⟩ = (grpHMap f (k + 1)).hom (pz G k x) := by
  simp only [pz, LinearMap.coe_comp, Function.comp_apply, grpHMap]
  have := congrArg (fun φ => φ.hom (cz G k x)) (π_map f (trivHom f) (k + 1))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  congr 1
  apply iCycles_injective H (k + 1)
  rw [i_cz]
  have := congrArg (fun φ => φ.hom (cz G k x))
    (HomologicalComplex.cyclesMap_i (chainsMap f (trivHom f)) (k + 1))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, i_cz, chainsMap_hom]

end PositivityTheory.KB.NaturalTheta
