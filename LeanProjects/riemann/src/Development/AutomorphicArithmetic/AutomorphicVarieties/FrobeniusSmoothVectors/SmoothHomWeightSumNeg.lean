import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_lt {n : ℕ} {i j : Fin n} (h : j < i) : w n i - w n j < 0 := by
  have h' : (j : ℕ) < (i : ℕ) := h
  unfold w
  split_ifs <;> omega

private theorem sum_neg {α : Type} (f : α → ℤ) (L : List α) (h : ∀ s ∈ L, f s ≤ 0) (h' : ∃ s ∈ L, f s < 0) :
    (L.map f).sum < 0 := by
  have key : ∀ L : List α, (∀ s ∈ L, f s ≤ 0) → (L.map f).sum ≤ 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun s hs => h s (by simp [hs]))
      omega
  induction L with
  | nil => simp at h'
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hL : ∀ s ∈ L, f s ≤ 0 := fun s hs => h s (by simp [hs])
    have hsum := key L hL
    obtain ⟨s, hs, hs'⟩ := h'
    rcases List.mem_cons.1 hs with rfl | hs
    · omega
    · have := ih hL ⟨s, hs, hs'⟩
      omega

private theorem lc_hom {k G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group k] (χ : G →* k)
    (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' (χ.ker : Set G), ?_, isOpenMap_mul_left g _ h, ⟨1, χ.ker.one_mem, mul_one g⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : χ x = 1 := MonoidHom.mem_ker.1 hx
  show χ (g * x) = y
  rw [map_mul, hx1, mul_one]
  exact hg

set_option maxHeartbeats 400000 in
theorem UpperTheory.smoothHom_weight_sum_neg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] (ρ : NRep F n Q), ρ.IsBar (algebraMap (ResidueField O) Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∃ ξ : S.A →+* Q, S.FPt ξ ∧ S.u.map ξ = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ ρ hbar htri hlc
  letI : IsCO O (ResidueField O) := (co_res O).1
  letI : Algebra O Q := ((algebraMap (ResidueField O) Q).comp (algebraMap O (ResidueField O))).toAlgebra
  haveI : IsScalarTower O (ResidueField O) Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CompactSpace F.G0 := by
    have hc : IsCompact (F.del.ker : Set F.Γ) := (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
    exact isCompact_iff_compactSpace.1 hc
  have hres : ∀ c : ResidueField O, res O (ResidueField O) c = c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact (res O (ResidueField O)).commutes a
  have hinj : Function.Injective (algebraMap (ResidueField O) Q) := (algebraMap (ResidueField O) Q).injective
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := by
    intro g i j h
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rw [htri] at hm
    exact Ideal.mem_bot.1 hm
  have hΨ : IsLocallyConstant (F.Ψ : F.Γ → (ResidueField O)ˣ) := lc_hom F.Ψ hF.Ψ_open
  have hcone : Cone O (ResidueField O) ρ := by
    refine ⟨fun g i => ⟨_, (hbar.1 g i).symm, hres _⟩, fun L hsum hex => ?_,
      fun i j => Submodule.fg_span (hlc i j).range_finite, fun i j N => (hlc i j).comp _, ?_⟩
    · refine ⟨0, Ideal.zero_mem _, ?_⟩
      rw [map_zero, eq_comm]
      apply List.prod_eq_zero
      rw [List.mem_map]
      by_contra hcon
      push_neg at hcon
      have hle : ∀ t ∈ L, w n t.2.1 - w n t.2.2 ≤ 0 := by
        intro t ht
        rcases lt_trichotomy t.2.1 t.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon t ht)
        · rw [h, sub_self]
        · exact (w_lt h).le
      obtain ⟨s, hs, hne⟩ := hex
      have hlt : w n s.2.1 - w n s.2.2 < 0 := by
        rcases lt_trichotomy s.2.1 s.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon s hs)
        · exact absurd h hne
        · exact w_lt h
      have h2 : (L.map fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2).sum < 0 :=
        sum_neg (fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2) L hle ⟨s, hs, hlt⟩
      exact absurd hsum (ne_of_lt h2)
    · refine ⟨fun v i g => ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O),
        fun v i => ⟨fun N => ?_, fun g => hres _⟩, fun v i g => (hbar.2 v i g).symm⟩
      have hcont : Continuous (F.loc v) :=
        continuous_subtype_val.comp (hF.loc_cont v)
      exact (hΨ.comp_continuous hcont).comp
        (fun u => Ideal.Quotient.mk (maximalIdeal (ResidueField O) ^ N)
          ((u ^ w n i : (ResidueField O)ˣ) : ResidueField O))
  obtain ⟨ξ, β, hmap, hβ⟩ := alg hF hn S (ResidueField O) Q hinj ρ hcone
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  refine ⟨(ξ : S.A →+* Q), ⟨?_, fun c => ξ.commutes c⟩, hmap⟩
  rw [Space.x0, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hb' : b ∈ maximalIdeal S.B := by rw [hmax]; exact hb
  have h0 : β b = 0 := by
    rw [← hres (β b), res_map β b]
    exact (res_eq_zero_iff O S.B b).2 hb'
  show ξ (S.inc b) = 0
  rw [hβ b, h0, map_zero]
