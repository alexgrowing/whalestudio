import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.odKill_char (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] :
    (l : K) = 0 := by
  obtain ⟨q, hq⟩ := CharP.exists K
  haveI := hq
  have hx : (q : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite K q)
  have h1 := congrArg (algebraMap ℤ_[l] K) (PadicInt.unitCoeff_spec hx)
  rw [map_natCast, CharP.cast_eq_zero, map_mul, map_pow, map_natCast] at h1
  have hu : algebraMap ℤ_[l] K (PadicInt.unitCoeff hx : ℤ_[l]) ≠ 0 :=
    ((PadicInt.unitCoeff hx).isUnit.map (algebraMap ℤ_[l] K)).ne_zero
  exact pow_eq_zero_iff'.mp ((mul_eq_zero.mp h1.symm).resolve_left hu) |>.1

theorem UpperTheory.V.Pa.B2.odKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (D : Dat x.A (plOf G)), IsOd h x X D → (∀ m : D.M.X, l • m = 0) ∧ (∀ w, ∀ m : (D.Q w).X, l • m = 0) ∧ ∀ u, ∀ g ∈ L.Ju u, ∀ m : (D.Q (inU G u)).X, (D.Q (inU G u)).ρ g m = m := by
  intro l _ L G G0 h n x X _ _ D hD
  have hlA : (l : x.A) = 0 := by
    show (l : PowerSeries x.K) = 0
    rw [← map_natCast (algebraMap x.K (PowerSeries x.K)) l, odKill_char l x.K, map_zero]
  refine ⟨fun m => ?_, fun w m => ?_, fun u g hg m => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · obtain ⟨m', rfl⟩ := D.surj (inU G u) m
    refine (D.equiv (inU G u) g m').symm.trans ?_
    congr 1
    let g' : G.G₀ := G.φu u g
    have hp : h.p₀ g' = G0.φu u g := Subtype.ext (by exact h.φu u g)
    have hmem : h.p₀ g' ∈ G0.frame.Iu u := by
      rw [hp]
      exact Subgroup.mem_map_of_mem _ hg
    have h1 : x.ρ (h.p₀ g') = 1 := x.ine u _ hmem
    have h2 : x.ρ (h.p₀ g'⁻¹) = 1 := by rw [map_inv h.p₀, map_inv x.ρ, h1, inv_one]
    apply hD.e.injective
    apply Subtype.ext
    show ((hD.e (D.M.ρ (g' : G.Γ) m')) : Matrix (Fin n) (Fin n) X) = hD.e m'
    rw [hD.act g' m']
    show ((x.ρ (h.p₀ g') : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * _ *
      ((x.ρ (h.p₀ g'⁻¹) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) = _
    rw [h1, h2, Units.val_one]
    simp
