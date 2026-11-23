import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ker_open {l : ℕ} [Fact l.Prime] {Γ S : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CommRing S] (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (φ : ℤ_[l] →+* S) (j : ℕ) (hφ : φ ((l : ℤ_[l]) ^ j) = 0) :
    IsOpen ((pushCh φ ε).ker : Set Γ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ :=
    ((Units.continuous_val.comp hε).sub continuous_const).norm
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(j : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have ho : IsOpen {g | ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < (l : ℝ) ^ (-(j : ℤ))} := isOpen_lt hc continuous_const
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using hp)) fun g hg => ?_
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).1 (le_of_lt hg)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : φ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := congrArg φ hc
    rw [map_mul, hφ, mul_zero, map_sub, map_one] at this
    exact (sub_eq_zero.1 this.symm)
  exact Units.ext h2

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (h : H) (a : A) :
    (D.comap φ).lam i (MonoidAlgebra.single h a) = D.lam i (MonoidAlgebra.single (φ h) a) := by
  have : (D.comap φ).chi (MonoidAlgebra.single h a) = D.chi (MonoidAlgebra.single (φ h) a) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  simp only [GDet.lam, this]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (h : G) (a : A) :
    f (D.lam i (MonoidAlgebra.single h a)) = (D.map f).lam i (MonoidAlgebra.single h (f a)) := by
  rw [← ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single h a)).2 i, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.Pa.Core.patched_lam_conj_twist_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (i : ℕ) (g g' : Ph0 Λ), (g' : Λ.Ph) = Λ.ct * g * Λ.ct⁻¹ → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, (W.t.D.lam i (MonoidAlgebra.single g'⁻¹ ((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) - W.t.D.lam i (MonoidAlgebra.single g 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m _ i g g' hg j
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := hO.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlR : (l : W.R) ∈ maximalIdeal W.R := by
    have := map_nonunit (algebraMap O W.R) _ hlO
    rwa [map_natCast] at this
  let q := Ideal.Quotient.mk (maximalIdeal W.R ^ j)
  let φ : ℤ_[l] →+* W.R ⧸ maximalIdeal W.R ^ j := q.comp ((algebraMap O W.R).comp (algebraMap ℤ_[l] O))
  have hφ : φ ((l : ℤ_[l]) ^ j) = 0 := by
    rw [map_pow, map_natCast, ← map_natCast q, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlR j)
  let V : OpenNormalSubgroup G0.Γ :=
    { toSubgroup := (pushCh φ G0.ε).ker
      isOpen' := ker_open G0.ε G0.ε_cont φ j hφ
      isNormal' := MonoidHom.normal_ker _ }
  refine (Λ.p_lim V).mono fun N hN => ?_
  have h1 : pushCh φ G0.ε ((T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹) = 1 := hN g
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 : Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
      Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j) (Λ.G.frame.eps O W.R (πo0 Λ g)) := by
    have h3 := congrArg Units.val h1
    change φ (G0.ε _ : ℤ_[l]ˣ) = φ (G0.ε _ : ℤ_[l]ˣ) at h3
    rw [(T.h N).ε, Λ.h.ε] at h3
    exact Units.ext h3
  refine ⟨W.t.D.lam i (MonoidAlgebra.single g'⁻¹
      (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) -
      W.t.D.lam i (MonoidAlgebra.single g 1), ?_, Or.inl ?_⟩
  · rw [sub_sub_sub_cancel_right, ← Ideal.Quotient.eq]
    change q _ = q _
    rw [lam_map, lam_map]
    have h4 := congrArg (fun z : (W.R ⧸ maximalIdeal W.R ^ j)ˣ => ((z ^ (1 - (n : ℤ)) : _ˣ) : W.R ⧸ maximalIdeal W.R ^ j)) h2
    simp only [← map_zpow (Units.map (q : W.R →* W.R ⧸ maximalIdeal W.R ^ j))] at h4
    exact congrArg (fun z => (W.t.D.map q).lam i (MonoidAlgebra.single g'⁻¹ z)) h4.symm
  · rw [map_sub, sub_eq_zero]
    change (m.ρ N).toRingHom _ = (m.ρ N).toRingHom _
    rw [lam_map, lam_map, (m.ρ_maps N).1, lam_comap, lam_comap, map_one, ← (A.A N).p.P i (πN0 Λ N g)]
    have e1 : πN0 Λ N g' = (T.GN N).frame.conj (πN0 Λ N g) := Subtype.ext (by
      change Λ.π N g' = (T.GN N).c * Λ.π N g * (T.GN N).c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_N])
    have e2 : Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R) ((T.GN N).frame.eps O W.R (πN0 Λ N g)) =
        (T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) := Units.ext ((m.ρ N).commutes _)
    have e3 : (m.ρ N).toRingHom (((T.GN N).frame.eps O W.R (πN0 Λ N g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R) =
        (((T.GN N).frame.eps O (A.A N).R (πN0 Λ N g) ^ (1 - (n : ℤ)) : (A.A N).Rˣ) : (A.A N).R) := by
      rw [← e2, ← map_zpow (Units.map ((m.ρ N).toRingHom : W.R →* (A.A N).R))]
      rfl
    rw [e3, map_inv, e1]
    congr 1
    simp [GFrame.star, GFrame.starOp]
