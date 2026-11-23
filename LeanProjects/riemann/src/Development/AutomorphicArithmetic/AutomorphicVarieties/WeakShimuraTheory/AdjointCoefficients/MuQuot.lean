import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ClosureComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at hp
  · exact h.cont.map _ (fun x hx =>
      (res_eq_zero_iff Λ R' _).mp ((res_map f x).trans ((res_eq_zero_iff Λ R x).mpr hx)))
  · rw [PD.map_map]
    convert h.red using 2
    exact RingHom.ext fun x => res_map f x

private theorem lifts_noMu {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) : Φ.noMu.Lifts a c P :=
  ⟨⟨h.pair.mult, h.pair.kill, h.pair.nrm, h.pair.low, h.pair.flag, fun _ _ hs => hs.elim⟩, h.cont, h.red⟩

theorem UpperTheory.V.Ws.X1.muQuot :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.noMu.IsDef a c P' → ∃ (g : R' →ₐ[Λ] R) (e : Φ.ι × Fin 2 → R'), Function.Surjective g ∧ RingHom.ker g = Ideal.span (Set.range e) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd c hres ζ hζ hν R _ _ _ P hP R' _ _ _ P' hP'
  obtain ⟨g, hg, -⟩ := hP'.2 R P (lifts_noMu hP.1)
  have hPψ := (X1.muIff Φ l a hstd c hres ζ hζ hν R P (lifts_noMu hP.1)).mp hP.1
  let e : Φ.ι × Fin 2 → R' := fun p => P'.ψ p.1 (Fin.castLE (by norm_num) p.2) (ζ p.1) - 1
  let I : Ideal R' := Ideal.span (Set.range e)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨v, i⟩, rfl⟩
      have key : ∀ j : Fin 4, g (P'.ψ v j (ζ v)) = P.ψ v j (ζ v) := by
        intro j
        rw [← hg, PD.map_ψ]
        rfl
      fin_cases i
      · simp [e, key, (hPψ v).1]
      · simp [e, key, (hPψ v).2]
    · exact map_zero g
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 := hIg 1 (htop ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let π : R' →ₐ[Λ] R' ⧸ I := Ideal.Quotient.mkₐ Λ I
  haveI : IsCO Λ (R' ⧸ I) := co_quot Λ R' (R' ⧸ I) π (Ideal.Quotient.mkₐ_surjective Λ I)
  have hQn : Φ.noMu.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := lifts_map hP'.1 π
  have hQ : Φ.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := by
    refine (X1.muIff Φ l a hstd c hres ζ hζ hν (R' ⧸ I) _ hQn).mpr (fun v => ⟨?_, ?_⟩)
    · rw [PD.map_ψ]
      have hm : e (v, 0) ∈ I := Ideal.subset_span ⟨(v, 0), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
    · rw [PD.map_ψ]
      have hm : e (v, 1) ∈ I := Ideal.subset_span ⟨(v, 1), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
  obtain ⟨h, hh, -⟩ := hP.2 (R' ⧸ I) _ hQ
  obtain ⟨π', -, huniq⟩ := hP'.2 (R' ⧸ I) _ hQn
  have hhg : h.comp g = π := by
    rw [huniq (h.comp g) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hg, hh]),
      huniq π rfl]
  let gb : R' ⧸ I →ₐ[Λ] R := Ideal.Quotient.liftₐ I g hIg
  obtain ⟨i0, -, huniqP⟩ := hP.2 R P hP.1
  have hgb : gb.comp π = g := by
    ext x
    rfl
  have hid : gb.comp h = AlgHom.id Λ R := by
    rw [huniqP (gb.comp h) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hh, PD.map_map,
        ← AlgHom.comp_toRingHom, hgb, hg]),
      huniqP (AlgHom.id Λ R) (by beta_reduce; rw [← hg, PD.map_map]; rfl)]
  refine ⟨g, e, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective Λ I (h y)
    refine ⟨z, ?_⟩
    have hy := congrArg (fun f : R →ₐ[Λ] R => f y) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
    rw [← hz] at hy
    exact hy
  · apply le_antisymm
    · intro x hx
      have hx' : π x = 0 := by
        rw [← hhg, AlgHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hx'
    · intro x hx
      exact RingHom.mem_ker.mpr (hIg x hx)
