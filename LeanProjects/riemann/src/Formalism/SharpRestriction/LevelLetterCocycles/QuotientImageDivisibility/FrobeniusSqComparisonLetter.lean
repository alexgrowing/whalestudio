import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsInIInPNPowSmulSubMap

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section At

variable (W : LocWach PD LL O v n)

theorem mkQ_mem_map_iff {M : Type} [AddCommGroup M] [Module O M] {K X : Submodule O M}
    (hK : K ≤ X) (z : M) : K.mkQ z ∈ X.map K.mkQ ↔ z ∈ X := by
  rw [← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hK]

theorem cmpD_sub (T : LocLat G Qp LL O) {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x - y) = Formalism.MainNotions.ArcLiftingSetup.cmpD W T x - Formalism.MainNotions.ArcLiftingSetup.cmpD W T y := by
  have h := cmpD_add W T ((W.N T).sub_mem hx hy) hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frobenius_sq_comparison_letter (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :
    φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)) ∈
      DcrisL PD T.ρ (W.emb (c - 1)) := by
  have h0 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T y ∈ DcrisL PD T.ρ (W.emb (c - 1 - 1 - 1)) := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (NDl_N W T hy)]
    exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T _ (NDl_N W T hy) (NDl_DL W T hy).1
  have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ (Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ h0)
  have e : c - 1 - 1 - 1 + 1 + 1 = c - 1 := by ring
  rw [e] at h2
  exact h2

theorem frobenius_sq_mem_lattice_image (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :
    φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)) ∈
      (fun z => φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T (c - 1 - 1 - 1) :=
  ⟨Formalism.MainNotions.ArcLiftingSetup.cmpD W T y, ⟨y, NDl_N W T hy, NDl_DL W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (NDl_N W T hy)⟩, rfl⟩

variable [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]

theorem frobenius_sq_bound_at (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB hh bb η' b' m : ℕ} {cc : ℝ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    (hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ bb • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)))
    (hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η' • W.φD T₂ z ∈ W.N T₂)
    (hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ hh • W.φD T₂ z ∈ W.N T₂)
    (hDc : ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c ∧
      ∃ L kO : ℕ, Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) ⧸
          (Xd W T₂ c kB ⊔ Submodule.span O (↑s : Set (W.DD T₂))).comap
            (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ cc * kO)
    (hDc2 : ∃ s : Finset (W.DD T₂), s.card ≤ m ∧
      (↑s : Set (W.DD T₂)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1) ∧
      ∃ L kO : ℕ, Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)) ⧸
          (Xd W T₂ (c - 1 - 1) hh ⊔ Submodule.span O (↑s : Set (W.DD T₂))).comap
            (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ cc * kO)
    [FiniteDimensional LL ↥(DcrisL PD T₂.ρ (W.emb (c - 1)))]
    (hRk : Module.finrank LL ↥((DcrisL PD T₂.ρ (W.emb (c - 1))).map
      (FilCris PD T₂.ρ (b' : ℤ)).mkQ) ≤ m)
    {k : ℤ}
    (hGc : ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      x ∈ FilCris PD T₂.ρ (b' : ℤ) → (PD.p : LL) ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    {e pad : ℕ} (hexp : (e : ℤ) + hh = pad + k + bb)
    (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (Fs : Submodule O FF) (w : ↥Fs →ₗ[O] W.DD T₂)
    (hw : ∀ f : ↥Fs, w f ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) :
    ∃ (F' : Submodule O FF) (hF' : F' ≤ Fs),
      Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc Fs F' 3 2 ∧
      ∀ f : ↥F', ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
        Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ e) • w (Submodule.inclusion hF' f) - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have φinj := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_inj (PD := PD) T₂
  have hwN : ∀ f, w f ∈ W.N T₂ := fun f => NDl_N W T₂ (hw f)

  set K5 := Kc W T₂ c with hK5def
  have hK5 := Kc_le W T₂ c kB h3₂ hmod₂ hR
  set ψ5 : ↥Fs →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) ⧸ K5 :=
    K5.mkQ ∘ₗ LinearMap.codRestrict (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) w hw with hψ5
  obtain ⟨s5, hs5, hs5N, L5, kO5, hL5, hkO5, hLc5⟩ := hDc
  have ch5 := pchain_DN W T₂ c kB K5 hK5 s5 hs5 hs5N L5 kO5 hL5 hkO5 hLc5 Fs ψ5
  set F5 := kerSub Fs ψ5 (((Xd W T₂ c kB).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).subtype).map K5.mkQ)
  have hF5 : F5 ≤ Fs := kerSub_le _ _ _
  have mem5 : ∀ f : ↥F5, w ⟨f, hF5 f.2⟩ ∈ Xd W T₂ c kB := by
    intro f
    have h := (mem_kerSub_coe Fs ψ5 _ ⟨f, hF5 f.2⟩).1 f.2
    exact (mkQ_mem_map_iff hK5 _).1 h
  have ex1 : ∀ f : ↥F5, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1),
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (w ⟨f, hF5 f.2⟩) =
        (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_of_mem_X W T₂ hs hR h3₂ hM₂ (mem5 f)
  choose y1 hy1 e1 using ex1
  have ex2 : ∀ f : ↥F5, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
      (PD.p : LL) ^ bb • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) =
        φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_up W T₂ hs h3₂ hmod₂ hU hMη (hy1 f)
  choose y2 hy2 e2 using ex2
  have hy1N : ∀ f, y1 f ∈ W.N T₂ := fun f => NDl_N W T₂ (hy1 f)
  have hy2N : ∀ f, y2 f ∈ W.N T₂ := fun f => NDl_N W T₂ (hy2 f)
  have add1 : ∀ f g : ↥F5, Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 (f + g)) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 g) := by
    intro f g
    apply φinj
    apply smul_right_injective _ (pow_ne_zero kB hp)
    have hwa : w ⟨((f + g : ↥F5) : FF), hF5 (f + g).2⟩ = w ⟨f, hF5 f.2⟩ + w ⟨g, hF5 g.2⟩ := by
      rw [← map_add]; rfl
    simp only
    rw [← e1 (f + g), hwa, cmpD_add W T₂ (hwN _) (hwN _), e1 f, e1 g, map_add, smul_add]
  have smul1 : ∀ (o : O) (f : ↥F5), Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 (o • f)) =
      algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) := by
    intro o f
    apply φinj
    apply smul_right_injective _ (pow_ne_zero kB hp)
    have hwa : w ⟨((o • f : ↥F5) : FF), hF5 (o • f).2⟩ = o • w ⟨f, hF5 f.2⟩ := by
      rw [← map_smul]; rfl
    simp only
    rw [← e1 (o • f), hwa, cmpD_osmul W T₂ o (hwN _), e1 f, map_smul, smul_comm]
  have add2 : ∀ f g : ↥F5, Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (f + g)) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 g) := by
    intro f g
    apply φinj
    rw [map_add, ← e2, ← e2, ← e2, add1, smul_add]
  have smul2 : ∀ (o : O) (f : ↥F5), Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (o • f)) =
      algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f) := by
    intro o f
    apply φinj
    rw [map_smul, ← e2, ← e2, smul1, smul_comm]

  set K6 := Kc W T₂ (c - 1 - 1) with hK6def
  have hK6 := Kc_le W T₂ (c - 1 - 1) hh h3₂ hmod₂ hR
  let ψ6 : ↥F5 →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)) ⧸ K6 :=
    { toFun := fun f => K6.mkQ ⟨y2 f, hy2 f⟩
      map_add' := fun f g => by
        rw [← map_add]
        apply (Submodule.Quotient.eq _).2
        show Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (f + g) - (y2 f + y2 g)) = 0
        rw [cmpD_sub W T₂ (hy2N _) ((W.N T₂).add_mem (hy2N _) (hy2N _)),
          cmpD_add W T₂ (hy2N _) (hy2N _), add2, sub_self]
      map_smul' := fun o f => by
        rw [RingHom.id_apply, ← map_smul]
        apply (Submodule.Quotient.eq _).2
        show Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (o • f) - o • y2 f) = 0
        have hoN : o • y2 f ∈ W.N T₂ := by
          rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ (hy2N f)
        rw [cmpD_sub W T₂ (hy2N _) hoN, cmpD_osmul W T₂ o (hy2N f), smul2, sub_self] }
  obtain ⟨s6, hs6, hs6N, L6, kO6, hL6, hkO6, hLc6⟩ := hDc2
  have ch6 := pchain_DN W T₂ (c - 1 - 1) hh K6 hK6 s6 hs6 hs6N L6 kO6 hL6 hkO6 hLc6 F5 ψ6
  set F6 := kerSub F5 ψ6
    (((Xd W T₂ (c - 1 - 1) hh).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)).subtype).map K6.mkQ)
  have hF6 : F6 ≤ F5 := kerSub_le _ _ _
  have mem6 : ∀ f : ↥F6, y2 ⟨f, hF6 f.2⟩ ∈ Xd W T₂ (c - 1 - 1) hh := by
    intro f
    have h := (mem_kerSub_coe F5 ψ6 _ ⟨f, hF6 f.2⟩).1 f.2
    exact (mkQ_mem_map_iff hK6 _).1 h
  have ex3 : ∀ f : ↥F6, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1 - 1),
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 ⟨f, hF6 f.2⟩) =
        (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_of_mem_X W T₂ hs hR h3₂ hM₂' (mem6 f)
  choose y3 hy3 e3 using ex3
  set ell : ↥F6 → T₂.V ⊗[Qp] B := fun f =>
    φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f)))
    with hell
  have add3 : ∀ f g : ↥F6, ell (f + g) = ell f + ell g := by
    intro f g
    have h : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 (f + g)) =
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 g) := by
      apply φinj
      apply smul_right_injective _ (pow_ne_zero hh hp)
      have h5 : (⟨((f + g : ↥F6) : FF), hF6 (f + g).2⟩ : ↥F5) = ⟨f, hF6 f.2⟩ + ⟨g, hF6 g.2⟩ := rfl
      simp only
      rw [← e3 (f + g), h5, add2, e3 f, e3 g, map_add, smul_add]
    simp only [hell, h, map_add]
  have smul3 : ∀ (o : O) (f : ↥F6), ell (o • f) = algebraMap O LL o • ell f := by
    intro o f
    have h : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 (o • f)) = algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f) := by
      apply φinj
      apply smul_right_injective _ (pow_ne_zero hh hp)
      have h5 : (⟨((o • f : ↥F6) : FF), hF6 (o • f).2⟩ : ↥F5) = o • ⟨f, hF6 f.2⟩ := rfl
      simp only
      rw [← e3 (o • f), h5, smul2, e3 f, map_smul, smul_comm]
    simp only [hell, h, map_smul]

  let ψ7 : ↥F6 →+ (T₂.V ⊗[Qp] B) ⧸ FilCris PD T₂.ρ (b' : ℤ) :=
    { toFun := fun f => (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell f)
      map_zero' := by
        have h := add3 0 0
        rw [add_zero] at h
        have h0 : ell 0 = 0 := by
          have := congrArg (fun z => z - ell 0) h
          simpa using this.symm
        rw [h0, map_zero]
      map_add' := fun f g => by rw [add3, map_add] }
  have hψ7 : ∀ (o : O) (x : ↥F6), ψ7 (o • x) = algebraMap O LL o • ψ7 x := by
    intro o x
    show (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell (o • x)) =
      algebraMap O LL o • (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell x)
    rw [smul3, map_smul]
  have hletter : ∀ f : ↥F6, ell f ∈ DcrisL PD T₂.ρ (W.emb (c - 1)) := fun f =>
    frobenius_sq_comparison_letter W T₂ c (hy3 f)
  have hrank : Module.finrank LL ↥(Submodule.span LL (Set.range ψ7)) ≤ m := by
    have hsub : Submodule.span LL (Set.range ψ7) ≤
        (DcrisL PD T₂.ρ (W.emb (c - 1))).map (FilCris PD T₂.ρ (b' : ℤ)).mkQ := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact ⟨ell f, hletter f, rfl⟩
    exact (Submodule.finrank_mono hsub).trans hRk
  have ch7 := pchain_of_gen (pstep_rank (lenO := lenOl PD (O := O)) (m := m) (c := cc) F6 ψ7 hψ7 hrank)
  set F7 := zeroSub F6 ψ7 hψ7
  have hF7 : F7 ≤ F6 := zeroSub_le _ _ _
  have chain : Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc Fs F7 3 2 :=
    ((ch5.trans ch6).trans ch7).mono (by norm_num) (by norm_num)
  refine ⟨F7, chain.le, chain, fun f => ?_⟩
  set f6 : ↥F6 := ⟨f, hF7 f.2⟩
  set f5 : ↥F5 := ⟨f, hF6 (hF7 f.2)⟩
  have hz : ψ7 f6 = 0 := (mem_zeroSub_coe F6 ψ7 hψ7 f6).1 f.2
  have hFil : ell f6 ∈ FilCris PD T₂.ρ (b' : ℤ) := (Submodule.Quotient.mk_eq_zero _).1 hz
  have hG := hGc (ell f6) (frobenius_sq_mem_lattice_image W T₂ c (hy3 f6)) hFil
  have hy : w ⟨f, hF5 f5.2⟩ ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c := hw _
  obtain ⟨x, hx1, hx2⟩ := exists_inI_inPN_pow_smul_sub_map W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hy
    (d1 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f5)) (d2 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f5))
    (d3 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f6)) (s₁ := 0) (s₂ := 0)
    (by rw [pow_zero, one_smul]; exact e1 f5) (e2 f5) (by rw [pow_zero, one_smul]; exact e3 f6) hG hexp
  refine ⟨x, hx1, ?_⟩
  have hxe : ((PD.p : O) ^ (e + 0 + 0)) = (PD.p : O) ^ e := by simp
  rw [hxe] at hx2
  exact hx2

end At

end Formalism.MainNotions.N.Pv.LocalLengthBound
