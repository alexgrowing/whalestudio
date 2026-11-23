import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem jointEig {ι V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) (c : ι → ℂ) (hc : ∀ i j, Commute (f i) (f j))
    (h : (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ≠ ⊥) :
    ∃ y, y ≠ 0 ∧ ∀ i, f i y = c i • y := by
  classical
  have hcN : ∀ i j, Commute (f i) (f j - c j • (1 : Module.End ℂ V)) := fun i j =>
    (hc i j).sub_right ((Commute.one_right _).smul_right _)
  have hW_inv : ∀ i, ∀ u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V),
      f i u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) := by
    intro i u hu
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hu ⊢
    intro j
    obtain ⟨k, hk⟩ := hu j
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← ((hcN i j).pow_right k).eq, Module.End.mul_apply, hk, map_zero]
  have hex : ∃ n, ∃ U : Submodule ℂ V, U ≠ ⊥ ∧
      U ≤ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ∧
      (∀ i, ∀ u ∈ U, f i u ∈ U) ∧ Module.finrank ℂ U = n :=
    ⟨_, _, h, le_rfl, hW_inv, rfl⟩
  obtain ⟨U, hU0, hUW, hUinv, hUn⟩ := Nat.find_spec hex
  have hker : ∀ i, ∀ u ∈ U, f i u = c i • u := by
    intro i
    have hNU : ∀ m : ℕ, ∀ u ∈ U, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ∈ U := by
      intro m
      induction m with
      | zero => intro u hu; simpa using hu
      | succ m ih =>
        intro u hu
        rw [pow_succ', Module.End.mul_apply]
        have hv := ih u hu
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact U.sub_mem (hUinv i _ hv) (U.smul_mem _ hv)
    let K : Submodule ℂ V := U ⊓ LinearMap.ker (f i - c i • (1 : Module.End ℂ V))
    have hKinv : ∀ j, ∀ u ∈ K, f j u ∈ K := by
      intro j u hu
      refine ⟨hUinv j u hu.1, ?_⟩
      have h2 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu.2
      show (f i - c i • (1 : Module.End ℂ V)) (f j u) = 0
      rw [← Module.End.mul_apply, ← (hcN j i).eq, Module.End.mul_apply, h2, map_zero]
    have hK0 : K ≠ ⊥ := by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hexk : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 :=
        (Module.End.mem_iInf_maxGenEigenspace_iff f c u).mp (hUW huU) i
      obtain ⟨k, hk, hkmin⟩ : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 ∧
          ∀ m < k, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ≠ 0 :=
        ⟨Nat.find hexk, Nat.find_spec hexk, fun m hm => Nat.find_min hexk hm⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        exact hu0 hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      refine (Submodule.ne_bot_iff K).mpr ⟨((f i - c i • (1 : Module.End ℂ V)) ^ m) u,
        ⟨hNU m u huU, ?_⟩, hkmin m (Nat.lt_succ_self m)⟩
      show (f i - c i • (1 : Module.End ℂ V)) (((f i - c i • (1 : Module.End ℂ V)) ^ m) u) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk
    have hle : Nat.find hex ≤ Module.finrank ℂ K :=
      Nat.find_min' hex ⟨K, hK0, le_trans inf_le_left hUW, hKinv, rfl⟩
    have hKU : K = U := Submodule.eq_of_le_of_finrank_eq inf_le_left
      (le_antisymm (Submodule.finrank_mono inf_le_left) (hUn ▸ hle))
    intro u hu
    have hu' : u ∈ K := hKU ▸ hu
    have h3 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu'.2
    simpa [sub_eq_zero] using h3
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨y, hy0, fun i => hker i y hyU⟩

theorem UpperTheory.Gal.Join.subQuot :
    UpperTheory.Gal.Join.SubQuot := by
  intro T X _ _ _ _ ρ μ
  have hc : ∀ s t : T, Commute (ρ s) (ρ t) := fun s t => by
    show ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  have iff1 : (∃ y, y ≠ 0 ∧ ∀ t : T, ρ t y = (μ t : ℂ) • y) ↔
      (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥ := by
    constructor
    · rintro ⟨y, hy0, hy⟩
      refine (Submodule.ne_bot_iff _).mpr ⟨y, ?_, hy0⟩
      rw [Module.End.mem_iInf_maxGenEigenspace_iff]
      intro t
      refine ⟨1, ?_⟩
      simp [hy t]
    · intro h
      exact jointEig (fun t => ρ t) (fun t => (μ t : ℂ)) hc h
  refine ⟨iff1, fun hy => ?_⟩
  have hWne := iff1.mp hy
  let c : T → ℂ := fun t => (μ t : ℂ)
  let Wχ : (T → ℂ) → Submodule ℂ X := fun χ => ⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t)
  let S : Submodule ℂ X := ⨆ χ ∈ {χ : T → ℂ | χ ≠ c}, Wχ χ
  have hind : iSupIndep Wχ :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo _
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hdisj : Disjoint (Wχ c) S := hind.disjoint_biSup (fun h => h rfl)
  have htop : Wχ c ⊔ S = ⊤ := by
    have h1 : ⨆ χ : T → ℂ, Wχ χ = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
        (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
        (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
    refine eq_top_iff.mpr (h1.symm.le.trans (iSup_le fun χ => ?_))
    by_cases hχ : χ = c
    · subst hχ; exact le_sup_left
    · exact le_sup_of_le_right (le_biSup Wχ (show χ ∈ {χ : T → ℂ | χ ≠ c} from hχ))
  have hWinv : ∀ χ t, ∀ x ∈ Wχ χ, ρ t x ∈ Wχ χ := by
    intro χ t x hx
    simp only [Wχ, Submodule.mem_iInf] at hx ⊢
    intro s
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc s t) (χ s) (hx s)
  have hSinv : ∀ t, ∀ x ∈ S, ρ t x ∈ S := by
    intro t
    have : S ≤ S.comap (ρ t) := iSup₂_le fun χ hχ x hx =>
      (le_biSup Wχ hχ) (hWinv χ t x hx)
    exact fun x hx => this hx
  have hNS : ∀ t (k : ℕ), ∀ x ∈ S, ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) x ∈ S := by
    intro t k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      have hv := ih x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact S.sub_mem (hSinv t _ hv) (S.smul_mem _ hv)
  have hSlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hS => hWne ?_
    have : Disjoint (Wχ c) ⊤ := hS ▸ hdisj
    exact disjoint_top.mp this
  obtain ⟨l0, hl00, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hSlt inferInstance
  let g : T → Module.End ℂ (Module.Dual ℂ X) := fun t => Module.Dual.transpose (R := ℂ) (ρ t)
  have hg : ∀ s t, Commute (g s) (g t) := by
    intro s t
    show g s * g t = g t * g s
    ext φ x
    simp only [Module.End.mul_apply, g, Module.Dual.transpose_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hc t s).eq, Module.End.mul_apply]
  have hpow : ∀ t (k : ℕ) (φ : Module.Dual ℂ X),
      ((g t - c t • (1 : Module.End ℂ (Module.Dual ℂ X))) ^ k) φ =
        φ ∘ₗ ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) := by
    intro t k
    induction k with
    | zero => intro φ; ext x; simp
    | succ k ih =>
      intro φ
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ]
      ext x
      simp [g, Module.Dual.transpose_apply, Module.End.mul_apply, smul_eq_mul]
  obtain ⟨l, hl0, hl⟩ := jointEig g c hg (by
    refine (Submodule.ne_bot_iff _).mpr ⟨l0, ?_, hl00⟩
    rw [Module.End.mem_iInf_maxGenEigenspace_iff]
    intro t
    refine ⟨Module.finrank ℂ X, ?_⟩
    rw [hpow]
    ext x
    have hx : x ∈ Wχ c ⊔ S := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hw' : w ∈ Module.End.maxGenEigenspace (ρ t) (c t) :=
      (Submodule.mem_iInf _).mp hw t
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hw'
    have hs' : l0 (((ρ t - c t • (1 : Module.End ℂ X)) ^ Module.finrank ℂ X) s) = 0 := by
      have hm := Submodule.mem_map_of_mem (f := l0) (hNS t (Module.finrank ℂ X) s hs)
      rw [hmap] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    simp only [LinearMap.comp_apply, map_add, hw', map_zero, zero_add, LinearMap.zero_apply]
    exact hs')
  refine ⟨l, hl0, fun t y => ?_⟩
  have := congrArg (fun φ : Module.Dual ℂ X => φ y) (hl t)
  simpa [g, Module.Dual.transpose_apply, smul_eq_mul] using this
