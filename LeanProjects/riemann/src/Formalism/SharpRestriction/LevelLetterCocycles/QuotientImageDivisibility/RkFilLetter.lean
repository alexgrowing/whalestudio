import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkDcrisLSumZero

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

section Jmp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem rk_fil_map (hK : Function.Bijective (algebraMap K₀ K)) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (hon : F.Onto) (a : ℤ) :
    (FilCris PD T₁.ρ a).map (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f) = FilCris PD T₂.ρ a ∧
      (Dcris PD T₁.ρ).map (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f) = Dcris PD T₂.ρ := by

  have hsurj : Function.Surjective F.f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← T₂.L.span, Submodule.span_le]
    intro y hy
    obtain ⟨x, -, hx⟩ := hon y hy
    exact LinearMap.mem_range.mpr ⟨x, hx⟩

  let ρ₀ : Representation LL G (LinearMap.ker F.f) :=
    { toFun := fun g => (T₁.ρ g).restrict (p := LinearMap.ker F.f) (q := LinearMap.ker F.f)
        (fun x hx => by
          rw [LinearMap.mem_ker] at hx ⊢
          rw [F.equiv, hx, map_zero])
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp [LinearMap.restrict_apply])
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by
        simp [LinearMap.restrict_apply, Module.End.mul_apply]) }
  have hι : ∀ g x, (LinearMap.ker F.f).subtype (ρ₀ g x) = T₁.ρ g ((LinearMap.ker F.f).subtype x) :=
    fun g x => rfl
  have hcr := hC (LinearMap.ker F.f) ρ₀ T₁.V T₁.ρ T₂.V T₂.ρ (LinearMap.ker F.f).subtype F.f hι
    F.equiv (Submodule.injective_subtype _) hsurj (Submodule.range_subtype _).symm h1
  have H := hE hK (LinearMap.ker F.f) ρ₀ T₁.V T₁.ρ T₂.V T₂.ρ (LinearMap.ker F.f).subtype F.f hι
    F.equiv (Submodule.injective_subtype _) hsurj (Submodule.range_subtype _).symm hcr.1 h1 h2
  exact ⟨(H.2.2.2 a).1, H.2.2.1⟩

variable [NeZero n] (W : LocWach PD LL O v n)

private theorem mulVB_add {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] (c c' : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (c + c') x =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x +
        mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [mulVB, add_mul, TensorProduct.tmul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

private theorem mulVB_smul {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] (q : Qp) (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (q • c) x =
      q • mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x := by
  have hq : algebraMap K₀ B (q • c) = q • algebraMap K₀ B c := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply Qp K₀ B q, Algebra.smul_def]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b =>
    simp only [mulVB, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply, hq, smul_mul_assoc, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

private theorem mulVB_mul {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] (d c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) d
        (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (d * c) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [mulVB, map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

private theorem exists_linear_tensor_action_mulVB {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] (x : V ⊗[Qp] B) :
    ∃ A : LL ⊗[Qp] K₀ →ₗ[LL] V ⊗[Qp] B, ∀ (l : LL) (c : K₀),
      A (l ⊗ₜ c) = l • mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x := by
  let φ : K₀ →ₗ[Qp] V ⊗[Qp] B :=
    { toFun := fun c => mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x
      map_add' := fun c c' => mulVB_add c c' x
      map_smul' := fun q c => mulVB_smul q c x }
  exact ⟨TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton LL _ φ),
    fun l c => by simp [φ]⟩

private theorem exists_emb_idempotent_projection (i : ZMod n) :
    ∃ (e : LL ⊗[Qp] K₀) (Li : LL ⊗[Qp] K₀ →ₗ[LL] LL),
      (∀ (l : LL) (c : K₀), Li (l ⊗ₜ c) = l * W.emb i c) ∧ Li e = 1 ∧
      ∀ d : K₀, (1 ⊗ₜ[Qp] d) * e = W.emb i d • e := by
  haveI := PD.finK₀
  classical
  obtain ⟨L, hL⟩ : ∃ L : ZMod n → (LL ⊗[Qp] K₀ →ₐ[LL] LL),
      ∀ k (l : LL) (c : K₀), L k (l ⊗ₜ c) = l * W.emb k c :=
    ⟨fun k => Algebra.TensorProduct.lift (Algebra.ofId LL LL) (W.emb k)
      (fun _ _ => Commute.all _ _), fun k l c => by simp⟩
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : LL ⊗[Qp] K₀ →ₗ[LL] (ZMod n → LL), ∀ z k, Θ z k = L k z :=
    ⟨LinearMap.pi (fun k => (L k).toLinearMap), fun _ _ => rfl⟩
  have hind : ∀ g : ZMod n → LL, (∀ c : K₀, ∑ k, W.emb k c * g k = 0) → ∀ k, g k = 0 := by
    intro g hg
    have hli := (linearIndependent_monoidHom K₀ LL).comp
      (fun k => ((W.emb k : K₀ →+* LL) : K₀ →* LL)) (by
        intro k k' h
        apply W.emb_bij.1
        ext c
        exact DFunLike.congr_fun h c)
    refine Fintype.linearIndependent_iff.1 hli g ?_
    funext c
    simpa [Finset.sum_apply, mul_comm] using hg c
  have hsurj : Function.Surjective Θ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hg := hind (fun k => f (fun j => if k = j then 1 else 0)) (by
      intro c
      have hmem : Θ (1 ⊗ₜ c) ∈ LinearMap.ker f := hle (LinearMap.mem_range_self _ _)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ f] at hmem
      simpa [hΘ, hL] using hmem)
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    simp [hg]
  have hrank : Module.finrank LL (LL ⊗[Qp] K₀) = Module.finrank LL (ZMod n → LL) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, ZMod.card]
    exact W.n_eq.symm
  have hinj : Function.Injective Θ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hsurj
  obtain ⟨e, he⟩ := hsurj (fun k => if k = i then 1 else 0)
  have hek : ∀ k, L k e = if k = i then 1 else 0 := fun k => by rw [← hΘ, he]
  refine ⟨e, (L i).toLinearMap, fun l c => hL i l c, by simpa using hek i, fun d => hinj ?_⟩
  funext k
  rw [hΘ, hΘ, map_mul, map_smul, hL, hek, one_mul]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem rk_fil_letter (hK : Function.Bijective (algebraMap K₀ K)) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ)
    (hon : F.Onto) (i : ZMod n) (a : ℤ) :
    (FilCris PD T₁.ρ a ⊓ DcrisL PD T₁.ρ (W.emb i)).map (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f) =
      FilCris PD T₂.ρ a ⊓ DcrisL PD T₂.ρ (W.emb i) := by
  obtain ⟨hF, -⟩ := rk_fil_map hK hE hC F h1 h2 hon a
  obtain ⟨e, Li, hLi, hLe, he⟩ := exists_emb_idempotent_projection W i
  have hFD : ∀ (T : LocLat G Qp LL O) (b : ℤ), FilCris PD T.ρ b ≤ Dcris PD T.ρ := by
    intro T b
    unfold FilCris
    exact inf_le_left
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzF, hzL⟩ := Submodule.mem_inf.1 hz
    rw [rk_mem_DcrisL] at hzL
    have hz2 : Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f z ∈ FilCris PD T₂.ρ a := by
      rw [← hF]; exact Submodule.mem_map_of_mem hzF
    refine Submodule.mem_inf.2 ⟨hz2, ?_⟩
    rw [rk_mem_DcrisL]
    refine ⟨hFD T₂ a hz2, fun d => ?_⟩
    rw [← rk_mapVB_mulVB, hzL.2 d, map_smul]
  · intro y hy
    obtain ⟨hyF, hyL⟩ := Submodule.mem_inf.1 hy
    rw [rk_mem_DcrisL] at hyL
    rw [← hF] at hyF
    obtain ⟨x, hx, rfl⟩ := hyF
    obtain ⟨A₁, hA₁⟩ := exists_linear_tensor_action_mulVB (LL := LL) (K₀ := K₀) (B := B) x
    obtain ⟨A₂, hA₂⟩ := exists_linear_tensor_action_mulVB (LL := LL) (K₀ := K₀) (B := B) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f x)
    have hmap : ∀ z, Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f (A₁ z) = A₂ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l c => rw [hA₁, hA₂, map_smul, rk_mapVB_mulVB]
      | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
    have hA₂e : ∀ z, A₂ z = Li z • Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f x := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l c => rw [hA₂, hLi, hyL.2 c, smul_smul]
      | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_smul]
    have hmulA : ∀ (d : K₀) z, mulVB (K₀ := K₀) (B := B) (LL := LL) d (A₁ z) = A₁ ((1 ⊗ₜ d) * z) := by
      intro d z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hA₁, hA₁, map_smul, mulVB_mul]
      | add z z' hz hz' => rw [map_add, map_add, hz, hz', mul_add, map_add]
    have hFA : ∀ z, A₁ z ∈ FilCris PD T₁.ρ a := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l c => rw [hA₁]; exact Submodule.smul_mem _ _ (rk_mulVB_FilCris (PD := PD) (ρ := T₁.ρ) c a hx)
      | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'
    refine ⟨A₁ e, Submodule.mem_inf.2 ⟨hFA e, ?_⟩, ?_⟩
    · rw [rk_mem_DcrisL]
      refine ⟨hFD T₁ a (hFA e), fun d => ?_⟩
      rw [hmulA, he, map_smul]
    · rw [hmap, hA₂e, hLe, one_smul]

theorem rk_jump_of (hK : Function.Bijective (algebraMap K₀ K)) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ)
    (hon : F.Onto) (τ : K →ₐ[Qp] LL) (i : ZMod n)
    (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i) (a : ℤ)
    (hj : IsJumpV PD T₂.ρ τ a) : IsJumpV PD T₁.ρ τ a := by

  have e : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ b : ℤ, FildR PD T.ρ τ b =
      (FilCris PD T.ρ b ⊓ DcrisL PD T.ρ (W.emb i)).map (ιV PD (LL := LL) (V := T.V)) := by
    intro T hT b
    rw [← hτ]
    exact ((hQ hK T.V T.ρ hT).2 τ).2.2 b

  have hnat : (ιV PD (LL := LL) (V := T₂.V)).comp (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL F.f) =
      (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := BdR) LL F.f).comp (ιV PD (LL := LL) (V := T₁.V)) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB, ιV]
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  have key : ∀ b : ℤ, FildR PD T₂.ρ τ b =
      (FildR PD T₁.ρ τ b).map (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := BdR) LL F.f) := by
    intro b
    rw [e T₂ h2 b, ← rk_fil_letter W hK hE hC hQ F h1 h2 hon i b, ← Submodule.map_comp, hnat,
      Submodule.map_comp, ← e T₁ h1 b]
  unfold IsJumpV at hj ⊢
  intro h
  apply hj
  rw [key (a + 1), key a, h]

end Jmp

end Formalism.MainNotions.N.Pv.LocalLengthBound
