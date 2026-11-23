import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImageLeClosGen
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS

section Group

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem uh_mul {H A B : Mat k r} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (hB : B ∈ Formalism.QuantumDeterminants.UH H) :
    A * B ∈ Formalism.QuantumDeterminants.UH H := by
  show (A * B)ᴴ * H * (A * B) = H
  have hA' : Aᴴ * H * A = H := hA
  have hB' : Bᴴ * H * B = H := hB
  calc (A * B)ᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [hA', hB']

theorem cay_inv {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) : P * P⁻¹ = 1 ∧ P⁻¹ * P = 1 ∧ (P⁻¹)ᴴ * Pᴴ = 1 := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  refine ⟨h1, Matrix.nonsing_inv_mul P hPu, ?_⟩
  rw [← conjTranspose_mul, h1, conjTranspose_one]

theorem ujset_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {M : Mat k r}
    (hM : M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * M * P⁻¹ ∈ UJset ε := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hM' : Mᴴ * Formalism.QuantumDeterminants.Hpk k r * M = Formalism.QuantumDeterminants.Hpk k r := hM
  show (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = Jm ε
  calc (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = (P⁻¹)ᴴ * (Mᴴ * (Pᴴ * Jm ε * P) * M) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hC, hM', ← hC]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem uh_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {u : Mat k r} (hu : u ∈ UJset ε) :
    P⁻¹ * u * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hu' : uᴴ * Jm ε * u = Jm ε := hu
  show (P⁻¹ * u * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * u * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hC]
  calc (P⁻¹ * u * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * u * P)
      = Pᴴ * (uᴴ * (((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹)) * u) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hu']

end Group

section Per

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Vp : Type*} [NormedAddCommGroup Vp]
  [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem ae_bdata {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hB : IsBData z c u π μW μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := hB.2.2.2.2.1
  have hN := hB.2.2.2.2.2
  have := hW.1
  have := hN.1
  have h1 : (μW.prod μN) ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : (μW.prod μN) (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) = 0 := by
    rw [Measure.prod_prod, hN.2.2.1, mul_zero]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_ofPred_eq, not_and_or] at hp
  rcases hp with hp | hp
  · exact Or.inl ⟨hp, trivial⟩
  · exact Or.inr ⟨trivial, hp⟩

theorem per_congr {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (ψ : Mat k r → ℂ) {F G : Mat k r → ℂ} (hFG : ∀ g ∈ UJset ε, F g = G g)
    (ξ : Vp) {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π F ξ x = per P μW μN ψ π G ξ x := by
  unfold per sInt
  apply integral_congr_ae
  filter_upwards [ae_bdata hB] with p hp
  have hm : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    uh_mul (uh_mul hp.1.1 hp.2.1) hx
  rw [hFG _ (ujset_conj hP hm)]

theorem eabB_zero {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {f : Mat k r → Vp}
    (hf : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = 0) (a b : Fin (2 * r + k + 1)) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : eabB ε P a b f x = 0 := by
  obtain ⟨-, h2, -⟩ := cay_inv hP
  have key : ∀ X, inG ε X → (fun t : ℝ => f (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P)) =
      fun _ => 0 := by
    intro X hX
    funext t
    apply hf
    have : P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P =
        x * (P⁻¹ * NormedSpace.exp ((t : ℂ) • X) * P) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [this]
    exact uh_mul hx (uh_conj hP (exp_smul_mem_UJset hX t))
  unfold eabB S7.EabV S7.EcV S7.RdV
  simp only
  rw [key _ (SmDerA.inG_cpart1 ε _), key _ (SmDerA.inG_cpart2 ε _)]
  simp

theorem per_add {u : Fin k → ℝ} {h : ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h)
    {F G : Mat k r → ℂ} (hFc : ContinuousOn F (UJset ε))
    (hFb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h)) (hGc : ContinuousOn G (UJset ε))
    (hGb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖G g‖ ≤ C * frob g ^ (1 - aExp ε h)) (ξ : Vp) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (F + G) ξ x =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x + per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π G ξ x := by
  have hi := (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hgap).1
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CG, hCG⟩ := hGb
  have iF := hi F CF hFc hCF x hx ξ
  have iG := hi G CG hGc hCG x hx ξ
  unfold per sInt
  rw [← integral_add iF iG]
  congr 1
  funext p
  simp only [Pi.add_apply, add_smul]

theorem per_smul (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (a : ℂ) (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π (a • F) ξ x = a • per P μW μN ψ π F ξ x := by
  unfold per sInt
  rw [← integral_smul]
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

end Per

section Fun

variable {n : ℕ} {ε : Fin n → Bool}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem contOn_of_smooth {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) :
    ContinuousOn F (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F', hU, hg, hF', hEq⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := hF'.continuousOn.continuousAt (hU.mem_nhds hg)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hEq g₀ hg hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg)] with g hg'
  exact hEq g hg'.2 hg'.1

theorem eqOn_unitary_of_toL2_eq {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (hG : IsSmoothL2 ε G)
    (h : toL2 ε F = toL2 ε G) : ∀ g ∈ UJset ε, F g = G g := by
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF.2 []
  have hG2 : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hG.2 []
  unfold toL2 at h
  rw [dif_pos hF2, dif_pos hG2] at h
  have hae := (MemLp.toLp_eq_toLp_iff hF2 hG2).1 h
  have hcF : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hF.1
  have hcG : Continuous (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hG.1
  have heq := (hcF.ae_eq_iff_eq (Formalism.REAL.muG ε) hcG).1 hae
  intro g hg
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  exact congrFun heq y

theorem toL2_congr_on_unitary_bis {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g ∈ UJset ε, F g = G g) :
    toL2 ε F = toL2 ε G := by
  classical
  have hfun : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (unitary_matrix_mem_set ε g)
  have key : ∀ f₁ f₂ : Formalism.REAL.UJ ε → ℂ, f₁ = f₂ →
      (if h : MemLp f₁ 2 (Formalism.REAL.muG ε) then h.toLp f₁ else 0) =
        (if h : MemLp f₂ 2 (Formalism.REAL.muG ε) then h.toLp f₂ else 0) := by
    rintro _ _ rfl; rfl
  exact key _ _ hfun

theorem toL2_add_smooth {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (hG : IsSmoothL2 ε G) :
    toL2 ε (F + G) = toL2 ε F + toL2 ε G := by
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF.2 []
  have hG2 : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hG.2 []
  have hS2 : MemLp (fun g : Formalism.REAL.UJ ε => (F + G) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF2.add hG2
  unfold toL2
  rw [dif_pos hS2, dif_pos hF2, dif_pos hG2]
  exact MemLp.toLp_add hF2 hG2

theorem toL2_smul_smooth (a : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) :
    toL2 ε (a • F) = a • toL2 ε F := by
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF.2 []
  have hS2 : MemLp (fun g : Formalism.REAL.UJ ε => (a • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hF2.const_smul a
  unfold toL2
  rw [dif_pos hS2, dif_pos hF2]
  exact MemLp.toLp_const_smul a hF2

theorem exists_phi {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (T : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (G : Submodule ℂ Y) (hsm : ∀ f ∈ G, IsSmoothL2 ε (T f)) :
    ∃ φ : Y →ₗ[ℂ] smD ε (rreg ε), ∀ f ∈ G, ((φ f : smD ε (rreg ε)) : L2 ε) = toL2 ε (T f) := by
  classical
  obtain ⟨Gc, hGc⟩ := Submodule.exists_isCompl G
  let T0 : G →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨toL2 ε (T f), toL2_mem_smD_of_isSmoothL2 (hsm f f.2)⟩
      map_add' := fun f f' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add]
        exact toL2_add_smooth (hsm f f.2) (hsm f' f'.2)
      map_smul' := fun a f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact toL2_smul_smooth a (hsm f f.2) }
  refine ⟨T0 ∘ₗ Submodule.projectionOnto G Gc hGc, fun f hf => ?_⟩
  have hpr : Submodule.projectionOnto G Gc hGc f = ⟨f, hf⟩ :=
    Submodule.projectionOnto_apply_left hGc ⟨f, hf⟩
  rw [LinearMap.comp_apply, hpr]
  rfl

theorem phi_intertwine {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (A : Fin n → Fin n → Module.End ℂ Y)
    (T : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (G : Submodule ℂ Y) (hsm : ∀ f ∈ G, IsSmoothL2 ε (T f))
    (hGA : ∀ a b, ∀ f ∈ G, A a b f ∈ G)
    (hder : ∀ a b, ∀ f ∈ G, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (T f) g = T (A a b f) g)
    (φ : Y →ₗ[ℂ] smD ε (rreg ε)) (hφ : ∀ f ∈ G, ((φ f : smD ε (rreg ε)) : L2 ε) = toL2 ε (T f)) :
    ∀ a b, ∀ f ∈ G, φ (A a b f) = smE ε (rreg ε) a b (φ f) := by
  intro a b f hf
  apply Subtype.ext
  have h1 : φ f = ⟨toL2 ε (T f), toL2_mem_smD_of_isSmoothL2 (hsm f hf)⟩ := Subtype.ext (hφ f hf)
  rw [hφ _ (hGA a b f hf), h1, rightDerivative_toL2 (hsm f hf)]
  exact (toL2_congr_on_unitary_bis (hder a b f hf)).symm

end Fun

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
